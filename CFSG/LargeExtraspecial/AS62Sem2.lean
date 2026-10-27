module

public import CFSG.LargeExtraspecial.AS62Sem
public import CFSG.LargeExtraspecial.AS62SemData2
public import Mathlib.GroupTheory.PresentedGroup

public section

namespace CFSG.LargeExtraspecial.AS62

open Sem

namespace Sem

variable {G : Type*} [Group G] {α : Type*} {rels : Set (FreeGroup α)} {f : α → G}

theorem toGroup_mk (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (w : FreeGroup α) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels w) = FreeGroup.lift f w :=
  rfl

theorem toGroup_mem (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) {K : Subgroup G}
    (hK : ∀ i, f i ∈ K) (x : PresentedGroup rels) : PresentedGroup.toGroup h x ∈ K :=
  PresentedGroup.generated_by rels (K.comap (PresentedGroup.toGroup h))
    (fun j => by simpa only [Subgroup.mem_comap, PresentedGroup.toGroup.of] using hK j) x

@[expose] def toSubgroup (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (K : Subgroup G)
    (hK : ∀ i, f i ∈ K) : PresentedGroup rels →* K :=
  (PresentedGroup.toGroup h).codRestrict K (toGroup_mem h hK)

theorem coe_toSubgroup (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (K : Subgroup G)
    (hK : ∀ i, f i ∈ K) (y : PresentedGroup rels) :
    (toSubgroup h K hK y : G) = PresentedGroup.toGroup h y :=
  rfl

theorem toSubgroup_of (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (K : Subgroup G)
    (hK : ∀ i, f i ∈ K) (i : α) : toSubgroup h K hK (PresentedGroup.of i) = ⟨f i, hK i⟩ :=
  Subtype.ext (PresentedGroup.toGroup.of h)

theorem le_card_of_injective (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (K : Subgroup G) [Finite K]
    (hK : ∀ i, f i ∈ K) {N : ℕ} (word : Fin N → List (α × Bool))
    (hinj : Function.Injective fun k => FreeGroup.lift f (FreeGroup.mk (word k))) :
    N ≤ Nat.card K := by
  have hg : Function.Injective fun k =>
      toSubgroup h K hK (PresentedGroup.mk rels (FreeGroup.mk (word k))) :=
    fun _ _ hkk => hinj (congrArg Subtype.val hkk)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ hg

theorem toSubgroup_surjective (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (K : Subgroup G)
    [Finite K] (hK : ∀ i, f i ∈ K) {N : ℕ} (word : Fin N → List (α × Bool))
    (hinj : Function.Injective fun k => FreeGroup.lift f (FreeGroup.mk (word k)))
    (hcard : Nat.card K ≤ N) : Function.Surjective (toSubgroup h K hK) := by
  have hg : Function.Injective fun k =>
      toSubgroup h K hK (PresentedGroup.mk rels (FreeGroup.mk (word k))) :=
    fun _ _ hkk => hinj (congrArg Subtype.val hkk)
  have hbij := hg.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact hcard)
  intro y
  obtain ⟨k, rfl⟩ := hbij.2 y
  exact ⟨_, rfl⟩

theorem toSubgroup_bijective (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (K : Subgroup G)
    [Finite K] (hK : ∀ i, f i ∈ K) {N : ℕ} (word : Fin N → List (α × Bool))
    (hinj : Function.Injective fun k => FreeGroup.lift f (FreeGroup.mk (word k)))
    (hcard : Nat.card K ≤ N) [Finite (PresentedGroup rels)]
    (hPG : Nat.card (PresentedGroup rels) ≤ N) : Function.Bijective (toSubgroup h K hK) :=
  (toSubgroup_surjective h K hK word hinj hcard).bijective_of_nat_card_le
    (hPG.trans (le_card_of_injective h K hK word hinj))

end Sem

namespace Frame

variable {G : Type*} [Group G] (F : Frame G)

instance finite_A : Finite F.A := Finite.of_injective F.σ F.σ_injective

theorem finite_H : Finite F.H := by
  have hsub : (F.H : Set G) ⊆ Set.range fun p : Fin 16 × F.A => F.vOf p.1.val * p.2 := by
    intro h hh
    obtain ⟨⟨c, q⟩, hc, a, -, rfl⟩ := F.rep_exists hh
    exact ⟨(⟨c, hc⟩, a), rfl⟩
  exact ((Set.finite_range _).subset hsub).to_subtype

theorem rep_zD : F.Rep (F.zz 0) zD := F.rep_zz 0

theorem rep_tD : F.Rep (F.zz 1) tD := F.rep_zz 1

theorem rep_A_iff (a : F.A) (q : ℕ) : F.Rep a (0, q) ↔ permCode (F.σ a) = q :=
  ⟨fun h => congrArg Prod.snd (F.rep_unique (F.rep_A a) h), fun h => h ▸ F.rep_A a⟩

theorem exists_σ_eq {p : Equiv.Perm (Fin 5)} (hp : p ∈ alternatingGroup (Fin 5)) :
    ∃ a : F.A, F.σ a = p := by
  rw [← F.σ_range] at hp
  exact hp

theorem exists_rep_of_perm {p : Equiv.Perm (Fin 5)} (hp : p ∈ alternatingGroup (Fin 5)) :
    ∃ a ∈ F.A, F.Rep a (0, permCode p) := by
  obtain ⟨a, rfl⟩ := F.exists_σ_eq hp
  exact ⟨a, a.2, F.rep_A a⟩

theorem mem_alternatingGroup_swap_mul_swap {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  rfl

theorem exists_rep_eD : ∃ e ∈ F.A, F.Rep e eD :=
  F.exists_rep_of_perm (p := Equiv.swap 1 2 * Equiv.swap 3 4)
    (mem_alternatingGroup_swap_mul_swap (by decide) (by decide))

theorem exists_rep_xD : ∃ x ∈ F.A, F.Rep x xD :=
  F.exists_rep_of_perm (p := Equiv.swap 2 3 * Equiv.swap 3 4)
    (mem_alternatingGroup_swap_mul_swap (by decide) (by decide))

theorem exists_rep_sD : ∃ s ∈ F.A, F.Rep s sD :=
  F.exists_rep_of_perm (p := Equiv.swap 0 1 * Equiv.swap 2 3)
    (mem_alternatingGroup_swap_mul_swap (by decide) (by decide))

variable {z t e x s : G}

theorem rep_gensB (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) :
    ∀ i, F.Rep (![z, t, e, x] i) (gdB i) := by
  intro i
  fin_cases i
  · exact hz
  · exact ht
  · exact he
  · exact hx

theorem rep_gens2 (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (hs : F.Rep s sD) : ∀ i, F.Rep (![z, t, e, x, s] i) (gd2 i) := by
  intro i
  fin_cases i
  · exact hz
  · exact ht
  · exact he
  · exact hx
  · exact hs

theorem lift_relsB_eq_one (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) : ∀ r ∈ relsB, FreeGroup.lift ![z, t, e, x] (FreeGroup.mk r) = 1 :=
  fun r hr => F.lift_eq_one_of_semEval (F.rep_gensB hz ht he hx) (semEval_relsB r hr)

theorem lift_rels2_eq_one (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) (hs : F.Rep s sD) :
    ∀ r ∈ rels2, FreeGroup.lift ![z, t, e, x, s] (FreeGroup.mk r) = 1 :=
  fun r hr => F.lift_eq_one_of_semEval (F.rep_gens2 hz ht he hx hs) (semEval_rels2 r hr)

theorem relsB_hold (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) :
    ∀ r ∈ {r : FreeGroup (Fin 4) | r ∈ relsB.map FreeGroup.mk},
      FreeGroup.lift ![z, t, e, x] r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact F.lift_relsB_eq_one hz ht he hx w hw

theorem rels2_hold (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (hs : F.Rep s sD) : ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ rels2.map FreeGroup.mk},
      FreeGroup.lift ![z, t, e, x, s] r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact F.lift_rels2_eq_one hz ht he hx hs w hw

theorem lift_bWord_injective (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) :
    Function.Injective fun k : Fin 192 => FreeGroup.lift ![z, t, e, x] (FreeGroup.mk (bWord k)) :=
  fun _ _ h => semEval_bWord_injective (F.semEval_eq_of_lift_eq (F.rep_gensB hz ht he hx) h)

theorem lift_h2Word_injective (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) (hs : F.Rep s sD) : Function.Injective fun k : Fin 960 =>
      FreeGroup.lift ![z, t, e, x, s] (FreeGroup.mk (h2Word k)) :=
  fun _ _ h => semEval_h2Word_injective (F.semEval_eq_of_lift_eq (F.rep_gens2 hz ht he hx hs) h)

theorem gensB_mem {K : Subgroup G} (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K) (hxK : x ∈ K) :
    ∀ i, ![z, t, e, x] i ∈ K := by
  intro i
  fin_cases i
  · exact hzK
  · exact htK
  · exact heK
  · exact hxK

theorem gens2_mem {K : Subgroup G} (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K) (hxK : x ∈ K)
    (hsK : s ∈ K) : ∀ i, ![z, t, e, x, s] i ∈ K := by
  intro i
  fin_cases i
  · exact hzK
  · exact htK
  · exact heK
  · exact hxK
  · exact hsK

omit [Group G] in
theorem gens2_castSucc (i : Fin 4) : ![z, t, e, x, s] (Fin.castSucc i) = ![z, t, e, x] i := by
  fin_cases i <;> rfl

@[expose] def homB (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (K : Subgroup G) (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K) (hxK : x ∈ K) :
    PresentedGroup {r : FreeGroup (Fin 4) | r ∈ relsB.map FreeGroup.mk} →* K :=
  toSubgroup (F.relsB_hold hz ht he hx) K (gensB_mem hzK htK heK hxK)

@[expose] def hom2 (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (hs : F.Rep s sD) (K : Subgroup G) (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K) (hxK : x ∈ K)
    (hsK : s ∈ K) : PresentedGroup {r : FreeGroup (Fin 5) | r ∈ rels2.map FreeGroup.mk} →* K :=
  toSubgroup (F.rels2_hold hz ht he hx hs) K (gens2_mem hzK htK heK hxK hsK)

variable {hz : F.Rep z zD} {ht : F.Rep t tD} {he : F.Rep e eD} {hx : F.Rep x xD}
  {hs : F.Rep s sD} {K : Subgroup G} {hzK : z ∈ K} {htK : t ∈ K} {heK : e ∈ K} {hxK : x ∈ K}
  {hsK : s ∈ K}

theorem homB_of (i : Fin 4) : F.homB hz ht he hx K hzK htK heK hxK (PresentedGroup.of i) =
    ⟨![z, t, e, x] i, gensB_mem hzK htK heK hxK i⟩ :=
  toSubgroup_of _ _ _ i

theorem coe_homB_mk (w : FreeGroup (Fin 4)) :
    (F.homB hz ht he hx K hzK htK heK hxK (PresentedGroup.mk _ w) : G) =
      FreeGroup.lift ![z, t, e, x] w :=
  rfl

theorem hom2_of (i : Fin 5) :
    F.hom2 hz ht he hx hs K hzK htK heK hxK hsK (PresentedGroup.of i) =
      ⟨![z, t, e, x, s] i, gens2_mem hzK htK heK hxK hsK i⟩ :=
  toSubgroup_of _ _ _ i

theorem coe_hom2_mk (w : FreeGroup (Fin 5)) :
    (F.hom2 hz ht he hx hs K hzK htK heK hxK hsK (PresentedGroup.mk _ w) : G) =
      FreeGroup.lift ![z, t, e, x, s] w :=
  rfl

theorem le_card_of_gensB (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) (K : Subgroup G) [Finite K] (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K)
    (hxK : x ∈ K) : 192 ≤ Nat.card K :=
  le_card_of_injective (F.relsB_hold hz ht he hx) K (gensB_mem hzK htK heK hxK) bWord
    (F.lift_bWord_injective hz ht he hx)

theorem le_card_of_gens2 (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) (hs : F.Rep s sD) (K : Subgroup G) [Finite K] (hzK : z ∈ K) (htK : t ∈ K)
    (heK : e ∈ K) (hxK : x ∈ K) (hsK : s ∈ K) : 960 ≤ Nat.card K :=
  le_card_of_injective (F.rels2_hold hz ht he hx hs) K (gens2_mem hzK htK heK hxK hsK) h2Word
    (F.lift_h2Word_injective hz ht he hx hs)

theorem range_toGroupB_le (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) : (PresentedGroup.toGroup (F.relsB_hold hz ht he hx)).range ≤ F.H := by
  rintro _ ⟨y, rfl⟩
  exact toGroup_mem _ (gensB_mem (F.mem_H_of_rep hz) (F.mem_H_of_rep ht) (F.mem_H_of_rep he)
    (F.mem_H_of_rep hx)) y

theorem le_card_range_toGroupB (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) :
    192 ≤ Nat.card (PresentedGroup.toGroup (F.relsB_hold hz ht he hx)).range := by
  have := F.finite_H
  have : Finite (PresentedGroup.toGroup (F.relsB_hold hz ht he hx)).range :=
    Finite.of_injective _ (Subgroup.inclusion_injective (F.range_toGroupB_le hz ht he hx))
  exact le_card_of_injective (F.relsB_hold hz ht he hx) _
    (fun i => MonoidHom.mem_range.2 ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩)
    bWord (F.lift_bWord_injective hz ht he hx)

theorem range_toGroup2_le (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) (hs : F.Rep s sD) :
    (PresentedGroup.toGroup (F.rels2_hold hz ht he hx hs)).range ≤ F.H := by
  rintro _ ⟨y, rfl⟩
  exact toGroup_mem _ (gens2_mem (F.mem_H_of_rep hz) (F.mem_H_of_rep ht) (F.mem_H_of_rep he)
    (F.mem_H_of_rep hx) (F.mem_H_of_rep hs)) y

theorem le_card_range_toGroup2 (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD)
    (hx : F.Rep x xD) (hs : F.Rep s sD) :
    960 ≤ Nat.card (PresentedGroup.toGroup (F.rels2_hold hz ht he hx hs)).range := by
  have := F.finite_H
  have : Finite (PresentedGroup.toGroup (F.rels2_hold hz ht he hx hs)).range :=
    Finite.of_injective _ (Subgroup.inclusion_injective (F.range_toGroup2_le hz ht he hx hs))
  exact le_card_of_injective (F.rels2_hold hz ht he hx hs) _
    (fun i => MonoidHom.mem_range.2 ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩)
    h2Word (F.lift_h2Word_injective hz ht he hx hs)

theorem homB_surjective (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (K : Subgroup G) [Finite K] (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K) (hxK : x ∈ K)
    (hcard : Nat.card K ≤ 192) : Function.Surjective (F.homB hz ht he hx K hzK htK heK hxK) :=
  toSubgroup_surjective _ K _ bWord (F.lift_bWord_injective hz ht he hx) hcard

theorem hom2_surjective (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (hs : F.Rep s sD) (K : Subgroup G) [Finite K] (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K)
    (hxK : x ∈ K) (hsK : s ∈ K) (hcard : Nat.card K ≤ 960) :
    Function.Surjective (F.hom2 hz ht he hx hs K hzK htK heK hxK hsK) :=
  toSubgroup_surjective _ K _ h2Word (F.lift_h2Word_injective hz ht he hx hs) hcard

theorem homB_bijective (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (K : Subgroup G) [Finite K] (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K) (hxK : x ∈ K)
    (hcard : Nat.card K ≤ 192)
    [Finite (PresentedGroup {r : FreeGroup (Fin 4) | r ∈ relsB.map FreeGroup.mk})]
    (hPG : Nat.card (PresentedGroup {r : FreeGroup (Fin 4) | r ∈ relsB.map FreeGroup.mk}) ≤ 192) :
    Function.Bijective (F.homB hz ht he hx K hzK htK heK hxK) :=
  toSubgroup_bijective _ K _ bWord (F.lift_bWord_injective hz ht he hx) hcard hPG

theorem hom2_bijective (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (hs : F.Rep s sD) (K : Subgroup G) [Finite K] (hzK : z ∈ K) (htK : t ∈ K) (heK : e ∈ K)
    (hxK : x ∈ K) (hsK : s ∈ K) (hcard : Nat.card K ≤ 960)
    [Finite (PresentedGroup {r : FreeGroup (Fin 5) | r ∈ rels2.map FreeGroup.mk})]
    (hPG : Nat.card (PresentedGroup {r : FreeGroup (Fin 5) | r ∈ rels2.map FreeGroup.mk}) ≤ 960) :
    Function.Bijective (F.hom2 hz ht he hx hs K hzK htK heK hxK hsK) :=
  toSubgroup_bijective _ K _ h2Word (F.lift_h2Word_injective hz ht he hx hs) hcard hPG

end Frame

end CFSG.LargeExtraspecial.AS62
