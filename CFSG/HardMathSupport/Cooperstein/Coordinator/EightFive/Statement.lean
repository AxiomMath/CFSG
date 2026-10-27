module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm

section Defs

variable {V : Type} [CommGroup V]

@[expose] def altPre {H : Subgroup (MulAut V)} {n : ℕ} (ψ : ↥H →* Perm (Fin n)) :
    Subgroup (MulAut V) :=
  ((alternatingGroup (Fin n)).comap ψ).map H.subtype

@[expose] def NatVia {H : Subgroup (MulAut V)} {n : ℕ} (ψ : ↥H →* Perm (Fin n))
    (U : Subgroup V) : Prop :=
  ∃ π : ↥U →* Multiplicative (altHeart n), Function.Surjective π ∧
    π.ker = (U ⊓ fixV (altPre ψ)).subgroupOf U ∧
    ∀ (h : ↥H) (u v : ↥U), (v : V) = (h : MulAut V) (u : V) →
      Multiplicative.toAdd (π v) = altAct (ψ h) (Multiplicative.toAdd (π u))

@[expose] def Exotic {H : Subgroup (MulAut V)} {n : ℕ} (ψ : ↥H →* Perm (Fin n)) : Prop :=
  commV (altPre ψ) ⊔ fixV (altPre ψ) = ⊤ ∧
  (∀ x : ↥H, (ψ x).IsThreeCycle →
    fixV (Subgroup.zpowers (x : MulAut V)) ⊓ commV (altPre ψ) = ⊥) ∧
  (ψ.range = ⊤ → ∀ B : Subgroup (MulAut V), IsFFStarOffender H B →
    Nat.card V = Nat.card B * Nat.card (fixV B))

end Defs

@[expose] def TPerm (n : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin n)), Function.Injective ψ →
      alternatingGroup (Fin n) ≤ ψ.range → (∃ A : Subgroup (MulAut V), IsFFStarOffender H A) →
        NatVia ψ (commV H) ∨
        (n = 7 ∧ ψ.range = alternatingGroup (Fin n) ∧ Nat.card (commV H) = 2 ^ 4) ∨
        (n = 8 ∧ Exotic ψ)

section AltPre

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem mem_altPre_iff {x : MulAut V} :
    x ∈ altPre ψ ↔ ∃ hx : x ∈ H, ψ ⟨x, hx⟩ ∈ alternatingGroup (Fin n) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hx, hψ⟩
    exact ⟨⟨x, hx⟩, hψ, rfl⟩

theorem coe_mem_altPre_iff {x : ↥H} :
    (x : MulAut V) ∈ altPre ψ ↔ ψ x ∈ alternatingGroup (Fin n) :=
  mem_altPre_iff.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem altPre_le : altPre ψ ≤ H :=
  Subgroup.map_subtype_le _

theorem altPre_subgroupOf : (altPre ψ).subgroupOf H = (alternatingGroup (Fin n)).comap ψ :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem altPre_normal : ((altPre ψ).subgroupOf H).Normal := by
  rw [altPre_subgroupOf]
  exact Subgroup.Normal.comap alternatingGroup.normal ψ

theorem conj_mem_altPre {g x : MulAut V} (hg : g ∈ H) (hx : x ∈ altPre ψ) :
    g * x * g⁻¹ ∈ altPre ψ := by
  have hxH : x ∈ H := altPre_le hx
  have hmem : (⟨g, hg⟩ : ↥H) * ⟨x, hxH⟩ * (⟨g, hg⟩ : ↥H)⁻¹ ∈ (altPre ψ).subgroupOf H :=
    altPre_normal.conj_mem _ (Subgroup.mem_subgroupOf.2 hx) _
  exact Subgroup.mem_subgroupOf.1 hmem

theorem le_normalizer_altPre : H ≤ Subgroup.normalizer (altPre ψ : Set (MulAut V)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_altPre hg, fun hx => ?_⟩
  have := conj_mem_altPre (H.inv_mem hg) hx
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

theorem altPre_eq_of_range_le (h : ψ.range ≤ alternatingGroup (Fin n)) : altPre ψ = H :=
  le_antisymm altPre_le fun x hx => mem_altPre_iff.2 ⟨hx, h ⟨⟨x, hx⟩, rfl⟩⟩

@[expose] def altPreHom (ψ : ↥H →* Perm (Fin n)) : ↥(altPre ψ) →* alternatingGroup (Fin n) :=
  (ψ.comp (Subgroup.inclusion altPre_le)).codRestrict (alternatingGroup (Fin n)) fun x =>
    (coe_mem_altPre_iff (ψ := ψ) (x := Subgroup.inclusion altPre_le x)).1 x.2

theorem coe_altPreHom (x : ↥(altPre ψ)) :
    (altPreHom ψ x : Perm (Fin n)) = ψ (Subgroup.inclusion altPre_le x) :=
  rfl

theorem altPreHom_surjective (hA : alternatingGroup (Fin n) ≤ ψ.range) :
    Function.Surjective (altPreHom ψ) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨x, hx⟩ := hA hσ
  refine ⟨⟨x, coe_mem_altPre_iff.2 (hx ▸ hσ)⟩, Subtype.ext ?_⟩
  rw [coe_altPreHom]
  exact hx

theorem altPreHom_injective (hψ : Function.Injective ψ) : Function.Injective (altPreHom ψ) := by
  intro x y hxy
  have h1 : ψ (Subgroup.inclusion altPre_le x) = ψ (Subgroup.inclusion altPre_le y) := by
    rw [← coe_altPreHom, ← coe_altPreHom, hxy]
  exact Subtype.ext (congrArg (fun z : ↥H => (z : MulAut V)) (hψ h1))

theorem isAltNaturalSection_of_natVia (hA : alternatingGroup (Fin n) ≤ ψ.range)
    {U : Subgroup V} (h : NatVia ψ U) : IsAltNaturalSection (altPre ψ) U n := by
  obtain ⟨π, hπ, hker, heq⟩ := h
  refine ⟨altPreHom ψ, altPreHom_surjective hA, π, hπ, hker, fun l u v huv x hx => ?_⟩
  rw [heq (Subgroup.inclusion altPre_le l) u v huv, coe_altPreHom, hx, altAct_mk]

theorem altPre_eq_of_restrict {L : Subgroup (MulAut V)} (hLH : L ≤ H)
    (hψ : Function.Injective ψ) (α : ↥L →* alternatingGroup (Fin n))
    (hα : Function.Surjective α)
    (hψα : ∀ l : ↥L, ψ (Subgroup.inclusion hLH l) = (α l : Perm (Fin n))) :
    altPre ψ = L := by
  refine le_antisymm (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨hxH, hxA⟩ := mem_altPre_iff.1 hx
    obtain ⟨l, hl⟩ := hα ⟨ψ ⟨x, hxH⟩, hxA⟩
    have hlx : Subgroup.inclusion hLH l = ⟨x, hxH⟩ := hψ (by rw [hψα, hl])
    have hlx' : (l : MulAut V) = x := congrArg Subtype.val hlx
    exact hlx' ▸ l.2
  · refine mem_altPre_iff.2 ⟨hLH hx, ?_⟩
    have h1 := hψα ⟨x, hx⟩
    rw [show Subgroup.inclusion hLH ⟨x, hx⟩ = ⟨x, hLH hx⟩ from rfl] at h1
    rw [h1]
    exact (α ⟨x, hx⟩).2

end AltPre

theorem exists_embedding {V : Type} [CommGroup V] [Finite V] {H L : Subgroup (MulAut V)}
    (hL : L = quasithinGenFitting H) {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (ι : ↥L ≃* alternatingGroup (Fin n)) (hLH : L ≤ H) :
    ∃ ψ : ↥H →* Perm (Fin n), Function.Injective ψ ∧
      ∀ l : ↥L, ψ (Subgroup.inclusion hLH l) = (ι l : Perm (Fin n)) := by
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hL]; exact le_normalizer_quasithinGenFitting H
  set cH : ↥H →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hHN) with hcH
  have hcH_apply : ∀ (h : ↥H) (l : ↥L),
      ((cH h l : ↥L) : MulAut V) = (h : MulAut V) * l * (h : MulAut V)⁻¹ := fun _ _ => rfl
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  set cA : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ hb
    with hcA
  set ψ : ↥H →* Perm (Fin n) :=
    cA.symm.toMonoidHom.comp ((MulAut.congr ι).toMonoidHom.comp cH) with hψ
  have hcAψ : ∀ h : ↥H, cA (ψ h) = MulAut.congr ι (cH h) := fun h => cA.apply_symm_apply _
  have hext : ∀ l : ↥L, ψ (Subgroup.inclusion hLH l) = (ι l : Perm (Fin n)) := by
    intro l
    apply cA.injective
    rw [hcAψ]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    obtain ⟨y, rfl⟩ := ι.surjective a
    have hy : cH (Subgroup.inclusion hLH l) y = l * y * l⁻¹ := Subtype.ext rfl
    rw [show cA (ι l : Perm (Fin n)) = MulAut.conjNormal (ι l : Perm (Fin n)) from rfl,
      MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      ι.symm_apply_apply, hy, map_mul, map_mul, map_inv]
    rfl
  refine ⟨ψ, ?_, hext⟩
  rw [injective_iff_map_eq_one]
  intro h h1
  have hc : cH h = 1 := by
    have h2 : MulAut.congr ι (cH h) = MulAut.congr ι 1 := by
      rw [← hcAψ, h1, map_one, map_one]
    exact (MulAut.congr ι).injective h2
  have hmem : (h : MulAut V) ∈
      H ⊓ Subgroup.centralizer (quasithinGenFitting H : Set (MulAut V)) := by
    refine Subgroup.mem_inf.2 ⟨h.2, ?_⟩
    rw [← hL, Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 : (h : MulAut V) * l * (h : MulAut V)⁻¹ = l := by
      rw [← hcH_apply h ⟨l, hl⟩, hc]
      rfl
    calc l * (h : MulAut V) = (h : MulAut V) * l * (h : MulAut V)⁻¹ * h := by rw [h2]
      _ = h * l := by group
  have hhL : (h : MulAut V) ∈ L := by
    have := centralizer_quasithinGenFitting_le H hmem
    rwa [← hL] at this
  have h2 := hext ⟨h, hhL⟩
  rw [show Subgroup.inclusion hLH ⟨(h : MulAut V), hhL⟩ = h from rfl, h1] at h2
  have h3 : ι ⟨h, hhL⟩ = 1 := Subtype.ext h2.symm
  have h4 : (⟨h, hhL⟩ : ↥L) = 1 := ι.injective (h3.trans (map_one ι).symm)
  exact Subtype.ext (congrArg (fun z : ↥L => (z : MulAut V)) h4)

theorem gf2EightFive_of_tperm (h : ∀ n : ℕ, (n = 7 ∨ 9 ≤ n) → TPerm n) : GF2EightFive := by
  intro V _ _ hV H L hL n hn hiso hA
  obtain ⟨ι⟩ := hiso
  have hLH : L ≤ H := by rw [hL]; exact quasithinGenFitting_le H
  obtain ⟨ψ, hψ, hψι⟩ := exists_embedding hL (by omega) (by omega) ι hLH
  have hpre : altPre ψ = L := altPre_eq_of_restrict hLH hψ ι.toMonoidHom ι.surjective hψι
  have hrange : alternatingGroup (Fin n) ≤ ψ.range := by
    intro σ hσ
    obtain ⟨l, hl⟩ := ι.surjective ⟨σ, hσ⟩
    exact ⟨Subgroup.inclusion hLH l, by rw [hψι, hl]⟩
  rcases h n hn V hV H ψ hψ hrange hA with hnat | ⟨h7, hr, hcard⟩ | ⟨h8, -⟩
  · left
    rw [← hpre]
    exact isAltNaturalSection_of_natVia hrange hnat
  · exact Or.inr ⟨h7, by rw [← hpre, altPre_eq_of_range_le hr.le], hcard⟩
  · omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
