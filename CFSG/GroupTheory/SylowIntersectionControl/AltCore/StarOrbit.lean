module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Orbits
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.TransitiveCase
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.SymIsolated

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction
open CFSG.Quasithin (omegaOneCenterOf)

theorem isPIsolatedOver_map_iff_of_injective {G G' : Type*} [Group G] [Group G'] [Finite G]
    [Finite G'] {p : ℕ} [Fact p.Prime] {f : G →* G'} (hf : Function.Injective f)
    {A B : Subgroup G} : IsPIsolatedOver p (A.map f) (B.map f) ↔ IsPIsolatedOver p A B := by
  set e := MonoidHom.ofInjective hf
  have key : ∀ C : Subgroup G, (C.map f).subgroupOf f.range = C.map e.toMonoidHom := by
    intro C
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, Subtype.ext (MonoidHom.ofInjective_apply hf)⟩
    · rintro ⟨c, hc, hce⟩
      exact ⟨c, hc, (MonoidHom.ofInjective_apply hf).symm.trans (congrArg Subtype.val hce)⟩
  rw [← isPIsolatedOver_subgroupOf_iff (K' := f.range) (map_le_range f B) (map_le_range f A),
    key, key]
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have h1 : IsPGroup p e.toMonoidHom.ker := by rw [hker]; exact IsPGroup.of_bot
  have h2 : e.toMonoidHom.ker ≤ B := by rw [hker]; exact bot_le
  have h3 : e.toMonoidHom.ker ≤ A := by rw [hker]; exact bot_le
  exact isPIsolatedOver_map_iff e.surjective h1 h2 h3

theorem le_normalizer_sup' {G : Type*} [Group G] {N A B : Subgroup G}
    (hA : N ≤ normalizer (A : Set G)) (hB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun n hn d hd => ?_
  have hmap : (A ⊔ B).map (MulAut.conj n).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (mem_normalizer_iff.mp (hA hn) a).mp ha
    · rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp (hB hn) b).mp hb
  exact hmap ⟨d, hd, rfl⟩

theorem _root_.CFSG.GroupTheory.IsPIsolatedOver.inf_of_normal_of_le
    {G : Type*} [Group G] [Finite G] {H N T : Subgroup G}
    (hiso : IsPIsolatedOver 2 N H) (hH : IsPGroup 2 H) (hHN : H ≤ N)
    (hN : N ≤ normalizer (H : Set G)) (hTN : T ≤ N) (hNT : N ≤ normalizer (T : Set G))
    {x : G} (hx : x ∈ T) (hxH : x ∉ H) (hx2 : x ^ 2 ∈ H) : IsPIsolatedOver 2 T (T ⊓ H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : ((T ⊔ H).subgroupOf N).IsSubnormal :=
    ((normal_subgroupOf_iff_le_normalizer (sup_le hTN hHN)).mpr
      (le_normalizer_sup' hNT hN)).isSubnormal
  have hp : 2 ∣ H.relIndex (T ⊔ H) := two_dvd_relIndex_of_sq_mem le_sup_right
    (sup_le (hTN.trans hN) le_normalizer) (mem_sup_left hx) hxH hx2
  exact (isPIsolatedOver_sup_iff hH (hTN.trans hN)).mp
    (hiso.of_isSubnormal_le_over hH hN le_sup_right le_rfl (sup_le hTN hHN) hY hp)

theorem _root_.CFSG.GroupTheory.IsPIsolatedOver.inf_of_normal
    {G : Type*} [Group G] [Finite G] {H T : Subgroup G}
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H) (hH : IsPGroup 2 H)
    (hTN : T ≤ normalizer (H : Set G)) (hNT : normalizer (H : Set G) ≤ normalizer (T : Set G))
    {x : G} (hx : x ∈ T) (hxH : x ∉ H) (hx2 : x ^ 2 ∈ H) : IsPIsolatedOver 2 T (T ⊓ H) :=
  IsPIsolatedOver.inf_of_normal_of_le hiso hH le_normalizer le_rfl hTN hNT hx hxH hx2

variable {α : Type} [Fintype α] [DecidableEq α] {H : Subgroup (Perm α)}

@[expose] def fixSet (H : Subgroup (Perm α)) : Set α := {x | ∀ h ∈ H, h x = x}

omit [Fintype α] [DecidableEq α] in
theorem fixSet_mem_setStab : normalizer (H : Set (Perm α)) ≤ setStab (fixSet H) := by
  intro n hn z
  constructor
  · intro hz h hh
    have := hz (n * h * n⁻¹) ((mem_normalizer_iff.mp hn h).mp hh)
    simp only [Perm.mul_apply] at this
    rw [show n⁻¹ (n z) = z from n.symm_apply_apply z] at this
    exact n.injective this
  · intro hz h hh
    have := hz (n⁻¹ * h * n⁻¹⁻¹) ((mem_normalizer_iff.mp (inv_mem hn) h).mp hh)
    simp only [inv_inv, Perm.mul_apply] at this
    exact (n.apply_symm_apply _).symm.trans (congrArg n this)

theorem swap_mem_normalizer_of_mem_fixSet {x y : α} (hx : x ∈ fixSet H) (hy : y ∈ fixSet H) :
    swap x y ∈ normalizer (H : Set (Perm α)) := by
  refine mem_normalizer_fintype fun h hh => ?_
  have hc : h * swap x y = swap x y * h := by rw [mul_swap_eq_swap_mul, hx h hh, hy h hh]
  rw [← hc, mul_inv_cancel_right]
  exact hh

theorem fixSet_subset_orbit {x : α} (hx : x ∈ fixSet H) :
    fixSet H ⊆ orbit (normalizer (H : Set (Perm α))) x := fun y hy =>
  ⟨⟨swap x y, swap_mem_normalizer_of_mem_fixSet hx hy⟩, swap_apply_left x y⟩

omit [Fintype α] [DecidableEq α] in
theorem fixOutside_le_setStab (O : Set α) : fixOutside O ≤ setStab O := fun g hg x => by
  by_cases hx : x ∈ O
  · refine iff_of_true ?_ hx
    by_contra h
    exact h (by rw [g.injective (hg (g x) h)]; exact hx)
  · rw [hg x hx]

omit [Fintype α] [DecidableEq α] in
theorem restrHom_eq_self {O : Set α} [DecidablePred (· ∈ O)] {g : Perm α}
    (hg : g ∈ fixOutside O) (hgs : g ∈ setStab O) : restrHom O ⟨g, hgs⟩ = g := by
  ext z
  by_cases hz : z ∈ O
  · rw [restrHom_apply_of_mem _ hz]
  · rw [restrHom_apply_of_not_mem _ hz, hg z hz]

omit [DecidableEq α] in
theorem restrSub_le (hH : IsPGroup 2 H) (hrad : IsRadical H) {O : Set α} [DecidablePred (· ∈ O)]
    (hO : normalizer (H : Set (Perm α)) ≤ setStab O) : restrSub O H ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨⟨h, hs⟩, hh, rfl⟩
  exact restrHom_mem hH hrad hO (mem_subgroupOf.mp hh)

omit [Fintype α] [DecidableEq α] in
theorem restrSub_le_fixOutside {O : Set α} [DecidablePred (· ∈ O)] :
    restrSub O H ≤ fixOutside O := by
  rintro _ ⟨g, -, rfl⟩ z hz
  exact restrHom_apply_of_not_mem _ hz

omit [DecidableEq α] in
theorem mem_normalizer_of_mem_fixOutside (hH : IsPGroup 2 H) (hrad : IsRadical H) {O : Set α}
    [DecidablePred (· ∈ O)] (hO : normalizer (H : Set (Perm α)) ≤ setStab O) {g : Perm α}
    (hgO : g ∈ fixOutside O) (hgK : g ∈ normalizer (restrSub O H : Set (Perm α))) :
    g ∈ normalizer (H : Set (Perm α)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOc : normalizer (H : Set (Perm α)) ≤ setStab Oᶜ := by rw [setStab_compl]; exact hO
  refine mem_normalizer_fintype fun h hh => ?_
  have hhN : h ∈ normalizer (H : Set (Perm α)) := le_normalizer hh
  have e : restrHom O ⟨h, hO hhN⟩ * restrHom Oᶜ ⟨h, hOc hhN⟩ = h :=
    restrHom_mul_restrHom_compl ⟨h, hO hhN⟩
  have hb : restrHom Oᶜ ⟨h, hOc hhN⟩ ∈ H := restrHom_mem hH hrad hOc hh
  have hcomm : g * restrHom Oᶜ ⟨h, hOc hhN⟩ = restrHom Oᶜ ⟨h, hOc hhN⟩ * g :=
    (Disjoint.commute fun z => by
      by_cases hz : z ∈ O
      · exact Or.inr (restrHom_apply_of_not_mem _ (by simpa using hz))
      · exact Or.inl (hgO z hz)).eq
  have hga : g * restrHom O ⟨h, hO hhN⟩ * g⁻¹ ∈ H := restrSub_le hH hrad hO
    ((mem_normalizer_iff.mp hgK _).mp (restrHom_mem_restrSub hh))
  have key : g * h * g⁻¹ = (g * restrHom O ⟨h, hO hhN⟩ * g⁻¹) * restrHom Oᶜ ⟨h, hOc hhN⟩ := by
    conv_lhs => rw [← e]
    calc g * (restrHom O ⟨h, hO hhN⟩ * restrHom Oᶜ ⟨h, hOc hhN⟩) * g⁻¹
        = g * restrHom O ⟨h, hO hhN⟩ * g⁻¹ * (g * restrHom Oᶜ ⟨h, hOc hhN⟩ * g⁻¹) := by group
      _ = _ := by rw [hcomm, mul_inv_cancel_right]
  rw [key]
  exact mul_mem hga hb

omit [Fintype α] [DecidableEq α] in
theorem le_normalizer_fixOutside {O : Set α} (hO : normalizer (H : Set (Perm α)) ≤ setStab O) :
    normalizer (H : Set (Perm α)) ≤ normalizer (fixOutside O : Set (Perm α)) :=
  le_normalizer_of_conj_mem fun n hn g hg z hz => by
    have hz' : n⁻¹ z ∉ O := fun h => hz ((hO (inv_mem hn) z).mp h)
    simp only [Perm.mul_apply]
    rw [hg _ hz']
    exact n.apply_symm_apply z

theorem card_orbit_eq_three_of_mem_fixSet (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α} (hx₀ : x₀ ∈ fixSet H)
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) :
    Nat.card (orbit (normalizer (H : Set (Perm α))) x₀) = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOfix : orbit (normalizer (H : Set (Perm α))) x₀ ⊆ fixSet H := by
    rintro _ ⟨⟨n, hn⟩, rfl⟩
    exact (fixSet_mem_setStab hn x₀).mpr hx₀
  have hTN : fixOutside (orbit (normalizer (H : Set (Perm α))) x₀) ≤
      normalizer (H : Set (Perm α)) := fun g hg => mem_normalizer_fintype fun h hh => by
    have hc : g * h = h * g := (Disjoint.commute fun z => by
      by_cases hz : z ∈ orbit (normalizer (H : Set (Perm α))) x₀
      · exact Or.inr (hOfix hz h hh)
      · exact Or.inl (hg z hz)).eq
    rw [hc, mul_inv_cancel_right]
    exact hh
  obtain ⟨x, -, hxO, hxH, hx2⟩ := he
  have hiso' := IsPIsolatedOver.inf_of_normal hiso hH hTN
    (le_normalizer_fixOutside (orbit_mem_setStab x₀)) hxO hxH hx2
  have hbot : fixOutside (orbit (normalizer (H : Set (Perm α))) x₀) ⊓ H = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    rw [mem_bot]
    ext z
    by_cases hz : z ∈ orbit (normalizer (H : Set (Perm α))) x₀
    · exact hOfix hz g (mem_inf.mp hg).2
    · exact (mem_inf.mp hg).1 z hz
  have hrange : (⊤ : Subgroup (Perm (orbit (normalizer (H : Set (Perm α))) x₀))).map
      (ofSubtype : Perm (orbit (normalizer (H : Set (Perm α))) x₀) →* Perm α) =
      fixOutside (orbit (normalizer (H : Set (Perm α))) x₀) := by
    ext g
    rw [← MonoidHom.range_eq_map, mem_range_ofSubtype_iff]
    constructor
    · intro h z hz
      by_contra hne
      exact hz (h (mem_support.mpr hne))
    · intro h z hz
      by_contra hzO
      exact (mem_support.mp hz) (h z hzO)
  rw [hbot, ← hrange, ← map_bot (ofSubtype :
    Perm (orbit (normalizer (H : Set (Perm α))) x₀) →* Perm α),
    isPIsolatedOver_map_iff_of_injective ofSubtype_injective] at hiso'
  rw [Nat.card_eq_fintype_card]
  exact card_eq_three_of_isPIsolatedOver_perm hiso'

theorem card_orbit_omegaOneCenter_restrSub_le_four (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α}
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm α))) x₀)]
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) {x : α}
    (hx : x ∈ orbit (normalizer (H : Set (Perm α))) x₀) :
    Nat.card (orbit (omegaOneCenterOf (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H))
      x) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrad := isRadical_of_isPIsolatedOver hH hiso
  have hO := orbit_mem_setStab (H := H) x₀
  have hKN : normalizer (H : Set (Perm α)) ≤
      normalizer (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H : Set (Perm α)) :=
    fun n hn => mem_normalizer_fintype fun k hk => conj_mem_restrSub hn (hO hn) hk
  have hTN := fun g (hg : g ∈ normalizer (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H :
      Set (Perm α)) ⊓ fixOutside (orbit (normalizer (H : Set (Perm α))) x₀)) =>
    mem_normalizer_of_mem_fixOutside hH hrad hO (mem_inf.mp hg).2 (mem_inf.mp hg).1
  obtain ⟨y, hyN, hyO, hyH, hy2⟩ := he
  have hiso' := IsPIsolatedOver.inf_of_normal hiso hH hTN
    ((le_inf (hKN.trans le_normalizer) (le_normalizer_fixOutside hO)).trans
      inf_normalizer_le_normalizer_inf)
    (mem_inf.mpr ⟨hKN hyN, hyO⟩) hyH hy2
  have hTH : (normalizer (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H :
      Set (Perm α)) ⊓ fixOutside (orbit (normalizer (H : Set (Perm α))) x₀)) ⊓ H =
      restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H := by
    refine le_antisymm (fun g hg => ?_)
      (le_inf (le_inf le_normalizer restrSub_le_fixOutside) (restrSub_le hH hrad hO))
    have hgO := (mem_inf.mp (mem_inf.mp hg).1).2
    rw [← restrHom_eq_self hgO (fixOutside_le_setStab _ hgO)]
    exact restrHom_mem_restrSub (mem_inf.mp hg).2
  rw [hTH] at hiso'
  refine card_orbit_omegaOneCenter_le_four (isPGroup_restrSub hH) restrSub_le_fixOutside
    (le_inf le_normalizer restrSub_le_fixOutside) inf_le_left inf_le_left
    (fun a ha b hb => ?_) hiso' hx
  obtain ⟨⟨n₁, hn₁⟩, rfl⟩ := ha
  obtain ⟨⟨n₂, hn₂⟩, rfl⟩ := hb
  refine ⟨n₂ * n₁⁻¹, hKN (mul_mem hn₂ (inv_mem hn₁)), ?_⟩
  change (n₂ * n₁⁻¹) (n₁ x₀) = n₂ x₀
  rw [Perm.mul_apply]
  exact congrArg n₂ (n₁.symm_apply_apply x₀)

end CFSG.GroupTheory.AltCore
