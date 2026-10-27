module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem alt_fixed_component_structure {n : ℕ} {τ : Perm (Fin n)} (hττ : τ * τ = 1)
    (hτ1 : τ ≠ 1) {P : Subgroup (alternatingGroup (Fin n))}
    (hPF : P ≤ fixedSubgroup (MulAut.conjNormal τ))
    (hP : IsPComponent 2 (P.subgroupOf (fixedSubgroup (MulAut.conjNormal τ)))) :
    IsSimpleGroup P ∧ (∀ x ∈ P, ∀ a, τ a ≠ a → (x : Perm (Fin n)) a = a) ∧
      (∀ a, τ a = a → ∃ x ∈ P, (x : Perm (Fin n)) a ≠ a) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
    Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) with hcdef
  have hcapp : ∀ x : alternatingGroup (Fin n), ((c τ x : alternatingGroup (Fin n)) : Perm (Fin n))
      = τ * x * τ⁻¹ := fun x => rfl
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hττ) hτ1
  set Q : Subgroup (Perm (Fin n)) := zpowers τ with hQdef
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2, pow_one])
  set N := normalizer (Q : Set (Perm (Fin n))) with hNdef
  set F := fixedSubgroup (c τ) with hFdef
  have hmemF : ∀ x : alternatingGroup (Fin n), x ∈ F ↔ τ * (x : Perm (Fin n)) = x * τ := by
    intro x
    change c τ x = x ↔ _
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      calc τ * (x : Perm (Fin n)) = τ * x * τ⁻¹ * τ := by group
        _ = x * τ := by rw [h1]
    · intro hx
      apply Subtype.ext
      rw [hcapp, hx]
      group
  have hcN : ∀ g : Perm (Fin n), τ * g = g * τ → g ∈ N := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [hQdef, ← Subgroup.zpowers_le, Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute τ g from hg) k).eq
  let ι : F →* N := ((alternatingGroup (Fin n)).subtype.comp F.subtype).codRestrict N
    fun x => hcN _ ((hmemF x.1).mp x.2)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = ((y : alternatingGroup (Fin n)) :
        Perm (Fin n)) := congrArg (fun z : N => (z : Perm (Fin n))) hxy
    exact Subtype.ext (Subtype.ext h1)
  set R : Subgroup N := (alternatingGroup (Fin n)).subgroupOf N with hRdef
  have hR : R.Normal := inferInstance
  have hrange : ι.range = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (x : alternatingGroup (Fin n)).2
    · intro y hy
      have hyA : (y : Perm (Fin n)) ∈ alternatingGroup (Fin n) := hy
      have hyτ : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp y.2 τ).mp (mem_zpowers τ)
      have hyτ' : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ = τ := by
        have hord : orderOf ((y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹) = 2 := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ2]
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
        rw [← hk] at hord ⊢
        rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_zero,
            orderOf_one] at hord
          omega
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_one]
      have hcomm : τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ := by
        calc τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ * y := by
              rw [hyτ']
          _ = (y : Perm (Fin n)) * τ := by group
      exact ⟨⟨⟨y, hyA⟩, (hmemF ⟨y, hyA⟩).mpr hcomm⟩, Subtype.ext rfl⟩
  let e₁ : F ≃* R := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  set L₀ := P.subgroupOf F with hL₀def
  have hL₁ : IsPComponent 2 (L₀.map e₁.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e₁ hP
  have hL := CatalogueBAlternating.pComponent_of_normal_subgroup 2 R (L₀.map e₁.toMonoidHom) hL₁
  set L := (L₀.map e₁.toMonoidHom).map R.subtype with hLdef
  obtain ⟨hdeg, hLeq, -⟩ := CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q hQ L hL
  let eL : L₀ ≃* L := (L₀.equivMapOfInjective e₁.toMonoidHom e₁.injective).trans
    ((L₀.map e₁.toMonoidHom).equivMapOfInjective R.subtype R.subtype_injective)
  let eA : L ≃* alternatingGroup (MulAction.fixedPoints Q (Fin n)) :=
    (MulEquiv.subgroupCongr hLeq).trans
      ((alternatingGroup (MulAction.fixedPoints Q (Fin n))).equivMapOfInjective _
        (CatalogueBAlternating.fixedPointsNormalizerHom_injective Q)).symm
  have : IsSimpleGroup (alternatingGroup (MulAction.fixedPoints Q (Fin n))) :=
    alternatingGroup.isSimpleGroup hdeg
  have hmemL : ∀ w : F, w ∈ L₀ → R.subtype (e₁ w) ∈ L := fun w hw =>
    mem_map_of_mem _ (mem_map_of_mem _ hw)
  have hfix : ∀ a, τ a = a ↔ a ∈ MulAction.fixedPoints Q (Fin n) := by
    intro a
    rw [MulAction.mem_fixedPoints]
    constructor
    · rintro ha ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact Perm.zpow_apply_eq_self_of_apply_eq_self ha k
    · intro h
      exact h ⟨τ, mem_zpowers τ⟩
  refine ⟨((subgroupOfEquivOfLe hPF).symm.trans (eL.trans eA)).isSimpleGroup, ?_, ?_⟩
  · intro x hx a ha
    have h1 := hmemL ⟨x, hPF hx⟩ hx
    rw [hLeq] at h1
    obtain ⟨g, -, hg⟩ := mem_map.mp h1
    have h2 := congrArg Subtype.val hg
    rw [CatalogueBAlternating.fixedPointsNormalizerHom_coe] at h2
    have hnot : a ∉ MulAction.fixedPoints Q (Fin n) := fun h => ha ((hfix a).mpr h)
    have h3 : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = Perm.ofSubtype g := h2.symm
    rw [h3, Perm.ofSubtype_apply_of_not_mem g hnot]
  · intro a ha
    have haF : a ∈ MulAction.fixedPoints Q (Fin n) := (hfix a).mp ha
    set a₀ : MulAction.fixedPoints Q (Fin n) := ⟨a, haF⟩ with ha₀
    have hcard : 5 ≤ Fintype.card (MulAction.fixedPoints Q (Fin n)) := by
      rwa [← Nat.card_eq_fintype_card]
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a₀
    have hs : 0 < ((Finset.univ.erase a₀).erase b).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      omega
    obtain ⟨c', hc'⟩ := Finset.card_pos.mp hs
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hc'
    obtain ⟨hcb, hca⟩ := hc'
    set g : Perm (MulAction.fixedPoints Q (Fin n)) := swap a₀ b * swap a₀ c' with hgdef
    have hg : g ∈ alternatingGroup (MulAction.fixedPoints Q (Fin n)) := by
      rw [Perm.mem_alternatingGroup, hgdef, Perm.sign_mul, Perm.sign_swap (Ne.symm hb),
        Perm.sign_swap (Ne.symm hca)]
      rfl
    have h1 : CatalogueBAlternating.fixedPointsNormalizerHom Q g ∈ L := by
      rw [hLeq]
      exact mem_map_of_mem _ hg
    obtain ⟨y, hy, hyeq⟩ := mem_map.mp h1
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hy
    refine ⟨(w : alternatingGroup (Fin n)), hw, ?_⟩
    have h2 := congrArg Subtype.val hyeq
    rw [CatalogueBAlternating.fixedPointsNormalizerHom_coe] at h2
    have h3 : ((w : alternatingGroup (Fin n)) : Perm (Fin n)) = Perm.ofSubtype g := h2
    rw [h3, Perm.ofSubtype_apply_of_mem g haF]
    have hga : g a₀ = c' := by
      rw [hgdef, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hca hcb]
    intro h
    have h4 : g a₀ = a₀ := Subtype.ext h
    rw [hga] at h4
    exact hca h4

end CFSG.ComponentClassification.GSThmB.Pump516
