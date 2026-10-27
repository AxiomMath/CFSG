module

public import CFSG.LargeExtraspecial.Timmesfeld.FStar

public section

namespace CFSG

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem IsExtraspecial2.toIsExtraspecialPGroup {Q : Subgroup G}
    (hQ : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 Q) :
    CFSG.IsExtraspecialPGroup 2 ↥Q := by
  have hcard : Nat.card (Subgroup.center ↥Q) = 2 := by
    have h := hQ.2.2
    rw [hQ.2.1, Subgroup.card_map_of_injective Q.subtype_injective] at h
    exact h
  have hcomm : _root_.commutator ↥Q = Subgroup.center ↥Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hQ.2.1
  have hcent : ∀ a b : ↥Q, ⁅a, b⁆ ∈ Subgroup.center ↥Q := by
    intro a b
    rw [← hcomm, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hsq : ∀ c ∈ Subgroup.center ↥Q, c ^ 2 = 1 := by
    intro c hc
    have h1 : (⟨c, hc⟩ : Subgroup.center ↥Q) ^ Nat.card (Subgroup.center ↥Q) = 1 := pow_card_eq_one'
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  have hpow : ∀ a : ↥Q, a ^ 2 ∈ Subgroup.center ↥Q := by
    intro a
    rw [Subgroup.mem_center_iff]
    intro g
    have hc := hcent g a
    have hc' := Subgroup.mem_center_iff.mp hc
    have e1 : g * a * g⁻¹ = ⁅g, a⁆ * a := by rw [commutatorElement_def]; group
    have e2 : g * a ^ 2 * g⁻¹ = a ^ 2 := by
      have : g * a ^ 2 * g⁻¹ = (g * a * g⁻¹) ^ 2 := (conj_pow).symm
      rw [this, e1, Commute.mul_pow (hc' a).symm, hsq _ hc, one_mul]
    calc g * a ^ 2 = (g * a ^ 2 * g⁻¹) * g := by group
      _ = a ^ 2 * g := by rw [e2]
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hQ.1⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hQ.1, hcomm, ?_, hcard⟩
  apply le_antisymm
  · rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥Q) (p := 2)]
    refine (Subgroup.closure_le _).2 ?_
    rintro x (hx | ⟨y, rfl⟩)
    · exact hcomm.le hx
    · exact hpow y
  · rw [← hcomm]
    exact CFSG.commutator_le_frattini_of_isPGroup (R := ↥Q) (p := 2)

theorem IsExtraspecial2.pow_two_mem_center {Q : Subgroup G}
    (hQ : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 Q) (q : ↥Q) :
    q ^ 2 ∈ Subgroup.center ↥Q := by
  have hcard : Nat.card (Subgroup.center ↥Q) = 2 := by
    have h := hQ.2.2
    rw [hQ.2.1, Subgroup.card_map_of_injective Q.subtype_injective] at h
    exact h
  have hcomm : _root_.commutator ↥Q = Subgroup.center ↥Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hQ.2.1
  have hcent : ∀ a b : ↥Q, ⁅a, b⁆ ∈ Subgroup.center ↥Q := by
    intro a b
    rw [← hcomm, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hsq : ∀ c ∈ Subgroup.center ↥Q, c ^ 2 = 1 := by
    intro c hc
    have h1 : (⟨c, hc⟩ : Subgroup.center ↥Q) ^ Nat.card (Subgroup.center ↥Q) = 1 := pow_card_eq_one'
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  rw [Subgroup.mem_center_iff]
  intro g
  have hc := hcent g q
  have hc' := Subgroup.mem_center_iff.mp hc
  have e1 : g * q * g⁻¹ = ⁅g, q⁆ * q := by rw [commutatorElement_def]; group
  have e2 : g * q ^ 2 * g⁻¹ = q ^ 2 := by
    have : g * q ^ 2 * g⁻¹ = (g * q * g⁻¹) ^ 2 := (conj_pow).symm
    rw [this, e1, Commute.mul_pow (hc' q).symm, hsq _ hc, one_mul]
  calc g * q ^ 2 = (g * q ^ 2 * g⁻¹) * g := by group
      _ = q ^ 2 * g := by rw [e2]

theorem IsExtraspecial2.mul_self_mem_center_map {F : Subgroup G}
    (hF : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 F) {f : G} (hf : f ∈ F) :
    f * f ∈ (Subgroup.center F).map F.subtype := by
  have h := CFSG.IsExtraspecial2.pow_two_mem_center hF (⟨f, hf⟩ : ↥F)
  refine ⟨(⟨f, hf⟩ : ↥F) ^ 2, h, ?_⟩
  simp [pow_two]

end CFSG
