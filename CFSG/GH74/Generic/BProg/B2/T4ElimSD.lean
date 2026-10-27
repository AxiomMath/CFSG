module

public import CFSG.GH74.Generic.BProg.B2.PuL4InnerSD

public section

namespace CFSG.GH74.Generic.BProg.B2.T4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.Generic.BProg.B2 CFSG.GH74.Generic.BProg.B2.PuL4InnerSD

@[expose] def ShapeS13 {N : Type} [Group N] (L : Subgroup N) : Prop :=
  ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
    (QShape1 (↥L ⧸ Z) ∨ QShape3 (↥L ⧸ Z))

namespace T4ElimSD

theorem false_of_noncentral_shape13 {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (htH : t ∈ H) {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : (q % 4 = 3 ∧ IVK.IsLnEps 4 ↥H 1 q) ∨ (q % 4 = 1 ∧ IVK.IsLnEps 4 ↥H (-1) q))
    (hnc : ¬ CFSG.GH74.IsCentralInvolution (⟨t, htH⟩ : ↥H)) (h13 : ShapeS13 L) : False := by
  obtain ⟨Z, -, hZo, hZn, h13'⟩ := h13
  have hLC : L ≤ H ⊓ centralizer ({t} : Set N) := hs.comp.1
  obtain ⟨ψ, hψ⟩ := q8_in_H_of_shape hLC hZn hZo (exists_q8_of_shape13 h13')
  set u : ↥H := ⟨t, htH⟩ with hu
  have hu2 : orderOf u = 2 := by rw [← Subgroup.orderOf_coe]; exact hs.inv
  have hcomm : ∀ y : ↥(H ⊓ centralizer ({t} : Set N)),
      Subgroup.inclusion inf_le_left y ∈ centralizer ({u} : Set ↥H) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 y.2.2
    exact this
  let ψK : QuaternionGroup 2 →* ↥(centralizer ({u} : Set ↥H)) :=
    ((Subgroup.inclusion inf_le_left).comp ψ).codRestrict _ (fun x => hcomm (ψ x))
  have hψK : Function.Injective ψK := by
    intro a b hab
    apply hψ
    have h1 : Subgroup.inclusion (inf_le_left : H ⊓ centralizer ({t} : Set N) ≤ H) (ψ a) =
        Subgroup.inclusion (inf_le_left : H ⊓ centralizer ({t} : Set N) ≤ H) (ψ b) :=
      congrArg Subtype.val hab
    exact Subgroup.inclusion_injective _ h1
  have hP : IsPGroup 2 ψK.range :=
    IsPGroup.of_surjective isPGroup_q8 ψK.rangeRestrict ψK.rangeRestrict_surjective
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨D₁, D₂, n, -, hSD, hcm, hbot, ⟨-, k₁, -, -, ⟨e₁⟩⟩, ⟨-, k₂, -, -, ⟨e₂⟩⟩, -⟩ :=
    ivk_4_12_nc hq h5 hK hu2 hnc S
  refine no_q8_of_dihedral_pair hcm hbot e₁ e₂
    ((centralizer ({u} : Set ↥H)).subtype.comp ψK) ?_ ?_
  · exact (centralizer ({u} : Set ↥H)).subtype_injective.comp hψK
  · intro x
    rw [← hSD]
    exact Subgroup.mem_map.2 ⟨ψK x, hS ⟨x, rfl⟩, rfl⟩

section Certified13


theorem false_of_inner_shape13_SD {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hSD : PuL4SD ↥H) (htH : t ∈ H)
    (h13 : ShapeS13 L) : False := by
  obtain ⟨p, f, hp, hp2, hf, hq3, ⟨h4, hL⟩ | ⟨h4, hU⟩⟩ := hSD
  · obtain ⟨hf1, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    have e' : ↥H ≃* PG (ModelData.lin F) := e
    have h5 : 5 ≤ Nat.card F := by rw [hF]; omega
    have h4' : Nat.card F % 4 = 3 := by rw [hF]; exact h4
    have hG : GoodModel (ModelData.lin F) := goodModel_lin h2 h5
    have hZ : ZsTwo (ModelData.lin F) := zsTwo_lin h4'
    have hC : ClsFacts (ModelData.lin F) := clsFacts_lin h2 h5 h4'
    have hx : orderOf (e' ⟨t, htH⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hs.inv
    rcases all_inv_classes hG hZ hC hx with hc | hc
    · exact PuL4Inner.false_of_inner_shape_model hG hs htH e' hc
    · have hSq : HasSqLift (ModelData.lin F) (e' ⟨t, htH⟩) (ModelData.lin F).xK :=
        HasSqLift.conj (ModelData.xK_mem_center _) (hasSqLift_wy _) hc
      have hnc := not_isCentralInvolution_of_sqLift hG hZ hSq
      have hnc' : ¬ CFSG.GH74.IsCentralInvolution (⟨t, htH⟩ : ↥H) := fun hcen =>
        hnc (ModelBlock.isCentralInvolution_map e' hcen)
      exact false_of_noncentral_shape13 hs htH (q := p ^ f) (Nat.odd_iff.mpr (by omega))
        (by omega) (Or.inl ⟨h4, Or.inl ⟨rfl, F, iF, fF, hF, ⟨e⟩⟩⟩) hnc' h13
  · obtain ⟨hf1, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    have e' : ↥H ≃* PG (ModelData.uni hF) := e
    have h5 : 5 ≤ p ^ f := by omega
    have hG : GoodModel (ModelData.uni hF) := goodModel_uni hF hp2 h5
    have hZ : ZsTwo (ModelData.uni hF) := zsTwo_uni hF h4
    have hC : ClsFacts (ModelData.uni hF) := clsFacts_uni hF hp2 h5 h4
    have hx : orderOf (e' ⟨t, htH⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hs.inv
    rcases all_inv_classes hG hZ hC hx with hc | hc
    · exact PuL4Inner.false_of_inner_shape_model hG hs htH e' hc
    · have hSq : HasSqLift (ModelData.uni hF) (e' ⟨t, htH⟩) (ModelData.uni hF).xK :=
        HasSqLift.conj (ModelData.xK_mem_center _) (hasSqLift_wy _) hc
      have hnc := not_isCentralInvolution_of_sqLift hG hZ hSq
      have hnc' : ¬ CFSG.GH74.IsCentralInvolution (⟨t, htH⟩ : ↥H) := fun hcen =>
        hnc (ModelBlock.isCentralInvolution_map e' hcen)
      exact false_of_noncentral_shape13 hs htH (q := p ^ f) (Nat.odd_iff.mpr (by omega))
        (by omega) (Or.inr ⟨h4, Or.inr ⟨rfl, F, iF, fF, hF, ⟨e⟩⟩⟩) hnc' h13

theorem false_of_inner_shape1_SD {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hSD : PuL4SD ↥H) (htH : t ∈ H)
    (h1 : ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      QShape1 (↥L ⧸ Z)) : False := by
  obtain ⟨Z, hZc, hZo, hZn, h1'⟩ := h1
  exact false_of_inner_shape13_SD hs hSD htH ⟨Z, hZc, hZo, hZn, Or.inl h1'⟩

end Certified13

end T4ElimSD

end CFSG.GH74.Generic.BProg.B2.T4
