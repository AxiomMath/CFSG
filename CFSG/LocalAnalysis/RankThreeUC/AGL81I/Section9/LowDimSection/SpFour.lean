module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Inputs
public import CFSG.GH74.GLS.LU.Local.FiveSL2
public import CFSG.Quasithin.Vol2.Ch10SecDClA

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open MatrixGroups CFSG.LocalAnalysis.ComponentInitial

private theorem center_statedSp_eq_statedScalars (n : ℕ) (K : Type) [Field K] :
    Subgroup.center (CFSG.Open.StatedSp n K) =
      (CFSG.Open.StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (CFSG.Open.StatedSp n K) := by
  rw [show CFSG.Open.StatedSp n K = TauCeti.GLSymplectic (Fin n) K from
    CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
  exact CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq

private theorem nonempty_quotCenter_equiv_statedProj_statedSp {Y : Type} [Group Y] {n : ℕ}
    {K : Type} [Field K] (e : Y ≃* CFSG.Open.StatedSp n K) :
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) :=
  ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
    (QuotientGroup.quotientMulEquivOfEq (center_statedSp_eq_statedScalars n K))⟩

private theorem nonempty_quotCenter_equiv_psl2 {Y : Type} [Group Y] {F : Type} [CommRing F]
    (e : Y ≃* SL(2, F)) : Nonempty ((Y ⧸ Subgroup.center Y) ≃* PSL(2, F)) :=
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

private theorem nonempty_psl2_five_equiv_alt_five :
    Nonempty (PSL(2, ZMod 5) ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h4 : 4 ≤ Nat.card (ZMod 5) := by rw [Nat.card_zmod]; norm_num
  have : IsSimpleGroup PSL(2, ZMod 5) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine CFSG.Quasithin.Vol2.Ch10.SecD.nonempty_alt5_of_card_sixty ?_
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, ZMod 5))
  rw [CFSG.GH74.GLS.LU.Local.Five.sl2_five_card (MulEquiv.refl _),
    CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card (MulEquiv.refl _)] at h
  change Nat.card (SL(2, ZMod 5) ⧸ Subgroup.center SL(2, ZMod 5)) = 60
  omega

private theorem nonempty_psl2_nine_equiv_alt_six :
    Nonempty (PSL(2, GaloisField 3 2) ≃* alternatingGroup (Fin 6)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  refine unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) ?_
  rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
  norm_num

theorem spFourQuasisimpleLowDim_of (hM : MitchellSpFourList) : SpFourQuasisimpleLowDim := by
  intro q _ hq Y hY hYq
  rcases hM q hq Y hY hYq with h | h | h | h | h | ⟨-, -, h⟩
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr (Or.inl (nonempty_quotCenter_equiv_statedProj_statedSp e)))
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl (nonempty_quotCenter_equiv_psl2 e))))
  · obtain ⟨e⟩ := h
    exact Or.inl (nonempty_quotCenter_equiv_psl2 e)
  · obtain ⟨e⟩ := h
    obtain ⟨e₁⟩ := nonempty_quotCenter_equiv_psl2 e
    obtain ⟨e₂⟩ := nonempty_psl2_five_equiv_alt_five
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e₁.trans e₂⟩))))
  · obtain ⟨e⟩ := h
    obtain ⟨e₁⟩ := nonempty_quotCenter_equiv_psl2 e
    obtain ⟨e₂⟩ := nonempty_psl2_nine_equiv_alt_six
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e₁.trans e₂⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
