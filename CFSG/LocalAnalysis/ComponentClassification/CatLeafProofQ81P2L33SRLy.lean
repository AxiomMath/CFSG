module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint

theorem ly_centralizer_not_isPGroup
    {T : Type*} [Group T] (hT : Nonempty (T ≃* NativeSporadic.Ly)) {t : T}
    (ht : orderOf t = 2) : ¬ IsPGroup 2 ↥(centralizer ({t} : Set T)) := by
  obtain ⟨-, -, ⟨φ⟩⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple hT t ht
  have hA : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  exact not_isPGroup_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (not_isPGroup_of_mulEquiv φ (not_isPGroup_of_three_dvd (by rw [hA]; norm_num)))

theorem forall_conj_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ α : MulAut X, ∃ g, α = MulAut.conj g) : ∀ α : MulAut Y, ∃ g, α = MulAut.conj g := by
  intro α
  obtain ⟨g, hg⟩ := h ((MulAut.congr e).symm α)
  refine ⟨e g, ?_⟩
  have := congrArg (MulAut.congr e) hg
  rw [MulEquiv.apply_symm_apply] at this
  rw [this]
  ext y
  simp [MulAut.congr_apply]

theorem sporNoTwoFix_Ly :
    SporNoTwoFix .Ly := by
  intro Y _ _ ⟨e₀⟩
  have e : Y ≃* NativeSporadic.Ly := e₀
  obtain ⟨-, -, hs⟩ := CFSG.Sporadic.Ly.fam_ly_simplicity
  have hsY : IsSimpleGroup Y := @MulEquiv.isSimpleGroup _ _ _ _ hs e
  have hZ : center Y = ⊥ := center_eq_bot_of_not_prime hsY
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ly.card_Ly) (by norm_num)
  have htop := CFSG.ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput
  have key : ∀ α : MulAut NativeSporadic.Ly, ∃ g : NativeSporadic.Ly, α = MulAut.conj g := by
    intro α
    have hα : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Ly := by
      rw [htop]
      trivial
    obtain ⟨g, hg⟩ := hα
    exact ⟨g, hg.symm⟩
  exact forall_of_inner hZ (forall_conj_of_mulEquiv e₀.symm key) fun t ht =>
    ly_centralizer_not_isPGroup ⟨e⟩ ht

end CFSG.ComponentClassification.HarrisLit.L33.SR
