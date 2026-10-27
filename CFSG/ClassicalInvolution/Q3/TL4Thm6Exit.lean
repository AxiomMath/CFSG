module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTools
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem lieModel_classical_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (ht : t = .PSL ∨ t = .PSU)
    (h : CFSG.Blueprint.LieModel A t n p f) : CFSG.Blueprint.LieModel B t n p f := by
  rcases h with ⟨htc, hadm, hm⟩ | ⟨-, htc, -⟩ | ⟨-, htc, -⟩ | ⟨-, htc, -⟩
  · refine Or.inl ⟨htc, hadm, ?_⟩
    rcases ht with rfl | rfl
    · obtain ⟨K, hK, hKf, hc, ⟨e'⟩⟩ := hm
      exact ⟨K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
    · obtain ⟨K, hK, hKf, hc, ⟨e'⟩⟩ := hm
      exact ⟨K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
  all_goals rcases ht with rfl | rfl <;> exact absurd htc (by decide)

theorem thm6Exit_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : FStarQuot X ≃* FStarQuot Y)
    (hidx : (genFittingFStar X).index = (genFittingFStar Y).index) (h : Thm6Exit X) :
    Thm6Exit Y := by
  rcases h with ⟨p, f, hp, hp2, ⟨hf, hl, hi⟩ | ⟨hl, hi⟩⟩ | ⟨⟨e'⟩, hi⟩
  · rw [hidx] at hi
    exact Or.inl ⟨p, f, hp, hp2,
      Or.inl ⟨hf, lieModel_classical_of_mulEquiv e (Or.inl rfl) hl, hi⟩⟩
  · rw [hidx] at hi
    refine Or.inl ⟨p, f, hp, hp2, Or.inr ⟨?_, hi⟩⟩
    rcases hl with hl | hl
    · exact Or.inl (lieModel_classical_of_mulEquiv e (Or.inl rfl) hl)
    · exact Or.inr (lieModel_classical_of_mulEquiv e (Or.inr rfl) hl)
  · rw [hidx] at hi
    exact Or.inr ⟨⟨e.symm.trans e'⟩, hi⟩

theorem center_eq_bot_of_simple {K : Type} [Group K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  rcases (Subgroup.center K).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center K := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

noncomputable def fstarQuotEquiv {Y : Type} [Group Y] [IsSimpleGroup ↥(genFittingFStar Y)]
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) :
    FStarQuot Y ≃* ↥(genFittingFStar Y) :=
  (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hnab)).trans
    QuotientGroup.quotientBot

theorem lieModel_fstarQuot {Y : Type} [Group Y] [IsSimpleGroup ↥(genFittingFStar Y)]
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a)
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (ht : t = .PSL ∨ t = .PSU)
    (h : CFSG.Blueprint.LieModel ↥(genFittingFStar Y) t n p f) :
    CFSG.Blueprint.LieModel (FStarQuot Y) t n p f :=
  lieModel_classical_of_mulEquiv (fstarQuotEquiv hnab).symm ht h

theorem thm6Exit_of_fstarQuot {Y : Type} [Group Y] [Finite Y] (hQ : TightFStarQuasisimple Y)
    (hNc : TA3.fstarCenter Y ≤ Subgroup.center Y) (h : Thm6Exit (Y ⧸ TA3.fstarCenter Y)) :
    Thm6Exit Y := by
  have hF := TA3.genFittingFStar_quotient_fstarCenter Y hQ hNc
  have := TA3.isSimpleGroup_fstarBar Y hQ
  have : IsSimpleGroup ↥(genFittingFStar (Y ⧸ TA3.fstarCenter Y)) :=
    (MulEquiv.subgroupCongr hF).isSimpleGroup
  have hnab : ∃ a b : ↥(genFittingFStar (Y ⧸ TA3.fstarCenter Y)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := TA3.exists_ne_comm_fstarBar Y hQ
    refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b, fun h => ?_⟩
    exact hab (by simpa using congrArg (MulEquiv.subgroupCongr hF) h)
  obtain ⟨e₁⟩ := TA3.nonempty_fstarBar_equiv Y
  let e : FStarQuot (Y ⧸ TA3.fstarCenter Y) ≃* FStarQuot Y :=
    ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hnab)).trans
      QuotientGroup.quotientBot).trans ((MulEquiv.subgroupCongr hF).trans e₁)
  refine thm6Exit_of_mulEquiv e ?_ h
  rw [hF]
  exact Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact Subgroup.map_subtype_le _)

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
