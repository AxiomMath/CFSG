module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {Y : Type} [Group Y]

theorem forall_mk_eq_iff_congr_centerDescend {M : Type} [Group M]
    (θ : (Y ⧸ Subgroup.center Y) ≃* M) (α : MulAut Y) (φ : MulAut M) :
    (∀ y : Y, θ (QuotientGroup.mk (α y)) = φ (θ (QuotientGroup.mk y))) ↔
      MulAut.congr θ (centerDescend Y α) = φ := by
  constructor
  · intro h
    ext x
    obtain ⟨z, rfl⟩ := θ.surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    change θ (centerDescend Y α (θ.symm (θ (QuotientGroup.mk y)))) = φ (θ (QuotientGroup.mk y))
    rw [MulEquiv.symm_apply_apply, centerDescend_mk]
    exact h y
  · rintro rfl y
    change θ (QuotientGroup.mk (α y)) =
      θ (centerDescend Y α (θ.symm (θ (QuotientGroup.mk y))))
    rw [MulEquiv.symm_apply_apply, centerDescend_mk]

theorem isInnDiagPSL3_iff_exists_marking (α : MulAut Y) :
    LocalBalance.IsInnDiagPSL3 α ↔
      ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (θ : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)),
          IsInnDiagPSL 3 θ (centerDescend Y α) := by
  constructor
  · rintro ⟨K, hK, hf, θ, φ, ⟨g, -, hg⟩, hθ⟩
    obtain rfl := (forall_mk_eq_iff_congr_centerDescend θ α φ).1 hθ
    exact ⟨K, hK, hf, θ, g, hg⟩
  · rintro ⟨K, hK, hf, θ, g, hg⟩
    exact ⟨K, hK, hf, θ, MulAut.congr θ (centerDescend Y α),
      ⟨g, mem_normalizer_statedSL g, hg⟩,
      (forall_mk_eq_iff_congr_centerDescend θ α _).2 rfl⟩

theorem isInnDiagPSL3_iff_mem_innAutDerived (α : MulAut Y) :
    LocalBalance.IsInnDiagPSL3 α ↔
      (∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nonempty ((Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K))) ∧
        centerDescend Y α ∈ innAutDerived (Y ⧸ Subgroup.center Y) := by
  rw [isInnDiagPSL3_iff_exists_marking]
  constructor
  · rintro ⟨K, hK, hf, θ, h⟩
    exact ⟨⟨K, hK, hf, ⟨θ⟩⟩, (isInnDiagPSL_three_iff_mem_innAutDerived θ _).1 h⟩
  · rintro ⟨⟨K, hK, hf, ⟨θ⟩⟩, h⟩
    exact ⟨K, hK, hf, θ, (isInnDiagPSL_three_iff_mem_innAutDerived θ _).2 h⟩

end CFSG.HardMathSupport.Solomon.Coordinator
