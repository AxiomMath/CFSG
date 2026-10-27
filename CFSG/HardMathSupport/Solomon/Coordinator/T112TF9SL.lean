module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9SLLift
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9SLCore
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_fieldType_SL {F : Type} [Field F] [Finite F] (hF : Nat.card F % 9 = 1)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (e : K ≃* ↥(CFSG.Open.StatedSL 3 F)) (H : Subgroup (MulAut K))
    (hH : CFSG.Open.IsElemAbelian 3 H) (h27 : Nat.card H = 27) :
    ∃ ψ ∈ H, ¬ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsInnerAut ψ ∧
      ∃ (M : GL (Fin 3) F) (σ : F ≃+* F), ∀ x : K,
        ((e (ψ x) : ↥(CFSG.Open.StatedSL 3 F)) : GL (Fin 3) F) =
          M * Matrix.GeneralLinearGroup.map (σ : F →+* F)
            (M⁻¹ * ((e x : ↥(CFSG.Open.StatedSL 3 F)) : GL (Fin 3) F) * M) * M⁻¹ := by
  let e₁ : K ≃* SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  have hinj := t112_liftHom_injective e₁ hq.1
  let H' : Subgroup (MulAut (projectiveSL 3 F)) := H.map (t112_liftHom e₁)
  have hH' : CFSG.Open.IsElemAbelian 3 H' := by
    have := hH.1
    refine ⟨Subgroup.map_isMulCommutative H (t112_liftHom e₁), ?_⟩
    rintro _ ⟨ψ, hψ, rfl⟩
    rw [← map_pow, hH.2 ψ hψ, map_one]
  have h27' : Nat.card H' = 27 := by
    rw [← h27]
    exact (Subgroup.card_map_of_injective hinj)
  obtain ⟨α, ⟨ψ, hψ, rfl⟩, hαD⟩ := exists_not_mem_linearAutGroup hF H' hH' h27'
  obtain ⟨M, σ, hMσ⟩ := exists_conj_fieldAut_of_pow_three (t112_liftHom e₁ ψ)
    (by rw [← map_pow, hH.2 ψ hψ, map_one]) hαD
  refine ⟨ψ, hψ, ?_, M, σ, ?_⟩
  · rintro ⟨g, hg⟩
    have hψg : ψ = MulAut.conj g := MulEquiv.ext fun t => by rw [hg t]; rfl
    apply hαD
    rw [hψg, liftHom_conj]
    exact conjAut_mem_linearAutGroup _
  · have hψ0 : ψ = MulAut.congr e₁.symm (stdAut M σ) := by
      apply hinj
      rw [hMσ, ← descendAut_stdAut]
      change _ = descendAut 3 F (MulAut.congr e₁ (MulAut.congr e₁.symm (stdAut M σ)))
      have hc : MulAut.congr e₁ (MulAut.congr e₁.symm (stdAut M σ)) = stdAut M σ :=
        MulEquiv.ext fun z => by simp [MulAut.congr_apply]
      rw [hc]
    intro x
    have h1 : e₁ (ψ x) = stdAut M σ (e₁ x) := by
      rw [hψ0]
      simp
    have h2 : ∀ y : K, ((e y : ↥(CFSG.Open.StatedSL 3 F)) : GL (Fin 3) F) =
        SpecialLinearGroup.toGL (e₁ y) := fun y => by
      have := congrArg (fun s : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) => (s : GL (Fin 3) F))
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).apply_symm_apply (e y))
      exact this.symm
    rw [h2, h2, h1, toGL_stdAut]

end CFSG.HardMathSupport.Solomon.Coordinator
