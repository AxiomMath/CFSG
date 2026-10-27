module

public import CFSG.LieType.ChevTwo.OppCl.AutLiftsNorm
public import CFSG.LieType.BorelTits.OrthogonalModels
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section Orth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_semilin_of_orth_similarity (Φ : QuadForm F (ι → F)) (H : Subgroup (GL ι F))
    (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ)
    (hQ : ∀ v : ι → F, Φ.Q (Matrix.mulVec (A : Matrix ι ι F) (fun i => φ (v i))) =
      μ * φ (Φ.Q v))
    (α : MulAut (StatedProj H))
    (hα : ∀ x : H, ∃ y : H, (y : GL ι F) =
        A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv ι φ
          (x : GL ι F) * A⁻¹ ∧
      α (QuotientGroup.mk x) = QuotientGroup.mk y) :
    ∃ s : Equiv.Perm (ι → F), s ∈ semilinGroup F (ι → F) ∧ SemiIsoQ Φ s ∧
      Induces (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) (natRep H) s α := by
  obtain ⟨c, hc⟩ := exists_unit_sq_mul_eq_one μ
  refine ⟨semilinMap (Matrix.GeneralLinearGroup.scalar ι c * A) φ, semilinMap_mem _ _,
    ⟨φ, fun v => ?_⟩, induces_of_conj_scalar H A c φ α fun h => ?_⟩
  · rw [semilinMap_scalar_mul, Φ.Q_smul, semilinMap_apply, hQ]
    linear_combination (φ (Φ.Q v)) * hc
  · obtain ⟨y, hy1, hy2⟩ := hα h
    refine ⟨y, ?_, hy2⟩
    rw [hy1]
    simp only [Units.val_mul]
    rfl

end Orth

section Aux

variable (F : Type) [Field F] [Finite F] [CharP F 2]

theorem exists_card_eq_two_pow_orth : ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨e, -, he⟩ := FiniteField.card F 2
  exact ⟨e, e.pos, by rw [Nat.card_eq_fintype_card, he]⟩

theorem induced_POmegaPlus_aux (n : ℕ) (hn : 5 ≤ n)
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus n F)))) :
    ∃ s : Equiv.Perm (Fin n ⊕ Fin n → F), s ∈ semilinGroup F (Fin n ⊕ Fin n → F) ∧
      SemiIsoQ (quadPlusForm n F) s ∧
      Induces (QuotientGroup.mk'
        ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedOmega (StatedQuadPlus n F))))
        (natRep (StatedOmega (StatedQuadPlus n F))) s α := by
  obtain ⟨f, hf, hcard⟩ := exists_card_eq_two_pow_orth F
  have hadm : StatedLieAdmissible .POmegaPlus n 2 f := ⟨Nat.prime_two, hf, by omega⟩
  obtain ⟨A, φ, μ, hQ, hα⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_plus hadm hn hcard α
  refine exists_semilin_of_orth_similarity (quadPlusForm n F) _ A φ μ (fun v => ?_) α hα
  have e := congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus n F)
  have h1 := hQ v
  rw [e, e] at h1
  exact h1

theorem induced_POmegaMinus_aux (n : ℕ) (hn : 4 ≤ n) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) :
    ∃ s : Equiv.Perm (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
      s ∈ semilinGroup F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ∧
      SemiIsoQ (quadMinusForm n F b c hirr) s ∧
      Induces (QuotientGroup.mk'
        ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).subgroupOf
          (StatedOmega (StatedQuadMinus n F b c))))
        (natRep (StatedOmega (StatedQuadMinus n F b c))) s α := by
  obtain ⟨f, hf, hcard⟩ := exists_card_eq_two_pow_orth F
  have hadm : StatedLieAdmissible .POmegaMinus n 2 f := ⟨Nat.prime_two, hf, hn⟩
  obtain ⟨A, φ, μ, hQ, hα⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_minus hadm hcard hirr α
  refine exists_semilin_of_orth_similarity (quadMinusForm n F b c hirr) _ A φ μ
    (fun v => ?_) α hα
  have e := congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus n F b c)
  have h1 := hQ v
  rw [e, e] at h1
  exact h1

end Aux

end CFSG.LieType.ChevTwo.OppCl
