module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoAct
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoStmt

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Factor


theorem exists_frame_aut {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hK : Nat.card K = ℓ ^ f)
    (D : LangE8Ten K) (v : WeylGroup Tag.E8)
    (hπ : ∀ i j : Fin 5, i ≠ j →
      (QuasiE8Ten.wE8Ten • sigmaRootE8A4 v i j : Fin Tag.E8.rank → ℤ) =
        sigmaRootE8A4 v (Fin.revPerm j) (Fin.revPerm i)) :
    ∃ (Φ : SL(5, D.L) ≃* SL(5, D.L)) (b : Fin 5 → Fin 5 → D.Lˣ),
      (∀ (i j : Fin 5) (hij : i ≠ j) (t : D.L),
        ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(5, D.L)) :
          Matrix (Fin 5) (Fin 5) D.L) =
        1 + Matrix.single (Fin.revPerm j) (Fin.revPerm i) ((b i j : D.L) * t ^ ℓ ^ f)) ∧
      ∀ X, D.nW * D.frobGL (rhoSigmaE8A4 D.L v X) * D.nW⁻¹ = rhoSigmaE8A4 D.L v (Φ X) := by
  classical
  choose! ε hε using fun i j hij => rhoSigmaE8A4_transvection (L := D.L) v i j hij
  have hnm : D.nW ∈ monomialSubgroup Tag.E8 D.L := canonicalRep_mem_monomialSubgroup D.L _
  have hconj : ∀ i j : Fin 5, i ≠ j → ∃ b : D.Lˣ, ∀ c : D.L,
      D.nW * pinnedX Tag.E8 D.L (sigmaRootE8A4 v i j) c * D.nW⁻¹ =
        pinnedX Tag.E8 D.L (sigmaRootE8A4 v (Fin.revPerm j) (Fin.revPerm i)) ((b : D.L) * c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_sigmaRootE8A4 v hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, weylQuotientHom_eq (mapsRootLines_canonicalRep _)]
    exact congrArg (fun r => pinnedX Tag.E8 D.L r ((μ : D.L) * c)) (hπ i j hij)
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E8) (ν := 5)
    (rhoSigmaE8A4 D.L v) (rhoSigmaE8A4_injective v) (sigmaRootE8A4 v) ε
    (fun i j hij t => hε i j hij t) D.Fr D.Fr_bijective D.nW
    (fun i j => (Fin.revPerm j, Fin.revPerm i))
    (fun i j hij => (Fin.revPerm.injective.ne hij).symm)
    (fun i j hij => ⟨Fin.revPerm.symm j, Fin.revPerm.symm i,
      (Fin.revPerm.symm.injective.ne hij).symm, by simp⟩) hconj
  refine ⟨Φ', b, fun i j hij t => ?_, hΦ'⟩
  rw [hshape i j hij t, D.hFr, hK]

theorem frame_factor_le_hyperClosure {K : Type} [Field K] [Finite K]
    (hK5 : 5 ∣ Nat.card K + 1) (D : LangE8Ten K) (v : WeylGroup Tag.E8)
    (S : Set (Fin Tag.E8.rank → ℤ))
    (hρS : (rhoSigmaE8A4 D.L v).range = rootSpan Tag.E8 D.L S)
    (hπ : ∀ i j : Fin 5, i ≠ j →
      (QuasiE8Ten.wE8Ten • sigmaRootE8A4 v i j : Fin Tag.E8.rank → ℤ) =
        sigmaRootE8A4 v (Fin.revPerm j) (Fin.revPerm i))
    (E : Subgroup (adjointGroup Tag.E8 K)) (hEc : Nat.card E = 5 ^ 3)
    (z e₀ e₁ : adjointGroup Tag.E8 K) (εz ε₀ ε₁ : ModGL Tag.E8 D.L)
    (hz : z ∈ E) (he₀ : e₀ ∈ E) (he₁ : e₁ ∈ E)
    (hιz : baseChangeGL (algebraMap K D.L) (z : ModGL Tag.E8 K) = D.g * εz * D.g⁻¹)
    (hι₀ : baseChangeGL (algebraMap K D.L) (e₀ : ModGL Tag.E8 K) = D.g * ε₀ * D.g⁻¹)
    (hι₁ : baseChangeGL (algebraMap K D.L) (e₁ : ModGL Tag.E8 K) = D.g * ε₁ * D.g⁻¹)
    (hs : HeisShape (rhoSigmaE8A4 D.L v) εz ε₀ ε₁)
    (hidx : ∀ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) →
      Subgroup.closure ({z, e₀ ^ a * e₁ ^ b} : Set (adjointGroup Tag.E8 K)) ≤ E ∧
      (Subgroup.closure ({z, e₀ ^ a * e₁ ^ b} : Set (adjointGroup Tag.E8 K))).relIndex E = 5) :
    D.frame S ≤ (hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E).map
      (adjointGroup Tag.E8 K).subtype := by
  classical
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  have hcard' : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨Φ, b, hΦ, hΦρ⟩ := exists_frame_aut hcard' D v hπ
  obtain ⟨hεz, M₀, M₁, ζ, c₀, c₁, hζ, hε₀, hε₁, hcomm, h₀, h₁⟩ := hs
  exact frame_le_hyperClosure hpp m.pos hcard' (hcard' ▸ hK5) D (rhoSigmaE8A4 D.L v)
    (rhoSigmaE8A4_injective v) hρS Φ Fin.revPerm b hΦ hΦρ E hEc z e₀ e₁ εz ε₀ ε₁ hz he₀ he₁
    hιz hι₀ hι₁ (fun A => by
      have h := hεz A
      rw [conjSLn_one'] at h
      calc εz * rhoSigmaE8A4 D.L v A = εz * rhoSigmaE8A4 D.L v A * εz⁻¹ * εz := by group
        _ = rhoSigmaE8A4 D.L v A * εz := by rw [h]) M₀ M₁ hε₀ hε₁ hζ hcomm h₀ h₁ hidx

theorem frames_le_hyperClosure {K : Type} [Field K] [Finite K]
    (hK5 : 5 ∣ Nat.card K + 1) (D : LangE8Ten K)
    (E : Subgroup (adjointGroup Tag.E8 K)) (hEc : Nat.card E = 5 ^ 3)
    (z e₀ e₁ : adjointGroup Tag.E8 K) (εz ε₀ ε₁ : ModGL Tag.E8 D.L)
    (hz : z ∈ E) (he₀ : e₀ ∈ E) (he₁ : e₁ ∈ E)
    (hιz : baseChangeGL (algebraMap K D.L) (z : ModGL Tag.E8 K) = D.g * εz * D.g⁻¹)
    (hι₀ : baseChangeGL (algebraMap K D.L) (e₀ : ModGL Tag.E8 K) = D.g * ε₀ * D.g⁻¹)
    (hι₁ : baseChangeGL (algebraMap K D.L) (e₁ : ModGL Tag.E8 K) = D.g * ε₁ * D.g⁻¹)
    (hA : HeisShape (rhoSigmaE8A4 D.L e8VA) εz ε₀ ε₁)
    (hB : HeisShape (rhoSigmaE8A4 D.L e8VB) εz ε₀ ε₁)
    (hidx : ∀ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) →
      Subgroup.closure ({z, e₀ ^ a * e₁ ^ b} : Set (adjointGroup Tag.E8 K)) ≤ E ∧
      (Subgroup.closure ({z, e₀ ^ a * e₁ ^ b} : Set (adjointGroup Tag.E8 K))).relIndex E = 5) :
    TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤
      (hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E).map
        (adjointGroup Tag.E8 K).subtype := by
  refine sup_le ?_ ?_
  · refine frame_factor_le_hyperClosure hK5 D e8VB TwClass.e8Ten.S₁
      ((rhoSigmaE8A4_range e8VB).trans (congrArg (rootSpan Tag.E8 D.L)
        (QuasiE8Ten.sigmaSet_B.trans QuasiE8Ten.S₁_eq.symm))) ?_ E hEc z e₀ e₁ εz ε₀ ε₁ hz he₀
      he₁ hιz hι₀ hι₁ hB hidx
    intro i j hij
    show (QuasiE8Ten.wE8Ten • sigmaRootE8A4 e8VB i j : Fin Tag.E8.rank → ℤ) =
      sigmaRootE8A4 e8VB (Fin.revPerm j) (Fin.revPerm i)
    rw [sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul, QuasiE8Ten.w_smul, e8VB_smul, e8VB_smul]
    exact QuasiE8Ten.graph_B i j hij
  · refine frame_factor_le_hyperClosure hK5 D e8VA TwClass.e8Ten.S₂
      ((rhoSigmaE8A4_range e8VA).trans (congrArg (rootSpan Tag.E8 D.L)
        (QuasiE8Ten.sigmaSet_A.trans QuasiE8Ten.S₂_eq.symm))) ?_ E hEc z e₀ e₁ εz ε₀ ε₁ hz he₀
      he₁ hιz hι₀ hι₁ hA hidx
    intro i j hij
    show (QuasiE8Ten.wE8Ten • sigmaRootE8A4 e8VA i j : Fin Tag.E8.rank → ℤ) =
      sigmaRootE8A4 e8VA (Fin.revPerm j) (Fin.revPerm i)
    rw [sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul, QuasiE8Ten.w_smul, e8VA_smul, e8VA_smul]
    exact QuasiE8Ten.graph_A i j hij

end Factor

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
