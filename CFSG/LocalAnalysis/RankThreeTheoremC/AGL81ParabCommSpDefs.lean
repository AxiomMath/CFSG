module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer)

@[expose] noncomputable def spResBlock (K : Type) [Field K] (m : ℕ) : Subgroup (StatedSp m K) := by
  classical
  exact if m = 1 ∧ Nat.card K = 2 then ⊤ else commutator (StatedSp m K)

variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

@[expose] def SpNormFix (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)
    (α : MulAut (StatedSp r K)) : Prop :=
  (∀ x ∈ flagStabilizer r K I, α x ∈ flagStabilizer r K I) ∧
    (∀ (b : ℕ) (hb : b ∈ I) (s : Matrix.SpecialLinearGroup (Fin (b - spFlagPrev I b)) K),
      ∃ u : flagStabilizer r K I, spFlagLeviHom hI htI u = 1 ∧
        (u : StatedSp r K) =
          α (spFlagCutEmb (spFlagPrev I b) b (hI b hb) (Matrix.SpecialLinearGroup.toGL s)) *
            (spFlagCutEmb (spFlagPrev I b) b (hI b hb) (Matrix.SpecialLinearGroup.toGL s))⁻¹) ∧
    (∀ c ∈ spResBlock K (r - t), ∃ u : flagStabilizer r K I, spFlagLeviHom hI htI u = 1 ∧
      (u : StatedSp r K) = α (spFlagResEmb t c) * (spFlagResEmb t c)⁻¹)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
