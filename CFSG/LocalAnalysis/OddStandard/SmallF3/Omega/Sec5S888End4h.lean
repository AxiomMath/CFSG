module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4g

public section

open CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

theorem xlevel_dichotomy (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c)
    {X : Type} [Group X] [Finite X] {S : Sylow 2 X} {V : Subgroup X} {W : Fin 4 → Subgroup X}
    {ρ : Fin 4 → X} (hX : XData S V W ρ) {A : Fin 4 → Subgroup X}
    (hAle : ∀ i, A i ≤ normalizer (V : Set X))
    (hAsub : ∀ i, ((A i).subgroupOf (normalizer (V : Set X))).IsSubnormal) :
    (∃ Nn : Subgroup X, Nn.Normal ∧ Odd (Nat.card Nn) ∧ ∀ i, (A i ⊔ Nn).IsSubnormal) ∨
      (∃ (Ob : Subgroup X) (_ : Ob.Normal) (B : Subgroup X) (i : Fin 4) (p n : ℕ)
        (_ : Fact p.Prime), Odd (Nat.card Ob) ∧ Ob ≤ B ∧ B.IsSubnormal ∧ W i ≤ B ∧ Odd p ∧
          0 < n ∧ 5 ≤ p ^ n ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧
            Nonempty (↥B ⧸ Ob.subgroupOf B ≃* PSL(2, GaloisField p n))) := by
  have hV : IsPGroup 2 V := IsPGroup.of_card hX.planes.card_V
  rcases xdata_dichotomy hGold hX with ⟨Nn, hNn, hodd, hVN⟩ | hB
  · left
    haveI := hNn
    exact ⟨Nn, hNn, hodd, fun i => caseA_subnormal hV hodd hVN (hAle i) (hAsub i)⟩
  · right
    exact caseB_data hN11a hN11b hN11c hX hB

end CFSG.OddStandard.SmallF3.Omega
