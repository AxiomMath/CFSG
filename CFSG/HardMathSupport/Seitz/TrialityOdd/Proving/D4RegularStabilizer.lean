module

public import CFSG.RankThree.Chevalley.SteinbergBID4RegularCentralizer

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem d4_rootCharStabilizer_subset_one {L : Type} [Field L]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a : Fin Tag.D4.rank → Lˣ}
    (hap : ∀ i, a i ^ p = 1) (hker : rootCharKernel (τ := Tag.D4) a = ∅) :
    rootCharStabilizer (τ := Tag.D4) a ⊆ ({1} : Set (WeylGroup Tag.D4)) := by
  intro u hu
  have hreg : ∀ α : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 α → rootChar a α ≠ 1 := fun α hα h1 => by
    have hmem : α ∈ rootCharKernel (τ := Tag.D4) a := ⟨hα, h1⟩
    rw [hker] at hmem
    exact hmem
  exact Set.mem_singleton_iff.2
    (CFSG.RankThree.Chevalley.eq_one_of_rootChar_smul hp (by omega) hap hreg hu)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

end
