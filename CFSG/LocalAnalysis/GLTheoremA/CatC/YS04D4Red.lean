module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04BCRes
public import CFSG.HardMathSupport.Timmesfeld.DFour.Tower
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.HardMathSupport.Timmesfeld.DFour

theorem meets_inner_of_three_not_dvd {S : Type} [Group S] [Finite S] {r f : ℕ}
    (hm : StatedClassicalModel S .POmegaPlus 4 r f) (hf : ¬ 3 ∣ f) :
    ∀ X : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 X → Nat.card X = 3 ^ 2 →
      ∃ x ∈ X ⊓ inner S, x ≠ 1 := by
  have h0 := hm
  obtain ⟨⟨hr, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := coordinate_facts_four hm K hK e
  exact meets_of_mulEquiv (p := 3) (k := 2)
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e)
    fun X hX hc => exists_inner_of_not_dvd _ hQ hab hidx hr hK Nat.prime_three (by norm_num) hf
      X hX.2 hc

@[expose] def KD26bcD4Char3Ne : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (r f : ℕ), StatedClassicalModel S .POmegaPlus 4 r f → 3 ∣ f → r ≠ 3 →
      ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D = 3 ^ 2 → D ⊓ inner S = ⊥ →
        ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup S, L ≤ fixSub y ∧ IsSimpleGroup ↥L ∧
          (∃ a b : ↥L, a * b ≠ b * a) ∧ 3 ∣ Nat.card L ∧
          ∀ g ∈ fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L

@[expose] def KD26bcD4Char3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (r f : ℕ), StatedClassicalModel S .POmegaPlus 4 r f → 3 ∣ f → r = 3 →
      ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D = 3 ^ 2 → D ⊓ inner S = ⊥ →
        ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup S, L ≤ fixSub y ∧ IsSimpleGroup ↥L ∧
          (∃ a b : ↥L, a * b ≠ b * a) ∧ 3 ∣ Nat.card L ∧
          ∀ g ∈ fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L

theorem statedModel_of_isPOmegaPlus8 {S : Type} [Group S] {q : ℕ} (hq : IsPOmegaPlus8 S q) :
    ∃ r f : ℕ, StatedClassicalModel S .POmegaPlus 4 r f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hq
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | D r qq =>
      change isPOmegaPlus8 q (TauCeti.LieTypeIndex.D r qq) at hi
      obtain rfl : r = 4 := by
        by_contra hr
        simp [isPOmegaPlus8, hr] at hi
      exact ⟨qq.p, qq.exponent,
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 qq hv e⟩
    | _ => exact (show False from hi).elim
  | _ => exact (show False from hi).elim

theorem kd26bcD4_of_split (h1 : KD26bcD4Char3Ne) (h2 : KD26bcD4Char3) : KD26bcD4 := by
  intro S _ _ hs hna q hq D hD hcard hinn
  obtain ⟨r, f, hm⟩ := statedModel_of_isPOmegaPlus8 hq
  by_cases h3 : 3 ∣ f
  · by_cases hr : r = 3
    · exact h2 S hs hna r f hm h3 hr D hD hcard hinn
    · exact h1 S hs hna r f hm h3 hr D hD hcard hinn
  · exfalso
    obtain ⟨x, hx, hx1⟩ := meets_inner_of_three_not_dvd hm h3 D hD hcard
    have hx' : x ∈ D ⊓ inner S := hx
    rw [hinn, Subgroup.mem_bot] at hx'
    exact hx1 hx'

end CFSG.LocalAnalysis.GLTheoremA
