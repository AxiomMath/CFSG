module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.Nodes
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusSplit

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.AGLEmbedding

@[expose] def AltPlusCellD4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (x : Y), CompParabE L J →
    p = 5 → PerfectSectionsAltSq p J → x ∈ L → x ^ p = 1 →
    x ∉ Subgroup.centralizer (L : Set Y) → (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    ∀ n : ℕ, Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 2 →
      False


theorem altPlusCellD_of_four (h4 : AltPlusCellD4) : AltPlusCellD := by
  intro Y _ _ L J p x hC hp hAlt hxL hxp hxC hfix hX _
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | twistedD r q =>
    obtain ⟨hq2, hq, hpq⟩ := hd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq2 e
    rw [hq2] at hm
    have hpq' : p ∣ 2 ^ q.exponent + 1 := by
      rwa [TauCeti.PrimePower.card_def, hq2] at hpq
    obtain ⟨hp5, hf2⟩ := eq_five_of_dvd_two_pow_add_one hp q.exponent_pos hpq'
    by_cases hf4 : 4 ≤ q.exponent
    · exact false_of_altPlus_pomegaMinus_of_four_le hC hp hAlt hm hpq' hf4
    · have hf2' : q.exponent = 2 := by
        by_contra hne
        have h3 : q.exponent = 3 := by omega
        rw [h3, hp5] at hpq'
        norm_num at hpq'
      rw [hf2'] at hm
      exact h4 Y L J p x hC hp5 hAlt hxL hxp hxC hfix r hm
  | _ => exact hd.elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
