module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.Cell
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank


theorem fixThreeVoid_twistedD_residual (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixThreeVoid (IsLieOf IdxTwistedDResidual) := by
  intro Y _ _ L J u h hX
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
  have hq : CFSG.Open.IsQuasisimple ↥L := h.parab.comp.2.2
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  cases d with
  | twistedD r q =>
    obtain ⟨hp2, hcardq, hr⟩ : q.p = 2 ∧ q.card = 2 ∧ (r = 4 ∨ r = 5) := hPd
    have hexp : q.exponent = 1 := by
      have hpos := q.exponent_pos
      by_contra hne
      have h2 : 2 ≤ q.exponent := by omega
      have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      rw [TauCeti.PrimePower.card_def, hp2] at hcardq
      omega
    have hZ : Nat.card (Subgroup.center ↥L) = 1 := by
      have hd : IdxTwistedD (.twistedD r q) := hp2
      obtain ⟨hd', hA, h2A⟩ := ToralCensus.rest_index (P := IdxTwistedD)
        (Or.inr (Or.inr (Or.inl rfl))) hd
      exact ToralCensus.card_center_eq_one_of_index hGA ⟨.twistedD r q, hv⟩ hd' hA h2A e
        h.parab.odd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp2 e
    rw [hp2, hexp] at hm
    obtain ⟨v, hbar⟩ := exists_fixBarFull_of_fixThreeHyp h hZ
    obtain ⟨⟨-, hf, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e'⟩⟩ := hm
    have hcard2 : Nat.card F = 2 := by simpa using hcard
    have := Fintype.ofFinite F
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
    have hn4 : 4 ≤ r := by omega
    exact false_of_fixBarFull_pomegaMinus hirr (n := r) hn4 hcard2 (hbar.map_mulEquiv e')
  | _ => exact hPd.elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
