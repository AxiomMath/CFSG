module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbGeneric
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwDMain
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

section TwistedD


theorem blockIb_false_twistedD_residual {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y}
    {x : Y} (hP : BlockIbParab Lb Pb)
    (hX : IsLieOf IdxTwistedDResidual (↥Lb ⧸ Subgroup.center ↥Lb))
    (hD : BlockIbData Lb Pb D x) : False := by
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
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
    have hclass : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb) :=
      Or.inl ⟨⟨_, hv⟩, hp2, ⟨e⟩⟩
    have hCP : CompParabE Lb Pb := CompParab.toE (compParab_of_blockIb hP hD hclass)
    obtain ⟨-, -, -, v, hv'⟩ := exists_centCycBar hCP Nat.prime_three hD.Dperf hD.Dle hD.Dcyc
      hD.Dcarry hD.hx hD.hx3 hD.hxC hD.free
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp2 e
    rw [hp2, hexp] at hm
    obtain ⟨⟨-, hf, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e'⟩⟩ := hm
    have hcard2 : Nat.card F = 2 := by simpa using hcard
    have := Fintype.ofFinite F
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
    exact false_of_centCycBar_pomegaMinus hr hirr hcard2 (hv'.map_mulEquiv e')
  | _ => exact hPd.elim

theorem blockIb_false_twistedD {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}
    (hP : BlockIbParab Lb Pb) (hX : IsLieOf IdxTwistedD (↥Lb ⧸ Subgroup.center ↥Lb))
    (hD : BlockIbData Lb Pb D x) : False :=
  (isLieOf_idxTwistedD_cases hX).elim
    (fun h => blockIb_false_of_centPerfectNoncyc kFactCentNoncycThree_twistedD hP h hD)
    (fun h => blockIb_false_twistedD_residual hP h hD)

theorem blockIbRankFam_twistedD : BlockIbRankFam (IsLieOf IdxTwistedD) := by
  intro Y _ _ Lb Pb D x hP hX hD
  exact (blockIb_false_twistedD hP hX hD).elim

theorem blockIbAbFam_twistedD : BlockIbAbFam (IsLieOf IdxTwistedD) := by
  intro Y _ _ Lb Pb D x hP hX hD
  exact (blockIb_false_twistedD hP hX hD).elim

end TwistedD

end CFSG.HardMathSupport.Curtis.UnitaryLevi
