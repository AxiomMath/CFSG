module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldE8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldE67Odd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldF4G2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEven
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEvenF4G2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2Three

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration
  CFSG.Blueprint.Chevalley

section Fields


theorem crossCharFamAt_E8_field :
    CrossCharFamAt .E8 (regimeExcField TauCeti.LieTypeIndex.E8 (degCount Tag.E8)) := by
  rintro idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf⟩
  by_cases hq2 : q.p = 2
  · exact crossCharFamAt_E8_fieldEven idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  · exact crossCharFamAt_E8_fieldOdd idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩

theorem crossCharFamAt_E7_field :
    CrossCharFamAt .E7 (regimeExcField TauCeti.LieTypeIndex.E7 (degCount Tag.E7)) := by
  rintro idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf⟩
  by_cases hq2 : q.p = 2
  · exact crossCharFamAt_E7_fieldEven idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  · exact crossCharFamAt_E7_fieldOdd idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩

theorem crossCharFamAt_E6_field :
    CrossCharFamAt .E6 (regimeExcField TauCeti.LieTypeIndex.E6 (degCount Tag.E6)) := by
  rintro idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf⟩
  by_cases hq2 : q.p = 2
  · exact crossCharFamAt_E6_fieldEven idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  · exact crossCharFamAt_E6_fieldOdd idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩

theorem crossCharFamAt_F4_field :
    CrossCharFamAt .F4 (regimeExcField TauCeti.LieTypeIndex.F4 (degCount Tag.F4)) := by
  rintro idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf⟩
  by_cases hq2 : q.p = 2
  · exact crossCharFamAt_F4_fieldEven idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  · exact crossCharFamAt_F4_fieldOdd idx hk p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩

@[expose] def regimeG2Field (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∧ 5 ≤ p ∧ p ∣ q.card ^ 2 - 1 ∧ p ∣ q.exponent

theorem crossCharFamAt_G2_field : CrossCharFamAt .G2 regimeG2Field := by
  rintro idx hk p hp hp2 hc ⟨q, hd, hp5, hdq, hpf⟩
  by_cases hq2 : q.p = 2
  · exact crossCharFamAt_G2_fieldEven idx hk p hp hp2 hc ⟨q, hd, hp5, hdq, hpf, hq2⟩
  · by_cases hq3 : q.p = 3
    · exact crossCharFamAt_G2_fieldThree idx hk p hp hp2 hc ⟨q, hd, hp5, hdq, hpf, hq3⟩
    · exact crossCharFamAt_G2_fieldOdd idx hk p hp hp2 hc ⟨q, hd, hp5, hdq, hpf, hq2, hq3⟩

theorem ge_three_or_field_of_not_regimeExcVac {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hc : Function.Injective c) (a : ℕ → ℕ) {idx : TauCeti.ValidLieTypeIndex} {p : ℕ}
    {q : TauCeti.PrimePower} (hq : idx.1 = c q) (h : ¬ regimeExcVac c a idx p) :
    3 ≤ a (orderOf ((q.card : ℕ) : ZMod p)) ∨
      (a (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∧ p ∣ q.exponent) := by
  by_contra h'
  push Not at h'
  obtain ⟨h3, h2f⟩ := h'
  rcases Nat.lt_or_ge (a (orderOf ((q.card : ℕ) : ZMod p))) 2 with h1 | h1
  · exact h (Or.inl ⟨q, hq, Nat.le_of_lt_succ h1⟩)
  · have h2 := le_antisymm (Nat.le_of_lt_succ h3) h1
    exact h (Or.inr ⟨q, hq, h2, h2f h2⟩)

theorem crossCharFamCat_of_ge_three {k : LieFamily}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex} (hc : Function.Injective c)
    (hk : ∀ d, k.Matches d → ∃ q, d = c q) (a : ℕ → ℕ)
    (hvac : CrossCharFamAt k (regimeExcVac c a)) (hfield : CrossCharFamAt k (regimeExcField c a))
    (h3 : CrossCharFamAt k fun idx p =>
      ∃ q : TauCeti.PrimePower, idx.1 = c q ∧ 3 ≤ a (orderOf ((q.card : ℕ) : ZMod p))) :
    CrossCharFamCat k := by
  refine crossCharFamCat_of_at (regimeExcVac c a) hvac ?_
  intro idx hidx p hp hp2 hch hR
  obtain ⟨q, hq⟩ := hk _ hidx
  rcases ge_three_or_field_of_not_regimeExcVac hc a hq hR with h3' | ⟨h2, hpf⟩
  · exact h3 idx hidx p hp hp2 hch ⟨q, hq, h3'⟩
  · exact hfield idx hidx p hp hp2 hch ⟨q, hq, h2, hpf⟩

theorem crossCharFamCat_E8_of_ge_three
    (h3 : CrossCharFamAt .E8 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧
      3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) : CrossCharFamCat .E8 :=
  crossCharFamCat_of_ge_three (fun _ _ h => TauCeti.LieTypeIndex.E8.inj h) (fun _ h => h) _
    crossCharFamAt_E8_vac crossCharFamAt_E8_field h3

theorem crossCharFamCat_E7_of_ge_three
    (h3 : CrossCharFamAt .E7 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧
      3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) : CrossCharFamCat .E7 :=
  crossCharFamCat_of_ge_three (fun _ _ h => TauCeti.LieTypeIndex.E7.inj h) (fun _ h => h) _
    crossCharFamAt_E7_vac crossCharFamAt_E7_field h3

theorem crossCharFamCat_E6_of_ge_three
    (h3 : CrossCharFamAt .E6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))) : CrossCharFamCat .E6 :=
  crossCharFamCat_of_ge_three (fun _ _ h => TauCeti.LieTypeIndex.E6.inj h) (fun _ h => h) _
    crossCharFamAt_E6_vac crossCharFamAt_E6_field h3

theorem crossCharFamCat_F4_of_ge_three
    (h3 : CrossCharFamAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p))) : CrossCharFamCat .F4 :=
  crossCharFamCat_of_ge_three (fun _ _ h => TauCeti.LieTypeIndex.F4.inj h) (fun _ h => h) _
    crossCharFamAt_F4_vac crossCharFamAt_F4_field h3

end Fields

end CFSG.HardMathSupport.Timmesfeld.CrossChar
