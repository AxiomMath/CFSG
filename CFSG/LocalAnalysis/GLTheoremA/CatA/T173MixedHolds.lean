module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedVanish
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.Open CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.T173X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {l : ℕ}

theorem stdVanishes_or_stdExtends (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Even l) (hq : l = 4 → Nat.card F = 2)
    {A : Subgroup ↥(orthDerived Q)} {d : ↥(orthDerived Q)} (hA : GLAIsBmax p A) (hd : IsStdElt p A d) :
    StdVanishes A d ∨ StdExtends p A d := by
  obtain ⟨U, ρ, i, j, hM⟩ := exists_mixedFrame hQ hdim hl hp hp2 hpq htype hA
  rcases standard_trichotomy hM hQ hdim hl hp hp2 hpq hq hd with
    ⟨k, hki, hkj, -, hfs, hL⟩ | ⟨hl5, hdz, hfs, hL⟩ | ⟨h, hh, hh1, hU, hL, hquasi⟩
  · exact Or.inl (stdVanishes_of_weightOne hM hQ hdim hl hp hp2 hd hki hkj hfs hL)
  · exact Or.inr (stdExtends_of_pair hM hQ hdim hl5 hp hp2 hpq hd hdz hfs hL)
  · exact Or.inl (stdVanishes_of_fullSupport hM hQ hdim hl hp hp2 hpq hd hh hh1 hU hL hquasi)

theorem modelFactMixedD : CFSG.LocalAnalysis.GLTheoremA.T173X.ModelFactMixedD := by
  intro F _ _ _ V _ _ _ Q l hQ hdim hl hlev hplus hF2 A d hA hd
  exact stdVanishes_or_stdExtends hQ hdim hl Nat.prime_three (by decide) (by rw [hF2])
    (iff_of_true hplus hlev) (fun _ => hF2) hA hd

theorem modelFactMixedTD : CFSG.LocalAnalysis.GLTheoremA.T173X.ModelFactMixedTD := by
  intro F _ _ _ V _ _ _ Q l p hQ hdim hl hodd hminus hp hp2 hpq A d hA hd
  have htype : IsPlusType Q ↔ Even l := iff_of_false hminus (Nat.not_even_iff_odd.2 hodd)
  have hq : l = 4 → Nat.card F = 2 := fun h => absurd hodd (by rw [h]; decide)
  exact stdVanishes_or_stdExtends hQ hdim hl hp hp2 hpq htype hq hA hd

end CFSG.LocalAnalysis.GLTheoremA.T173M

end
