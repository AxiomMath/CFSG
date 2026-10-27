module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkL3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Hbar

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem admRank3_fl3 (k : Kind) {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hp2 : p ≠ 2) (hLie : LieModel Y .PSL 3 p f) : AdmRank3 k Y := by
  intro E hE hadm
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hE
  have hE' : IsElementaryAbelian 2 ↥(E.map (MulAut.congr e).toMonoidHom) :=
    IsElementaryAbelian.map (MulAut.congr e).toMonoidHom
  have hcE : Nat.card ↥(E.map (MulAut.congr e).toMonoidHom) = Nat.card ↥E :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  rw [← hcE]
  refine RkL3.card_le_eight hp hp2 hLie e _ hE' ?_
  rintro _ ⟨x, hxE, rfl⟩ hx1 A σ hσ hxeq
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hxx : x * x = 1 := by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian x hxE
  exact RkL3.false_of_fixed_kindFactorAll hp hp2 hf hcard e hxx A σ hσ hxeq
    (fun Z _ _ hns Q hQ hsec =>
      hadm x hxE hx1' Z hns (IsSection.of_le_le (fun y hy => hQ y hy) hsec))

theorem rankCell_fl3 : RankCell FL3 := by
  intro k _ Y _ _ _ hY
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  exact ⟨EL3.l3_not_kindFactorAll k hp hf (hp.odd_of_ne_two hp2).pow hLie,
    admRank3_fl3 k hp hf hp2 hLie⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
