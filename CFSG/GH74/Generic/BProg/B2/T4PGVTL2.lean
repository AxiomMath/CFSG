module

public import CFSG.GH74.Generic.BProg.B2.T4PGVTBasic
import CFSG.GH74.Generic.S1.Exo.Q3HNoQ8L2

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup

theorem Q3Cent.false_of_psl2 {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {K : Subgroup N} (hs : Q3Cent H t K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : LieModel ↥K .PSL 2 p f) : False := by
  obtain ⟨ψ, hψ⟩ := hs.exists_q8
  exact CFSG.GH74.Generic.S1.Exo.no_q8_of_psl2_model hp hp2
    (PumpupTableBasic.stated_of_lieModel (Or.inl rfl) hK) ψ hψ

theorem q3_l2 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Q3Empty (fun X _ => LieModel X .PSL 2 p f) := by
  intro N _ _ H t K hs hH
  obtain ⟨ψ, hψ⟩ := hs.exists_q8_H
  exact CFSG.GH74.Generic.S1.Exo.no_q8_of_psl2_model hp hp2
    (PumpupTableBasic.stated_of_lieModel (Or.inl rfl) hH) ψ hψ

theorem q3_ree (f : ℕ) : Q3Empty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro N _ _ H t K hs hH
  obtain ⟨ψ, hψ⟩ := hs.exists_q8_H
  exact PumpupTableRee.ree_no_q8
    (CFSG.GH74.Generic.BProg.B1.reeTitsModel_of_lieModel_twistedG2 hH) ψ hψ

end CFSG.GH74.Generic.BProg.B2.T4.PGV
