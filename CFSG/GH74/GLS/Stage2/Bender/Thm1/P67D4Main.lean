module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Cover
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.OddAut.LangR

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2.Ivk47

section Cover

theorem cf67CoreDeriv_D4_cover (J : Type) [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J)
    (hY : FD4 (J ⧸ Subgroup.center J)) (r : ℕ) (hr : r.Prime)
    (hd : r ∣ Nat.card (Subgroup.center J)) : CF67CoreDeriv (J ⧸ Subgroup.center J) r := by
  exfalso
  obtain ⟨p, f, hp, hf, hp2, hM⟩ := hY
  have hcen := d4_center_eq_bot hJ hp hp2 hf hM
  rw [hcen, Subgroup.card_bot] at hd
  exact absurd (Nat.le_of_dvd one_pos hd) (by have := hr.two_le; omega)

end Cover

end CFSG.GH74.GLS.Stage2.Bender.Thm1
