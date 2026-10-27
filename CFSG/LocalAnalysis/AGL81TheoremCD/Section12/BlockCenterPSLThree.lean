module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecTop
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockReduce
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourJComp

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem center_barM_eq_bot_of_psl_three_odd
    {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) {f : ℕ} (hf : Odd f)
    (hm : StatedClassicalModel (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) .PSL 3 2 f) :
    Subgroup.center ↥(barM M L) = ⊥ := by
  have hodd := CFSG.AGLEmbedding.LeviBlock.odd_card_center_barM hL
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
  obtain ⟨F, iF, iFin, φ, hF, hcov⟩ :=
    CFSG.QuasithinUnique.Setup.X7Sec.exists_cover_of_model hperf hodd hf.pos hm
  rw [← hcov.map_scalars, eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨c, hc3, hcy⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars.mp hy
  have hc1 : c = 1 := by
    have hdvd : orderOf c ∣ Nat.gcd 3 (Nat.card Fˣ) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_natCard c)
    rw [Nat.card_units, hF, gcd_three_two_pow_sub_one_of_odd hf] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  have hy1 : y = 1 := by
    refine Subtype.ext ?_
    rw [hcy, hc1]
    simp
  rw [hy1, map_one, Subgroup.mem_bot]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
