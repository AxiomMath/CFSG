module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FGS432
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5GB

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_hat_fix_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hh : IsHat ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
      ↥(alternatingGroup (Fin 6)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  classical
  set F := quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) with hFdef
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hKF := c.autI_oTwoUpper_le_genFitting_ch615 hU (hout_of_isHat_ch615 hh)
  have hXF := le_normalizer_genFitting_ch615 hU
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  have hTF : autI hU T ≤ Subgroup.normalizer (F : Set (MulAut _)) :=
    fun x hx => hXF (autI_mono hU (c.hH.1.1.trans le_sup_right) hx)
  have hDF : autI hU D ≤ Subgroup.normalizer (F : Set (MulAut _)) :=
    fun x hx => hXF (autI_mono hU (hD.1.trans le_sup_left) hx)
  by_cases hDc : autI hU D ≤ Subgroup.centralizer (F : Set (MulAut _))
  · apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    rw [← Subgroup.mem_centralizer_iff.mp (hDc hy) k (hKF hk), mul_inv_cancel_right]
    exact hk
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  obtain ⟨d, hdD, hdF, hd1⟩ := exists_mem_of_not_le_centralizer_hat_ch615 hh hS
    (inf_le_left.trans (autI_mono hU le_sup_right)) (c.isSolvable_autI_ch615 hU)
    (autI_mono hU (hD.1.trans le_sup_left)) hDF hDsodd
    (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
    (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
      c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hDc
  obtain ⟨w, hwF, hw1, hwT⟩ := exists_fix_ch615 IntMod.sq_eq_one (c.isPGroup_autI_ch615 hU)
    hfix fun t ht w hw => mem_fixV_of_conj_ch615 (hTF ht) hw
  exact c.false_of_fix_ch615_F4 h432 hU hD hw1 hwT (fun k hk => hwF k (hKF hk)) hdD hd1
    (hwF d hdF)

end Cx615C

end CFSG.Quasithin.H13
