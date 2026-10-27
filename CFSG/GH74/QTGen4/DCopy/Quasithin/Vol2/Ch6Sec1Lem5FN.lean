module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FGS432
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FN

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_le_dLemma_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hdl : DLemmaFacts_ch615 F)
    (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hTF : autI hU T ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hDF : autI hU D ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hKF : autI hU (oTwoUpper H) ≤ F) (hS : IsSylowTwoOf (autI hU T ⊓ F) F)
    (hfix : fixV F ≠ ⊥) : False := by
  classical
  obtain ⟨-, hout, hNS, hself⟩ := hdl
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
  obtain ⟨d, hdD, hdF, hd1, -⟩ := exists_mem_of_not_le_centralizer_ch615 hout hZ
    hS.isPGroup hS.le (hNS _ hS) (hself _ hS) (inf_le_left.trans (autI_mono hU le_sup_right))
    (autI_mono hU (hD.1.trans le_sup_left)) (c.isSolvable_autI_ch615 hU) hDF hDsodd
    (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
    (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
      c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hDc
  obtain ⟨w, hwF, hw1, hwT⟩ := exists_fix_ch615 IntMod.sq_eq_one (c.isPGroup_autI_ch615 hU)
    hfix fun t ht w hw => mem_fixV_of_conj_ch615 (hTF ht) hw
  exact c.false_of_fix_ch615_F4 h432 hU hD hw1 hwT (fun k hk => hwF k (hKF hk)) hdD hd1
    (hwF d hdF)

theorem false_of_case1_dLemma_fix_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hdl : DLemmaFacts_ch615 (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (hZ : ∀ g ∈ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))),
      (∀ x ∈ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))), g * x = x * g) → g = 1)
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hK := c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1
  exact c.false_of_le_dLemma_ch615_F4 h432 hU hN hD hdl hZ
    (fun x hx => le_normalizer_genFitting_ch615 hU (autI_mono hU (c.hH.1.1.trans le_sup_right) hx))
    (fun x hx => le_normalizer_genFitting_ch615 hU (autI_mono hU (hD.1.trans le_sup_left) hx))
    hK (c.isSylowTwoOf_genFitting_ch615 hU) hfix

end Cx615C

namespace Cx615C

theorem false_of_case1_alt_six_fix_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* ↥(alternatingGroup (Fin 6)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := isSimpleGroup_alt_six_ch615
    exact e.isSimpleGroup
  have hdl := dLemmaFacts_alt_six_ch615 e
  exact c.false_of_case1_dLemma_fix_ch615_F4 h432 hU hN hdl (center_of_isSimpleGroup_ch615 hs hdl.1)
    hfix

theorem false_of_case1_l32_fix_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  obtain ⟨e'⟩ := nonempty_l32_ch615 hK e
  exact c.false_of_case1_dLemma_fix_ch615_F4 h432 hU hN (dLemmaFacts_l32_ch615 e')
    (fun _ hg h => eq_one_of_commute_l32_ch615 e' hg h) hfix

end Cx615C

namespace Cx615C

theorem false_of_case1_small_fix_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (hnab : ∃ a b : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))), a * b ≠ b * a)
    (hcase : (∃ k : ℕ, (k = 6 ∨ k = 7 ∨ k = 8) ∧
        Nonempty (↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
          alternatingGroup (Fin k))) ∨
      ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 3 ≤ k ∧ Nat.card F = 2 ∧
        Nonempty (↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* projectiveSL k F))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  have hdl := dLemmaFacts_of_smallAlt_ch615 hs hnab hcase
  exact c.false_of_case1_dLemma_fix_ch615_F4 h432 hU hN hdl (center_of_isSimpleGroup_ch615 hs hdl.1)
    hfix

theorem false_of_case1_alt_seven_fix_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* ↥(alternatingGroup (Fin 7)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  exact c.false_of_case1_small_fix_ch615_F4 h432 hU hN hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple hq)
    (Or.inl ⟨7, by norm_num, ⟨e⟩⟩) hfix

theorem false_of_case1_binary_linear_fix_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    {k : ℕ} (hk : 3 ≤ k)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL k (ZMod 2)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := CFSG.Quasithin.B69.isSimpleGroup_statedSL_two h2 hk
    exact e.isSimpleGroup
  exact c.false_of_case1_small_fix_ch615_F4 h432 hU hN hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple hq)
    (Or.inr ⟨k, ZMod 2, inferInstance, inferInstance, hk, h2,
      ⟨e.trans ((CFSG.Quasithin.B69.statedSLEquivStatedProj h2 k).trans
        (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL k (ZMod 2)))⟩⟩) hfix

end Cx615C

end CFSG.Quasithin.H13
