module

public import CFSG.GH74.GLS.Stage1.Thm4.L98e
public import CFSG.GH74.GLS.Stage1.Thm4.Fstar98
public import CFSG.GH74.GLS.Stage1.Thm4.Resid98
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

theorem LBar_eq_top_of_cover {G : Type} [Group G] [Finite G] (z : G) {n : ℕ} (hn : 4 ≤ n)
    (hX : IsDoubleCoverOfAlt (CentralizerBar z) n) : LBar z = ⊤ := by
  rw [CFSG.GH74.GLS.Stage1.Thm6.Prod.LBar_eq z, oPrimePResidual_eq_top_of_cover hX hn,
    CFSG.GH74.GLS.Stage1.Thm6.Prod.innerE_eq_top_of_quasisimple z hX.1]
  exact inf_top_eq _

theorem barOf_eq_top_of_sup {G : Type} [Group G] {z : G} {K : Subgroup G} (hKN : K.subgroupOf (Cz z) ⊔ pPrimeCore 2 ↥(Cz z) = ⊤) : barOf z K = ⊤ := by
  have hN : (pPrimeCore 2 ↥(Cz z)).map (toBar z) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    exact (QuotientGroup.eq_one_iff n).2 hn
  have e : ((K.subgroupOf (Cz z)) ⊔ pPrimeCore 2 ↥(Cz z)).map (toBar z) =
      (K.subgroupOf (Cz z)).map (toBar z) := by
    rw [Subgroup.map_sup, hN, sup_bot_eq]
  unfold barOf
  rw [← e, hKN, Subgroup.map_top]
  exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem core (hA : IVK_5_1_index) (hC : IVK_5_1f) (hD : IVK_5_1d) (hF : Step9_8_Fstar)
    (h96 : Lemma9_6) (hinv : Step9_8_inv) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt Lh n) (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hSylG : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) :
    S ≤ K ∧ K.subgroupOf (Cz z) ⊔ pPrimeCore 2 ↥(Cz z) = ⊤ := by
  haveI : (K.subgroupOf (Cz z)).Normal := h.K_normal_C
  have hyp := h.hypC hF hn8 hn11 hcov
  have hc := core_S_le (N := pPrimeCore 2 ↥(Cz z)) (K := K.subgroupOf (Cz z))
    (S := S.subgroupOf (Cz z)) hA hD hyp odd_card_pPrimeCore h.sylowC (fun u hu hu2 => by
      have hu2' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
      exact hinv G Lh z t S K h.std h.r1 h.q1 (u : G) hu hu2'
        (h.inv_S_conj hA hC hF h96 hn8 hn11 hcov hsimple hnab hSylG (u : G) hu hu2'))
  refine ⟨fun s hs => ?_, hc.2⟩
  exact hc.1 (show (⟨s, h.S_le hs⟩ : ↥(Cz z)) ∈ S.subgroupOf (Cz z) from hs)

theorem S_le_LC (hL : LBar z = ⊤) : S ≤ LC z := by
  intro s hs
  have hsC : s ∈ Cen z := h.S_le hs
  obtain ⟨k, hk⟩ := h.sylowC.isPGroup ⟨⟨s, hsC⟩, hs⟩
  have hk' : (⟨s, hsC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
    have := congrArg (fun x : ↥(S.subgroupOf (Cz z)) => ((x : ↥(Cz z)) : G)) hk
    simpa using this
  exact (CFSG.GH74.GLS.Stage1.Thm6.Prod.mem_LC_iff_of_pElt z ⟨s, hsC⟩ hk').2
    (by rw [hL]; exact Subgroup.mem_top _)

theorem sporadic (hA : IVK_5_1_index) (hB : IVK_5_1g) (hC : IVK_5_1f) (hD : IVK_5_1d)
    (hF : Step9_8_Fstar) (h96 : Lemma9_6) (hinv : Step9_8_inv) :
    ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Stage1Sporadic G z S n ∧ IsCentralInvolution z := by
  obtain ⟨n, hn8, hn11, hcov⟩ := h.std.cover
  have hsimple : IsSimpleGroup G := h.std.std.kps.1
  have hnab : ∃ a b : G, a * b ≠ b * a := h.std.std.kps.2.1
  obtain ⟨hSylG, hcen⟩ := h.sylowG hB hF hn8 hn11 hcov
  have hcore := h.core hA hC hD hF h96 hinv hn8 hn11 hcov hsimple hnab hSylG
  have hbar : barOf z K = ⊤ := barOf_eq_top_of_sup hcore.2
  have hcover : IsDoubleCoverOfAlt (CentralizerBar z) n :=
    isDoubleCoverOfAlt_congr ((MulEquiv.subgroupCongr hbar).trans Subgroup.topEquiv) (h.cover_bar hcov)
  have hL : LBar z = ⊤ := LBar_eq_top_of_cover z (by omega) hcover
  have hSL : S ≤ LC z := h.S_le_LC hL
  have hRC : RC S z = S := inf_eq_left.2 hSL
  refine ⟨n, hn8, hn11, ⟨⟨h.zcen hB hF hn8 hn11 hcov, fun hne => absurd hRC hne,
    fun U hU _ _ => hU.trans hSL⟩, h.one_class hA hB hC hF h96 hn8 hn11 hcov hsimple hnab, hcover, hL⟩,
    hcen⟩

end Ctx98

theorem lemma_9_8 (h96 : Lemma9_6) (hQ1 : Step9_8_Q1) (hinv : Step9_8_inv)
    (hA : IVK_5_1_index) (hB : IVK_5_1g) (hC : IVK_5_1f) (hD : IVK_5_1d) : Lemma9_8 := by
  intro G _ _ Lh _ z t S K hstd hr1
  have h : Ctx98 G Lh z t S K := ⟨hstd, hr1, hQ1 G Lh z t S K hstd hr1⟩
  exact h.sporadic hA hB hC hD step9_8_fstar h96 hinv

theorem prop_9_3 (h97 : Lemma9_7) (h96 : Lemma9_6) (hQ1 : Step9_8_Q1) (hinv : Step9_8_inv)
    (hA : IVK_5_1_index) (hB : IVK_5_1g) (hC : IVK_5_1f) (hD : IVK_5_1d) : Prop9_3 := by
  intro G _ _ Lh _ z t S K hstd
  have hr1 := h97 G Lh z t S K hstd
  exact ⟨hr1, lemma_9_8 h96 hQ1 hinv hA hB hC hD G Lh z t S K hstd hr1⟩

end CFSG.GH74.GLS.Stage1.Thm4
