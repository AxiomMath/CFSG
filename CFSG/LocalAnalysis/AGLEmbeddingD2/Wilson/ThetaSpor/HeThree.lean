
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeBase

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeSmall
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.HeldB.CertPBridgeCheckInputs
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Data.CFSGNative.He.Certificate
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeCheck

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.LocalRank
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

theorem counts_parts :
    countWPar 1 (commB heThreeBA heBase)
        (heBlock0.filter fun t0 => heThreeBA[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] = 7560 ∧
    countWPar 1 (commB heThreeBB heBase)
        (heBlock0.filter fun t0 => heThreeBB[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] = 504 ∧
    countWPar 1 (fun w => fixB heBase w 3) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] = 12609 := by
  have h := heThree_counts
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_cent_A :
    Nat.card (centralizerIn heP (bOf heThreeWordsA)) = 7560 := by
  rw [centralizerIn, card_inf_centralizer]
  have hd := bigDataA
  exact (card_heP_eq_count_filter (f := commB (heThreeArr (heThreeWordsA.getD 0 [])) heBase)
    (g := commB (heThreeArr (heThreeWordsA.getD 0 [])) heBase)
    (fun x => bOf heThreeWordsA * x = x * bOf heThreeWordsA) _ (by norm_num)
    (fun w x hw hx => commB_iff_heP (rep_bOf hd) bOf_mem hw hx)
    fun t0 _ t1 h1 t2 h2 => commB_prune hd.zero (heBlock12_fix0 h1 h2).1
      (heBlock12_fix0 h1 h2).2).trans counts_parts.1

theorem card_cent_B :
    Nat.card (centralizerIn heP (bOf heThreeWordsB)) = 504 := by
  rw [centralizerIn, card_inf_centralizer]
  have hd := bigDataB
  exact (card_heP_eq_count_filter (f := commB (heThreeArr (heThreeWordsB.getD 0 [])) heBase)
    (g := commB (heThreeArr (heThreeWordsB.getD 0 [])) heBase)
    (fun x => bOf heThreeWordsB * x = x * bOf heThreeWordsB) _ (by norm_num)
    (fun w x hw hx => commB_iff_heP (rep_bOf hd) bOf_mem hw hx)
    fun t0 _ t1 h1 t2 h2 => commB_prune hd.zero (heBlock12_fix0 h1 h2).1
      (heBlock12_fix0 h1 h2).2).trans counts_parts.2.1

theorem card_heP_cube0 :
    Nat.card {x : heP // (x : Equiv.Perm (Fin 8330)) ^ 3 = 1 ∧
      (x : Equiv.Perm (Fin 8330)) 0 = 0} = 12609 :=
  (card_heP_eq_count_filter (f := fun w => fixB heBase w 3)
    (g := fun w => fixB heBase w 3 && (evR w 0 == 0))
    (fun x => x ^ 3 = 1 ∧ x 0 = 0) _ (by norm_num)
    (fun w x hw hx => by
      have h := CFSG.Sporadic.Schreier.fixB_iff_eq_one heP_baseFaithful heBase_lt hw hx 3
      rw [Bool.and_eq_true, h, evR_zero_iff hw])
    fun t0 _ t1 h1 t2 h2 => zero_prune (fun w => fixB heBase w 3) (t0 := t0)
      (heBlock12_fix0 h1 h2).1 (heBlock12_fix0 h1 h2).2).trans counts_parts.2.2

theorem ncard_heThrees_zero :
    {x | x ∈ heThrees ∧ x 0 = 0}.ncard = 12608 := by
  have h1 : {x : Equiv.Perm (Fin 8330) | x ∈ heP ∧ x ^ 3 = 1 ∧ x 0 = 0}.ncard = 12609 := by
    rw [← card_heP_cube0, ← Nat.card_coe_set_eq]
    exact Nat.card_congr {
      toFun := fun x => ⟨⟨x, x.2.1⟩, x.2.2⟩
      invFun := fun x => ⟨x.1, x.1.2, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h2 : {x : Equiv.Perm (Fin 8330) | x ∈ heP ∧ x ^ 3 = 1 ∧ x 0 = 0} =
      insert 1 {x | x ∈ heThrees ∧ x 0 = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hx, hx3, hx0⟩
      by_cases h : x = 1
      · exact Or.inl h
      · exact Or.inr ⟨⟨hx, orderOf_eq_prime hx3 h⟩, hx0⟩
    · rintro (rfl | ⟨⟨hx, hx3⟩, hx0⟩)
      · exact ⟨heP.one_mem, one_pow 3, rfl⟩
      · refine ⟨hx, ?_, hx0⟩
        rw [← hx3]
        exact pow_orderOf_eq_one x
  have h3 : (1 : Equiv.Perm (Fin 8330)) ∉ {x | x ∈ heThrees ∧ x 0 = 0} := fun h => by
    have := h.1.2
    rw [orderOf_one] at this
    exact absurd this (by norm_num)
  rw [h2, Set.ncard_insert_of_notMem h3 (Set.toFinite _)] at h1
  omega

theorem ncard_conjClass_A :
    (conjClass heP (bOf heThreeWordsA)).ncard = 533120 := by
  have h := ncard_conjClass_mul_card heP (bOf heThreeWordsA)
  rw [card_cent_A, card_heP] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

theorem ncard_conjClass_B :
    (conjClass heP (bOf heThreeWordsB)).ncard = 7996800 := by
  have h := ncard_conjClass_mul_card heP (bOf heThreeWordsB)
  rw [card_cent_B, card_heP] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

theorem three_conj_cases
    {s : Equiv.Perm (Fin 8330)} (hs : s ∈ heP) (hs3 : orderOf s = 3) :
    s ∈ conjClass heP (bOf heThreeWordsA) ∨ s ∈ conjClass heP (bOf heThreeWordsB) := by
  have hXf := Set.toFinite heThrees
  have h0f := Set.toFinite (conjClass heP (bOf heThreeWordsA))
  have h1f := Set.toFinite (conjClass heP (bOf heThreeWordsB))
  have hdisj : Disjoint h0f.toFinset h1f.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    rw [Set.Finite.mem_toFinset] at hx0 hx1
    obtain ⟨c, hc, rfl⟩ := hx0
    obtain ⟨d, hd, hx⟩ := hx1
    have hmem : bOf heThreeWordsB ∈ conjClass heP (bOf heThreeWordsA) :=
      ⟨d⁻¹ * c, heP.mul_mem (heP.inv_mem hd) hc, by
        rw [show bOf heThreeWordsB = d⁻¹ * (d * bOf heThreeWordsB * d⁻¹) * d by group, ← hx]
        group⟩
    have hle := Set.ncard_le_ncard (conjClass_subset_of_mem hmem) (Set.toFinite _)
    rw [ncard_conjClass_A, ncard_conjClass_B] at hle
    omega
  have hYX : h0f.toFinset ∪ h1f.toFinset ⊆ hXf.toFinset := by
    rw [Finset.union_subset_iff, Set.Finite.toFinset_subset_toFinset,
      Set.Finite.toFinset_subset_toFinset]
    exact ⟨conjClass_subset_heThrees bOf_mem (orderOf_bOf bigDataA),
      conjClass_subset_heThrees bOf_mem (orderOf_bOf bigDataB)⟩
  have hfilter : (hXf.toFinset.filter fun x => x 0 = 0).card = 12608 := by
    rw [← ncard_heThrees_zero, ← Set.ncard_coe_finset]
    apply congrArg Set.ncard
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hsumX : ∑ x ∈ hXf.toFinset, fixCard x = 8330 * 12608 := by
    rw [sum_fixCard_eq (G := heP) 0 (fun q => ?_) hXf.toFinset (fun x hx h hh => ?_), hfilter]
    · have := heP_pretransitive
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq heP (0 : Fin 8330) q
      exact ⟨g, g.2, hg⟩
    · rw [Set.Finite.mem_toFinset] at hx ⊢
      exact heThrees_conj hx hh
  have hsumY : ∑ x ∈ h0f.toFinset ∪ h1f.toFinset, fixCard x =
      533120 * 77 + 7996800 * 8 := by
    rw [Finset.sum_union hdisj, sum_fixCard_conjClass, sum_fixCard_conjClass,
      ncard_conjClass_A, ncard_conjClass_B, fixCard_bOf bigDataA, fixCard_bOf bigDataB]
  have hrest : ∑ x ∈ hXf.toFinset \ (h0f.toFinset ∪ h1f.toFinset), fixCard x = 0 := by
    have h := Finset.sum_sdiff hYX (f := fixCard)
    omega
  have hsX : s ∈ hXf.toFinset := (Set.Finite.mem_toFinset _).2 ⟨hs, hs3⟩
  by_contra hno
  rw [not_or] at hno
  have hsY : s ∉ h0f.toFinset ∪ h1f.toFinset := by
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact fun h => h.elim hno.1 hno.2
  have hx0 := (Finset.sum_eq_zero_iff.1 hrest) s (Finset.mem_sdiff.2 ⟨hsX, hsY⟩)
  obtain ⟨q, hq⟩ := exists_fix_of_orderOf_three (n := 8330) (by norm_num) hs3
  rw [fixCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hx0
  exact hx0 (Finset.mem_univ q) hq

theorem heThree_theta_A :
    aschbacherSolvableCore 3 (centralizerIn heP (bOf heThreeWordsA)) = ⊥ :=
  (heThree_theta bigDataA (by norm_num) heThreeXA heThreeXA_eq radA
    (by rw [card_cent_A, card_heThreeXA])).2

theorem heThree_theta_B :
    aschbacherSolvableCore 3 (centralizerIn heP (bOf heThreeWordsB)) = ⊥ :=
  (heThree_theta bigDataB (by norm_num) heThreeXB heThreeXB_eq radB
    (by rw [card_cent_B, card_heThreeXB])).2

theorem theta_centralizerIn_order_three
    {s : Equiv.Perm (Fin 8330)} (hs : s ∈ heP)
    (hs3 : orderOf s = 3) : aschbacherSolvableCore 3 (centralizerIn heP s) = ⊥ := by
  rcases three_conj_cases hs hs3 with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · exact theta_centralizerIn_conj hc heThree_theta_A
  · exact theta_centralizerIn_conj hc heThree_theta_B

theorem thetaCent_heP :
    ∀ s : heP, s ^ 3 = 1 → s ≠ 1 →
      aschbacherSolvableCore 3 (Subgroup.centralizer ({s} : Set heP)) = ⊥ := by
  intro s hs3 hs1
  have h3 : orderOf (s : Equiv.Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hs3 hs1
  exact theta_bot_of_mulEquiv (heCentralizerEquiv s) (theta_centralizerIn_order_three s.2 h3)

theorem thetaCent_he :
    ∀ b : Blueprint.NativeSporadic.He, b ^ 3 = 1 → b ≠ 1 →
      aschbacherSolvableCore 3
        (Subgroup.centralizer ({b} : Set Blueprint.NativeSporadic.He)) = ⊥ := by
  intro b hb3 hb1
  obtain ⟨hb3', hb1'⟩ := @pow_three_of_mulEquiv _ _ Units.instGroup _ heEquivP b hb3 hb1
  exact theta_bot_of_mulEquiv (@centralizerEquiv _ _ Units.instGroup _ heEquivP b)
    (thetaCent_heP (heEquivP b) hb3' hb1')

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

end
