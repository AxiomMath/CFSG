module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycTransport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharU42
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.Sporadic.Schreier.TitsOuterTwo
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

namespace OffCharU42

open CFSG.GH74.Exceptional CFSG.LieType.Multipliers.U42

theorem seqL_eq_of_W_eq {l₁ l₂ : List (Fin 45)} (h : W l₁ = W l₂) (j : Fin 45) :
    seqL l₁ j = seqL l₂ j := by
  have h' : (⟨W l₁, W_mem l₁⟩ : Y43) = ⟨W l₂, W_mem l₂⟩ := Subtype.ext h
  rw [← seqFun_eq_seqL, ← seqFun_eq_seqL, ← sigma43_W, ← sigma43_W, h']

theorem wx2_not_comm : ¬ ∀ j, seqL ([2] ++ wx2) j = seqL (wx2 ++ [2]) j := by decide +kernel

theorem W_wx2_not_mem_zpowers : W wx2 ∉ Subgroup.zpowers (W wx1) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hc : Commute (W [2]) (W wx1) := by
    show W [2] * W wx1 = W wx1 * W [2]
    rw [← W_append, ← W_append]
    exact W_eq_of_seqL wt_comm
  have hc' : Commute (W [2]) (W wx2) := by
    rw [← hk]
    exact hc.zpow_right k
  have h : W ([2] ++ wx2) = W (wx2 ++ [2]) := by
    rw [W_append, W_append]
    exact hc'.eq
  exact wx2_not_comm (seqL_eq_of_W_eq h)

theorem two_le_pRank_psp43 : 2 ≤ Open.pRank 3 (⊤ : Subgroup PSp43) := by
  have h1 : orderOf (W wx1) = 3 :=
    orderOf_eq_prime (W_pow_three wx1_pow) (W_ne_one_of_seqL wx1_ne)
  have hc : W wx1 * W wx2 = W wx2 * W wx1 := by
    rw [← W_append, ← W_append]
    exact W_eq_of_seqL wx12_comm
  exact two_le_openPRank_of_commuting Nat.prime_three h1 (W_pow_three wx2_pow) hc
    W_wx2_not_mem_zpowers

end OffCharU42

namespace OffCharSp

open Matrix CFSG.Fischer.Classification CFSG.LocalAnalysis.ComponentInitial

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable (n : ℕ)

noncomputable def zPair (i : Fin n) : SpH (pairedSympForm (ZMod 2) n) :=
  tr (pairedSympForm_alt n) (eI n i) * tr (pairedSympForm_alt n) (fI n i)

theorem zPair_pow_three (i : Fin n) : zPair n i ^ 3 = 1 :=
  tr_mul_tr_pow_three (pairedSympForm_alt n) (b_eI_fI_self n i)

theorem zPair_ne_one (i : Fin n) : zPair n i ≠ 1 := by
  intro h
  have halt := pairedSympForm_alt n
  have h1 : tr halt (eI n i) = tr halt (fI n i) := by
    rw [zPair, mul_eq_one_iff_eq_inv, tr_inv] at h
    exact h
  have h2 := congrArg (fun g => act g (fI n i)) h1
  simp only [act_tr] at h2
  have h3 : pairedSympForm (ZMod 2) n (fI n i) (eI n i) = 1 := by
    rw [b_symm halt, b_eI_fI_self]
  rw [h3, halt, one_smul, zero_smul, add_zero, add_eq_left] at h2
  have h4 := b_eI_fI_self n i
  rw [h2] at h4
  simp at h4

theorem zPair_comm (i j : Fin n) : zPair n i * zPair n j = zPair n j * zPair n i := by
  by_cases h : i = j
  · rw [h]
  have halt := pairedSympForm_alt n
  have hac : Commute (tr halt (eI n i)) (tr halt (eI n j)) := tr_comm halt (b_eI_eI n i j)
  have had : Commute (tr halt (eI n i)) (tr halt (fI n j)) :=
    tr_comm halt (by rw [b_eI_fI]; simp [h])
  have hbc : Commute (tr halt (fI n i)) (tr halt (eI n j)) :=
    tr_comm halt (by rw [b_fI_eI]; simp [h])
  have hbd : Commute (tr halt (fI n i)) (tr halt (fI n j)) := tr_comm halt (b_fI_fI n i j)
  exact Commute.mul_left (Commute.mul_right hac had) (Commute.mul_right hbc hbd)

theorem tr_eI_comm_zPair {i j : Fin n} (h : i ≠ j) :
    Commute (tr (pairedSympForm_alt n) (eI n j)) (zPair n i) := by
  have halt := pairedSympForm_alt n
  have h1 : Commute (tr halt (eI n j)) (tr halt (eI n i)) := tr_comm halt (b_eI_eI n j i)
  have h2 : Commute (tr halt (eI n j)) (tr halt (fI n i)) :=
    tr_comm halt (by rw [b_eI_fI]; simp [Ne.symm h])
  exact Commute.mul_right h1 h2

theorem tr_eI_not_comm_zPair (j : Fin n) :
    ¬ Commute (tr (pairedSympForm_alt n) (eI n j)) (zPair n j) := by
  intro hc
  have halt := pairedSympForm_alt n
  have hbraid := tr_braid halt (b_eI_fI_self n j)
  have hee := tr_mul_self halt (eI n j)
  refine zPair_ne_one n j ?_
  have h : tr halt (eI n j) * (tr halt (eI n j) * tr halt (fI n j)) =
      tr halt (eI n j) * tr halt (fI n j) * tr halt (eI n j) := hc.eq
  have h2 : tr halt (fI n j) = tr halt (fI n j) * tr halt (eI n j) * tr halt (fI n j) := by
    calc tr halt (fI n j) = tr halt (eI n j) * (tr halt (eI n j) * tr halt (fI n j)) := by
          rw [← mul_assoc, hee, one_mul]
      _ = tr halt (eI n j) * tr halt (fI n j) * tr halt (eI n j) := h
      _ = tr halt (fI n j) * tr halt (eI n j) * tr halt (fI n j) := hbraid
  have h3 : tr halt (fI n j) * (tr halt (eI n j) * tr halt (fI n j)) = tr halt (fI n j) * 1 := by
    rw [mul_one, ← mul_assoc]
    exact h2.symm
  exact mul_left_cancel h3

theorem zPair_not_mem_zpowers {i j : Fin n} (h : i ≠ j) :
    zPair n j ∉ Subgroup.zpowers (zPair n i) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hc' : Commute (tr (pairedSympForm_alt n) (eI n j)) (zPair n j) := by
    rw [← hk]
    exact (tr_eI_comm_zPair n h).zpow_right k
  exact tr_eI_not_comm_zPair n j hc'

theorem two_le_pRank_three_spH (hn : 2 ≤ n) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup (SpH (pairedSympForm (ZMod 2) n))) := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  exact two_le_openPRank_of_commuting Nat.prime_three
    (orderOf_eq_prime (zPair_pow_three n i0) (zPair_ne_one n i0)) (zPair_pow_three n i1)
    (zPair_comm n i0 i1) (zPair_not_mem_zpowers n h01)

end OffCharSp

section Catalog

theorem two_le_pRank_three_linThreeFour {K : Type} [Group K] [Finite K] (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hqe : q.exponent = 2) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hk : Nat.card (GaloisField q.p q.exponent) = 4 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hq2, hqe]
    norm_num
  have e' : K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField q.p q.exponent) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_of_mulEquiv hk e']

theorem two_le_pRank_three_unitaryFour {K : Type} [Group K] [Finite K] (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hqe : q.exponent = 1) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
  rw [hq2, hqe] at h
  obtain ⟨e'⟩ := OffCharU42.nonempty_mulEquiv_psp43
    (CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two h)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
  exact OffCharU42.two_le_pRank_psp43

theorem two_le_pRank_three_typeB (r : ℕ) (hr : 3 ≤ r) {K : Type} [Group K] [Finite K]
    (q : TauCeti.PrimePower) (hq2 : q.p = 2) (hqe : q.exponent = 1)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr e
  rw [hq2, hqe] at h
  obtain ⟨e'⟩ := OffCharSp.nonempty_mulEquiv_spH r h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
  exact OffCharSp.two_le_pRank_three_spH r (by omega)

end Catalog

section Tits


theorem not_dvd_card_outer_tits {K : Type} [Group K] (hv : TauCeti.LieTypeIndex.tits.Valid)
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) := by
  obtain ⟨-, -, hO, -⟩ := CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound K 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  rw [hO]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

end Tits

end CFSG.AGLEmbedding
