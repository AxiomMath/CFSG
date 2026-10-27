module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharSp
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycExc
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenNarrow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactNineThreeListRankOneProof
import CFSG.Sporadic.Bridge.J3Surj

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open

theorem le_pRank_sylow {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K] {k : ℕ}
    (h : k ≤ Open.pRank p (⊤ : Subgroup K)) (T : Sylow p K) :
    k ≤ Open.pRank p (T : Subgroup K) := by
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  obtain ⟨T₀, hET₀⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow (MulEquiv.refl K) T₀.isPGroup'
    T₀.not_dvd_index T
  rw [hΦ]
  exact CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt (Subgroup.map_mono hET₀)
    (isElemAbelian_map _ hE) (by rw [Subgroup.card_map_of_injective Φ.injective, hEc])

theorem three_le_pRank_spFour {p : ℕ} (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsSpFourIndex p d) {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : 3 ≤ Open.pRank p (⊤ : Subgroup K) := by
  obtain ⟨x, hv⟩ := d
  obtain ⟨q, ⟨hq, h1, hdq⟩ | ⟨rfl, hq2, h1, hdq⟩⟩ := hd
  · simp only at hdq
    subst hdq hq
    have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    obtain ⟨-, -, h⟩ := CFSG.SectionRank.classical_model_rank hp2 hC
    rw [h1] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
    · omega
    · omega
  · simp only at hdq
    subst hdq
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    rw [hq2, h1] at h
    obtain ⟨-, -, h⟩ := CFSG.SectionRank.classical_model_rank (by norm_num)
      (CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two h)
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
    · omega
    · omega

section SpSix

open Matrix CFSG.Fischer.Classification CFSG.LocalAnalysis.ComponentInitial
  CFSG.AGLEmbedding.OffCharSp

theorem three_le_pRank_three_spH :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (SpH (pairedSympForm (ZMod 2) 3))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set z : Fin 3 → SpH (pairedSympForm (ZMod 2) 3) := zPair 3
  have h01 : (0 : Fin 3) ≠ 1 := by norm_num
  have h02 : (0 : Fin 3) ≠ 2 := by norm_num
  have h12 : (1 : Fin 3) ≠ 2 := by norm_num
  have hc01 : Commute (z 0) (z 1) := zPair_comm 3 0 1
  have hE₂ : IsElemAbelian 3 (Subgroup.closure ({z 0, z 1} : Set _)) :=
    IsElemAbelian.closure_of_commute
      (by rintro a (rfl | rfl) b (rfl | rfl); exacts [rfl, hc01, hc01.symm, rfl])
      (by rintro a (rfl | rfl); exacts [zPair_pow_three 3 0, zPair_pow_three 3 1])
  have hE₂c : Nat.card (Subgroup.closure ({z 0, z 1} : Set _)) = 3 ^ 2 :=
    CFSG.HardMathSupport.Dickson.I271.card_closure_pair_sq hc01 (zPair_pow_three 3 0)
      (zPair_pow_three 3 1) (zPair_ne_one 3 0) (zPair_not_mem_zpowers 3 h01)
  have hcomm : ∀ g ∈ Subgroup.closure ({z 0, z 1} : Set _),
      Commute (tr (pairedSympForm_alt 3) (eI 3 2)) g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      exacts [tr_eI_comm_zPair 3 h02, tr_eI_comm_zPair 3 h12]
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hz2 : z 2 ∉ Subgroup.closure ({z 0, z 1} : Set _) := fun h =>
    tr_eI_not_comm_zPair 3 2 (hcomm _ h)
  have hz2c' : ∀ g ∈ Subgroup.closure ({z 0, z 1} : Set _), Commute g (z 2) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      exacts [zPair_comm 3 0 2, zPair_comm 3 1 2]
    | one => exact Commute.one_left _
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  have hz2c : ∀ g ∈ Subgroup.closure ({z 0, z 1} : Set _), g * z 2 = z 2 * g :=
    fun g hg => (hz2c' g hg).eq
  obtain ⟨hF, hFc⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen
    Nat.prime_three hE₂ (zPair_pow_three 3 2) hz2 hz2c
  exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hF
    (by rw [hFc, hE₂c]; norm_num)

theorem three_le_pRank_sp62 {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) {K : Type}
    [Group K] [Finite K] (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨q, hq2, hqe, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .B 3 q := hdq
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2 le_rfl e
  rw [hq2, hqe] at h
  obtain ⟨e'⟩ := CFSG.AGLEmbedding.OffCharSp.nonempty_mulEquiv_spH 3 h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
  exact three_le_pRank_three_spH

end SpSix

theorem three_le_pRank_a9 {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 9)) : 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
  exact CFSG.SectionRank.three_le_pRank_alternating le_rfl

theorem three_le_pRank_j3
    {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) : 3 ≤ Open.pRank 3 (⊤ : Subgroup K) :=
  ListRankOne.of_carrier_elem (s := .J3) (k := 3) Nat.prime_three
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv CFSG.SectionRank.J3_elementary_three_rank_three e

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
