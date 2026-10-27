module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4AI
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

section CaseAi

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement MatrixGroups Matrix

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp611

theorem le_centralizer_of_isHStar_ch6_F4 (h5172 : Stmt5_1_7_two_F4) (h : Hyp611 G T M L V 4)
    (hJN : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G)) {H : Subgroup G}
    (hH : IsHStar T M H) :
    H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  by_contra hZH
  obtain ⟨hLJ, -⟩ := h5172 G T M L V H 4 h.toHyp5_0_1 h.module hH hZH
  have hcJ : ⁅L, thompsonJ T⁆ ≤ thompsonJ T := by
    rw [Subgroup.commutator_le]
    intro l hl j hj
    rw [commutatorElement_def]
    exact (thompsonJ T).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hJN (Subgroup.mem_sup_left hl)) j).mp hj)
      ((thompsonJ T).inv_mem hj)
  have hLT : L ≤ T := hLJ ▸ hcJ.trans (thompsonJ_le_self T)
  have hL2 : IsPGroup 2 ↥L := h.sylow.1.to_le hLT
  have htop : CFSG.pCore 2 ↥L = ⊤ := by
    rw [eq_top_iff]
    exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance
      (hL2.of_equiv (Subgroup.topEquiv (G := ↥L)).symm)
  have hcard := h.card_quot_four_ch6
  rw [htop] at hcard
  rw [← Subgroup.index, Subgroup.index_top] at hcard
  exact absurd hcard (by norm_num)

theorem normalizer_le_and_isUniqueM_ch6_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611 G T M L V 4) :
    Subgroup.normalizer (V : Set G) ≤ M ∧
      IsUniqueM (Subgroup.normalizer (ch6Q T V : Set G)) M := by
  have hU := h.isUniqueM_F4 h432
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.isElemAbelian
  have hQ := h.centralizer_eq
  have hQ1 : ch6Q T V ≠ ⊥ := by rw [hQ]; exact h.maximal.1.2.2.2
  have hQ2 : IsPGroup 2 (ch6Q T V) := h.sylow.1.to_le inf_le_left
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  exact ⟨le_of_isUniqueM_of_le_twoLocal hU h.sup_le_normalizer ⟨V, h.ne_bot, hV2, rfl⟩,
    ⟨⟨h.maxTwoLocal, le_of_isUniqueM_of_le_twoLocal hU hLTQ ⟨_, hQ1, hQ2, rfl⟩⟩,
      fun M' hM' => hU.2 M' ⟨hM'.1, hLTQ.trans hM'.2⟩⟩⟩

theorem oTwoFIn_le_ch6_F4 (h432 : Stmt4_3_2_F4) (hH11 : Ch6InH11) (h : Hyp611 G T M L V 4)
    (horth : IsOrthCh5 L V 4) (hr : 1 < rParam V) {M₁ : Subgroup G}
    (hXT : xFiveCh6 T L ⊔ T ≤ M₁) : oTwoFIn M₁ ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQS, hST, hSL⟩ := h.pCoreOf_xFive_props_ch6 horth
  set S := pCoreOf 2 (xFiveCh6 T L ⊔ T) with hSdef
  have hV := h.isElemAbelian
  have hVQ : V ≤ ch6Q T V := fun v hv =>
    ⟨h.le_T hv, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (B2F.isElemAbelian_comm hV hw hv)⟩
  have hVS : V ≤ S := hVQ.trans hQS
  have hJ := h.thompsonJk_one_le_ch6 hH11 horth hVS hST hSL
  have hSM₁ : S ≤ M₁ := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hXT
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

  have hTM₁ : T ≤ M₁ := le_sup_right.trans hXT
  have hQ₁S : pCoreOf 2 M₁ ≤ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf hTM₁)).trans le_sup_right)
      (hXT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁)
  set K := oTwoFIn M₁ with hKdef
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := hSM₁.trans C2Six.le_normalizer_oTwoFIn

  have hPK : pCoreOf 2 K ≤ S ⊓ K := by
    refine le_inf ?_ (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    refine le_trans ?_ hQ₁S
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans
        (Subgroup.map_subtype_le _ : oTwoFIn M₁ ≤ M₁))
      (C2Six.le_normalizer_oTwoFIn.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hodd : ¬ 2 ∣ (pCoreOf 2 K).relIndex K := by
    have h1 : Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) := odd_card_oTwoFIn_quotient M₁
    have e : (pCoreOf 2 K).relIndex K = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
      show (((CFSG.Open.pCore 2 ↥K).map K.subtype).comap K.subtype).index = _
      rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
      rfl
    rw [e]
    exact fun h2 => (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
  have hSyl : IsSylowIn 2 S (S ⊔ K) := by
    refine ⟨le_sup_left, hS2, fun h2 => hodd ?_⟩
    rw [relIndex_sup_eq_inf_ch6 hSK] at h2
    exact h2.trans (Subgroup.relIndex_dvd_of_le_left K hPK)
  have hsolv : Group.IsSolvable ↥(S ⊔ K) := by
    rw [sup_comm]
    exact isSolvable_oTwoFIn_sup hSM₁ hS2
  obtain ⟨hNV, hNQ⟩ := h.normalizer_le_and_isUniqueM_ch6_F4 h432
  have := ch6InE626_proved G T V M (S ⊔ K) S 1 h.sylow h.ne_bot hV h.le_T h.T_le_normalizer hNV
    hNQ one_pos (by exact_mod_cast E1.solvable_nParam_le_one hsolv) hSyl hQS hST
    (by exact_mod_cast hr) hJ
  exact le_sup_right.trans this.1

end Hyp611

@[expose] def Res614EndGame_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V M₁ K₁ X : Subgroup G),
    Hyp611 G T M L V 4 → IsOrthCh5 L V 4 → quasithinIsMaxTwoLocal M₁ →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ → M₁ ≠ M →
    K₁ ∈ cComp M₁ → CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) → ¬ K₁ ≤ M →
    X ≤ L → X ≤ M₁ → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 →
    ((X ⊓ T).subgroupOf X).Normal → T ≤ Subgroup.normalizer (X : Set G) →
    X ≤ Subgroup.normalizer (K₁ : Set G) → X ≤ conjClosure K₁ T →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ conjClosure K₁ T : Subgroup G) : Set G) → False

end CaseAi

end CFSG.Quasithin.H13
