module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotS331

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

namespace Hyp5_2_2p

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}
  (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
include hyp

theorem B_le_normalizer_L2_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hLie : Stmt5_2_L2Lie_F4) : B ≤ Subgroup.normalizer (L₂ : Set G) := by
  obtain ⟨-, -, hBS, hSK, -⟩ := hyp.S_facts_F4 h510 h331 hR
  obtain ⟨-, -, hX⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hyp.notation59 hyp.choice
  have hBH : B ≤ H := hyp.notation59.1.1.trans inf_le_right
  have hBK : B ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hBH.trans (le_normalizer_oTwoUpper H)
  refine hX B hBK ?_ hyp.notation59.1.2.1
  rw [← hSK]
  exact fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hBS hb, hBK hb⟩

theorem T_le_normalizer_sDp_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) :
    T ≤ Subgroup.normalizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) := by
  obtain ⟨-, hTS, -⟩ := hyp.S_facts_F4 h510 h331 hR
  rw [← hyp.sup_Y_eq_F4 h510 h331 hR]
  exact le_normalizer_sup_of_le_of_le (hyp.T_le_normalizer_Y hF) hTS

theorem B_le_normalizer_sDp_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) :
    B ≤ Subgroup.normalizer ((Dp ⊔ sec52S M H : Subgroup G) : Set G) := by
  obtain ⟨-, -, hBS, -⟩ := hyp.S_facts_F4 h510 h331 hR
  rw [← hyp.sup_Y_eq_F4 h510 h331 hR]
  exact le_normalizer_sup_of_le_of_le (hyp.B_le_normalizer_Y_F4 hF h510 h331 hR) hBS

theorem le_normalizer_G0_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hLie : Stmt5_2_L2Lie_F4) :
    (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B ≤
      Subgroup.normalizer ((Dp ⊔ (L₂ ⊔ sec52S M H) : Subgroup G) : Set G) := by
  have e : Dp ⊔ (L₂ ⊔ sec52S M H) = (Dp ⊔ sec52S M H) ⊔ L₂ := by
    rw [sup_comm L₂, ← sup_assoc, sup_comm _ L₂, ← sup_assoc, sup_comm L₂ Dp]
  rw [e]
  exact sup_le (le_normalizer_sup_of_le_of_le
      (inf_le_left.trans (hyp.T_le_normalizer_sDp_F4 hF h510 h331 hR)) inf_le_right)
    (le_normalizer_sup_of_le_of_le (hyp.B_le_normalizer_sDp_F4 hF h510 h331 hR)
      (hyp.B_le_normalizer_L2_F4 h510 h331 hR hLie))

theorem Dp_not_le_normalizer_L2_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hL2 : Stmt5_2_L2_F4) :
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) := by
  intro hDp
  obtain ⟨-, -, -, -, hSL, -⟩ := hyp.S_facts_F4 h510 h331 hR
  obtain ⟨-, hKL₂⟩ := hL2 G T M L H B D L₂ n hyp.toHyp5_1_8 hyp.notation59 hyp.choice
  have hTLS : T ⊓ L ≤ sec52S M H := hSL ▸ inf_le_left
  have hYN : (T ⊓ L) ⊔ Dp ≤ Subgroup.normalizer (L₂ : Set G) :=
    sup_le (hTLS.trans hyp.S_le) hDp
  have hTY := hyp.T_le_normalizer_Y hF
  apply hyp.Dp_not_le
  intro d hd
  have key : ∀ k ∈ conjClosure L₂ T, d * k * d⁻¹ ∈ conjClosure L₂ T := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht, z, hz, rfl⟩ := hx
      have hdt : t⁻¹ * d * t ∈ (T ⊓ L) ⊔ Dp := by
        have := (Subgroup.mem_normalizer_iff.mp (hTY (T.inv_mem ht)) d).mp
          (Subgroup.mem_sup_right hd)
        simpa using this
      have hz' : (t⁻¹ * d * t) * z * (t⁻¹ * d * t)⁻¹ ∈ L₂ :=
        (Subgroup.mem_normalizer_iff.mp (hYN hdt) z).mp hz
      have e : d * (t * z * t⁻¹) * d⁻¹ =
          t * ((t⁻¹ * d * t) * z * (t⁻¹ * d * t)⁻¹) * t⁻¹ := by group
      rw [e]
      exact mem_conjClosure ht hz'
    | one => simp
    | mul x y _ _ hx hy =>
      have e : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  have hle : (oTwoUpper H).map (MulAut.conj d).toMonoidHom ≤ oTwoUpper H := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hKL₂] at hk ⊢
    exact key k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj d).injective])

theorem ne_facts_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hL2 : Stmt5_2_L2_F4) (hLie : Stmt5_2_L2Lie_F4)
    (hO : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥) :
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ ∧
      ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B ∧
      T ⊓ Subgroup.normalizer (L₂ : Set G) < T ∧ L₂ < oTwoUpper H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  set G₀ := Dp ⊔ (L₂ ⊔ sec52S M H) with hG₀
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀
  set X₀ := G₀ ⊔ T₀ ⊔ B with hX₀
  have hG₀X : G₀ ≤ X₀ := le_sup_left.trans le_sup_left
  have hX₀N : X₀ ≤ Subgroup.normalizer (G₀ : Set G) := by
    refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
    · exact le_sup_left.trans (hyp.le_normalizer_G0_F4 hF h510 h331 hR hLie)
    · exact le_sup_right.trans (hyp.le_normalizer_G0_F4 hF h510 h331 hR hLie)
  have hle : pCoreOf 2 G₀ ≤ pCoreOf 2 X₀ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 G₀).trans hG₀X)
      (hX₀N.trans (normalizer_le_normalizer_pCoreOf 2 G₀)) (pCoreOf_isPGroup 2 G₀)
  have hX₀O : pCoreOf 2 X₀ ≠ ⊥ := fun h0 => hO (le_bot_iff.mp (h0 ▸ hle))
  have hHX : ¬ H ≤ X₀ := by
    intro hHX
    have hTX : T ≤ X₀ := hyp.hStar.1.1.trans hHX
    have hOT : pCoreOf 2 X₀ ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf hTX)
    have hDpX : Dp ≤ X₀ := le_sup_left.trans hG₀X
    have hle' : pCoreOf 2 X₀ ≤ pCoreOf 2 (Dp ⊔ H) :=
      le_pCoreOf_of_le_normalizer 2 (hOT.trans (hyp.hStar.1.1.trans le_sup_right))
        ((sup_le hDpX hHX).trans (le_normalizer_pCoreOf 2 X₀)) (pCoreOf_isPGroup 2 X₀)
    rw [hyp.pCore_Dp] at hle'
    exact hX₀O (le_bot_iff.mp hle')
  obtain ⟨-, hKL₂⟩ := hL2 G T M L H B D L₂ n hyp.toHyp5_1_8 hyp.notation59 hyp.choice
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hT₀T : T₀ < T := by
    refine lt_of_le_of_ne inf_le_left fun heq => hHX ?_
    have hTN : T ≤ Subgroup.normalizer (L₂ : Set G) := heq ▸ inf_le_right
    have hKL : oTwoUpper H ≤ L₂ := by
      rw [hKL₂]
      exact conjClosure_le fun t ht z hz =>
        (Subgroup.mem_normalizer_iff.mp (hTN ht) z).mp hz
    have hL₂X : L₂ ≤ X₀ := (le_sup_left.trans le_sup_right).trans hG₀X
    have hTX : T ≤ X₀ := heq ▸ (le_sup_right.trans le_sup_left)
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hTH]
    exact sup_le (hKL.trans hL₂X) hTX
  refine ⟨hX₀O, hHX, hT₀T, lt_of_le_of_ne hyp.choice.le_oTwoUpper fun heq => ?_⟩
  apply hT₀T.ne
  refine le_antisymm inf_le_left (le_inf le_rfl ?_)
  rw [heq]
  exact hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)

end Hyp5_2_2p

end CFSG.Quasithin.H13
