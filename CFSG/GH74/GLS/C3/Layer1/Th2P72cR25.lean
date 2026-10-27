module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR24
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR22
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR23

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

@[expose] def B_row2_stageB : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    ∀ (v t z : G) (L P E : Subgroup G),
      orderOf v = 2 → orderOf t = 2 → orderOf z = 2 →
      IsPCompIn 2 (centralizer ({v} : Set G)) L → IsUnbalancingTriple v t L →
      (Nonempty (kBar L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model (kBar L) Odd) →
      (∀ g ∈ centralizer ({v} : Set G), g ∈ normalizer (L : Set G)) →
      CFSG.IsElementaryAbelian 2 ↥E → pRank 2 ↥E = 2 → t ∈ E →
      (∀ e ∈ E, e * z = z * e) → (∀ e ∈ E, e * v = v * e) →
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥P ≃* DihedralGroup (2 ^ (n - 1)))) →
      z ∈ P → (∀ p ∈ P, z * p = p * z) → (∀ p ∈ P, ∀ e ∈ E, p * e = e * p) → P ⊓ E = ⊥ →
      (∃ e₁ ∈ E, e₁ ≠ 1 ∧ v = z * e₁) →
      z ∈ normalizer (L : Set G) → z ∉ centralizerSection L (pPrimeCoreOf 2 L) →
      (∀ e ∈ E, e ≠ 1 → ∃ N : Subgroup G, E ≤ N ∧
        (∀ c ∈ centralizer ({e} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N) ∧
        ∀ F : Subgroup G, E ≤ F → F ≤ N → CFSG.IsElementaryAbelian 2 ↥F → F = E) →
      False

section Assembly

theorem b_thm2_p72c_row2_of_leaf (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (hleaf : B_row2_stageB) : B_thm2_p72c_row2 := by
  intro G _ _ hG x y K T S hstd hnt hrow hbal B t J hpick hE2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hθ
  have hθ' : thetaHalf 2 B = ⊥ := hθ
  have hbalB : IsKBal 3 B ∧ IsWeakKBal 2 B := hbal B hpick.mem
  obtain ⟨-, h7B2⟩ := seven_B_of_thetaHalf_eq_bot hbalB.1 hθ'
  have hK : HasL2Model (kBar K) (fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5) := hrow
  obtain ⟨hcen, hP⟩ := hstd.centerless_and_shape hG hL34 h102
  have hcd := hstd.commDisj hcen
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hpick.elem
  obtain ⟨eJK⟩ := hpick.bar
  have hsimpleJ : IsSimpleGroup (kBar J) := by
    obtain ⟨F, _, _, hF, -, ⟨eF⟩⟩ := IVK.exists_l2Field_of_hasL2Model_pred (fun q hq => hq.1) hK
    exact (eJK.isSimpleGroup_congr).2 (IVK.Proofs2.isSimpleGroup_of_l2 hF eF)
  have hP2 : IsPGroup 2 ↥(T ⊓ K) := hstd.T_pGroup.to_le inf_le_left
  have hPne : (T ⊓ K) ≠ ⊥ := by
    obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
    intro h0
    have : Nat.card ↥U ≤ Nat.card ↥(⊥ : Subgroup G) := by
      refine Nat.card_le_card_of_injective (Subgroup.inclusion (h0 ▸ hU.1)) (Subgroup.inclusion_injective _)
    rw [hU.2.2] at this
    simp at this
  obtain ⟨z, hzP, hz2, hzc⟩ := Th2.exists_central_involution hP2 hPne
  set E : Subgroup G := B ⊓ (T ⊓ CxK x K) with hE
  have hEB : E ≤ B := inf_le_left
  have hEQ : E ≤ T ⊓ CxK x K := inf_le_right
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := isElementaryAbelian_le hpick.elem hEB
  have hE2' : pRank 2 ↥E = 2 := le_antisymm (hstd.pRank_le_two_of_le_Q hG hL34 h102 hEQ) hE2
  have hzB : z ∈ B := by
    set EP : Subgroup G := B ⊓ (T ⊓ K) with hEP
    have hEPel : CFSG.IsElementaryAbelian 2 ↥EP := isElementaryAbelian_le hpick.elem inf_le_left
    have hEPrk : pRank 2 ↥EP = 2 := by rw [hpick.rank_P]; exact pRank_eq_two_of_rankTwoShape hP
    have hzEP : z ∈ EP := by
      by_contra hzn
      have hzel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hz2
      have hcdz : CommDisj (zpowers z) EP := by
        refine ⟨fun p hp q hq => ?_, ?_⟩
        · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
          exact (Commute.zpow_left (show Commute z q from hzc q hq.2) m).eq
        · refine eq_bot_iff.2 fun w hw => ?_
          rcases mem_zpowers_two hz2 hw.1 with h0 | h0
          · simp [h0]
          · exact absurd (h0 ▸ hw.2) hzn
      have hrk3 := hcdz.pRank_sup hzel hEPel le_rfl le_rfl
      rw [Th2.pRank_zpowers_of_orderOf_two hz2, hEPrk] at hrk3
      have hle : zpowers z ⊔ EP ≤ T ⊓ K :=
        sup_le (zpowers_le.2 hzP) (inf_le_right)
      have := C3.Layer1.Back.pRank_mono' hle
      rw [hrk3, pRank_eq_two_of_rankTwoShape hP] at this
      omega
    exact hzEP.1
  obtain ⟨v, L, hvA, hvE, hvz, hv2, hL, hunb, hzN, hzL⟩ :=
    Th2.Obs.row2_triple hG hL34 h102 hstd hpick hsimpleJ hE2 h7B2 hzP hz2 hzB
  have hu := kBar_u2_of_unbal hG hL34 h102 hunb
  have hLN := centralizer_le_normalizer_of_u2 hG.pRank_eq_four.le hv2 hL hu
  have hcommzE : ∀ p ∈ zpowers z, ∀ q ∈ E, p * q = q * p := by
    intro p hp q hq
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
    exact (Commute.zpow_left (show Commute z q from hBc z hzB q (hEB hq)) m).eq
  obtain ⟨p, hp, e₁, he₁, hve⟩ := exists_mul_of_mem_sup_of_commute hcommzE hvA
  have hve1 : ∃ e₁ ∈ E, e₁ ≠ 1 ∧ v = z * e₁ := by
    rcases mem_zpowers_two hz2 hp with h0 | h0
    · exfalso
      apply hvE
      rw [hve, h0, one_mul]
      exact he₁
    · refine ⟨e₁, he₁, fun h1 => hvz ?_, by rw [hve, h0]⟩
      rw [hve, h0, h1, mul_one]
  have hPE : (T ⊓ K) ⊓ E = ⊥ := by
    refine eq_bot_iff.2 fun w hw => ?_
    have : w ∈ (T ⊓ K) ⊓ (T ⊓ CxK x K) := ⟨hw.1, hEQ hw.2⟩
    rw [hcd.inf] at this
    exact this
  obtain ⟨n, hn3, hdih⟩ := Th2.Obs.exists_dihedral_P hstd hK
  refine hleaf G hG v t z L (T ⊓ K) E hv2 hpick.t_two hz2 hL hunb hu hLN hEel hE2' hpick.t_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_ hve1 hzN hzL ?_
  · intro e he; exact hBc e (hEB he) z hzB
  · intro e he
    have hvB : v ∈ B := (sup_le (zpowers_le.2 hzB) hEB) hvA
    exact hBc e (hEB he) v hvB
  · exact ⟨n, hn3, hdih⟩
  · exact hzP
  · exact hzc
  · intro p hp e he; exact hcd.comm p hp e (hEQ he)
  · exact hPE
  · intro e he he1
    have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq e (hEB he)) he1
    exact Th2.Obs.row2_maximality hG hL34 h102 hstd hpick.elem hpick.x_mem hE2' he he2

end Assembly

end CFSG.GH74.GLS
