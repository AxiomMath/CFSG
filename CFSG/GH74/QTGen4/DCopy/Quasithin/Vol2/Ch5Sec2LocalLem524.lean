module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5111
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsBS331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem524

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

@[expose] def Stmt5_2_L2Lie_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsL2Choice T H L₂ →
      IsRankOneListed (oTwoQuot ↥L₂) ∧ borelOf L₂ T ≤ M ∧
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
        X ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        Odd (Nat.card X) → X ≤ Subgroup.normalizer (L₂ : Set G)

theorem stmt5_2_4_of_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (h510 : Stmt5_1_10_F4)
    (h521 : Stmt5_2_1_F4) (hLie : Stmt5_2_L2Lie_F4) : Stmt5_2_4_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  obtain ⟨k, -, hBorel, hBK, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  obtain ⟨-, -, hX⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  have hS : sec52S M H ≤ Subgroup.normalizer (L₂ : Set G) :=
    h521 G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice hyp.notL34
  have hDL : D ≤ L := hN.2.1.1.trans inf_le_left
  have hDM : D ≤ M := hDL.trans h.L_le
  have hDK : D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hyp.D_le
  have hDMK : D ≤ Subgroup.normalizer ((M ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    (le_inf (hDM.trans Subgroup.le_normalizer) hDK).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hO := hyp.toHyp5_1_8.pCoreOf_inf_oTwoUpper_eq hBorel
  have hDTK : D ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [← hO]
    exact hDMK.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hDodd : Odd (Nat.card D) := hN.2.1.2.1
  have hDL₂ : D ≤ Subgroup.normalizer (L₂ : Set G) := hX D hDK hDTK hDodd
  have hBH : B ≤ H := hN.1.1.trans inf_le_right
  have hBKn : B ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hBH.trans (le_normalizer_oTwoUpper H)
  have hMK := hyp.toHyp5_1_8.borel_eq hBorel
  have hBTK : B ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    have := hBK.1
    rw [hMK] at this
    exact this.trans inf_le_right
  have hBL₂ : B ≤ Subgroup.normalizer (L₂ : Set G) := hX B hBKn hBTK hBK.2.1
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := hN.2.2
  have hDB : D ≤ Subgroup.normalizer (B : Set G) := le_normalizer_of_isHall hBK hDodd hBD hDMK
  refine ⟨hDK, ⟨hDB, hBD⟩, ⟨?_, ?_, ?_⟩, sup_le (sup_le hDL₂ hS) hBL₂⟩
  ·
    exact hN.1.1.trans (le_normalizer_pCoreOf 2 _)
  ·
    have hSK : sec52S M H ⊓ oTwoUpper H = T ⊓ oTwoUpper H :=
      hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
    have hL₂K := hyp.choice.le_oTwoUpper
    have hSL₂ : sec52S M H ⊓ L₂ = (T ⊓ oTwoUpper H) ⊓ L₂ := by
      rw [← hSK, inf_assoc, inf_eq_right.mpr hL₂K]
    rw [hSL₂]
    exact (le_inf hDTK hDL₂).trans Subgroup.inf_normalizer_le_normalizer_inf
  ·
    set S := sec52S M H with hSdef
    have hSL : S ⊓ L = T ⊓ L := h.inf_L_eq_F4 h331 hR hyp.hStar
    have hTLS : T ⊓ L ≤ S := hSL ▸ inf_le_left
    have hSM : S ≤ M := (pCoreOf_le 2 _).trans inf_le_left
    have hSLn : S ≤ Subgroup.normalizer (L : Set G) := hSM.trans h.normal
    have hSTL : S ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [← hSL]
      exact (le_inf Subgroup.le_normalizer hSLn).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hSX : S ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := fun s hs =>
      mem_normalizer_inf_normalizer (hSLn hs) (hSTL hs)
    have hXeq : D ⊔ (T ⊓ L) = borelL T L := h.borelL_eq_sup hN.2.1
    have hDTL : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      hN.2.1.1.trans inf_le_right
    have hX1 : ((borelL T L : Subgroup G) : Set G) =
        (D : Set G) * ((T ⊓ L : Subgroup G) : Set G) := by
      rw [← hXeq]
      exact Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L) hDTL
    have hX2 : ((borelL T L : Subgroup G) : Set G) =
        ((T ⊓ L : Subgroup G) : Set G) * (D : Set G) := by
      rw [← hXeq, sup_comm]
      exact Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ L) D hDTL
    have hSXc : (S : Set G) * ((borelL T L : Subgroup G) : Set G) =
        ((borelL T L : Subgroup G) : Set G) * (S : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (borelL T L) hSX,
        ← Subgroup.coe_mul_of_right_le_normalizer_left (borelL T L) S hSX, sup_comm]
    have hS1 : (S : Set G) * ((T ⊓ L : Subgroup G) : Set G) = (S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left S (T ⊓ L)
        (hTLS.trans Subgroup.le_normalizer), sup_eq_left.mpr hTLS]
    have hS2 : ((T ⊓ L : Subgroup G) : Set G) * (S : Set G) = (S : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (T ⊓ L) S
        (hTLS.trans Subgroup.le_normalizer), sup_eq_right.mpr hTLS]
    calc (D : Set G) * (S : Set G) = (D : Set G) * (((T ⊓ L : Subgroup G) : Set G) * S) := by
          rw [hS2]
      _ = ((borelL T L : Subgroup G) : Set G) * S := by rw [hX1, mul_assoc]
      _ = (S : Set G) * ((borelL T L : Subgroup G) : Set G) := hSXc.symm
      _ = (S : Set G) * (((T ⊓ L : Subgroup G) : Set G) * D) := by rw [hX2]
      _ = (S : Set G) * D := by rw [← mul_assoc, hS1]

end CFSG.Quasithin.H13
