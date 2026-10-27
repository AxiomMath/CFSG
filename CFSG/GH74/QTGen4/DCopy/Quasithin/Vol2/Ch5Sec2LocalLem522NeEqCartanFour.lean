module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2Lie
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartan
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartanFour

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem stmt5_2_2_eq_cartan_rank2_of_F4 (h510 : Stmt5_1_10_F4) (hF : FactL2LieParabolic)
    (hL2 : Stmt5_2_L2_F4) : Stmt5_2_2_eq_cartan_rank2_F4 := by
  have hC4 := factRank2CartanFour_holds
  intro G _ _ T M L V H B D L₂ Dp n p hyp hL₂K hL4 hKC hnb P hP hL₂P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨k, hk, htype, -, hMK⟩ :=
    nonBender_type_F4 h510 hyp.toHyp5_1_8 hyp.notation59 hKC hnb rfl
  obtain ⟨hL₂eq, hpsl, hborel, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
  have hSL₂ : IsSylowTwoOf (T ⊓ L₂) L₂ :=
    (hL2 G T M L H B D L₂ n hyp.toHyp5_1_8 hyp.notation59 hyp.choice).1
  obtain ⟨D₀, hD₀, -, -⟩ := F1.exists_cartan hSL₂
  have h1 := (isCyclic_card_of_isHall_borelOf hk (Or.inl ⟨by simp [classicalTags], hpsl⟩) hSL₂
    hD₀).2
  have h2 := (isCyclic_card_of_isHall_borelOf le_rfl hL4 hSL₂ hD₀).2
  have hk2 : k = 2 := by
    have h3 : 2 ^ k - 1 = 3 := h1.symm.trans (h2.trans (by norm_num))
    have h4 := Nat.one_le_two_pow (n := k)
    generalize hq : 2 ^ k = q at h3 h4
    have h5 : 2 ^ k = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h5
  subst hk2
  obtain ⟨-, -, -, hBH, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
  rw [hMK] at hBH
  have hOT : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := F7.isSylowTwoOf_pCoreOf_le hTK
  have hBK : B ≤ oTwoUpper H := hBH.1.trans inf_le_left
  have hBodd : Odd (Nat.card ↥B) := hBH.2.1
  have hBb : Lin2.IsHallTwoPrimeOf (modO2Image (oTwoUpper H) B)
      (Subgroup.normalizer ((modO2Image (oTwoUpper H) (T ⊓ oTwoUpper H) :
        Subgroup (O2Q (oTwoUpper H))) : Set (O2Q (oTwoUpper H)))) := by
    have h1 := isHallTwoPrimeOf_modO2Image (X := oTwoUpper H) inf_le_left hBH
    rwa [modO2Image_inf_normalizer le_rfl inf_le_right (fun x hx => hOT hx.2),
      Vol2.Ch11.SecS.modO2Image_self, top_inf_eq] at h1
  obtain ⟨hEA, hcard⟩ := hC4 (O2Q (oTwoUpper H)) htype hyp.notL34 _ _
    (Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTK) hBb
  have hL₂K' : L₂ ≤ oTwoUpper H := hL₂eq ▸ (perfectCore_le P).trans hP.1
  have hYN : oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L₂ : Set G) := by
    rw [hL₂eq]
    exact hP.2.1.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P))
  have hYi : borelOf L₂ T ≤
      oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [← hMK]
    exact le_inf hborel (inf_le_left.trans hL₂K')
  refine ⟨isElemAbelian_of_modO2Image hBK hBodd hEA,
    (Vol2.Ch11.SecS.card_modO2Image_of_odd hBK hBodd).symm.trans hcard,
    isHallTwoPrimeOf_inf_borelOf hBH hL₂K' hYN hYi⟩

end CFSG.Quasithin.H13
