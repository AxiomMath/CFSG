module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2Lie
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Cartan
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Eight
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113C2

public section
namespace CFSG.Quasithin.H13.D42

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem dvd_card_rank2_F4 (h510 : Stmt5_1_10_F4) (hF : FactL2LieParabolic)
    {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ} (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
    (hL8 : LieModel (O2Q L₂) .PSL 2 2 3) (hSL₂ : IsSylowTwoOf (T ⊓ L₂) L₂)
    (hKC : quasithinIsCComponent (oTwoUpper H) H) (hnb : ¬ IsBenderAny (O2Q (oTwoUpper H)))
    {P : Subgroup G} (hP : IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P)
    (hL₂P : quasithinIsCComponent L₂ P) : 49 ∣ Nat.card ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨k, hk, htype, -, hMK⟩ :=
    nonBender_type_F4 h510 hyp.toHyp5_1_8 hyp.notation59 hKC hnb rfl
  obtain ⟨-, hpsl, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
  obtain ⟨D₀, hD₀, -, -⟩ := F1.exists_cartan hSL₂
  have h1 := (isCyclic_card_of_isHall_borelOf hk (Or.inl ⟨by simp [classicalTags], hpsl⟩) hSL₂
    hD₀).2
  have h2 := (isCyclic_card_of_isHall_borelOf (by norm_num) hL8 hSL₂ hD₀).2
  have hk3 : k = 3 := by
    have h3 : 2 ^ k - 1 = 7 := h1.symm.trans (h2.trans (by norm_num))
    have h4 := Nat.one_le_two_pow (n := k)
    generalize hq : 2 ^ k = q at h3 h4
    have h5 : 2 ^ k = 2 ^ 3 := by omega
    exact Nat.pow_right_injective le_rfl h5
  subst hk3
  obtain ⟨-, -, -, hBH, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
  rw [hMK] at hBH
  have hOT : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := F7.isSylowTwoOf_pCoreOf_le hTK
  have hBK : B ≤ oTwoUpper H := hBH.1.trans inf_le_left
  have hBb : Lin2.IsHallTwoPrimeOf (modO2Image (oTwoUpper H) B)
      (Subgroup.normalizer ((modO2Image (oTwoUpper H) (T ⊓ oTwoUpper H) :
        Subgroup (O2Q (oTwoUpper H))) : Set (O2Q (oTwoUpper H)))) := by
    have h1 := isHallTwoPrimeOf_modO2Image (X := oTwoUpper H) inf_le_left hBH
    rwa [modO2Image_inf_normalizer le_rfl inf_le_right (fun x hx => hOT hx.2),
      Vol2.Ch11.SecS.modO2Image_self, top_inf_eq] at h1
  have hdvd := dvd_card_of_rank2_eight htype (Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTK) hBb
  rwa [Vol2.Ch11.SecS.card_modO2Image_of_odd hBK hBH.2.1] at hdvd

theorem dvd_card_B_F4 (h510 : Stmt5_1_10_F4) (hF : FactL2LieParabolic)
    (h38 : Vol2Native.A38ForSQTKCat) {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}
    (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p) (hL₂K : L₂ < oTwoUpper H)
    (hL8 : LieModel (O2Q L₂) .PSL 2 2 3) (hSL₂ : IsSylowTwoOf (T ⊓ L₂) L₂) :
    49 ∣ Nat.card ↥B := by
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, rfl, P, hP, hL₂P⟩
  ·
    obtain ⟨-, -, hBorel, hBH, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
    rw [hyp.toHyp5_1_8.borel_eq hBorel] at hBH
    obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hyp.hStar.1.2 hTH hK₁ hKeq hL₂K
    have h49 := tc.sq_dvd_card hK₁ hTH (by norm_num) hL8 hBH
    norm_num at h49
    exact h49
  · exact dvd_card_rank2_F4 h510 hF hyp hL8 hSL₂ hK₁ hnb hP hL₂P

end CFSG.Quasithin.H13.D42
