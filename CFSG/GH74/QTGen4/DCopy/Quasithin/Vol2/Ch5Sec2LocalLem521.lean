module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsBS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Background.A3Structure312Embed
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_2_L2Gen_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D K₁ P L₂ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → quasithinIsCComponent K₁ H →
    oTwoUpper H = conjClosure K₁ T → ¬ IsBenderAny (O2Q K₁) → K₁ = oTwoUpper H →
    IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P → quasithinIsCComponent L₂ P →
      oTwoUpper H = conjClosure L₂ T

@[expose] def Stmt5_2_1_par_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsL2Choice T H L₂ →
    IsLieRankTwoK T H →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
        (∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
          X ≤ Subgroup.normalizer (P : Set G)) →
        X ≤ Subgroup.normalizer (L₂ : Set G)

theorem stmt5_2_L2_of_F4 (hgen : Stmt5_2_L2Gen_F4) : Stmt5_2_L2_F4 := by
  intro G _ _ T M L H B D L₂ n hyp hN hL₂
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hL₂
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  · exact ⟨A312.isSylowTwoOf_inf_of_subnormal hK₁.2.2.1 hTH, hKeq⟩
  · refine ⟨?_, hgen G T M L H B D K₁ P L₂ n hyp hN hK₁ hKeq hnb hK1eq hP hL₂P⟩
    have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
      A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
    have hTKP : T ⊓ oTwoUpper H ≤ P :=
      (le_inf inf_le_right Subgroup.le_normalizer).trans hP.2.1
    have hTP : IsSylowTwoOf (T ⊓ oTwoUpper H) P := A4.isSylowTwoOf_mono hTK hTKP hP.1
    have hL₂K : L₂ ≤ oTwoUpper H := (A3.subnormal_le hL₂P.2.2.1).trans hP.1
    have hsyl := A312.isSylowTwoOf_inf_of_subnormal hL₂P.2.2.1 hTP
    have heq : T ⊓ oTwoUpper H ⊓ L₂ = T ⊓ L₂ := by
      rw [inf_assoc, inf_eq_right.mpr hL₂K]
    rw [heq] at hsyl
    exact hsyl

theorem stmt5_2_1_of_F4 (h510 : Stmt5_1_10_F4) (h5111 : Stmt5_1_11_F4) (hpar : Stmt5_2_1_par_F4) :
    Stmt5_2_1_F4 := by
  intro G _ _ T M L H B D L₂ n hyp hN hL₂ hnot
  have h := hyp.toHyp5_0_1
  have hSH : sec52S M H ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hSK : sec52S M H ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hSH.trans (le_normalizer_oTwoUpper H)
  by_cases hrk : IsLieRankTwoK T H
  · obtain ⟨-, -, h3⟩ := h5111 G T M L H B D n hyp hN
    rcases h3 hrk with hi | hii
    · exact hpar G T M L H B D L₂ n hyp hN hL₂ hrk (sec52S M H) hSK hi
    · exact absurd hii.1 hnot
  ·
    obtain ⟨k, hk, -, -, K₁, hK₁, hKeq, hcases⟩ := h510 G T M L H B D n hyp hN
    have hk2 : 2 ≤ k := hk.1
    have hBender : K₁ = oTwoUpper H ∧ IsBenderAny (O2Q (oTwoUpper H)) := by
      rcases hcases with ⟨hlt, -⟩ | ⟨h1, h2⟩ | ⟨-, h2, -⟩
      · exact absurd (Or.inl ⟨K₁, hK₁, hKeq, hlt⟩) hrk
      · exact ⟨h1, k, hk2, h2⟩
      · exact absurd (Or.inr ⟨k, h2⟩) hrk
    obtain ⟨K₁', hK₁', hKeq', hcase'⟩ := hL₂
    have hK₁'K : K₁' ≤ oTwoUpper H := by
      rw [hKeq']
      exact le_conjClosure K₁' T
    have hK₁'eq : K₁' = oTwoUpper H := by
      by_contra hne
      exact hrk (Or.inl ⟨K₁', hK₁', hKeq', lt_of_le_of_ne hK₁'K hne⟩)
    rcases hcase' with ⟨-, rfl⟩ | ⟨hnb, -, -⟩
    · rw [hK₁'eq]
      exact hSK
    · rw [hK₁'eq] at hnb
      exact absurd hBender.2 hnb

end CFSG.Quasithin.H13
