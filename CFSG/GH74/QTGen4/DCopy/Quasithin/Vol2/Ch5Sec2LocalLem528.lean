module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_2_8_Sz_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
    (IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .twistedF4 0 n) ∧
      IsL2Quot n (oTwoQuot ↥L) ∧ Nat.card (pCoreOf 2 L) = (2 ^ n) ^ 11 ∧
      (∃ a : ℕ, n = 2 * a + 1 ∧ Nonempty (oTwoQuot ↥(oTwoUpper H) ≃* Sz a)) ∧
      Nat.card (pCoreOf 2 (oTwoUpper H)) = (2 ^ n) ^ 10) →
    ∀ Kh : Subgroup G, oTwoUpper H < Kh → quasithinIsMaximalLocal T Kh → False

@[expose] def Stmt5_2_8_blocks_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
    ((IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSL 3 n) ∨
        IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSp 2 n)) ∧
      IsBlock2 L L ∧ IsLin2Type L n ∧ IsBlock2 (oTwoUpper H) (oTwoUpper H) ∧
      IsLin2Type (oTwoUpper H) n) →
    ∀ Kh : Subgroup G, oTwoUpper H < Kh → quasithinIsMaximalLocal T Kh →
      IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSL 3 2) ∧
        CFSG.Quasithin.IsExcA7Block Kh

@[expose] def Stmt5_2_8_U4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
    (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧
      (IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSU 4 m) ∨
        IsU4ExtTwo m (sec52Alpha M L H B D L₂)) ∧
      IsOmega4MinusBlock L m ∧ IsL2Quot m (oTwoQuot ↥(oTwoUpper H)) ∧
      IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (oTwoUpper H))) →
    ∀ Kh : Subgroup G, oTwoUpper H < Kh → quasithinIsMaximalLocal T Kh →
      Kh ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G)

@[expose] def Stmt5_2_8_special_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
    ∀ Kh : Subgroup G, oTwoUpper H < Kh → quasithinIsMaximalLocal T Kh →
    ((IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .G2 0 n) ∧
        IsL2Quot n (oTwoQuot ↥L) ∧ IsL2Quot n (oTwoQuot ↥(oTwoUpper H)) ∧
        IsSpecialPow 2 (2 ^ n) 2 ↥(pCoreOf 2 (oTwoUpper H)) ∧
        Nat.card (pCoreOf 2 L) = (2 ^ n) ^ 5) ∨
      (IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .trialityD4 0 n) ∧
        IsL2Quot n (oTwoQuot ↥L) ∧ Nat.card (pCoreOf 2 L) = (2 ^ n) ^ 11 ∧
        IsL2Quot (3 * n) (oTwoQuot ↥(oTwoUpper H)) ∧
        IsSpecialPow 2 (2 ^ n) 4 ↥(pCoreOf 2 (oTwoUpper H))) ∨
      ((∃ m : ℕ, n = 2 * m ∧ 2 < n ∧
          (IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSU 4 m) ∨
            IsU4ExtTwo m (sec52Alpha M L H B D L₂)) ∧
          IsOmega4MinusBlock L m ∧ IsL2Quot m (oTwoQuot ↥(oTwoUpper H)) ∧
          IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (oTwoUpper H))) ∧
        Kh ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G))) → False

theorem stmt5_2_8_of_F4 (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hbl : Stmt5_2_8_blocks_F4) (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) : Stmt5_2_8_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have h := hyp.toHyp5_0_1
  obtain ⟨-, hL₂K, -, -, -, hcases, -, -⟩ := h526 G T M L V H B D L₂ n hyp
  have hKloc := hyp.isLocal_oTwoUpper hL₂K

  obtain ⟨Kh, hKKh, hmax⟩ :=
    Finite.exists_le_maximal (p := fun X : Subgroup G => quasithinIsLocal T X ∧ oTwoUpper H ≤ X)
      ⟨hKloc, le_rfl⟩
  have hKhmax : quasithinIsMaximalLocal T Kh :=
    ⟨hmax.1.1, fun X hX hKhX => le_antisymm (hmax.2 ⟨hX, hKKh.trans hKhX⟩ hKhX) hKhX⟩
  by_cases heq : Kh = oTwoUpper H
  · left
    rw [← heq]
    exact hKhmax
  have hlt : oTwoUpper H < Kh := lt_of_le_of_ne hKKh (Ne.symm heq)
  unfold Cases5_2_6 at hcases
  rcases hcases with c1 | c2 | c3 | c4 | c5 | c6 | c7
  · obtain ⟨hα, hA7⟩ := hbl G T M L V H B D L₂ n hyp ⟨Or.inl c1.1, c1.2⟩ Kh hlt hKhmax
    exact Or.inr ⟨hα, Kh, hlt, hKhmax, hA7⟩
  · obtain ⟨hα, hA7⟩ := hbl G T M L V H B D L₂ n hyp ⟨Or.inr c2.1, c2.2⟩ Kh hlt hKhmax
    exact Or.inr ⟨hα, Kh, hlt, hKhmax, hA7⟩
  · exact (hsp G T M L V H B D L₂ n hyp Kh hlt hKhmax (Or.inl c3)).elim
  · exact (hsp G T M L V H B D L₂ n hyp Kh hlt hKhmax (Or.inr (Or.inl c4))).elim
  · exact (hSz G T M L V H B D L₂ n hyp c5 Kh hlt hKhmax).elim
  · have hQ := hU4 G T M L V H B D L₂ n hyp c6 Kh hlt hKhmax
    exact (hsp G T M L V H B D L₂ n hyp Kh hlt hKhmax (Or.inr (Or.inr ⟨c6, hQ⟩))).elim
  ·
    exfalso
    obtain ⟨-, -, -, -, ⟨F, hFf, hFfin, hF, ⟨e⟩⟩, -⟩ := c7
    have hEq : CFSG.Open.StatedSU 3 4 F = CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 2) F := rfl
    have hSU : IsSU3 (2 ^ 2) (ModO2 (oTwoUpper H)) := by
      refine ⟨F, hFf, hFfin, by rw [hF]; norm_num, ⟨?_⟩⟩
      exact ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥(oTwoUpper H))).trans e).trans
        (MulEquiv.subgroupCongr hEq)
    have hlist : A128FourList (ModO2 (oTwoUpper H)) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨2, Or.inr hSU⟩)))))))))))))
    have hKmax := h1284 G h.qtke h.simple h.nonabelian T (oTwoUpper H) hKloc hlist
    exact heq (hKmax.2 Kh hmax.1.1 hKKh)

end CFSG.Quasithin.H13
