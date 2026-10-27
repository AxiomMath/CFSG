module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113D4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsBS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_2_2_bot_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥ → False

@[expose] def Stmt5_2_2_ne_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p → pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ → False

theorem stmt5_2_2_of_F4
    (h39 : Vol2Native.A39ForSQTKCat) (h510 : Stmt5_1_10_F4) (h516 : Stmt5_1_6_F4)
    (h5113 : Stmt5_1_13C_F4) (h5114 : Stmt5_1_14_F4) (h521 : Stmt5_2_1_F4) (hF : L2TorusFact)
    (hL2 : Ch5L2ChoiceExists_F4) (hbot : Stmt5_2_2_bot_F4) (hne : Stmt5_2_2_ne_F4) : Stmt5_2_2C_F4 := by
  intro G _ _ T M L V H B D n hyp hN hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hH := hyp.hStar
  refine or_iff_not_imp_left.mpr fun hDK => ?_
  by_contra hC2

  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := h.isSylowTwoOf hTH
  have hT1 : T ≠ ⊥ := by
    intro hT
    apply hH.1.2
    have := F7.isSylowTwoOf_pCoreOf_le hTsyl
    rw [hT] at this
    exact le_bot_iff.mp this
  set Z := quasithinOmegaOneCenter T with hZdef
  have hZT : Z ≤ T := (Subgroup.closure_le _).mpr fun _ hz => hz.1.1
  have hZcT : Z ≤ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun _ hz => hz.1.2
  have hZ2 : IsPGroup 2 Z := h.sylow.1.to_le hZT
  have hZ1 : Z ≠ ⊥ := CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot h.sylow.1 hT1

  obtain ⟨-, -, -, -, K₁, hK₁, hKeq, -⟩ := h510 G T M L H B D n hyp hN
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hK₁H : K₁ ≤ H := A3.subnormal_le hK₁.2.2.1
  have hK₁loc : K₁ ∈ lFamily T := cComp_mem_of_le hK₁ le_sup_left (sup_le hK₁H hTH)
  have hhatEx : ∀ X : Subgroup G, T ≤ X → K₁ ≤ X → pCoreOf 2 X ≠ ⊥ →
      ∃ Kh₁ : Subgroup G, IsHatComp X K₁ Kh₁ := by
    intro X hTX hK₁X hX
    obtain ⟨Kh₁, ⟨hKh₁, hK₁Kh₁⟩, huniq⟩ :=
      Vol2Native.lemma_1_2_4_existsUnique hloc Vol2Native.a37ForSQTKCat_proved h39 hX
        (h.isSylowTwoOf hTX) hK₁X hK₁loc
    exact ⟨Kh₁, hKh₁, hK₁Kh₁, fun Y hY hK₁Y => huniq Y ⟨hY, hK₁Y⟩⟩

  have hkey : ∀ D' : Subgroup G, D' ≤ D → pCoreOf 2 (D' ⊔ H) ≠ ⊥ →
      D' ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    intro D' hD' hO
    have hX : InH H (D' ⊔ H) := ⟨le_sup_right, hO⟩
    obtain ⟨Kh₁, hhat⟩ := hhatEx (D' ⊔ H) (hTH.trans le_sup_right) (hK₁H.trans le_sup_right) hO
    rcases h5113 G T M L V H B D K₁ (D' ⊔ H) Kh₁ n hyp hN hV hK₁ hKeq hX hhat with
      h1 | h2 | h3
    · exact (le_inf hD' le_sup_left).trans h1
    · exfalso
      obtain ⟨hL4, hn2, hA5, hKhZ, hiso, hZ⟩ := h2
      apply hC2
      left

      have hTCZ : T ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZcT
      have hK₁CZ : K₁ ≤ Subgroup.centralizer (Z : Set G) :=
        hhat.2.1.trans ((le_conjClosure Kh₁ T).trans hKhZ)
      have hZCZ : Z ≤ Subgroup.centralizer (Z : Set G) :=
        hZcT.trans (Subgroup.centralizer_le hZT)
      have hOCZ : pCoreOf 2 (Subgroup.centralizer (Z : Set G)) ≠ ⊥ :=
        pCoreOf_ne_bot_of_le_centerOf hZ2 hZ1 hZCZ (Subgroup.le_centralizer_iff.mpr le_rfl)
      obtain ⟨Kz₁, hz⟩ := hhatEx _ hTCZ hK₁CZ hOCZ
      obtain ⟨hKZeq, hor⟩ := hZ Kz₁ hz
      refine ⟨hL4, hn2, hA5, ?_, ?_⟩
      · rw [← hKZeq, hKeq]
        exact conjClosure_mono hz.2.1 le_rfl
      · rcases hor with heq | ⟨-, hM23⟩
        · exact o2q_cases_of_eq (heq.trans hKZeq) hiso
        · exact o2q_cases_of_eq hKZeq (Or.inr (Or.inr hM23))
    · exact absurd (Or.inr h3) hC2

  have hD := hN.2.1
  have hO : pCoreOf 2 (D ⊔ H) = ⊥ := by
    by_contra hne'
    exact hDK (hkey D le_rfl hne')
  obtain ⟨hev, hcase⟩ := h516 G T M L V H D n h hV hH hD hO
  obtain ⟨hcyc, hcard⟩ := h.isCyclic_card_of_isHall hF hD

  have hE : (n = 2 ∨ n = 4 ∨ n = 8) ∧ ∃ E : Subgroup G, E ≤ D ∧
      (Nat.card E = 3 ∨ Nat.card E = 15) ∧ ¬ E ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    have hD24 : n = 2 ∨ n = 4 → (n = 2 ∨ n = 4 ∨ n = 8) ∧ ∃ E : Subgroup G, E ≤ D ∧
        (Nat.card E = 3 ∨ Nat.card E = 15) ∧
          ¬ E ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
      rintro (h2 | h4)
      · refine ⟨Or.inl h2, D, le_rfl, Or.inl ?_, hDK⟩
        rw [hcard, h2]
        norm_num
      · refine ⟨Or.inr (Or.inl h4), D, le_rfl, Or.inr ?_, hDK⟩
        rw [hcard, h4]
        norm_num
    rcases hcase with ⟨h2, -⟩ | ⟨h24, -⟩ | ⟨h2, -⟩ | ⟨-, -, -, hDpm⟩
    · exact hD24 (Or.inl h2)
    · exact hD24 h24
    · exact hD24 (Or.inl h2)
    ·
      obtain ⟨m, hm⟩ := hev
      have hn2 : n / 2 = m := by omega
      have hm0 : m ≠ 0 := by have := h.two_le; omega
      have hcard' : Nat.card D = (2 ^ (n / 2) - 1) * (2 ^ (n / 2) + 1) := by
        rw [hcard, hn2, two_pow_sub_one_mul_add_one, hm, two_mul]
      have hpos1 : 0 < 2 ^ (n / 2) - 1 := by
        have : 2 ≤ 2 ^ (n / 2) := by
          rw [hn2]
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm0)
        omega
      obtain ⟨Dp, Dm, hDp, hDm, hcDp, hcDm, hDle⟩ := exists_le_sup_of_isCyclic hcyc
        (hn2 ▸ coprime_two_pow_sub_one_add_one hm0) hcard' hpos1 (by positivity)
      obtain ⟨hcen, hor⟩ := hDpm Dp Dm hDp hDm hcDp hcDm
      have hDmK : Dm ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
        hkey Dm hDm (pCoreOf_ne_bot_of_le_centerOf hZ2 hZ1 (hcen.trans inf_le_left)
          (hcen.trans inf_le_right))
      have hDpK : ¬ Dp ≤ Subgroup.normalizer (oTwoUpper H : Set G) := fun hle =>
        hDK (hDle.trans (sup_le hle hDmK))
      have h48 : n = 4 ∨ n = 8 := by
        rcases hor with hne' | h48
        · exact absurd (hkey Dp hDp hne') hDpK
        · exact h48
      rcases h48 with h4 | h8
      · exact hD24 (Or.inr h4)
      · refine ⟨Or.inr (Or.inr h8), Dp, hDp, Or.inr ?_, hDpK⟩
        rw [hcDp, h8]
        norm_num
  obtain ⟨hn248, E, hED, hEcard, hEK⟩ := hE

  have hEcyc : IsCyclic ↥E := Subgroup.isCyclic_of_le hED
  obtain ⟨p, Dp, hp, hDpD, hDpcard, hDpK⟩ : ∃ (p : ℕ) (Dp : Subgroup G), (p = 3 ∨ p = 5) ∧
      Dp ≤ D ∧ Nat.card Dp = p ∧ ¬ Dp ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rcases hEcard with h3 | h15
    · exact ⟨3, E, Or.inl rfl, hED, h3, hEK⟩
    · obtain ⟨D3, D5, h3E, h5E, hc3, hc5, hle⟩ :=
        exists_le_sup_of_isCyclic hEcyc (by norm_num : Nat.Coprime 3 5) (by rw [h15])
          (by norm_num) (by norm_num)
      by_cases h3K : D3 ≤ Subgroup.normalizer (oTwoUpper H : Set G)
      · by_cases h5K : D5 ≤ Subgroup.normalizer (oTwoUpper H : Set G)
        · exact absurd (hle.trans (sup_le h3K h5K)) hEK
        · exact ⟨5, D5, Or.inr rfl, h5E.trans hED, hc5, h5K⟩
      · exact ⟨3, D3, Or.inl rfl, h3E.trans hED, hc3, h3K⟩
  have hODp : pCoreOf 2 (Dp ⊔ H) = ⊥ := by
    by_contra hne'
    exact hDpK (hkey Dp hDpD hne')

  have hL34 : ¬ LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 := by
    intro hL34
    obtain ⟨-, -, -, ⟨-, -, hDB⟩, -⟩ := h5114 G T M L V H B D n hyp hN hV hL34
    apply hDK
    rw [hDB]
    exact (hN.1.1.trans inf_le_right).trans (le_normalizer_oTwoUpper H)

  obtain ⟨L₂, hL₂⟩ := hL2 G T M L H B D n hyp hN
  have hSL₂ := h521 G T M L H B D L₂ n hyp hN hL₂ hL34
  have hp2 : Hyp5_2_2p G T M L V H B D L₂ Dp n p :=
    { toHyp5_1_8 := hyp
      notation59 := hN
      ch5Module := hV
      not_le := hDK
      not_two := fun h => hC2 (Or.inl h)
      notL34 := hL34
      choice := hL₂
      S_le := hSL₂
      n_cases := hn248
      pCore_D := hO
      p_cases := hp
      Dp_le := hDpD
      card_Dp := hDpcard
      Dp_not_le := hDpK
      pCore_Dp := hODp }
  by_cases hG₀ : pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) = ⊥
  · exact hbot G T M L V H B D L₂ Dp n p hp2 hG₀
  · exact hne G T M L V H B D L₂ Dp n p hp2 hG₀

end CFSG.Quasithin.H13
