module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeSteps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522Ne
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeStepsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_2_ne_conj_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) →
    ∀ T₁ : Subgroup G,
      IsSylowTwoOf T₁ (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) →
      T ⊓ Subgroup.normalizer (L₂ : Set G) < T₁ → quasithinIsSylowTwo T₁ → T₁ ≤ M →
        oTwoUpper H = conjClosure L₂ T₁

@[expose] def Stmt5_2_2_ne_lt_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) →
    ∀ T₁ : Subgroup G,
      IsSylowTwoOf T₁ (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) →
      T ⊓ Subgroup.normalizer (L₂ : Set G) < T₁ → quasithinIsSylowTwo T₁ → T₁ ≤ M →
      oTwoUpper H = conjClosure L₂ T₁ → False

@[expose] def Stmt5_2_2_ne_eq_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) →
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (L₂ : Set G))
      (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) → False

theorem stmt5_2_2_ne_core_of_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (h432 : Stmt4_3_2_F4) (hA : Stmt5_2_2_ne_index_F4) (hB : Stmt5_2_2_ne_conj_F4) (hC : Stmt5_2_2_ne_lt_F4)
    (hD : Stmt5_2_2_ne_eq_F4) : Stmt5_2_2_ne_core_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set X₀ := Dp ⊔ (L₂ ⊔ S) ⊔ T₀ ⊔ B with hX₀def
  have hT₀X₀ : T₀ ≤ X₀ := le_sup_right.trans le_sup_left
  have hT₀2 : IsPGroup 2 ↥T₀ := h.sylow.1.to_le inf_le_left
  obtain ⟨T₁, hT₁, hT₀T₁⟩ := A4.exists_isSylowTwoOf_ge hT₀X₀ hT₀2
  rcases eq_or_lt_of_le hT₀T₁ with heq | hlt
  · rw [← heq] at hT₁
    exact hD G T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp hT₁

  have hidx := hA G T M L V H B D L₂ Dp n p hyp hL₂K hT₀
  have hT : Nat.card T = 2 * Nat.card T₀ := by
    have := Subgroup.relIndex_mul_card T₀ T
    rw [hidx, inf_eq_left.mpr inf_le_left] at this
    exact this.symm
  have hT₁le : Nat.card T₁ ≤ Nat.card T :=
    card_le_of_isPGroup_of_quasithinIsSylowTwo h.sylow hT₁.2.1
  have hidx₁ : T₀.relIndex T₁ = 2 := by
    have h1 := Subgroup.relIndex_mul_card T₀ T₁
    rw [inf_eq_left.mpr hT₀T₁] at h1
    have hne : T₀.relIndex T₁ ≠ 1 := fun h0 =>
      hlt.ne (le_antisymm hT₀T₁ (Subgroup.relIndex_eq_one.mp h0))
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    have h2 : T₀.relIndex T₁ * Nat.card T₀ ≤ 2 * Nat.card T₀ := by rw [h1, ← hT]; exact hT₁le
    have h3 : T₀.relIndex T₁ ≤ 2 := Nat.le_of_mul_le_mul_right h2 hpos
    have h4 : T₀.relIndex T₁ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact (Nat.card_pos (α := T₁)).ne' h1.symm
    omega
  have hT₁card : Nat.card T₁ = Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card T₀ T₁
    rw [inf_eq_left.mpr hT₀T₁, hidx₁] at h1
    rw [← h1, hT]
  have hT₁syl : quasithinIsSylowTwo T₁ := quasithinIsSylowTwo_of_card_eq h.sylow hT₁.2.1 hT₁card

  have hT₁N : T₁ ≤ Subgroup.normalizer (T₀ : Set G) := by
    have hn : (T₀.subgroupOf T₁).Normal := Subgroup.normal_of_index_eq_two hidx₁
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T₁).mp hn
  obtain ⟨-, -, -, -, hSL, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hTL : T ⊓ L ≤ T₀ := by
    intro x hx
    have hxS : x ∈ S ⊓ L := by
      rw [hSL]
      exact hx
    exact ⟨hx.1, hyp.S_le hxS.1⟩
  have hT₀L : T₀ ⊓ L = T ⊓ L :=
    le_antisymm (inf_le_inf_right L inf_le_left) (le_inf hTL inf_le_right)
  have hsylL : IsSylowTwoOf (T₀ ⊓ L) L := by
    rw [hT₀L]
    exact A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left
      h.sup_le_normalizer
  obtain ⟨-, hN⟩ := h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
    h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩
  have hT₁M : T₁ ≤ M := hT₁N.trans (hN T₀ inf_le_left hsylL)
  exact hC G T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp T₁ hT₁ hlt hT₁syl hT₁M
    (hB G T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp T₁ hT₁ hlt hT₁syl hT₁M)

end CFSG.Quasithin.H13
