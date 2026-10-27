module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223JMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152U21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T H V H₁ H₂ : Subgroup G}

theorem input15112J_of_F4 (h15112 : StageLemma15112)
    (h15208 : StageLemma15208_F4) (hN : StageNotation15209_F4) : Input15112J_F4 := by
  intro G _ _ T Mc M hs H hH H₁ H₂ hP
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hT : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hC := (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  have hNo := hN G T Mc M hs H hH
  obtain ⟨_, ⟨A₀, hA₀, -⟩, -⟩ := hNo.sigmaPrime_nonempty
  obtain ⟨A₁, hA₁, A₂, hA₂, hA₁T, hA₂T, hA₁H₁, hA₂H₂⟩ :=
    exists_delta_pair hT φ hP ⟨A₀, hA₀⟩
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hY := card_join_pair hP hA₁H₁ hA₂H₂ (hNo.card_delta A₁ hA₁) (hNo.card_delta A₂ hA₂)
  have hN₁ : (thompsonJ H ⊔ pCoreOf 2 H).relIndex H = 2 := relIndex_J_sup_Q hC ⟨φ⟩
  have hN₁H : thompsonJ H ⊔ pCoreOf 2 H ≤ H :=
    sup_le (S152Fin.thompsonJ_le_left H) (pCoreOf_le 2 H)
  have hcard := card_inf_index_two hT φ hN₁H hN₁
  have hAle : ∀ A, A ∈ deltaSet H (V154 T Mc M) → A ≤ T → A ≤ thompsonJ T := fun A hA hAT =>
    le_iSup₂_of_le A ⟨hAT, hA.1.2.1, fun B hBT hB => hA.1.2.2 B (hBT.trans hT.1) hB⟩ le_rfl
  have hYX : A₁ ⊔ A₂ ⊔ pCoreOf 2 H ≤ thompsonJ T ⊔ pCoreOf 2 H :=
    sup_le (sup_le ((hAle A₁ hA₁ hA₁T).trans le_sup_left) ((hAle A₂ hA₂ hA₂T).trans le_sup_left))
      le_sup_right
  have hXN : thompsonJ T ⊔ pCoreOf 2 H ≤ (thompsonJ H ⊔ pCoreOf 2 H) ⊓ T :=
    le_inf (sup_le ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans le_sup_left) le_sup_right)
      (sup_le (S152Fin.thompsonJ_le_left T) hQT)
  have hYN : A₁ ⊔ A₂ ⊔ pCoreOf 2 H = (thompsonJ H ⊔ pCoreOf 2 H) ⊓ T :=
    Subgroup.eq_of_le_of_card_ge (hYX.trans hXN) (by rw [hcard, hY])
  have hXY : thompsonJ T ⊔ pCoreOf 2 H = A₁ ⊔ A₂ ⊔ pCoreOf 2 H :=
    le_antisymm (hXN.trans hYN.symm.le) hYX
  have hXcard : Nat.card ↥(thompsonJ T ⊔ pCoreOf 2 H) = 4 * Nat.card (pCoreOf 2 H) := by
    rw [hXY]; exact hY
  have hXT : thompsonJ T ⊔ pCoreOf 2 H ≤ T := hXN.trans inf_le_right
  have hXB : thompsonJ T ⊔ pCoreOf 2 H ≤ H₁ ⊔ H₂ := by
    rw [hXY]
    exact sup_le (sup_le (hA₁H₁.trans le_sup_left) (hA₂H₂.trans le_sup_right))
      (hP.le₁.1.trans le_sup_left)
  have hq : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  refine ⟨⟨hXB, hT.2.1.to_le hXT, ?_⟩, ?_⟩
  · show ¬ 2 ∣ (thompsonJ T ⊔ pCoreOf 2 H).relIndex (H₁ ⊔ H₂)
    have h1 := Subgroup.relIndex_mul_card (thompsonJ T ⊔ pCoreOf 2 H) (H₁ ⊔ H₂)
    rw [inf_eq_left.mpr hXB, hXcard, card_sup_pair hP] at h1
    have h2 : (thompsonJ T ⊔ pCoreOf 2 H).relIndex (H₁ ⊔ H₂) * 4 * Nat.card (pCoreOf 2 H) =
        36 * Nat.card (pCoreOf 2 H) := by
      rw [mul_assoc]
      exact h1
    have h3 := Nat.eq_of_mul_eq_mul_right hq h2
    omega
  · have h1 := Subgroup.relIndex_mul_card (thompsonJ T ⊔ pCoreOf 2 H) T
    rw [inf_eq_left.mpr hXT, hXcard, card_T hT φ] at h1
    have h2 : (thompsonJ T ⊔ pCoreOf 2 H).relIndex T * 4 * Nat.card (pCoreOf 2 H) =
        8 * Nat.card (pCoreOf 2 H) := by
      rw [mul_assoc]
      exact h1
    have h3 := Nat.eq_of_mul_eq_mul_right hq h2
    omega

end S15223

end CFSG.Quasithin
