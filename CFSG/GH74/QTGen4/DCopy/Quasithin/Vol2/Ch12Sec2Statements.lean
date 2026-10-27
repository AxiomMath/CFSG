module

public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Stmt12_2_6_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    (∀ m ∈ Subgroup.normalizer (L : Set G),
      CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
    ∀ U H : Subgroup G, U ≠ ⊥ → U ≤ V → H ≤ Subgroup.normalizer (U : Set G) →
      H ⊓ Subgroup.normalizer (L : Set G) = H ⊓ Subgroup.normalizer (V : Set G)

@[expose] def Stmt12_2_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Hyp1223 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G) →
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
      (IsPrimeReduced 2 ((VZ T H).subgroupOf H) ∧
        T ⊓ Subgroup.centralizer (VZ T H : Set G) = pCoreOf 2 H ∧
        pCoreOf 2 H ≤ H ⊓ Subgroup.centralizer (VZ T H : Set G) ∧
        H ⊓ Subgroup.centralizer (VZ T H : Set G) ≤
          kerIn (H ⊓ Subgroup.normalizer (V : Set G)) H) ∧
      (¬ Group.IsSolvable ↥H →
        LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2 ∧
        ∃ Y : Subgroup G, oTwoUpper H ≤ Y ∧ quasithinIsMaximalLocal T Y ∧
          quasithinIsFaithfulLocal T Y ∧
          ((Y = oTwoUpper H ∧ IsA5ModuleSum (oTwoUpper H) ⁅VZ T H, oTwoUpper H⁆) ∨
            (Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
                alternatingGroup (Fin 7)) ∧
              CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
              T ≤ Subgroup.normalizer (Y : Set G) ∧
              ∀ VY : Subgroup G, IsIrrPlusIn Y (reducedAggregate (Y ⊔ T)) T VY →
                T ≤ Subgroup.normalizer (VY : Set G) ∧
                  (Nat.card VY = 2 ^ 4 ∨ Nat.card VY = 2 ^ 6))))

@[expose] def Stmt12_1_11_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    ∀ n : ℕ, (n = 4 ∨ n = 5) →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
    ∀ V V₁ V₂ : Subgroup G, V ≤ Subgroup.normalizer (L : Set G) →
      IsPrimeReduced 2 (V.subgroupOf (Subgroup.normalizer (L : Set G))) →
      Nonempty (↥(autOn (Subgroup.normalizer (L : Set G)) V) ≃*
        MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) →
      V₁ ⊓ V₂ = ⊥ → V₁ ⊔ V₂ = V →
      L ≤ Subgroup.normalizer (V₁ : Set G) → L ≤ Subgroup.normalizer (V₂ : Set G) →
      (∃ _ : IsMulCommutative ↥V₁, BinaryNaturalSL (V := ↥V₁) (autOn L V₁) ⊤ ⊥ n 1) →
      (∃ _ : IsMulCommutative ↥V₂, BinaryNaturalSL (V := ↥V₂) (autOn L V₂) ⊤ ⊥ n 1) →
      ¬ IsXSectionIso₂ L V₁ ⊥ V₂ ⊥ → False

@[expose] def Stmt12_2_5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (h : Hyp1223 G T L V),
    ∀ v ∈ V, v ≠ 1 →
      h.Lv v ≤ h.Mv v ∧ h.Mv v ≤ Subgroup.normalizer (h.Lv v : Set G) ∧
      CharTwo (h.Mv v) ∧ cgsIn (h.Gv v) h.Q ≤ h.Mv v ∧ h.Mv v ≤ h.MV

@[expose] def Stmt12_2_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    Subgroup.closure {x | x ∈ Subgroup.normalizer (L : Set G) ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} = L ∨
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) ∨
    ((∃ n : ℕ, (n = 6 ∨ n = 7) ∧ Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
          alternatingGroup (Fin n))) ∧
      L = Subgroup.closure {x | x ∈ Subgroup.normalizer (L : Set G) ∧ orderOf x = 3})

@[expose] def Stmt12_2_9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
        Subgroup.normalizer (L : Set G)) ∧
    (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
        Subgroup.normalizer (L : Set G) → L = ⁅L, thompsonJ T⁆)

@[expose] def Stmt12_2_10_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (h : Hyp1223 G T L V),
    h.MVbar ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) =
        autOn L V ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) ∧
      oTwoUpper h.MVbar = autOn L V ∧ h.MVbar = autOn L V ⊔ autOn T V

@[expose] def Stmt12_2_16_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → ∀ g : G, CFSG.conjugate V g = V ∨ V ⊓ CFSG.conjugate V g = ⊥

@[expose] def Stmt12_2_17_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V →
      weakClosureW0 T V ≤ T ⊓ Subgroup.centralizer (V : Set G) ∧
      T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) ∧
      Subgroup.normalizer (weakClosureW0 T V : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Stmt12_2_18_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
      ¬ V ≤ pCoreOf 2 H

@[expose] def Stmt12_2_20_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nat.card V = 2 ^ n ∧
      autOn L V = ⊤ ∧ (∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1) ∧
      T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G))

@[expose] def Stmt12_2_24_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nat.card V = 2 ^ n ∧ IsLnBlock L n

@[expose] def Stmt12_2_25_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V →
      Subgroup.normalizer (L : Set G) = L ∧ V = pCoreOf 2 L ∧
      (Nat.card V = 2 ^ 3 ∨ Nat.card V = 2 ^ 4) ∧ Nat.card (quasithinOmegaOneCenter T) = 2

@[expose] def Stmt12_2_26_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L

@[expose] def Stmt12_2_27_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → ∀ n : ℕ, (n = 3 ∨ n = 4) → IsLnBlock L n → Nat.card V = 2 ^ n →
    Subgroup.normalizer (L : Set G) = L → V = pCoreOf 2 L →
    (∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L) →
      (n = 4 → Nonempty (G ≃* NativeSporadic.M24) ∨ LieModel G .PSL 5 2 1) ∧
      (n = 3 → LieModel G .PSL 4 2 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 9)))

theorem stmt12_2_13_of_chain_F4 (h24 : Stmt12_2_24_F4) (h25 : Stmt12_2_25_F4) (h26 : Stmt12_2_26_F4)
    (h27 : Stmt12_2_27_F4) : Stmt12_2_13_F4 := by
  rw [stmt12_2_13_iff_F4]
  intro G _ _ T L V hH
  by_cases hE : NoEscape12_2_13 L V
  · obtain ⟨n, hn, hV, hB⟩ := h24 G T L V hH hE
    obtain ⟨hML, hVO, hV34, -⟩ := h25 G T L V hH hE
    obtain ⟨e⟩ := nonempty_mulEquiv_sl_of_isLnBlock hB
    have hn34 : n = 3 ∨ n = 4 := by
      rcases hV34 with h | h <;> rw [hV] at h <;>
        have := Nat.pow_right_injective (le_refl 2) h <;> omega
    obtain ⟨h4, h3⟩ := h27 G T L V hH hE n hn34 hB hV hML hVO (h26 G T L V hH hE)
    rcases hn34 with rfl | rfl
    · rcases h3 rfl with h | h
      · exact Or.inr (Or.inl ⟨3, Or.inl rfl, ⟨e⟩, h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨e⟩, h⟩))
    · rcases h4 rfl with h | h
      · exact Or.inr (Or.inr (Or.inr ⟨⟨e⟩, h⟩))
      · exact Or.inr (Or.inl ⟨4, Or.inr rfl, ⟨e⟩, h⟩)
  · left
    unfold NoEscape12_2_13 at hE
    push Not at hE
    obtain ⟨v, hv, hv1, hC⟩ := hE
    exact ⟨v, hv, hv1, hC⟩

end CFSG.Quasithin.H13
