module

public import CFSG.LocalAnalysis.GH72.Sec5E4b
public import CFSG.LocalAnalysis.GH72.Sec5Roles

public section

namespace CFSG.GH72

open Subgroup

namespace E4b

open G5d

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

theorem exists_isCovering_b2_of {p : ℕ} (hp : p.Prime)
    (h48ii : ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A))
    (hN₀ : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) fun L _ => IsKleinFour L)
    (h51 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → (∃ x ∈ 𝔖.X A, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ 𝔖.Y A ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt p A H (𝔖.Y A)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C y) ∧ ¬ 𝔖.X A ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt p A H (𝔖.X A)))
    (h52i : (∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H (𝔖.M₀ A) (O (𝔖.M A)) ∧
        Sec4Setting.PConstrainedWrt p A H (𝔖.Y A)) →
      ∀ P, IsMaxInvIn p A ⊤ P →
        𝔖.IsCoveringFirst p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G))
            (𝔖.Y A))
    (hKcfg : ∀ P : Subgroup G, IsMaxInvIn p A ⊤ P →
      (∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N)) →
      (∀ K, CFSG.IsPLocal p K → A ≤ K →
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K (𝔖.sec5Roles hAS hA).swap.X) →
      ∃ 𝔨 : Sec5KConfig (𝔖.sec5Roles hAS hA).swap p, 𝔨.P = P)
    (h59K : (∀ K, CFSG.IsPLocal p K → A ≤ K →
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K (𝔖.sec5Roles hAS hA).swap.X) →
      ∀ (𝔨 : Sec5KConfig (𝔖.sec5Roles hAS hA).swap p) (Q : Subgroup G), Q ≤ 𝔨.P →
      A ≤ normalizer (Q : Set G) → 𝔨.P ≤ normalizer (Q : Set G) →
      (∀ y ∈ (𝔖.sec5Roles hAS hA).swap.Y, y ≠ 1 → ¬ Q ≤ C y) →
      ∃ W : Subgroup G, Q = (𝔨.R ⊓ Q) ⊔ W ∧ IsCyclic W ∧ A ≤ normalizer (W : Set G) ∧
        W ≤ 𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ∧ ⁅(𝔖.sec5Roles hAS hA).swap.X, W⁆ = W)
    (h511K : (∀ K, CFSG.IsPLocal p K → A ≤ K →
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K (𝔖.sec5Roles hAS hA).swap.X) →
      ∀ (𝔨 : Sec5KConfig (𝔖.sec5Roles hAS hA).swap p) (Q : Subgroup G), Q ≤ 𝔨.P →
      A ≤ normalizer (Q : Set G) → 𝔨.P ≤ normalizer (Q : Set G) →
      (∀ y ∈ (𝔖.sec5Roles hAS hA).swap.Y, y ≠ 1 → ¬ Q ≤ C y) → 𝔨.P = Q ⊔ 𝔨.R →
      ∀ W : Subgroup G, (Q = (𝔨.R ⊓ Q) ⊔ W ∧ IsCyclic W ∧ A ≤ normalizer (W : Set G) ∧
        W ≤ 𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ∧ ⁅(𝔖.sec5Roles hAS hA).swap.X, W⁆ = W) →
      𝔨.P = 𝔨.Pstar ∧ 𝔨.P = 𝔨.U ⊔ W)
    (hD : ∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
      ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D)
    (hx : ∀ x ∈ 𝔖.X A, x ≠ 1 → ¬ Sec4Setting.PConstrainedWrt p A (C x) (𝔖.Y A)) :
    ∃ H, 𝔖.IsCovering p A H := by
  by_contra hno
  obtain ⟨D, hDp, hAD, hAD', hDgen⟩ := hD
  obtain ⟨P, hP, hDP⟩ := exists_isMaxInvIn_ge (H := ⊤) le_top hDp hAD
  have hW : ∀ K, CFSG.IsPLocal p K → A ≤ K →
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K (𝔖.sec5Roles hAS hA).swap.X :=
    fun _ hK hAK hcov => not_pConstrainedWrt_Y_of 𝔖 hAS hA h48ii hN₀ h52i hno hP hK hAK hcov
  obtain ⟨𝔨, h𝔨P⟩ := hKcfg P hP (exists_pLocal_covers_M₀ 𝔖 hA hp hDp hAD hAD' hDgen) hW
  have hQY : ∀ y ∈ (𝔖.sec5Roles hAS hA).swap.Y, y ≠ 1 → ¬ 𝔨.P ≤ C y := fun x hx' hx1 => by
    rw [h𝔨P]
    exact not_le_C_of 𝔖 hAS hA h48ii hN₀ hp h51 hx hno hDp hAD hAD' hDgen hP hDP hx' hx1
  have hAQ : A ≤ normalizer (𝔨.P : Set G) := 𝔨.hP.2.2.1
  obtain ⟨W, hW59⟩ := h59K hW 𝔨 𝔨.P le_rfl hAQ le_normalizer hQY
  have hPR : 𝔨.P = 𝔨.P ⊔ 𝔨.R := (sup_eq_left.mpr inf_le_left).symm
  obtain ⟨hPP, -⟩ := h511K hW 𝔨 𝔨.P le_rfl hAQ le_normalizer hQY hPR W hW59
  have hPK : P ≤ 𝔨.K := by
    rw [← h𝔨P, hPP]
    exact inf_le_right
  obtain ⟨hKloc, hAK, hcovK, -⟩ := 𝔨.hK
  exact hno ⟨𝔨.K, isCovering_of 𝔖 hAS hA h48ii hN₀ hKloc hAK hcovK hP hPK⟩

theorem hE4b_of {p : ℕ} (hp : p.Prime)
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h51 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → (∃ x ∈ 𝔖.X A, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ 𝔖.Y A ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt p A H (𝔖.Y A)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C y) ∧ ¬ 𝔖.X A ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt p A H (𝔖.X A)))
    (h52i : (∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H (𝔖.M₀ A) (O (𝔖.M A)) ∧
        Sec4Setting.PConstrainedWrt p A H (𝔖.Y A)) →
      ∀ P, IsMaxInvIn p A ⊤ P →
        𝔖.IsCoveringFirst p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G))
            (𝔖.Y A))
    (hKcfg : ∀ P : Subgroup G, IsMaxInvIn p A ⊤ P →
      (∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N)) →
      (∀ K, CFSG.IsPLocal p K → A ≤ K →
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K (𝔖.sec5Roles hAS hA).swap.X) →
      ∃ 𝔨 : Sec5KConfig (𝔖.sec5Roles hAS hA).swap p, 𝔨.P = P)
    (h59K : (∀ K, CFSG.IsPLocal p K → A ≤ K →
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K (𝔖.sec5Roles hAS hA).swap.X) →
      ∀ (𝔨 : Sec5KConfig (𝔖.sec5Roles hAS hA).swap p) (Q : Subgroup G), Q ≤ 𝔨.P →
      A ≤ normalizer (Q : Set G) → 𝔨.P ≤ normalizer (Q : Set G) →
      (∀ y ∈ (𝔖.sec5Roles hAS hA).swap.Y, y ≠ 1 → ¬ Q ≤ C y) →
      ∃ W : Subgroup G, Q = (𝔨.R ⊓ Q) ⊔ W ∧ IsCyclic W ∧ A ≤ normalizer (W : Set G) ∧
        W ≤ 𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ∧ ⁅(𝔖.sec5Roles hAS hA).swap.X, W⁆ = W)
    (h511K : (∀ K, CFSG.IsPLocal p K → A ≤ K →
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K (𝔖.sec5Roles hAS hA).swap.X) →
      ∀ (𝔨 : Sec5KConfig (𝔖.sec5Roles hAS hA).swap p) (Q : Subgroup G), Q ≤ 𝔨.P →
      A ≤ normalizer (Q : Set G) → 𝔨.P ≤ normalizer (Q : Set G) →
      (∀ y ∈ (𝔖.sec5Roles hAS hA).swap.Y, y ≠ 1 → ¬ Q ≤ C y) → 𝔨.P = Q ⊔ 𝔨.R →
      ∀ W : Subgroup G, (Q = (𝔨.R ⊓ Q) ⊔ W ∧ IsCyclic W ∧ A ≤ normalizer (W : Set G) ∧
        W ≤ 𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ∧ ⁅(𝔖.sec5Roles hAS hA).swap.X, W⁆ = W) →
      𝔨.P = 𝔨.Pstar ∧ 𝔨.P = 𝔨.U ⊔ W)
    (hmain : (∃ y ∈ (𝔖.sec5Roles hAS hA).swap.X, y ≠ 1 ∧
        Sec4Setting.PConstrainedWrt p A (C y) (𝔖.sec5Roles hAS hA).swap.Y) →
      QuotIs (𝔖.sec5Roles hAS hA).swap.M₀ (O (𝔖.sec5Roles hAS hA).swap.M)
        (fun L _ => IsL2OrA7 L 5) →
      (∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧
        Covers K (𝔖.sec5Roles hAS hA).swap.N₀ (O (𝔖.sec5Roles hAS hA).swap.N)) →
      ∃ H, (𝔖.sec5Roles hAS hA).swap.IsCovering p H) :
    IsKleinFour 𝔖.S₁ →
      (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
        ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
      (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ Sec4Setting.PConstrainedWrt p A (C y) (𝔖.X A)) →
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ¬ Sec4Setting.PConstrainedWrt p A (C x) (𝔖.Y A)) →
      ∃ H, 𝔖.IsCovering p A H := by
  intro _ hD hy hx
  obtain ⟨L, _, f, hf, hker, hL | hL⟩ := h48.1
  ·
    obtain ⟨D, hDp, hAD, hAD', hDgen⟩ := hD
    obtain ⟨H, hH⟩ := hmain hy ⟨L, inferInstance, f, hf, hker, hL⟩
      (exists_pLocal_covers_M₀ 𝔖 hA hp hDp hAD hAD' hDgen)
    exact ⟨H, (Sec4Setting.sec5Roles_isCovering 𝔖 hAS hA).mp
      ((Sec5Roles.isCovering_swap (𝔖.sec5Roles hAS hA)).mp hH)⟩
  ·
    exact exists_isCovering_b2_of 𝔖 hAS hA hp h48.2.1 ⟨L, inferInstance, f, hf, hker, hL⟩ h51 h52i
      hKcfg h59K h511K hD hx

end E4b

end CFSG.GH72
