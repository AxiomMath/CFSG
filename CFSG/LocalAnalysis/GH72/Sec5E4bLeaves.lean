module

public import CFSG.LocalAnalysis.GH72.Sec5E4bAssembly
public import CFSG.LocalAnalysis.GH72.Sec4Four
public import CFSG.LocalAnalysis.GH72.WalterE16
import CFSG.LocalAnalysis.GH72.Sec4Prop46
import CFSG.LocalAnalysis.GH72.Sec5Four
import CFSG.LocalAnalysis.GH72.Sec5One
import CFSG.LocalAnalysis.GH72.Sec5OneN
import CFSG.LocalAnalysis.GH72.Sec5Second
import CFSG.LocalAnalysis.GH72.Sec5TExists
import CFSG.LocalAnalysis.GH72.Sec5ZJ
public import CFSG.LocalAnalysis.GH72.Sec5Tools

public section

namespace CFSG.GH72

open Subgroup

namespace Sec5Roles

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A) {p : ℕ}
  (hp : p.Prime) (hp2 : p ≠ 2)

include hp hp2 in
theorem prop_5_4_main_of_sec4
    (h315 : (∃ H₁ : Subgroup (Bar (C ρ.z₁)), bar (C ρ.z₁) ρ.S₁ ⊓ H₁ = ⊥ ∧
        bar (C ρ.z₁) ρ.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C ρ.z₁) ρ.S₁ : Set (Bar (C ρ.z₁))) ∧
        bar (C ρ.z₁) ρ.S₂ ≤ ⁅H₁, H₁⁆ ∧
        (IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C ρ.z₁))) 5 ∨ ⁅H₁, H₁⁆ = bar (C ρ.z₁) ρ.S₂)) ∧
      (∃ K₁ : Subgroup (Bar (C ρ.z₂)), bar (C ρ.z₂) ρ.S₂ ⊓ K₁ = ⊥ ∧
        bar (C ρ.z₂) ρ.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C ρ.z₂) ρ.S₂ : Set (Bar (C ρ.z₂))) ∧
        bar (C ρ.z₂) ρ.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C ρ.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C ρ.z₂) ρ.S₁)))
    (h45 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A H P₁ →
      IsMaxInvIn p A H P₂ → ∃ g ∈ H ⊓ normalizer (A : Set G),
        P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h46 : ∀ t : ℕ, t.Prime → t ≠ 2 → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn t A ⊤ P₁ →
      IsMaxInvIn t A ⊤ P₂ → ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h47 : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₂ ρ.M₀ ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (A : Set G)) ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (ρ.S₂ : Set G)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → O2 (C x) = (O2 ρ.M ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (ρ.M₀ ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₁ ρ.N₀ ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (A : Set G)) ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (ρ.S₁ : Set G)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → O2 (C y) = (O2 ρ.N ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (ρ.N₀ ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h411 : (∀ x ∈ ρ.X, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, ρ.X⁆ ⊔ ⁅⁅D, ρ.Y⁆, ⁅D, ρ.Y⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, ρ.Y⁆ ⊔ ⁅⁅D, ρ.X⁆, ⁅D, ρ.X⁆⁆ ≤ O (C y)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h1ML : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, ∃ L₁ : Subgroup (Bar H), W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧
        Covers W ρ.M₀ (O ρ.M) ∧ H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧
        ((W ⊔ O H).subgroupOf H).Normal ∧ O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) ∧
        L₁.Normal ∧ bar H ρ.X ≤ L₁ ∧ L₁ ⊓ bar H W = ⊥ ∧
        L₁ ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) ∧
        L₁ ⊔ bar H W ⊔ normalizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) = ⊤)
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H A : Set (Bar H)))
    (hx₀ : ∃ x₀ ∈ ρ.X, x₀ ≠ 1 ∧ Sec4Setting.PConstrainedWrt p A (C x₀) ρ.Y)
    (hHns : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5))
    (hKex : ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K ρ.N₀ (O ρ.N)) :
    ∃ H, ρ.IsCovering p H := by
  have h52 := fun {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) =>
    ρ.prop_5_2_of ht ht2 (h46 t ht ht2) h1M h1N h47 h48 h413
  have hXN₀ : ρ.X ≤ ρ.N₀ := ρ.X_le_S₁.trans h48.2.1.le
  have hT : ∀ 𝔠 : Sec5ConfigR ρ p, Nonempty (Sec5ConfigTR 𝔠) := fun 𝔠 =>
    𝔠.exists_sec5ConfigT_of
      (𝔠.lemma_5_8_of exists_three_element_mem_normalizer_kleinFour h48.1 hXN₀) h48
      (𝔠.lemma_5_7_of exists_three_element_mem_normalizer_kleinFour)
      (𝔠.lemma_5_9_of isCyclic_of_odd_of_kleinFour_le_normalizer
        exists_le_centralizer_of_odd_of_kleinFour_le_normalizer
        exists_three_element_mem_normalizer_kleinFour h48.1 hXN₀ h45
        (ρ.lemma_5_6_of hp hp2 (h52 hp hp2) 𝔠.x₀ 𝔠.hx₀.1 𝔠.hx₀.2.1 𝔠.hx₀.2.2 𝔠.hno) h1N)
      (𝔠.exists_isElemAbelian_le_R_inf_Q_of
        exists_le_centralizer_of_odd_of_kleinFour_le_normalizer
        exists_three_element_mem_normalizer_kleinFour)
      (𝔠.toSec5KConfig.isCyclic_commutator_Pstar_X_of isCyclic_of_odd_of_kleinFour_le_normalizer
        exists_le_centralizer_of_odd_of_kleinFour_le_normalizer).1
      h315 h411 h413
  exact ρ.prop_5_4_main_of hp hp2 (h46 p hp hp2) h413 (ρ.Y_le_S₂.trans h47.2.1.le) h1M h1N
    (fun x hx hx1 hCx P hP => ρ.lemma_5_5_of hp hp2 (h52 hp hp2).1 x hx hx1 hCx P hP)
    (fun x hx hx1 hCx hno => ρ.lemma_5_6_of hp hp2 (h52 hp hp2) x hx hx1 hCx hno) hT
    (fun _ 𝔱 hC => 𝔱.lemma_5_14 hC)
    (fun _ 𝔱 hC Tt hTt => 𝔱.lemma_5_17_of (h52 𝔱.ht.1 𝔱.ht.2.1) 𝔱.lemma_5_15
      (𝔱.lemma_5_16_of h411) hC Tt hTt)
    (fun _ 𝔱 hC => 𝔱.lemma_5_19_of h47 hHns h1M h1ML
      (ρ.lemma_5_1_of 𝔱.ht.1 𝔱.ht.2.1 h1M h1N h47 h48)
      (ρ.prop_5_2_cover_first_of 𝔱.ht.1 𝔱.ht.2.1 h1M h47 h413)
      (fun hO => exists_isMaxInvIn_mul_comm_of_permutable hO) hC)
    hx₀ hHns hKex

end Sec5Roles

theorem hmain_of_leaves
    (h315 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
        (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
          H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
          bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
        (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
          K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
          bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
          (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂))) :
    ∀ {G : Type} [Group G] [Finite G] {A : Subgroup G} {p : ℕ}, p.Prime → p ≠ 2 →
      ∀ 𝔖' : Sec4Setting G, A ≤ 𝔖'.S → IsE16 A →
      (∃ x₀ ∈ 𝔖'.X A, x₀ ≠ 1 ∧ Sec4Setting.PConstrainedWrt p A (C x₀) (𝔖'.Y A)) →
      (∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K (𝔖'.N₀ A) (O (𝔖'.N A))) →
      ∃ H, 𝔖'.IsCovering p A H := by
  intro G _ _ A p hp hp2 𝔖 hAS hA hx₀ hKex
  have h315' := h315 𝔖.toSec3Setting 𝔖.fusion
  have h317' := h317 𝔖.toSec3Setting 𝔖.fusion
  have h315z := h315' 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have h317z := h317' 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have h44 := 𝔖.prop_4_4_of h315' h317' walterE16
  have h44J := 𝔖.prop_4_4_J_of h315' h317' walterE16
  have h47 := 𝔖.lemma_4_7_of hAS hA h315'
  have h48 := 𝔖.lemma_4_8_of hAS hA h315'
  have h1M := Sec4Setting.sec5_one_M_of (𝔖 := 𝔖) h44 h315z h317z h47 h48 hAS hA
  have h1ML := Sec4Setting.sec5_one_M_L₁_of (𝔖 := 𝔖) h44 h315z h317z h47 h48 hAS hA
  obtain ⟨L, _, f, hf, hker, hL⟩ := h47.1
  obtain ⟨H, hH⟩ := (𝔖.sec5Roles hAS hA).prop_5_4_main_of_sec4 hp hp2
    (Sec4Setting.prop_3_15_weaken 𝔖 h315z)
    (fun H hH hAH P₁ P₂ h₁ h₂ =>
      𝔖.lemma_4_5_of h44 h44J h315' h317' H hH A hAH hA p hp hp2 P₁ P₂ h₁ h₂)
    (𝔖.prop_4_6_of h44 h44J h315' h317' A hA) (Sec4Setting.lemma_4_7_weaken 𝔖 h47) h48
    (𝔖.lemma_4_11_of hAS hA h315z isCyclic_of_odd_of_kleinFour_le_normalizer)
    (𝔖.lemma_4_13_of hA h315z h47 h48) (Sec4Setting.sec5_one_M_weaken 𝔖 h1M)
    (fun H hH hAH hcov => by
      obtain ⟨W, L₁, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h1ML H hH hAH hcov
      exact ⟨W, L₁, h₁, h₂, h₃, h₄, h₅, h₆, Or.inl (h₇.mono (by norm_num)), h₈⟩)
    (Sec4Setting.sec5_one_N_of (𝔖 := 𝔖) hAS hA h44 h315z h317z h47 h48) hx₀
    ⟨L, inferInstance, f, hf, hker, hL.mono (by norm_num)⟩ hKex
  exact ⟨H, (Sec4Setting.sec5Roles_isCovering 𝔖 hAS hA).mp hH⟩

theorem hE4b_of_leaves
    (h315 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
        (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
          H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
          bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
        (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
          K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
          bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
          (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂))) :
    ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}, A ≤ 𝔖.S → IsE16 A →
      ∀ {p : ℕ}, p.Prime → p ≠ 2 → IsKleinFour 𝔖.S₁ →
      (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
        ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
      (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ Sec4Setting.PConstrainedWrt p A (C y) (𝔖.X A)) →
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ¬ Sec4Setting.PConstrainedWrt p A (C x) (𝔖.Y A)) →
      ∃ H, 𝔖.IsCovering p A H := by
  intro G _ _ 𝔖 A hAS hA p hp hp2
  have h315' := h315 𝔖.toSec3Setting 𝔖.fusion
  have h317' := h317 𝔖.toSec3Setting 𝔖.fusion
  have h315z := h315' 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have h317z := h317' 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have h44 := 𝔖.prop_4_4_of h315' h317' walterE16
  have h44J := 𝔖.prop_4_4_J_of h315' h317' walterE16
  have h45 := fun (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) (P₁ P₂ : Subgroup G)
      (h₁ : IsMaxInvIn p A H P₁) (h₂ : IsMaxInvIn p A H P₂) =>
    𝔖.lemma_4_5_of h44 h44J h315' h317' H hH A hAH hA p hp hp2 P₁ P₂ h₁ h₂
  have h46 := 𝔖.prop_4_6_of h44 h44J h315' h317' A hA
  have h47 := 𝔖.lemma_4_7_of hAS hA h315'
  have h48 := 𝔖.lemma_4_8_of hAS hA h315'
  have h413 := 𝔖.lemma_4_13_of hA h315z h47 h48
  have h1M := Sec4Setting.sec5_one_M_of (𝔖 := 𝔖) h44 h315z h317z h47 h48 hAS hA
  have h1N := Sec4Setting.sec5_one_N_of (𝔖 := 𝔖) hAS hA h44 h315z h317z h47 h48
  have hXN₀ : (𝔖.sec5Roles hAS hA).swap.X ≤ (𝔖.sec5Roles hAS hA).swap.N₀ :=
    (𝔖.sec5Roles hAS hA).swap.X_le_S₁.trans h47.2.1.le
  have h48i := (Sec4Setting.lemma_4_7_weaken 𝔖 h47).1
  exact E4b.hE4b_of 𝔖 hAS hA hp h48
    (fun H hH hAH => 𝔖.lemma_5_1_of hAS hA hp hp2 h1M h1N h47 h48 H hH hAH)
    (𝔖.prop_5_2_of hAS hA hp hp2 (h46 p hp hp2) h1M h1N h47 h48 h413).1
    (fun P hP hKex hW => (𝔖.sec5Roles hAS hA).swap.exists_sec5KConfig_of hp hp2 (h46 p hp hp2)
      (fun H hH => (h413 H hH).1) (Sec4Setting.sec5_one_M_weaken 𝔖 h1M) hW hKex hP)
    (fun hW 𝔨 Q hQP hAQ hPQ hQY => 𝔨.lemma_5_9_of Q hQP hAQ hPQ hQY
      isCyclic_of_odd_of_kleinFour_le_normalizer
      exists_le_centralizer_of_odd_of_kleinFour_le_normalizer h48i hXN₀ h45 hW
      (Sec4Setting.sec5_one_M_weaken 𝔖 h1M))
    (fun _ 𝔨 Q hQP hAQ hPQ hQY hPQR W hW => 𝔨.lemma_5_11_of Q hQP hPQR
      (𝔨.lemma_5_8_of Q hQP hAQ hPQ hQY h48i hXN₀) W hW)
    (fun hx hns hK => (𝔖.sec5Roles hAS hA).swap.prop_5_4_main_of_sec4 hp hp2
      (Sec4Setting.prop_3_15_weaken 𝔖 h315z).symm h45 h46 h48
      (Sec4Setting.lemma_4_7_weaken 𝔖 h47)
      (𝔖.lemma_4_11_of hAS hA h315z isCyclic_of_odd_of_kleinFour_le_normalizer).symm
      (fun H hH => (h413 H hH).symm) h1N
      (Sec4Setting.sec5_one_N_L₂_of (𝔖 := 𝔖) hAS hA h44 h315z h317z h47 h48 hns)
      (Sec4Setting.sec5_one_M_weaken 𝔖 h1M) hx hns hK)

end CFSG.GH72
