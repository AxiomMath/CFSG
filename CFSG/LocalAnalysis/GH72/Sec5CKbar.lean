module

public import CFSG.LocalAnalysis.GH72.Sec5C
public import CFSG.LocalAnalysis.GH72.Sec5B
public import CFSG.LocalAnalysis.GH72.Sec5CBar

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

theorem quotIs_of_isL2OrA7_bar {G : Type} [Group G] {H W M₀ OM : Subgroup G} {q : ℕ}
    (hWH : W ≤ H) (hWM₀ : W ≤ M₀) (hOM : OM ≤ M₀) (hM₀OM : M₀ ≤ normalizer (OM : Set G))
    (hcov : Covers W M₀ OM) (hO : O H ⊓ W = W ⊓ OM) (hW : IsL2OrA7 (bar H W) q) :
    QuotIs M₀ OM (fun L _ => IsL2OrA7 L q) := by
  have : (OM.subgroupOf M₀).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOM).mpr hM₀OM
  obtain ⟨e⟩ := nonempty_bar_mulEquiv_of_covers (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hWH hWM₀ hcov hM₀OM hO
  exact ⟨_, _, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _,
    isL2OrA7_of_mulEquiv e.symm hW⟩

namespace Sec5KConfig

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔨 : Sec5KConfig ρ p)

theorem commutator_K₁_Y_le : ⁅𝔨.K₁, ρ.Y⁆ ≤ O 𝔨.K₁ := 𝔨.hK₁q.1

theorem exists_W : ∃ W : Subgroup G, W ≤ 𝔨.K₁ ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧
    Covers W ρ.N₀ (O ρ.N) ∧ 𝔨.K₁ = W ⊔ 𝔨.Pstar ⊔ ρ.Y ⊔ O 𝔨.K₁ ∧
    ((W ⊔ O 𝔨.K₁).subgroupOf 𝔨.K₁).Normal ∧ O 𝔨.K₁ ⊓ W = W ⊓ O ρ.N ∧
    (IsL2OrA7 (bar 𝔨.K₁ W) 5 ∨ (bar 𝔨.K₁ W = bar 𝔨.K₁ ρ.X ∧ IsKleinFour (bar 𝔨.K₁ W))) :=
  𝔨.hK₁q.2

theorem V_eq : 𝔨.P ⊓ 𝔨.K ⊓ O 𝔨.K₁ = 𝔨.V := 𝔨.hK₁.2.2.2

theorem U_le_K₁ : 𝔨.U ≤ 𝔨.K₁ := 𝔨.U_le_Pstar.trans 𝔨.Pstar_le_K₁

theorem U_le_centralizer_X : 𝔨.U ≤ centralizer (ρ.X : Set G) :=
  inf_le_left.trans inf_le_right

theorem oddCore_bar_K₁ : CFSG.oddCore (Bar 𝔨.K₁) = ⊥ := oddCore_quotient_oddCore_eq_bot _

theorem bar_W_normal {W : Subgroup G} (hWK₁ : W ≤ 𝔨.K₁)
    (hWn : ((W ⊔ O 𝔨.K₁).subgroupOf 𝔨.K₁).Normal) : (bar 𝔨.K₁ W).Normal := by
  have h := bar_normal hWn
  rwa [bar_sup_O hWK₁] at h

theorem bar_Y_le_center : bar 𝔨.K₁ ρ.Y ≤ center (Bar 𝔨.K₁) := by
  have h : bar 𝔨.K₁ ⁅𝔨.K₁, ρ.Y⁆ = ⊥ := bar_eq_bot_iff.mpr (inf_le_left.trans 𝔨.commutator_K₁_Y_le)
  rw [bar_commutator le_rfl 𝔨.Y_le_K₁, bar_self] at h
  intro y hy
  rw [mem_center_iff]
  intro g
  have := commutator_mem_commutator (mem_top g) hy
  rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem bar_K₁_eq {W : Subgroup G} (hWK₁ : W ≤ 𝔨.K₁)
    (hK₁W : 𝔨.K₁ = W ⊔ 𝔨.Pstar ⊔ ρ.Y ⊔ O 𝔨.K₁) :
    bar 𝔨.K₁ W ⊔ bar 𝔨.K₁ 𝔨.Pstar ⊔ bar 𝔨.K₁ ρ.Y = ⊤ := by
  have h := congrArg (bar 𝔨.K₁) hK₁W
  rw [bar_self] at h
  have h1 : W ⊔ 𝔨.Pstar ⊔ ρ.Y ≤ 𝔨.K₁ := sup_le (sup_le hWK₁ 𝔨.Pstar_le_K₁) 𝔨.Y_le_K₁
  rw [h, bar_sup_O h1, bar_sup (sup_le hWK₁ 𝔨.Pstar_le_K₁) 𝔨.Y_le_K₁,
    bar_sup hWK₁ 𝔨.Pstar_le_K₁]

theorem bar_W_sup_Pstar_normal {W : Subgroup G} (hWK₁ : W ≤ 𝔨.K₁)
    (hK₁W : 𝔨.K₁ = W ⊔ 𝔨.Pstar ⊔ ρ.Y ⊔ O 𝔨.K₁) :
    (bar 𝔨.K₁ W ⊔ bar 𝔨.K₁ 𝔨.Pstar).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← 𝔨.bar_K₁_eq hWK₁ hK₁W]
  exact sup_le le_normalizer (𝔨.bar_Y_le_center.trans (center_le_normalizer _))

theorem nonempty_bar_W_mulEquiv {L : Type} [Group L] (f : ρ.N₀ →* L)
    (hf : Function.Surjective f) (hker : f.ker = (O ρ.N).subgroupOf ρ.N₀)
    {W : Subgroup G} (hWK : W ≤ 𝔨.K₁ ⊓ ρ.N₀) (hWcov : Covers W ρ.N₀ (O ρ.N))
    (hWO : O 𝔨.K₁ ⊓ W = W ⊓ O ρ.N) : Nonempty (bar 𝔨.K₁ W ≃* L) :=
  nonempty_bar_mulEquiv_of_covers f hf hker (hWK.trans inf_le_left) (hWK.trans inf_le_right)
    hWcov ρ.N₀_le_normalizer_O_N hWO

include 𝔨 in
theorem X_le_N₀ : ρ.X ≤ ρ.N₀ := by
  obtain ⟨W, hWK, hXW, -⟩ := 𝔨.exists_W
  exact hXW.trans (hWK.trans inf_le_right)

include 𝔨 in
theorem quotIs_N₀ :
    QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) := by
  obtain ⟨W, hWK, -, hWcov, -, -, hWO, hWL⟩ := 𝔨.exists_W
  have : ((O ρ.N).subgroupOf ρ.N₀).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ρ.N₀_le_normalizer_O_N
  obtain ⟨e⟩ := 𝔨.nonempty_bar_W_mulEquiv (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hWK hWcov hWO
  refine ⟨_, _, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _, ?_⟩
  rcases hWL with hL | ⟨-, hL⟩
  · exact Or.inl (isL2OrA7_of_mulEquiv e.symm hL)
  · exact Or.inr (@isKleinFour_of_mulEquiv _ _ _ _ hL e)

theorem isKleinFour_bar_X : IsKleinFour (bar 𝔨.K₁ ρ.X) :=
  isKleinFour_bar_of_le 𝔨.X_le_K₁ ρ.isKleinFour_X

theorem isMaxInvIn_bar_Pstar : IsMaxInvIn p (bar 𝔨.K₁ A) ⊤ (bar 𝔨.K₁ 𝔨.Pstar) :=
  isMaxInvIn_bar 𝔨.hp 𝔨.hp2 ρ.isPGroup_A 𝔨.A_le_K₁
    (𝔨.hK.2.2.2.1.of_le 𝔨.Pstar_le_K₁ 𝔨.K₁_le_K)

theorem bar_U_le_centralizer_bar_X :
    bar 𝔨.K₁ 𝔨.U ≤ centralizer (bar 𝔨.K₁ ρ.X : Set (Bar 𝔨.K₁)) :=
  bar_le_centralizer 𝔨.U_le_centralizer_X

theorem bar_U_ne_bot {Q : Subgroup G} (h : ¬ Q ⊓ 𝔨.U ≤ 𝔨.V) : bar 𝔨.K₁ 𝔨.U ≠ ⊥ := by
  intro hU
  apply h
  intro x hx
  have hxO : x ∈ O 𝔨.K₁ := bar_eq_bot_iff.mp hU ⟨hx.2, 𝔨.U_le_K₁ hx.2⟩
  rw [← 𝔨.V_eq]
  exact ⟨𝔨.U_le_Pstar hx.2, hxO⟩

theorem eq_bot_of_bar_eq_bot {W : Subgroup G} (hWP : W ≤ 𝔨.Pstar) (hWX : ⁅ρ.X, W⁆ = W)
    (hW : bar 𝔨.K₁ W = ⊥) : W = ⊥ := by
  have hWO : W ≤ O 𝔨.K₁ := fun w hw => bar_eq_bot_iff.mp hW ⟨hw, 𝔨.Pstar_le_K₁ (hWP hw)⟩
  have hWV : W ≤ 𝔨.V := fun w hw => 𝔨.V_eq ▸ ⟨hWP hw, hWO hw⟩
  have hWC : ρ.X ≤ centralizer (W : Set G) :=
    le_centralizer_iff.mp (hWV.trans (le_centralizer_iff.mp 𝔨.X_le_centralizer_V))
  rw [← hWX]
  exact (commutator_eq_bot_iff_le_centralizer).mpr hWC

end Sec5KConfig

namespace Sec5ConfigR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔠 : Sec5ConfigR ρ p)

include 𝔠 in
theorem Y_le_M₀ : ρ.Y ≤ ρ.M₀ := by
  obtain ⟨W, hWH, hYW, -⟩ := 𝔠.exists_covering_W_H₁
  exact hYW.trans (hWH.trans inf_le_right)

include 𝔠 in
theorem quotIs_M₀ : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5) := by
  obtain ⟨W, hWH, -, hWcov, -, hWO, hWL⟩ := 𝔠.exists_covering_W_H₁
  exact quotIs_of_isL2OrA7_bar (hWH.trans inf_le_left) (hWH.trans inf_le_right) le_sup_right
    ρ.M₀_le_normalizer_O_M hWcov hWO hWL

end Sec5ConfigR

end CFSG.GH72
