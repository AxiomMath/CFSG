module

public import CFSG.LocalAnalysis.GH72.Sec5FourConfig
public import CFSG.LocalAnalysis.GH72.Sec5Nineteen
public import CFSG.LocalAnalysis.GH72.Sec5Seventeen
public import CFSG.LocalAnalysis.GH72.PGammaL2Permutable
import CFSG.LocalAnalysis.GH72.G3bNineteen
import CFSG.LocalAnalysis.GH72.Sec5ZJ

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

open G5d

namespace Sec5Roles

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A) {p : ℕ}
  (hp : p.Prime) (hp2 : p ≠ 2)

include hp hp2 in
theorem prop_5_4_main_of
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    (hYM₀ : ρ.Y ≤ ρ.M₀)
    (h1R : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H A : Set (Bar H)))
    (h55 : ∀ x ∈ ρ.X, x ≠ 1 → Sec4Setting.PConstrainedWrt p A (C x) ρ.Y →
      ∀ P : Subgroup G, IsMaxInvIn p A ⊤ P →
        ρ.IsCoveringFirst p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.Y)
    (h56 : ∀ x ∈ ρ.X, x ≠ 1 → Sec4Setting.PConstrainedWrt p A (C x) ρ.Y →
      (¬ ∃ H, ρ.IsCovering p H) →
      ∀ K, CFSG.IsPLocal p K → A ≤ K → Covers K ρ.N₀ (O ρ.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K ρ.X)
    (hT : ∀ 𝔠 : Sec5ConfigR ρ p, Nonempty (Sec5ConfigTR 𝔠))
    (h514 : ∀ (𝔠 : Sec5ConfigR ρ p) (𝔱 : Sec5ConfigTR 𝔠),
      𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) ≠ ⊥ → ∃ H, ρ.IsCovering p H)
    (h517 : ∀ (𝔠 : Sec5ConfigR ρ p) (𝔱 : Sec5ConfigTR 𝔠),
      𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥ →
      ∀ Tt : Subgroup G, IsMaxInvIn 𝔱.t A ⊤ Tt →
        ρ.IsCovering 𝔱.t (normalizer (CFSG.ambientMaxCardZJ Tt : Set G)))
    (h519 : ∀ (𝔠 : Sec5ConfigR ρ p) (𝔱 : Sec5ConfigTR 𝔠),
      𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥ →
      ∃ Tt : Subgroup G, IsMaxInvIn 𝔱.t A ⊤ Tt ∧
        𝔠.P ≤ normalizer (CFSG.ambientMaxCardZJ Tt : Set G))
    (hx₀ : ∃ x₀ ∈ ρ.X, x₀ ≠ 1 ∧ Sec4Setting.PConstrainedWrt p A (C x₀) ρ.Y)
    (hHns : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5))
    (hKex : ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K ρ.N₀ (O ρ.N)) :
    ∃ H, ρ.IsCovering p H := by
  by_contra hno
  obtain ⟨x₀, hx₀X, hx₀1, hx₀c⟩ := hx₀
  obtain ⟨𝔠⟩ := ρ.exists_sec5ConfigR_of hp hp2 h46 h413 hHns h1R h1N h55 h56
    ⟨hx₀X, hx₀1, hx₀c⟩ hKex hno
  obtain ⟨𝔱⟩ := hT 𝔠
  by_cases hC : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥
  · obtain ⟨Tt, hTt, hPJ⟩ := h519 𝔠 𝔱 hC
    exact hno (𝔱.exists_isCovering_of_end hHns hYM₀ h1R h413 hPJ (h517 𝔠 𝔱 hC Tt hTt))
  · exact hno (h514 𝔠 𝔱 hC)

end Sec5Roles

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)

include hAS hA in
theorem C_ne_top_of_mem_Y {y : G} (hy : y ∈ 𝔖.Y A) (hy1 : y ≠ 1) : C y ≠ ⊤ :=
  (𝔖.sec5Roles hAS hA).C_ne_top_of_mem_Y hy hy1

include hAS hA hp in
theorem prop_5_4_of
    (h51 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → (∃ x ∈ 𝔖.X A, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ 𝔖.Y A ≤ centralizer (P : Set G)) →
        PConstrainedWrt p A H (𝔖.Y A)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C y) ∧ ¬ 𝔖.X A ≤ centralizer (P : Set G)) →
        PConstrainedWrt p A H (𝔖.X A)))
    (hmain : ∀ 𝔖' : Sec4Setting G, A ≤ 𝔖'.S → IsE16 A →
      (∃ x₀ ∈ 𝔖'.X A, x₀ ≠ 1 ∧ PConstrainedWrt p A (C x₀) (𝔖'.Y A)) →
      (∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K (𝔖'.N₀ A) (O (𝔖'.N A))) →
      ∃ H, 𝔖'.IsCovering p A H)
    (hE4b : IsKleinFour 𝔖.S₁ →
      (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
        ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
      (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ PConstrainedWrt p A (C y) (𝔖.X A)) →
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ¬ PConstrainedWrt p A (C x) (𝔖.Y A)) →
      ∃ H, 𝔖.IsCovering p A H)
    (hD : ∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
      ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) :
    ∃ H, 𝔖.IsCovering p A H := by
  obtain ⟨D, hDp, hAD, hAD', hDgen⟩ := hD
  have hA2 : IsPGroup 2 A := isPGroup_of_isE16 hA
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => G4b.comm_of_isE16 hA ha hb
  have hXA : 𝔖.X A ≤ A := G4b.X_le_A 𝔖
  have hYA : 𝔖.Y A ≤ A := G4b.Y_le_A 𝔖
  obtain ⟨x, hxX, hx1, y, hyY, hy1, hD₀⟩ : ∃ x ∈ 𝔖.X A, x ≠ 1 ∧ ∃ y ∈ 𝔖.Y A, y ≠ 1 ∧
      ¬ A ≤ centralizer ((D ⊓ O (C x) ⊓ O (C y) : Subgroup G) : Set G) := by
    by_contra h
    push Not at h
    apply hAD'
    rw [le_centralizer_iff]
    exact hDgen.le.trans (E4b.xySup_le_of fun x hx hx1 y hy hy1 =>
      le_centralizer_iff.mp (h x hx hx1 y hy hy1))
  have hD₀p : IsPGroup p (D ⊓ O (C x) ⊓ O (C y) : Subgroup G) :=
    hDp.to_le (inf_le_left.trans inf_le_left)
  have hAD₀ : A ≤ normalizer ((D ⊓ O (C x) ⊓ O (C y) : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
      ⟨hAD ha, le_normalizer_O _ (E4b.le_C_of_mem hA hxX.1 ha)⟩,
      le_normalizer_O _ (E4b.le_C_of_mem hA hyY.1 ha)⟩
  have hD₀1 : D ⊓ O (C x) ⊓ O (C y) ≠ ⊥ := by
    intro hbot
    apply hD₀
    rw [hbot]
    intro a _
    rw [mem_centralizer_iff]
    intro d hd
    rw [SetLike.mem_coe, mem_bot] at hd
    rw [hd, one_mul, mul_one]
  have hKN : ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K (𝔖.N₀ A) (O (𝔖.N A)) :=
    exists_pLocal_covers_of_le_O hp hA2 hAc hYA hyY (N₀_le 𝔖 A) (O_N_le_N₀ 𝔖 A) hD₀p hD₀1
      inf_le_right
  have hKM : ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K (𝔖.M₀ A) (O (𝔖.M A)) :=
    exists_pLocal_covers_of_le_O hp hA2 hAc hXA hxX (M₀_le 𝔖 A) (O_M_le_M₀ 𝔖 A) hD₀p hD₀1
      (inf_le_left.trans inf_le_right)
  by_cases hxa : ∃ x₀ ∈ 𝔖.X A, x₀ ≠ 1 ∧ PConstrainedWrt p A (C x₀) (𝔖.Y A)
  · exact hmain 𝔖 hAS hA hxa hKN
  push Not at hxa
  have hYD₀ : 𝔖.Y A ≤ centralizer ((D ⊓ O (C x) ⊓ O (C y) : Subgroup G) : Set G) := by
    by_contra hY
    exact hxa x hxX hx1 ((h51 (C x) (E4b.C_ne_top 𝔖 hAS hA hxX hx1)
      (E4b.le_C_of_mem hA hxX.1)).1 (E4b.covers_C 𝔖 hxX) ⟨x, hxX, hx1, _,
        inf_le_left.trans (inf_le_right.trans (map_subtype_le _)), hD₀p, hAD₀,
        inf_le_left.trans inf_le_right, hY⟩)
  have hXD₀ : ¬ 𝔖.X A ≤ centralizer ((D ⊓ O (C x) ⊓ O (C y) : Subgroup G) : Set G) := fun hX =>
    hD₀ ((G4b.X_sup_Y 𝔖 hAS hA).ge.trans (sup_le hX hYD₀))
  have hCy : PConstrainedWrt p A (C y) (𝔖.X A) :=
    (h51 (C y) (C_ne_top_of_mem_Y 𝔖 hAS hA hyY hy1) (E4b.le_C_of_mem hA hyY.1)).2
      (fun _ hn => mem_sup_left ⟨centralizer_le (Set.singleton_subset_iff.mpr hyY)
        (N₀_le 𝔖 A hn), hn⟩)
      ⟨y, hyY, hy1, _, inf_le_right.trans (map_subtype_le _), hD₀p, hAD₀, inf_le_right, hXD₀⟩
  rcases 𝔖.decomp.dih₁.isKleinFour_or_isDihNonab with h4 | h₁
  · exact hE4b h4 ⟨D, hDp, hAD, hAD', hDgen⟩ ⟨y, hyY, hy1, hCy⟩ hxa
  ·
    let 𝔖' : Sec4Setting G :=
      { S := 𝔖.S, S₁ := 𝔖.S₂, S₂ := 𝔖.S₁, decomp := 𝔖.decomp.swap h₁,
        noIndexTwo := 𝔖.noIndexTwo, mc := 𝔖.mc, fusion := 𝔖.fusion.swap, z₁ := 𝔖.z₂,
        z₂ := 𝔖.z₁, hz₁ := 𝔖.hz₂, hz₂ := 𝔖.hz₁ }
    obtain ⟨H, hHloc, hHM, hHN⟩ := hmain 𝔖' hAS hA ⟨y, hyY, hy1, hCy⟩ hKM
    exact ⟨H, hHloc, hHN, hHM⟩

end Sec4Setting

end CFSG.GH72
