module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

variable {G : Type} [Group G]

theorem u3abel_commute {T F : Subgroup G} {t₁ t₂ c₁ c₂ : G} (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (hc₂t₂ : t₂ * c₂ = c₂ * t₂) (hf₁ : t₁ * c₁ ∈ F) (hf₂ : t₂ * c₂ ∈ F)
    (hFT : ∀ a ∈ F ⊓ T, ∀ f ∈ F, a * f = f * a) (n : ℤ) (hn : c₂ ^ n = c₁) :
    (t₁ * c₁) * (t₂ * c₂) = (t₂ * c₂) * (t₁ * c₁) := by
  set f₁ := t₁ * c₁ with hf₁def
  set f₂ := t₂ * c₂ with hf₂def
  have hpow : f₂ ^ n = t₂ ^ n * c₁ := by
    rw [hf₂def, (Commute.mul_zpow (show Commute t₂ c₂ from hc₂t₂) n), hn]
  have hs : f₂ ^ n * f₁⁻¹ = t₂ ^ n * t₁⁻¹ := by
    rw [hpow, hf₁def, mul_inv_rev]
    group
  have hsF : f₂ ^ n * f₁⁻¹ ∈ F ⊓ T := by
    refine ⟨F.mul_mem (F.zpow_mem hf₂ n) (F.inv_mem hf₁), ?_⟩
    rw [hs]
    exact T.mul_mem (T.zpow_mem ht₂ n) (T.inv_mem ht₁)
  set s := f₂ ^ n * f₁⁻¹ with hsdef
  have hc : Commute s f₂ := hFT _ hsF f₂ hf₂
  have hc' : Commute s⁻¹ f₂ := hc.inv_left
  have hcc : Commute (f₂ ^ n) f₂ := (Commute.refl f₂).zpow_left n
  have hf₁eq : f₁ = s⁻¹ * f₂ ^ n := by rw [hsdef, mul_inv_rev, inv_inv, inv_mul_cancel_right]
  calc f₁ * f₂ = (s⁻¹ * f₂ ^ n) * f₂ := by rw [← hf₁eq]
    _ = s⁻¹ * (f₂ ^ n * f₂) := mul_assoc _ _ _
    _ = s⁻¹ * (f₂ * f₂ ^ n) := by rw [hcc.eq]
    _ = (s⁻¹ * f₂) * f₂ ^ n := (mul_assoc _ _ _).symm
    _ = (f₂ * s⁻¹) * f₂ ^ n := by rw [hc'.eq]
    _ = f₂ * (s⁻¹ * f₂ ^ n) := mul_assoc _ _ _
    _ = f₂ * f₁ := by rw [← hf₁eq]

theorem u3abel_exists_zpow {p : ℕ} [Fact p.Prime] [Finite G] {Z : Subgroup G}
    (hZp : IsPGroup p Z) (hZc : IsCyclic Z) (c₁ c₂ : G) (h₁ : c₁ ∈ Z) (h₂ : c₂ ∈ Z) :
    (∃ n : ℤ, c₂ ^ n = c₁) ∨ ∃ n : ℤ, c₁ ^ n = c₂ := by
  set a : Z := ⟨c₁, h₁⟩
  set b : Z := ⟨c₂, h₂⟩
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hZp) a
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hZp) b
  have key : ∀ (u v : Z) (i j : ℕ), orderOf u = p ^ i → orderOf v = p ^ j → i ≤ j →
      ∃ n : ℤ, v ^ n = u := by
    intro u v i j hu hv hij
    have hle : zpowers u ≤ zpowers v := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hu, hv]
      exact pow_dvd_pow p hij
    exact mem_zpowers_iff.mp (hle (mem_zpowers u))
  rcases le_total i j with hij | hji
  · left
    obtain ⟨n, hn⟩ := key a b i j hi hj hij
    exact ⟨n, congrArg Subtype.val hn⟩
  · right
    obtain ⟨n, hn⟩ := key b a j i hj hi hji
    exact ⟨n, congrArg Subtype.val hn⟩

theorem u3abel_isMulCommutative {p : ℕ} [Fact p.Prime] [Finite G] {T Z F : Subgroup G}
    (hZp : IsPGroup p Z) (hZc : IsCyclic Z) (hTZ : ∀ t ∈ T, ∀ c ∈ Z, t * c = c * t)
    (hFTZ : F ≤ T ⊔ Z) (hFT : ∀ a ∈ F ⊓ T, ∀ f ∈ F, a * f = f * a) : IsMulCommutative F := by
  have hTN : T ≤ normalizer (Z : Set G) := fun t ht =>
    Subgroup.centralizer_le_normalizer (Z : Set G)
      (mem_centralizer_iff.mpr fun c hc => (hTZ t ht c hc).symm)
  have hdec : ∀ f ∈ F, ∃ t ∈ T, ∃ c ∈ Z, f = t * c := fun f hf => by
    have hf' : f ∈ ((T ⊔ Z : Subgroup G) : Set G) := hFTZ hf
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T Z hTN] at hf'
    obtain ⟨t, ht, c, hc, rfl⟩ := hf'
    exact ⟨t, ht, c, hc, rfl⟩
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  show (a : G) * b = b * a
  obtain ⟨t₁, ht₁, c₁, hc₁, ha⟩ := hdec a a.2
  obtain ⟨t₂, ht₂, c₂, hc₂, hb⟩ := hdec b b.2
  have ha' : t₁ * c₁ ∈ F := ha ▸ a.2
  have hb' : t₂ * c₂ ∈ F := hb ▸ b.2
  rw [ha, hb]
  rcases u3abel_exists_zpow hZp hZc c₁ c₂ hc₁ hc₂ with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact u3abel_commute ht₁ ht₂ (hTZ t₂ ht₂ c₂ hc₂) ha' hb' hFT n hn
  · exact (u3abel_commute ht₂ ht₁ (hTZ t₁ ht₁ c₁ hc₁) hb' ha' hFT n hn).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
