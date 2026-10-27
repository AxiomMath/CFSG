module

public import CFSG.ClassicalInvolution.Asc77.AscR10Fus
public import CFSG.ClassicalInvolution.Asc77.AscR10Sg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}




theorem Std20.r_fus_plus [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    (h9 : p ^ f ≠ 9) {b : G} (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) {s : G} (hs2 : s * s = 1)
    (hsb : s * b = b * s) (hsz : ∃ g : G, s = g * z * g⁻¹) :
    ∃ c : G, c * b = b * c ∧ s = c * z * c⁻¹ := by
  obtain ⟨c₀, hc₀b, hc₀S⟩ := d.r_exists_conj_into_S c7 c9 h8 h9 hb hk hu huo hact hs2 hsb
  generalize hs₁ : c₀⁻¹ * s * c₀ = s₁ at hc₀S
  have hs : s = c₀ * s₁ * c₀⁻¹ := by rw [← hs₁]; group
  have hs₁2 : s₁ * s₁ = 1 := by
    have : s₁ * s₁ = c₀⁻¹ * (s * s) * c₀ := by rw [← hs₁]; group
    rw [this, hs2]; group
  have hs₁b : s₁ * b = b * s₁ := by
    rw [← hs₁]
    calc c₀⁻¹ * s * c₀ * b = c₀⁻¹ * s * (c₀ * b) := by group
      _ = c₀⁻¹ * s * (b * c₀) := by rw [hc₀b]
      _ = c₀⁻¹ * (s * b) * c₀ := by group
      _ = c₀⁻¹ * (b * s) * c₀ := by rw [hsb]
      _ = (c₀⁻¹ * b) * s * c₀ := by group
      _ = (b * c₀⁻¹) * s * c₀ := by
        have : c₀⁻¹ * b = b * c₀⁻¹ := by
          calc c₀⁻¹ * b = c₀⁻¹ * b * c₀ * c₀⁻¹ := by group
            _ = c₀⁻¹ * (b * c₀) * c₀⁻¹ := by group
            _ = c₀⁻¹ * (c₀ * b) * c₀⁻¹ := by rw [hc₀b]
            _ = b * c₀⁻¹ := by group
        rw [this]
      _ = b * (c₀⁻¹ * s * c₀) := by group
  have hX1 : (1 : G) ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
    (sec20X (CoreAssembly.conjClass K) z K K').one_mem
  have hs₁N : s₁ ∈ Subgroup.normalizer (K : Set G) :=
    (c9 h8).2.2 s₁ hc₀S (by rw [hs₁2]; exact hX1)
  have hs₁z : ∃ g : G, s₁ = g * z * g⁻¹ := by
    obtain ⟨g, hg⟩ := hsz
    exact ⟨c₀⁻¹ * g, by rw [← hs₁, hg]; group⟩
  obtain ⟨c₁, hc₁b, hc₁⟩ := d.r_fusion_S c7 c9 h8 h9 hb hk hu huo hact hs₁2 hs₁b hs₁N hs₁z
  refine ⟨c₀ * c₁, ?_, ?_⟩
  · calc c₀ * c₁ * b = c₀ * (c₁ * b) := by group
      _ = c₀ * (b * c₁) := by rw [hc₁b]
      _ = (c₀ * b) * c₁ := by group
      _ = (b * c₀) * c₁ := by rw [hc₀b]
      _ = b * (c₀ * c₁) := by group
  · calc s = c₀ * s₁ * c₀⁻¹ := hs
      _ = c₀ * (c₁ * z * c₁⁻¹) * c₀⁻¹ := by rw [hc₁]
      _ = c₀ * c₁ * z * (c₀ * c₁)⁻¹ := by group


theorem Std20.r_noConj_plus [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    (h9 : p ^ f ≠ 9) {b : G} (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) (g : G) :
    g⁻¹ * b * g ∉ sec20X (CoreAssembly.conjClass K) z K K' := by
  intro ha'
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  have hCz : g⁻¹ * b * g ∈ Subgroup.centralizer ({z} : Set G) := d.r10a_X_le_C ha'
  have hcomm : z * (g⁻¹ * b * g) = (g⁻¹ * b * g) * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp hCz).symm
  have hbs : (g * z * g⁻¹) * b = b * (g * z * g⁻¹) := by
    calc (g * z * g⁻¹) * b = g * (z * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * z) * g⁻¹ := by rw [hcomm]
      _ = b * (g * z * g⁻¹) := by group
  have hs2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [d.viol.hzK.sq]; group
  obtain ⟨c, hca, hcz⟩ := d.r_fus_plus c7 c9 h8 h9 hb hk hu huo hact hs2 hbs ⟨g, rfl⟩
  have hd₀ : g⁻¹ * c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ = z := by
      calc (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * z * c⁻¹) * g := by group
        _ = z := by rw [← hcz]; group
    calc (g⁻¹ * c) * z = ((g⁻¹ * c) * z * (g⁻¹ * c)⁻¹) * (g⁻¹ * c) := by group
      _ = z * (g⁻¹ * c) := by rw [this]
  have hinv : (g⁻¹ * c)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hd₀
  have hnorm' := le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins hinv
  have h5 : (g⁻¹ * c)⁻¹ * (g⁻¹ * b * g) * ((g⁻¹ * c)⁻¹)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hnorm' _).mp ha'
  have h6 : (g⁻¹ * c)⁻¹ * (g⁻¹ * b * g) * ((g⁻¹ * c)⁻¹)⁻¹ = b := by
    calc (g⁻¹ * c)⁻¹ * (g⁻¹ * b * g) * ((g⁻¹ * c)⁻¹)⁻¹ = c⁻¹ * b * c := by group
      _ = b := by rw [mul_assoc, ← hca, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h6] at h5
  exact hb.not_mem_X h5

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
