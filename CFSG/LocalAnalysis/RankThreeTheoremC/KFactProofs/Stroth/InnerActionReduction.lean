module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction

open CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type} [Group K]

theorem mem_center_of_conj_eq_one {x : K} (hx : MulAut.conj x = 1) : x ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro y
  have h := congrArg (fun α : MulAut K => α y) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc y * x = x * y * x⁻¹ * x := by rw [h]
    _ = x * y := by group

theorem exists_eq_conj_of_mem_inner [Finite K] {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center K = ⊥) (P : Sylow p K) {φ : MulAut K} (hφ : ∃ n : ℕ, φ ^ (p ^ n) = 1)
    (hc : ∀ g ∈ (P : Subgroup K), φ * MulAut.conj g = MulAut.conj g * φ) (hin : φ ∈ inner K) :
    ∃ g ∈ (P : Subgroup K), φ = MulAut.conj g := by
  obtain ⟨h, rfl⟩ := hin
  obtain ⟨n, hn⟩ := hφ
  refine ⟨h, ?_, rfl⟩
  have hhn : h ^ (p ^ n) = 1 := by
    have h1 : MulAut.conj (h ^ (p ^ n)) = 1 := by rw [map_pow]; exact hn
    have h2 := mem_center_of_conj_eq_one h1
    rw [hZ] at h2
    exact h2
  have hpz : IsPGroup p (Subgroup.zpowers h) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨n, Subtype.ext ?_⟩
    show (h ^ m) ^ (p ^ n) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hhn, one_zpow]
  have hcomm : ∀ g ∈ (P : Subgroup K), h * g = g * h := by
    intro g hg
    have h1 : MulAut.conj (h * g * (g * h)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hc g hg]
      group
    have h2 := mem_center_of_conj_eq_one h1
    rw [hZ, Subgroup.mem_bot] at h2
    calc h * g = h * g * (g * h)⁻¹ * (g * h) := by group
      _ = g * h := by rw [h2, one_mul]
  have hnorm : Subgroup.zpowers h ≤ Subgroup.normalizer ((P : Subgroup K) : Set K) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      rw [hcomm g hg, mul_inv_cancel_right]
      exact hg
    · intro hg
      have : g = h * g * h⁻¹ := by
        have := hcomm (h * g * h⁻¹) hg
        calc g = h⁻¹ * (h * g * h⁻¹) * h := by group
          _ = h⁻¹ * (h * (h * g * h⁻¹) * h⁻¹) * h := by
            rw [show h * (h * g * h⁻¹) * h⁻¹ = h * g * h⁻¹ by
              rw [this]; group]
          _ = h * g * h⁻¹ := by group
      rw [this]
      exact hg
  have hsup : IsPGroup p (((P : Subgroup K) ⊔ Subgroup.zpowers h : Subgroup K)) :=
    IsPGroup.to_sup_of_normal_left' P.isPGroup' hpz hnorm
  have heq := P.is_maximal' hsup le_sup_left
  have : h ∈ (P : Subgroup K) ⊔ Subgroup.zpowers h :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers h)
  rwa [heq] at this

theorem center_eq_bot_of_simple (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) :
    Subgroup.center K = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
