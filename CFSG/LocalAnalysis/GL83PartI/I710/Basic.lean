module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace GL83.I710

open CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type*} [Group K] {p : ℕ}

theorem mem_sylow_of_commute [Fact p.Prime] (P : Sylow p K) {k : K} (hk : ∃ n : ℕ, k ^ (p ^ n) = 1)
    (hc : ∀ g ∈ (P : Subgroup K), k * g = g * k) : k ∈ (P : Subgroup K) := by
  obtain ⟨n, hn⟩ := hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hn)
  have hkp : IsPGroup p (Subgroup.zpowers k) := IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  have hnorm : (P : Subgroup K) ≤ Subgroup.normalizer (Subgroup.zpowers k : Set K) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgk : g * k * g⁻¹ = k := by rw [← hc g hg, mul_inv_cancel_right]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by simp only [← conj_zpow, hgk]⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have hcz : g * k ^ z = k ^ z * g := ((Commute.symm (hc g hg)).zpow_right z).eq
      beta_reduce at hz ⊢
      calc k ^ z = g⁻¹ * (g * k ^ z) := by group
        _ = g⁻¹ * (k ^ z * g) := by rw [hcz]
        _ = g⁻¹ * (g * x * g⁻¹ * g) := by rw [hz]
        _ = x := by group
  have hsup : IsPGroup p ↥((P : Subgroup K) ⊔ Subgroup.zpowers k) :=
    P.isPGroup'.to_sup_of_normal_right' hkp hnorm
  have heq := P.is_maximal' hsup le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k)

theorem exists_eq_conj_of_mem_inner [Fact p.Prime] (hZ : Subgroup.center K = ⊥) (P : Sylow p K)
    {φ : MulAut K} (hφ : ∃ n : ℕ, φ ^ (p ^ n) = 1)
    (hcomm : ∀ g ∈ (P : Subgroup K), φ * MulAut.conj g = MulAut.conj g * φ)
    (hinn : φ ∈ inner K) : ∃ g ∈ (P : Subgroup K), φ = MulAut.conj g := by
  obtain ⟨k, rfl⟩ := hinn
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hc : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g => by
      have h := congrArg (fun φ : MulAut K => φ g) hk
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      have h2 : k * g = g * k := by
        calc k * g = k * g * k⁻¹ * k := by group
          _ = g * k := by rw [h]
      exact h2.symm
    rw [hZ] at hc
    exact hc
  refine ⟨k, mem_sylow_of_commute P ?_ fun g hg => hinj ?_, rfl⟩
  · obtain ⟨n, hn⟩ := hφ
    exact ⟨n, hinj (by rw [map_pow, map_one]; exact hn)⟩
  · rw [map_mul, map_mul]
    exact hcomm g hg

end GL83.I710
