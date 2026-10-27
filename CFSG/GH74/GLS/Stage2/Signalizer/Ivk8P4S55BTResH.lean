module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupInner

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResA7

open Equiv Equiv.Perm Subgroup

theorem conj_eq_or_inv {G : Type*} [Group G] {σ d : G} {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) (hd : d * d = 1) (hdσ : d * σ * d⁻¹ ∈ zpowers σ) :
    d * σ * d⁻¹ = σ ∨ d * σ * d⁻¹ = σ⁻¹ := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hdσ
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hconj : ∀ n : ℤ, d * σ ^ n * d⁻¹ = (d * σ * d⁻¹) ^ n := fun n => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  have h1 : σ ^ (m * m) = σ := by
    have : σ = d * (d * σ * d⁻¹) * d⁻¹ := by
      rw [hdi, show d * (d * σ * d) * d = (d * d) * σ * (d * d) by group, hd]
      group
    calc σ ^ (m * m) = (σ ^ m) ^ m := by rw [zpow_mul]
      _ = (d * σ * d⁻¹) ^ m := by rw [hm]
      _ = d * σ ^ m * d⁻¹ := (hconj m).symm
      _ = d * (d * σ * d⁻¹) * d⁻¹ := by rw [hm]
      _ = σ := this.symm
  have h2 : σ ^ ((m - 1) * (m + 1)) = 1 := by
    rw [show (m - 1) * (m + 1) = m * m - 1 by ring, zpow_sub, h1, zpow_one, mul_inv_cancel]
  have h3 : (p : ℤ) ∣ (m - 1) * (m + 1) := by
    rw [← hσ]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h2
  rcases (Int.Prime.dvd_mul' hp h3) with h4 | h4
  · left
    rw [← hm]
    have : σ ^ (m - 1) = 1 := by
      rw [← hσ] at h4
      exact orderOf_dvd_iff_zpow_eq_one.mp h4
    rw [show m = (m - 1) + 1 by ring, zpow_add, this, one_mul, zpow_one]
  · right
    rw [← hm]
    have : σ ^ (m + 1) = 1 := by
      rw [← hσ] at h4
      exact orderOf_dvd_iff_zpow_eq_one.mp h4
    rw [show m = (m + 1) - 1 by ring, zpow_sub, this, one_mul, zpow_one]

theorem exists_commute_of_four {G : Type*} [Group G] {σ : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hσ : orderOf σ = p) {D : Subgroup G} (hD2 : ∀ d ∈ D, d * d = 1) (hD4 : Nat.card D = 4)
    (hDσ : ∀ d ∈ D, d * σ * d⁻¹ ∈ zpowers σ) : ∃ d ∈ D, d ≠ 1 ∧ d * σ = σ * d := by
  have hcomm : ∀ d : G, d * σ * d⁻¹ = σ → d * σ = σ * d := fun d h => by
    calc d * σ = d * σ * d⁻¹ * d := by group
      _ = σ * d := by rw [h]
  by_contra hcon
  push Not at hcon
  have hinv : ∀ d ∈ D, d ≠ 1 → d * σ * d⁻¹ = σ⁻¹ := fun d hd hd1 =>
    (conj_eq_or_inv hp hσ (hD2 d hd) (hDσ d hd)).resolve_left
      (fun h => hcon d hd hd1 (hcomm d h))
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ :=
    CFSG.ComponentClassification.AutL2Facts.exists_two_ne_of_card_four D hD4
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hxy
    calc x = x * (x * y) := by rw [h, mul_one]
      _ = y := by rw [← mul_assoc, hD2 x hx, one_mul]
  have h1 := hinv _ (D.mul_mem hx hy) hxy1
  have h2 : x * y * σ * (x * y)⁻¹ = x * (y * σ * y⁻¹) * x⁻¹ := by group
  rw [h2, hinv y hy hy1, show x * σ⁻¹ * x⁻¹ = (x * σ * x⁻¹)⁻¹ by group, hinv x hx hx1,
    inv_inv] at h1
  have h3 : σ ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [h1]
    exact inv_mul_cancel σ
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hσ] at h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)

theorem isCycle_of_orderOf {p : ℕ} (hp : p = 5 ∨ p = 7) {σ : Perm (Fin 7)}
    (hσ : orderOf σ = p) : σ.IsCycle ∧ σ.support.card = p := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hall : ∀ m ∈ σ.cycleType, m = p := by
    intro m hm
    have h1 := dvd_of_mem_cycleType hm
    rw [hσ] at h1
    have h2 := two_le_of_mem_cycleType hm
    rcases (Nat.dvd_prime hpp).mp h1 with h | h
    · omega
    · exact h
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) p :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum := sum_cycleType_le σ
  rw [hrep, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hne : σ.cycleType ≠ 0 := by
    rw [Ne, cycleType_eq_zero]
    rintro rfl
    rw [orderOf_one] at hσ
    rcases hp with rfl | rfl <;> omega
  have hc1 : Multiset.card σ.cycleType ≠ 0 := fun h => hne (Multiset.card_eq_zero.mp h)
  have hc : Multiset.card σ.cycleType = 1 := by rcases hp with rfl | rfl <;> omega
  refine ⟨card_cycleType_eq_one.mp hc, ?_⟩
  rw [← sum_cycleType, hrep, hc, Multiset.sum_replicate, one_smul]

theorem fixes_support_of_commute {n : ℕ} {σ d : Perm (Fin n)} (hσ : σ.IsCycle)
    (hodd : Odd (orderOf σ)) (hd : d * d = 1) (hc : Commute d σ) :
    ∀ x ∈ σ.support, d x = x := by
  obtain ⟨hc', hmem⟩ := hσ.commute_iff.mp hc
  set d₁ := ofSubtype (subtypePerm d hc') with hd₁
  have hd₁2 : d₁ * d₁ = 1 := by
    rw [hd₁, ← map_mul]
    have : subtypePerm d hc' * subtypePerm d hc' = 1 := by
      ext x
      simp only [Perm.mul_apply, subtypePerm_apply, Perm.one_apply]
      rw [← Perm.mul_apply, hd, Perm.one_apply]
    rw [this, map_one]
  have hd₁1 : d₁ = 1 := by
    have h1 : orderOf d₁ ∣ orderOf σ := orderOf_dvd_of_mem_zpowers hmem
    have h2 : orderOf d₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hd₁2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h1
      exact absurd (Odd.of_dvd_nat hodd h1) (by decide)
  intro x hx
  have h1 : d₁ x = d x := by
    rw [hd₁, ofSubtype_apply_of_mem _ hx, subtypePerm_apply]
  rw [← h1, hd₁1, Perm.one_apply]

theorem eq_one_of_commute_seven {σ d : Perm (Fin 7)} (hσ : orderOf σ = 7) (hd : d * d = 1)
    (hc : Commute d σ) : d = 1 := by
  obtain ⟨hcyc, hcard⟩ := isCycle_of_orderOf (Or.inr rfl) hσ
  have hsupp : σ.support = Finset.univ := Finset.eq_univ_of_card _ (by rw [hcard]; rfl)
  have hfix := fixes_support_of_commute hcyc (by rw [hσ]; decide) hd hc
  ext x
  rw [hfix x (by rw [hsupp]; exact Finset.mem_univ x), Perm.one_apply]

theorem isSwap_of_commute_five {σ d : Perm (Fin 7)} (hσ : orderOf σ = 5) (hd : d * d = 1)
    (hd1 : d ≠ 1) (hc : Commute d σ) : d.IsSwap := by
  obtain ⟨hcyc, hcard⟩ := isCycle_of_orderOf (Or.inl rfl) hσ
  have hfix := fixes_support_of_commute hcyc (by rw [hσ]; decide) hd hc
  have hsub : d.support ⊆ σ.supportᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro hxs
    exact (mem_support.mp hx) (hfix x hxs)
  have hle : d.support.card ≤ 2 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, hcard, Fintype.card_fin] at this
    exact this
  have hge : 2 ≤ d.support.card := two_le_card_support_of_ne_one hd1
  exact card_support_eq_two.mp (le_antisymm hle hge)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResA7
