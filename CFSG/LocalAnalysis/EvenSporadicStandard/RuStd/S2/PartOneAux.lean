module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type*} [Group G]

theorem card_sup_of_commute {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G))
    (hd : Disjoint A B) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod, Nat.card_congr (mulEquivProdSup hAB hd).toEquiv]

theorem sq_one_sup {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G))
    (hA : ∀ a ∈ A, a * a = 1) (hB : ∀ b ∈ B, b * b = 1) : ∀ x ∈ A ⊔ B, x * x = 1 := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hAB hx
  have hab : a * b = b * a := mem_centralizer_iff.1 (hAB hb) a ha
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [hA a ha, hB b hb, one_mul]

theorem sq_one_zpowers {x : G} (hx : x * x = 1) : ∀ y ∈ zpowers x, y * y = 1 := by
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  rw [← zpow_add, ← two_mul]
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  rw [zpow_mul]
  simp [show x ^ (2 : ℤ) = 1 from by rw [zpow_two]; exact hx]

theorem involution_mem_of_sup {f : G} {D : Subgroup G} (hfD : D ≤ centralizer ({f} : Set G))
    (hd : Disjoint (zpowers f) D) (hodd : Odd (orderOf f)) {x : G} (hx : x ∈ zpowers f ⊔ D)
    (hx2 : x * x = 1) : x ∈ D := by
  have hle : D ≤ centralizer (zpowers f : Set G) := fun d hd' =>
    mem_centralizer_iff.2 fun y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 (hfD hd') : Commute d f) k).eq.symm
  obtain ⟨a, ha, d, hdD, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  have hcomm : f ^ k * d = d * f ^ k :=
    mem_centralizer_iff.1 (hle hdD) _ (mem_zpowers_iff.2 ⟨k, rfl⟩)
  have h1 : (f ^ k) * (f ^ k) * (d * d) = 1 := by
    calc (f ^ k) * (f ^ k) * (d * d) = f ^ k * (f ^ k * d) * d := by group
      _ = f ^ k * (d * f ^ k) * d := by rw [hcomm]
      _ = f ^ k * d * (f ^ k * d) := by group
      _ = 1 := hx2
  have h2 : f ^ (2 * k) = (d * d)⁻¹ := by
    rw [two_mul, zpow_add]
    exact eq_inv_of_mul_eq_one_left h1
  have hmem : f ^ (2 * k) ∈ zpowers f ⊓ D := ⟨mem_zpowers_iff.2 ⟨_, rfl⟩, by
    rw [h2]; exact D.inv_mem (D.mul_mem hdD hdD)⟩
  rw [hd.eq_bot, mem_bot] at hmem
  have h3 : ((orderOf f : ℕ) : ℤ) ∣ 2 * k := orderOf_dvd_iff_zpow_eq_one.2 hmem
  have h4 : ((orderOf f : ℕ) : ℤ) ∣ k := by
    obtain ⟨m, hm⟩ := hodd
    have hcop : IsCoprime ((orderOf f : ℕ) : ℤ) 2 := by
      rw [hm]; push_cast; exact ⟨1, -m, by ring⟩
    exact hcop.dvd_of_dvd_mul_left h3
  have h5 : f ^ k = 1 := orderOf_dvd_iff_zpow_eq_one.1 h4
  rw [h5, one_mul]
  exact hdD

theorem mem_normalizer_sup_zpowers {U : Subgroup G} {t g : G}
    (htU : zpowers t ≤ centralizer (U : Set G))
    (hgU : g ∈ normalizer (U : Set G)) (hgt : g * t = t * g) :
    g ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (U : Set G) → g * t = t * g →
      ∀ x ∈ U ⊔ zpowers t, g * x * g⁻¹ ∈ U ⊔ zpowers t := by
    intro g hgU hgt x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (A := U) (B := zpowers t) htU hx
    have hgb : g * b * g⁻¹ = b := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      rw [(Commute.zpow_right (hgt : Commute g t) k).eq]; group
    have hga : g * a * g⁻¹ ∈ U := (mem_normalizer_iff.1 hgU a).1 ha
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e, hgb]
    exact mul_mem_sup hga hb
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hgU hgt x, fun hx => ?_⟩
  have hgU' : g⁻¹ ∈ normalizer (U : Set G) := (normalizer (U : Set G)).inv_mem hgU
  have hgt' : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hgt]
      _ = t * g⁻¹ := by group
  have := key g⁻¹ hgU' hgt' _ hx
  simpa [mul_assoc] using this

end CFSG.EvenSporadicStandard.RuStd.S2
