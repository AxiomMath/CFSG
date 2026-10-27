module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Core
public import Certificates.Data.ExceptionalSL3

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem l16a_zpowers_eq_one_or_self {z : G} (hz : z * z = 1) {x : G} (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℕ) = 1 := by rwa [pow_two]
  rw [zpow_eq_zpow_emod' k h2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    show z ^ (k % (2 : ℤ)) = 1
    rw [hk]
    simp
  · right
    show z ^ (k % (2 : ℤ)) = z
    rw [hk]
    simp

private def l16aI : SL23 := ⟨!![0, 1; -1, 0], by decide⟩

private def l16aJ : SL23 := ⟨!![1, 1; 1, -1], by decide⟩

private theorem l16a_ij_pow : l16aI ^ 4 = 1 ∧ l16aJ ^ 4 = 1 := by
  decide +kernel

private theorem l16a_words : ∀ x : SL23, x ^ 4 = 1 →
    ∃ m : Fin 4, ∃ n : Fin 2, x = l16aI ^ (m : ℕ) * l16aJ ^ (n : ℕ) := by
  decide +kernel

private theorem l16a_signs : ∀ s₁ s₂ : SL23, s₁ * s₁ = 1 → s₂ * s₂ = 1 →
    ∃ w : SL23, w ^ 4 = 1 ∧ w * l16aI * w⁻¹ = s₁ * l16aI ∧ w * l16aJ * w⁻¹ = s₂ * l16aJ := by
  decide +kernel

private theorem l16a_conj_word (a b x : G) (m n : ℕ) :
    x * (a ^ m * b ^ n) * x⁻¹ = (x * a * x⁻¹) ^ m * (x * b * x⁻¹) ^ n := by
  rw [conj_pow, conj_pow]
  group

theorem l16a_q8_inner {K : Subgroup G} (e : ↥K ≃* SL23) {z : G} (hz : z ∈ K)
    (hz2 : z * z = 1) {g : G}
    (hg : ∀ u ∈ K, u ^ 4 = 1 → g * u * g⁻¹ * u⁻¹ ∈ zpowers z) :
    ∃ w ∈ K, w ^ 4 = 1 ∧ ∀ u ∈ K, u ^ 4 = 1 → g * u * g⁻¹ = w * u * w⁻¹ := by
  obtain ⟨a, ha⟩ : ∃ a : ↥K, e a = l16aI := ⟨e.symm l16aI, e.apply_symm_apply _⟩
  obtain ⟨b, hb⟩ : ∃ b : ↥K, e b = l16aJ := ⟨e.symm l16aJ, e.apply_symm_apply _⟩
  have ha4 : (a : G) ^ 4 = 1 := by
    have h : a ^ 4 = 1 := e.injective (by rw [map_pow, ha, map_one]; exact l16a_ij_pow.1)
    simpa using congrArg Subtype.val h
  have hb4 : (b : G) ^ 4 = 1 := by
    have h : b ^ 4 = 1 := e.injective (by rw [map_pow, hb, map_one]; exact l16a_ij_pow.2)
    simpa using congrArg Subtype.val h
  have hεK : ∀ ε : G, ε ∈ zpowers z → ε ∈ K := fun ε hε => (Subgroup.zpowers_le.mpr hz) hε
  have hεsq : ∀ (ε : G) (hε : ε ∈ zpowers z),
      e ⟨ε, hεK ε hε⟩ * e ⟨ε, hεK ε hε⟩ = 1 := by
    intro ε hε
    rw [← map_mul, ← map_one e]
    congr 1
    apply Subtype.ext
    rcases l16a_zpowers_eq_one_or_self hz2 hε with h | h <;> simp [h, hz2]
  have hε₁ := hg (a : G) a.2 ha4
  have hε₂ := hg (b : G) b.2 hb4
  obtain ⟨w, hw4, hwi, hwj⟩ := l16a_signs _ _ (hεsq _ hε₁) (hεsq _ hε₂)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥K, e w₀ = w := ⟨e.symm w, e.apply_symm_apply _⟩
  rw [← ha, ← hw₀] at hwi
  rw [← hb, ← hw₀] at hwj
  have hwa : (w₀ : G) * a * (w₀ : G)⁻¹ = g * a * g⁻¹ := by
    have h1 : w₀ * a * w₀⁻¹ = ⟨g * a * g⁻¹ * (a : G)⁻¹, hεK _ hε₁⟩ * a := by
      apply e.injective
      simpa only [map_mul, map_inv] using hwi
    simpa using congrArg Subtype.val h1
  have hwb : (w₀ : G) * b * (w₀ : G)⁻¹ = g * b * g⁻¹ := by
    have h1 : w₀ * b * w₀⁻¹ = ⟨g * b * g⁻¹ * (b : G)⁻¹, hεK _ hε₂⟩ * b := by
      apply e.injective
      simpa only [map_mul, map_inv] using hwj
    simpa using congrArg Subtype.val h1
  refine ⟨w₀, w₀.2, ?_, ?_⟩
  · have h : w₀ ^ 4 = 1 := e.injective (by rw [map_pow, hw₀, hw4, map_one])
    simpa using congrArg Subtype.val h
  · intro u hu h4
    have hx4 : (e ⟨u, hu⟩) ^ 4 = 1 := by
      rw [← map_pow, ← map_one e]
      congr 1
      apply Subtype.ext
      simpa using h4
    obtain ⟨m, n, hmn⟩ := l16a_words _ hx4
    have hu' : (⟨u, hu⟩ : ↥K) = a ^ (m : ℕ) * b ^ (n : ℕ) := by
      apply e.injective
      rw [map_mul, map_pow, map_pow, ha, hb]
      exact hmn
    have hu'' : u = (a : G) ^ (m : ℕ) * (b : G) ^ (n : ℕ) := by
      simpa using congrArg Subtype.val hu'
    rw [hu'', l16a_conj_word, l16a_conj_word, hwa, hwb]

theorem Sec5B517Q8.exists_inner {K : Fin 4 → Subgroup G} {z : G} (hq : Sec5B517Quad K z) {g : G}
    (hg : ∀ q ∈ Sec5B517Q8 hq, g * q * g⁻¹ * q⁻¹ ∈ zpowers z) :
    ∃ w ∈ Sec5B517Q8 hq, ∀ q ∈ Sec5B517Q8 hq, g * q * g⁻¹ = w * q * w⁻¹ := by
  have hfac : ∀ k : Fin 4, ∃ w ∈ K k, w ^ 4 = 1 ∧
      ∀ u ∈ K k, u ^ 4 = 1 → g * u * g⁻¹ = w * u * w⁻¹ := fun k =>
    l16a_q8_inner (Classical.choice (hq.iso k)) (hq.z_mem k) hq.z_sq
      (fun u hu h4 => hg u (Sec5B517Q8.mem_of_mem hq hu h4))
  choose w hwK hw4 hwg using hfac
  refine ⟨Sec5B517Prod w, ⟨w, fun i => ⟨hwK i, hw4 i⟩, rfl⟩, ?_⟩
  intro q hqQ
  obtain ⟨k, hk, rfl⟩ := hqQ
  have hkK : ∀ i, k i ∈ K i := fun i => (hk i).1
  rw [sec5b517_prod_inv hq hwK, sec5b517_prod_mul hq hwK hkK,
    sec5b517_prod_mul hq (fun i => (K i).mul_mem (hwK i) (hkK i))
      (fun i => (K i).inv_mem (hwK i))]
  have e0 := hwg 0 (k 0) (hk 0).1 (hk 0).2
  have e1 := hwg 1 (k 1) (hk 1).1 (hk 1).2
  have e2 := hwg 2 (k 2) (hk 2).1 (hk 2).2
  have e3 := hwg 3 (k 3) (hk 3).1 (hk 3).2
  calc g * Sec5B517Prod k * g⁻¹
      = (g * k 0 * g⁻¹) * (g * k 1 * g⁻¹) * (g * k 2 * g⁻¹) * (g * k 3 * g⁻¹) := by
        simp only [Sec5B517Prod]
        group
    _ = Sec5B517Prod fun i => w i * k i * (w i)⁻¹ := by
        rw [e0, e1, e2, e3]
        rfl

end CFSG.OddStandard.SmallF3.Omega
