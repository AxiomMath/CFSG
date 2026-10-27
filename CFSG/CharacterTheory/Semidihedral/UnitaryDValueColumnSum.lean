module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueColumnLinear
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.UnitaryDValue.Columns

open CFSG.TwoRankLowerBound.Helpers

theorem column_sums {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (B : Finset basis.index) (Q P : Subgroup G)
    (μ : Q →* ℂˣ) (h : ℕ) (hQ : Nat.card Q = 3 ^ (h + 2))
    (hμ1 : ∀ u : Q, ((μ u : ℂˣ) : ℂ) = 1 ↔ (u : G) ∈ P)
    (hμsum : ∑ u : Q, (1 - ((μ u : ℂˣ) : ℂ)) = Nat.card Q)
    (hweight : ∀ u : Q, (u : G) ∉ P →
      ∑ u' : Q, (if IsConj (u : G) (u' : G) then 1 - ((μ u'⁻¹ : ℂˣ) : ℂ) else 0) = 27)
    (hnorm : ∀ u u' : Q, (u : G) ∉ P → (u' : G) ∉ P →
      ∑ c ∈ B, (basis.representation c).character u *
          (basis.representation c).character (u' : G)⁻¹ =
        if IsConj (u : G) (u' : G) then (3 : ℂ) ^ h else 0)
    (hone : ∀ u : Q, (u : G) ∉ P →
      ∑ c ∈ B, (basis.representation c).character 1 * (basis.representation c).character u =
        0) :
    ∑ c ∈ B, column Q μ (basis.representation c).character ^ 2 = 3 ∧
      ∑ c ∈ B, (basis.representation c).character 1 *
        column Q μ (basis.representation c).character = 0 := by
  set χ : basis.index → G → ℂ := fun c => (basis.representation c).character with hχ
  set w : Q → ℂ := fun u => 1 - ((μ u : ℂˣ) : ℂ) with hw
  have hwP : ∀ u : Q, (u : G) ∈ P → w u = 0 := fun u hu => by
    simp only [hw, (hμ1 u).mpr hu, sub_self]
  have hwinvP : ∀ u : Q, (u : G) ∈ P → w u⁻¹ = 0 := fun u hu =>
    hwP _ (by simpa using P.inv_mem hu)
  have hcol : ∀ c, column Q μ (χ c) = (Nat.card Q : ℂ)⁻¹ * ∑ u : Q, χ c u * w u := fun c => rfl
  have hcolinv : ∀ c, column Q μ (χ c) =
      (Nat.card Q : ℂ)⁻¹ * ∑ u : Q, χ c (u : G)⁻¹ * w u⁻¹ := by
    intro c
    rw [hcol]
    congr 1
    exact (Equiv.sum_comp (Equiv.inv Q) (fun u => χ c u * w u)).symm
  constructor
  · have hsq : ∀ c, column Q μ (χ c) ^ 2 = (Nat.card Q : ℂ)⁻¹ ^ 2 *
        ∑ u : Q, ∑ u' : Q, w u * w u'⁻¹ * (χ c u * χ c (u' : G)⁻¹) := by
      intro c
      rw [pow_two]
      nth_rw 1 [hcol c]
      rw [hcolinv c, mul_mul_mul_comm, ← pow_two, Finset.sum_mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => by ring
    have hexpand : ∑ c ∈ B, column Q μ (χ c) ^ 2 = (Nat.card Q : ℂ)⁻¹ ^ 2 *
        ∑ u : Q, ∑ u' : Q, w u * w u'⁻¹ * ∑ c ∈ B, χ c u * χ c (u' : G)⁻¹ := by
      simp_rw [hsq, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
    have hterm : ∀ u u' : Q, w u * w u'⁻¹ * ∑ c ∈ B, χ c u * χ c (u' : G)⁻¹ =
        (3 : ℂ) ^ h * (w u * (if IsConj (u : G) (u' : G) then w u'⁻¹ else 0)) := by
      intro u u'
      by_cases hu : (u : G) ∈ P
      · rw [hwP u hu]
        ring
      by_cases hu' : (u' : G) ∈ P
      · rw [hwinvP u' hu']
        simp
      rw [hnorm u u' hu hu']
      split_ifs <;> ring
    have hinner : ∀ u : Q, ∑ u' : Q, w u * w u'⁻¹ * ∑ c ∈ B, χ c u * χ c (u' : G)⁻¹ =
        27 * 3 ^ h * w u := by
      intro u
      simp_rw [hterm]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      by_cases hu : (u : G) ∈ P
      · rw [hwP u hu]
        ring
      · rw [hweight u hu]
        ring
    rw [hexpand, Finset.sum_congr rfl fun u _ => hinner u, ← Finset.mul_sum, hμsum, hQ]
    have h3 : (3 : ℂ) ^ h ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp
    ring
  · have hexpand : ∑ c ∈ B, χ c 1 * column Q μ (χ c) =
        (Nat.card Q : ℂ)⁻¹ * ∑ u : Q, w u * ∑ c ∈ B, χ c 1 * χ c u := by
      simp_rw [hcol, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun c _ => by ring
    have hzero : ∀ u : Q, w u * ∑ c ∈ B, χ c 1 * χ c u = 0 := by
      intro u
      by_cases hu : (u : G) ∈ P
      · rw [hwP u hu, zero_mul]
      · rw [hone u hu, mul_zero]
    rw [hexpand, Finset.sum_eq_zero fun u _ => hzero u, mul_zero]

theorem column_eq_of_const {G : Type*} [Group G] [Fintype G] (Q P : Subgroup G) (μ : Q →* ℂˣ)
    (hμ1 : ∀ u : Q, ((μ u : ℂˣ) : ℂ) = 1 ↔ (u : G) ∈ P)
    (hμsum : ∑ u : Q, (1 - ((μ u : ℂˣ) : ℂ)) = Nat.card Q) (χ : G → ℂ) (a : ℂ)
    (hχ : ∀ u : Q, (u : G) ∉ P → χ u = a) : column Q μ χ = a := by
  have hterm : ∀ u : Q, χ u * (1 - ((μ u : ℂˣ) : ℂ)) = a * (1 - ((μ u : ℂˣ) : ℂ)) := by
    intro u
    by_cases hu : (u : G) ∈ P
    · rw [(hμ1 u).mpr hu, sub_self, mul_zero, mul_zero]
    · rw [hχ u hu]
  have hQ0 : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [column, Finset.sum_congr rfl fun u _ => hterm u, ← Finset.mul_sum, hμsum]
  field_simp

theorem exists_third_entry {ι : Type*} (B : Finset ι) (n d : ι → ℤ) {a b : ι} (ha : a ∈ B)
    (hb : b ∈ B) (hab : a ≠ b) (hna : n a = 1) (hnb : n b = -1) (hda : d a = 1)
    (hd : ∀ c, 0 ≤ d c) (hdb : 1 < d b) (hsq : ∑ c ∈ B, n c ^ 2 = 3)
    (hdeg : ∑ c ∈ B, d c * n c = 0) : ∃ c ∈ B, d c = d b - 1 := by
  set B' := (B.erase a).erase b with hB'
  have hb' : b ∈ B.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hsplit : ∀ f : ι → ℤ, ∑ c ∈ B, f c = f a + f b + ∑ c ∈ B', f c := by
    intro f
    rw [← Finset.add_sum_erase B f ha, ← Finset.add_sum_erase (B.erase a) f hb', add_assoc]
  have hsq' : ∑ c ∈ B', n c ^ 2 = 1 := by
    have := hsplit (fun c => n c ^ 2)
    simp only [hna, hnb] at this
    linarith
  have hdeg' : ∑ c ∈ B', d c * n c = d b - 1 := by
    have := hsplit (fun c => d c * n c)
    simp only [hna, hnb, hda] at this
    linarith
  obtain ⟨c, hc, hnc⟩ : ∃ c ∈ B', n c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero (fun c hc => by rw [hcon c hc]; ring)] at hsq'
    norm_num at hsq'
  have hsplit' := Finset.add_sum_erase B' (fun x => n x ^ 2) hc
  have hnonneg : 0 ≤ ∑ x ∈ B'.erase c, n x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hpos : 0 < n c ^ 2 := by positivity
  have hnc2 : n c ^ 2 = 1 := by linarith
  have hzero : ∀ x ∈ B'.erase c, n x = 0 := by
    have h0 : ∑ x ∈ B'.erase c, n x ^ 2 = 0 := by linarith
    intro x hx
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (n y))).mp h0 x hx
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hdc : d c * n c = d b - 1 := by
    rw [← Finset.add_sum_erase B' _ hc,
      Finset.sum_eq_zero (fun x hx => by rw [hzero x hx, mul_zero]), add_zero] at hdeg'
    exact hdeg'
  have hpm : n c = 1 ∨ n c = -1 := by
    have : (n c - 1) * (n c + 1) = 0 := by linear_combination hnc2
    rcases mul_eq_zero.mp this with h | h
    · left
      linarith
    · right
      linarith
  refine ⟨c, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc), ?_⟩
  rcases hpm with h | h
  · rw [h, mul_one] at hdc
    exact hdc
  · rw [h] at hdc
    have := hd c
    linarith

end CFSG.Semidihedral.UnitaryDValue.Columns
