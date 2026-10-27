module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.Coordinator

variable {G : Type*} [Group G]

theorem eq_one_of_conj_eq_mul_of_odd {a b g : G} (hab : a * b = b * a) (ha : a * a = 1) {k : ℕ}
    (hb : b ^ (2 * k + 1) = 1) (h : g * b * g⁻¹ = a * b) : a = 1 := by
  have h1 : (g * b * g⁻¹) ^ (2 * k + 1) = 1 := by
    rw [conj_pow, hb, mul_one, mul_inv_cancel]
  rw [h, (Commute.mul_pow hab (2 * k + 1)), hb, mul_one] at h1
  have ha2 : a ^ 2 = 1 := by rw [sq, ha]
  rwa [pow_succ, pow_mul, ha2, one_pow, one_mul] at h1

theorem gLAPPrimeCoreOf_eq_bot_of_fixed_graph [Finite G] {E : Set G} {p : ℕ}
    (hE2 : ∀ e ∈ E, e * e = 1) (hE1 : ∀ e ∈ E, e ≠ 1)
    (hE3 : ∀ e ∈ E, ∀ f ∈ E, e * f ≠ f * e → e * f * (e * f) * (e * f) = 1)
    (hEc : ∀ e ∈ E, ∀ g : G, g * e * g⁻¹ ∈ E) (s : G)
    (hT0 : ∃ e ∈ E, e * s = s * e)
    (hT1 : ∀ x ∈ E, x * s = s * x → ∃ y ∈ E, y * s = s * y ∧ y ≠ x ∧ x * y = y * x)
    (hT2 : ∀ x ∈ E, x * s = s * x → ∀ y ∈ E, y * s = s * y → x * y ≠ y * x →
      ∃ z ∈ E, z * s = s * z ∧ z * x = x * z ∧ z * y = y * z)
    (hloc : ∀ x ∈ E, x * s = s * x →
      ∀ n ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)), n * x = x * n →
        n = 1 ∨ n = x) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  set N := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) with hN
  have hnotN : ∀ x ∈ E, x * s = s * x → x ∉ N := by
    intro x hx hxs hxN
    obtain ⟨y, hy, hys, hyx, hxy⟩ := hT1 x hx hxs
    rcases hloc y hy hys x hxN hxy with h | h
    · exact hE1 x hx h
    · exact hyx h.symm
  obtain ⟨e, he, hes⟩ := hT0
  have heC : e ∈ Subgroup.centralizer ({s} : Set G) :=
    (Subgroup.mem_centralizer_singleton_iff (g := s)).2 hes
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hE2 e he)
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnC : n ∈ Subgroup.centralizer ({s} : Set G) := GLAPPrimeCoreOf_le _ hn
  have hyE : n * e * n⁻¹ ∈ E := hEc e he n
  have hys : n * e * n⁻¹ * s = s * (n * e * n⁻¹) :=
    (Subgroup.mem_centralizer_singleton_iff (g := s)).1
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnC heC) (Subgroup.inv_mem _ hnC))
  have hm : e * (n * e * n⁻¹) ∈ N := by
    have h1 := N.mul_mem (GLAPPrimeCoreOf_conj_mem e heC n hn) (N.inv_mem hn)
    rwa [hei, show e * n * e * n⁻¹ = e * (n * e * n⁻¹) by group] at h1
  by_cases hc : e * (n * e * n⁻¹) = (n * e * n⁻¹) * e
  · have hme : e * (n * e * n⁻¹) * e = e * (e * (n * e * n⁻¹)) := by
      rw [mul_assoc, ← hc]
    rcases hloc e he hes _ hm hme with h | h
    · have hye : n * e * n⁻¹ = e := by
        have := eq_inv_of_mul_eq_one_right h
        rwa [hei] at this
      have hne : n * e = e * n := by
        calc n * e = n * e * n⁻¹ * n := by group
          _ = e * n := by rw [hye]
      rcases hloc e he hes n hn hne with h' | h'
      · exact h'
      · exact absurd (h' ▸ hn) (hnotN e he hes)
    · exfalso
      apply hE1 _ hyE
      calc n * e * n⁻¹ = e⁻¹ * (e * (n * e * n⁻¹)) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
  · exfalso
    have h3 := hE3 e he _ hyE hc
    obtain ⟨z, hz, hzs, hze, hzy⟩ := hT2 e he hes _ hyE hys hc
    have hmz : e * (n * e * n⁻¹) * z = z * (e * (n * e * n⁻¹)) := by
      rw [mul_assoc, ← hzy, ← mul_assoc, ← hze, mul_assoc]
    have hm1 : e * (n * e * n⁻¹) ≠ 1 := by
      intro h1
      apply hc
      have hye : n * e * n⁻¹ = e := by
        have := eq_inv_of_mul_eq_one_right h1
        rwa [hei] at this
      rw [hye]
    rcases hloc z hz hzs _ hm hmz with h | h
    · exact hm1 h
    · have hz2 := hE2 z hz
      rw [← h] at hz2
      rw [hz2, one_mul] at h3
      exact hm1 h3

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
