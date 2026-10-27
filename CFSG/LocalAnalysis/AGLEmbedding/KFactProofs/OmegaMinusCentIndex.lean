module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentBasic
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem sq_mem_elementaryGroup (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V)
    {P P' : HypPair Q} (hP : P.Orth P') {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : g ^ 2 ∈ elementaryGroup Q := by
  have hv₀Q : Q (P.e + P.f) = 1 := by
    rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef]
    simp
  have hv₀ : P.e + P.f ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at hv₀Q
    exact zero_ne_one hv₀Q
  set t₀ := reflect Q (P.e + P.f) with ht₀
  have ht₀O : t₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := reflect_mem_orthogonalGroup Q _
  have ht₀inv : t₀⁻¹ = t₀ := reflect_inv Q _
  have hconj : ∀ e ∈ elementaryGroup Q, t₀ * e * t₀ ∈ elementaryGroup Q := fun e he => by
    have := conj_mem_elementaryGroup ht₀O he
    rwa [ht₀inv] at this
  have hrefl : ∀ v : V, reflect Q v ∈ elementaryGroup Q ∨ reflect Q v * t₀ ∈ elementaryGroup Q := by
    intro v
    rcases zmod_two_cases (Q v) with h | h
    · left
      rw [reflect_of_map_eq_zero h]
      exact one_mem _
    · right
      have hv0 : v ≠ 0 := fun h0 => by
        rw [h0, QuadraticMap.map_zero] at h
        exact zero_ne_one h
      obtain ⟨e, he, hev⟩ := exists_mem_elementaryGroup_apply_eq hQ hP hv₀ hv0 (by rw [hv₀Q, h])
      have heO := elementaryGroup_le_orthogonalGroup Q he
      have hrv : reflect Q v = e * t₀ * e⁻¹ := by
        rw [ht₀, ← hev]
        exact (reflect_conj heO _).symm
      have h1 : t₀ * e⁻¹ * t₀ ∈ elementaryGroup Q := hconj _ (inv_mem he)
      have h2 : reflect Q v * t₀ = e * (t₀ * e⁻¹ * t₀) := by
        rw [hrv]
        simp only [mul_assoc]
      rw [h2]
      exact mul_mem he h1
  have hcls : TauCeti.QuadraticMap.orthogonalGroup Q = Subgroup.closure (Set.range (reflect Q)) :=
    orthogonalGroup_eq_closure_reflect hQ (by omega) (Or.inl h5)
  have h1 : t₀ * t₀ = 1 := by simpa [ht₀inv] using mul_inv_cancel t₀
  have hst : ∀ y : V ≃ₗ[ZMod 2] V, t₀ * (t₀ * y) = y := fun y => by
    rw [← mul_assoc, h1, one_mul]
  have key : ∀ g, g ∈ Subgroup.closure (Set.range (reflect Q)) →
      g ∈ elementaryGroup Q ∨ g * t₀ ∈ elementaryGroup Q := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact hrefl v
    | one => exact Or.inl (one_mem _)
    | mul a b ha hb iha ihb =>
      rcases iha with ha' | ha' <;> rcases ihb with hb' | hb'
      · exact Or.inl (mul_mem ha' hb')
      · right
        rw [mul_assoc]
        exact mul_mem ha' hb'
      · right
        have : a * b * t₀ = (a * t₀) * (t₀ * b * t₀) := by
          simp only [mul_assoc, hst]
        rw [this]
        exact mul_mem ha' (hconj b hb')
      · left
        have : a * b = (a * t₀) * (t₀ * (b * t₀) * t₀) := by
          simp only [mul_assoc, hst, h1, mul_one]
        rw [this]
        exact mul_mem ha' (hconj _ hb')
    | inv a ha iha =>
      rcases iha with ha' | ha'
      · exact Or.inl (inv_mem ha')
      · right
        have h2 : t₀ * a⁻¹ ∈ elementaryGroup Q := by
          have := inv_mem ha'
          rwa [mul_inv_rev, ht₀inv] at this
        have : a⁻¹ * t₀ = t₀ * (t₀ * a⁻¹) * t₀ := by
          simp only [hst]
        rw [this]
        exact hconj _ h2
  rw [hcls] at hg
  rcases key g hg with h | h
  · rw [pow_two]
    exact mul_mem h h
  · have h2 : t₀ * g ∈ elementaryGroup Q := by
      have := hconj _ h
      rwa [show t₀ * (g * t₀) * t₀ = t₀ * g from by
        simp only [mul_assoc, h1, mul_one]] at this
    have : g ^ 2 = (g * t₀) * (t₀ * g) := by
      rw [pow_two]
      simp only [mul_assoc, hst]
    rw [this]
    exact mul_mem h h2

theorem mem_elementaryGroup_of_pow_three (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {P P' : HypPair Q} (hP : P.Orth P') {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h3 : g ^ 3 = 1) :
    g ∈ elementaryGroup Q := by
  have h2 := sq_mem_elementaryGroup hQ h5 hP hg
  have : g = (g ^ 2) ^ 2 := by
    rw [← pow_mul]
    calc g = g ^ 3 * g := by rw [h3, one_mul]
      _ = g ^ (2 * 2) := by rw [← pow_succ]
  rw [this]
  exact pow_mem h2 2

theorem le_elementaryGroup_of_perfect (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {P P' : HypPair Q} (hP : P.Orth P')
    {D : Subgroup (V ≃ₗ[ZMod 2] V)} (hD : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hDp : ⁅D, D⁆ = D) : D ≤ elementaryGroup Q := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set N := (elementaryGroup Q).subgroupOf O with hN
  have hNn : N.Normal := elementaryGroup_subgroupOf_normal Q
  have hsq : ∀ y : O, y * y ∈ N := fun y => by
    rw [hN, Subgroup.mem_subgroupOf]
    have := sq_mem_elementaryGroup hQ h5 hP y.2
    rwa [pow_two] at this
  have hq : ∀ z : O ⧸ N, z * z = 1 := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hsq y
  have hcomm : ∀ a b : O, ⁅a, b⁆ ∈ N := by
    intro a b
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have ha := hq (a : O ⧸ N)
    have hb := hq (b : O ⧸ N)
    have hab := hq ((a : O ⧸ N) * (b : O ⧸ N))
    have ha' : ((a : O ⧸ N))⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb' : ((b : O ⧸ N))⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rw [ha', hb']
    simpa [mul_assoc] using hab
  rw [← hDp]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have := hcomm ⟨a, hD ha⟩ ⟨b, hD hb⟩
  rw [hN, Subgroup.mem_subgroupOf] at this
  exact this

end CFSG.AGLEmbedding.OmegaMinusCent
