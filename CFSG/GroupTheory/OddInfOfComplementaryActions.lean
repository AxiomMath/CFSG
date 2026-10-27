module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G] {Q E₁ E₂ P₁ P₂ O : Subgroup G}

private theorem eq_one_of_mem_Q_inf_O (hQ : IsPGroup 2 Q)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    {x : G} (hxQ : x ∈ Q) (hxO : x ∈ O) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (orderOf x) := ((hO x).mp hxO).2
  obtain ⟨k, hk⟩ := hQ.exists_orderOf_eq_pow ⟨x, hxQ⟩
  have hk' : orderOf x = 2 ^ k := by simpa only [Subgroup.orderOf_mk] using hk
  rw [hk'] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_odd_iff_even.mpr
      (by rw [Nat.even_pow]; exact ⟨even_two, hne⟩)) hodd
  exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])

section Projection

variable {E F : Subgroup G}

private noncomputable def proj₁
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f) (q : G) : G := by
  classical
  exact if hq : q ∈ Q then Classical.choose (hEF q hq) else 1

private noncomputable def proj₂
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f) (q : G) : G := by
  classical
  exact if hq : q ∈ Q then
    Classical.choose ((Classical.choose_spec (hEF q hq)).2)
  else 1

private theorem proj₁_mem (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f)
    {q : G} (hq : q ∈ Q) : proj₁ hEF q ∈ E := by
  classical
  unfold proj₁
  rw [dif_pos hq]
  exact (Classical.choose_spec (hEF q hq)).1

private theorem proj₂_mem (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f)
    {q : G} (hq : q ∈ Q) : proj₂ hEF q ∈ F := by
  classical
  unfold proj₂
  rw [dif_pos hq]
  exact (Classical.choose_spec ((Classical.choose_spec (hEF q hq)).2)).1

private theorem proj₁_mul_proj₂ (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f)
    {q : G} (hq : q ∈ Q) : proj₁ hEF q * proj₂ hEF q = q := by
  classical
  unfold proj₁ proj₂
  rw [dif_pos hq, dif_pos hq]
  exact (Classical.choose_spec ((Classical.choose_spec (hEF q hq)).2)).2.symm

private theorem proj₁_eq_of_decomp (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f)
    (hbot : E ⊓ F = ⊥) {q e f : G} (hq : q ∈ Q) (he : e ∈ E) (hf : f ∈ F)
    (h : q = e * f) : e = proj₁ hEF q := by
  classical
  have h₁ : proj₁ hEF q ∈ E := proj₁_mem hEF hq
  have h₂ : proj₂ hEF q ∈ F := proj₂_mem hEF hq
  have hdec : proj₁ hEF q * proj₂ hEF q = q := proj₁_mul_proj₂ hEF hq
  have heq : e * f = proj₁ hEF q * proj₂ hEF q := by rw [← h, hdec]
  have hcalc : e⁻¹ * proj₁ hEF q = f * (proj₂ hEF q)⁻¹ := by
    calc e⁻¹ * proj₁ hEF q
        = e⁻¹ * (proj₁ hEF q * proj₂ hEF q) * (proj₂ hEF q)⁻¹ := by group
      _ = e⁻¹ * (e * f) * (proj₂ hEF q)⁻¹ := by rw [← heq]
      _ = f * (proj₂ hEF q)⁻¹ := by group
  have hmem : e⁻¹ * proj₁ hEF q ∈ E ⊓ F := by
    refine Subgroup.mem_inf.mpr ⟨E.mul_mem (E.inv_mem he) h₁, ?_⟩
    rw [hcalc]
    exact F.mul_mem hf (F.inv_mem h₂)
  have hmem' : e⁻¹ * proj₁ hEF q ∈ (⊥ : Subgroup G) := by simpa [hbot] using hmem
  have hone : e⁻¹ * proj₁ hEF q = 1 := by simpa using hmem'
  exact inv_mul_eq_one.mp hone

private theorem proj₂_eq_of_decomp (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f)
    (hbot : E ⊓ F = ⊥) {q e f : G} (hq : q ∈ Q) (he : e ∈ E) (hf : f ∈ F)
    (h : q = e * f) : f = proj₂ hEF q := by
  classical
  have h₁ : proj₁ hEF q ∈ E := proj₁_mem hEF hq
  have h₂ : proj₂ hEF q ∈ F := proj₂_mem hEF hq
  have hdec : proj₁ hEF q * proj₂ hEF q = q := proj₁_mul_proj₂ hEF hq
  have heq : e * f = proj₁ hEF q * proj₂ hEF q := by rw [← h, hdec]
  have hcalc : e⁻¹ * proj₁ hEF q = f * (proj₂ hEF q)⁻¹ := by
    calc e⁻¹ * proj₁ hEF q
        = e⁻¹ * (proj₁ hEF q * proj₂ hEF q) * (proj₂ hEF q)⁻¹ := by group
      _ = e⁻¹ * (e * f) * (proj₂ hEF q)⁻¹ := by rw [← heq]
      _ = f * (proj₂ hEF q)⁻¹ := by group
  have hmem : f * (proj₂ hEF q)⁻¹ ∈ E ⊓ F := by
    refine Subgroup.mem_inf.mpr ⟨?_, F.mul_mem hf (F.inv_mem h₂)⟩
    rw [← hcalc]
    exact E.mul_mem (E.inv_mem he) h₁
  have hmem' : f * (proj₂ hEF q)⁻¹ ∈ (⊥ : Subgroup G) := by simpa [hbot] using hmem
  have hone : f * (proj₂ hEF q)⁻¹ = 1 := by simpa using hmem'
  exact mul_inv_eq_one.mp hone

private theorem proj₂_one (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f)
    (hbot : E ⊓ F = ⊥) : proj₂ hEF (1 : G) = 1 := by
  classical
  have h := proj₂_eq_of_decomp hEF hbot (Q.one_mem) (E.one_mem) (F.one_mem)
    (by simp : (1 : G) = 1 * 1)
  exact h.symm

private theorem proj₁_mul (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f) (hbot : E ⊓ F = ⊥)
    (hEQ : E ≤ Q) (hFQ : F ≤ Q)
    {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) :
    proj₁ hEF (q * q') = proj₁ hEF q * proj₁ hEF q' := by
  classical
  have h₁ : proj₁ hEF q ∈ E := proj₁_mem hEF hq
  have h₁' : proj₁ hEF q' ∈ E := proj₁_mem hEF hq'
  have h₂ : proj₂ hEF q ∈ F := proj₂_mem hEF hq
  have h₂' : proj₂ hEF q' ∈ F := proj₂_mem hEF hq'
  have hcomm : proj₂ hEF q * proj₁ hEF q' = proj₁ hEF q' * proj₂ hEF q :=
    hQcomm _ (hFQ h₂) _ (hEQ h₁')
  have hdec : q * q' = (proj₁ hEF q * proj₁ hEF q') *
      (proj₂ hEF q * proj₂ hEF q') := by
    calc q * q' = (proj₁ hEF q * proj₂ hEF q) *
          (proj₁ hEF q' * proj₂ hEF q') := by
            rw [proj₁_mul_proj₂ hEF hq, proj₁_mul_proj₂ hEF hq']
      _ = proj₁ hEF q * (proj₂ hEF q * proj₁ hEF q') * proj₂ hEF q' := by group
      _ = proj₁ hEF q * (proj₁ hEF q' * proj₂ hEF q) * proj₂ hEF q' := by rw [hcomm]
      _ = (proj₁ hEF q * proj₁ hEF q') *
          (proj₂ hEF q * proj₂ hEF q') := by group
  exact (proj₁_eq_of_decomp hEF hbot (Q.mul_mem hq hq')
    (E.mul_mem h₁ h₁') (F.mul_mem h₂ h₂') hdec).symm

private theorem proj₂_mul (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f) (hbot : E ⊓ F = ⊥)
    (hEQ : E ≤ Q) (hFQ : F ≤ Q)
    {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) :
    proj₂ hEF (q * q') = proj₂ hEF q * proj₂ hEF q' := by
  classical
  have h₁ : proj₁ hEF q ∈ E := proj₁_mem hEF hq
  have h₁' : proj₁ hEF q' ∈ E := proj₁_mem hEF hq'
  have h₂ : proj₂ hEF q ∈ F := proj₂_mem hEF hq
  have h₂' : proj₂ hEF q' ∈ F := proj₂_mem hEF hq'
  have hcomm : proj₂ hEF q * proj₁ hEF q' = proj₁ hEF q' * proj₂ hEF q :=
    hQcomm _ (hFQ h₂) _ (hEQ h₁')
  have hdec : q * q' = (proj₁ hEF q * proj₁ hEF q') *
      (proj₂ hEF q * proj₂ hEF q') := by
    calc q * q' = (proj₁ hEF q * proj₂ hEF q) *
          (proj₁ hEF q' * proj₂ hEF q') := by
            rw [proj₁_mul_proj₂ hEF hq, proj₁_mul_proj₂ hEF hq']
      _ = proj₁ hEF q * (proj₂ hEF q * proj₁ hEF q') * proj₂ hEF q' := by group
      _ = proj₁ hEF q * (proj₁ hEF q' * proj₂ hEF q) * proj₂ hEF q' := by rw [hcomm]
      _ = (proj₁ hEF q * proj₁ hEF q') *
          (proj₂ hEF q * proj₂ hEF q') := by group
  exact (proj₂_eq_of_decomp hEF hbot (Q.mul_mem hq hq')
    (E.mul_mem h₁ h₁') (F.mul_mem h₂ h₂') hdec).symm

private theorem proj₁_conj {U : Subgroup G}
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f) (hbot : E ⊓ F = ⊥)
    (hUQ : U ≤ Subgroup.normalizer (Q : Set G))
    (hUE : U ≤ Subgroup.normalizer (E : Set G))
    (hUF : ∀ u ∈ U, ∀ f ∈ F, u * f = f * u)
    {a q : G} (ha : a ∈ U) (hq : q ∈ Q) :
    proj₁ hEF (a * q * a⁻¹) = a * proj₁ hEF q * a⁻¹ := by
  classical
  have haq : a * q * a⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hUQ ha) q).mp hq
  have h₁ : a * proj₁ hEF q * a⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hUE ha) (proj₁ hEF q)).mp (proj₁_mem hEF hq)
  have h₂ : a * proj₂ hEF q * a⁻¹ = proj₂ hEF q := by
    calc a * proj₂ hEF q * a⁻¹ = (a * proj₂ hEF q) * a⁻¹ := rfl
      _ = (proj₂ hEF q * a) * a⁻¹ := by
            rw [hUF a ha (proj₂ hEF q) (proj₂_mem hEF hq)]
      _ = proj₂ hEF q := by group
  have hdec : a * q * a⁻¹ = (a * proj₁ hEF q * a⁻¹) * (a * proj₂ hEF q * a⁻¹) := by
    calc a * q * a⁻¹ = a * (proj₁ hEF q * proj₂ hEF q) * a⁻¹ := by
          rw [proj₁_mul_proj₂ hEF hq]
      _ = (a * proj₁ hEF q * a⁻¹) * (a * proj₂ hEF q * a⁻¹) := by group
  have h := proj₁_eq_of_decomp hEF hbot haq h₁
    (by rw [h₂]; exact proj₂_mem hEF hq) hdec
  exact h.symm

private theorem proj₂_conj {U : Subgroup G}
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f) (hbot : E ⊓ F = ⊥)
    (hUQ : U ≤ Subgroup.normalizer (Q : Set G))
    (hUE : U ≤ Subgroup.normalizer (E : Set G))
    (hUF : ∀ u ∈ U, ∀ f ∈ F, u * f = f * u)
    {a q : G} (ha : a ∈ U) (hq : q ∈ Q) :
    proj₂ hEF (a * q * a⁻¹) = proj₂ hEF q := by
  classical
  have haq : a * q * a⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hUQ ha) q).mp hq
  have h₁ : a * proj₁ hEF q * a⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hUE ha) (proj₁ hEF q)).mp (proj₁_mem hEF hq)
  have h₂ : a * proj₂ hEF q * a⁻¹ = proj₂ hEF q := by
    calc a * proj₂ hEF q * a⁻¹ = (a * proj₂ hEF q) * a⁻¹ := rfl
      _ = (proj₂ hEF q * a) * a⁻¹ := by
            rw [hUF a ha (proj₂ hEF q) (proj₂_mem hEF hq)]
      _ = proj₂ hEF q := by group
  have hdec : a * q * a⁻¹ = (a * proj₁ hEF q * a⁻¹) * (a * proj₂ hEF q * a⁻¹) := by
    calc a * q * a⁻¹ = a * (proj₁ hEF q * proj₂ hEF q) * a⁻¹ := by
          rw [proj₁_mul_proj₂ hEF hq]
      _ = (a * proj₁ hEF q * a⁻¹) * (a * proj₂ hEF q * a⁻¹) := by group
  have h := proj₂_eq_of_decomp hEF hbot haq h₁
    (by rw [h₂]; exact proj₂_mem hEF hq) hdec
  rw [h₂] at h
  exact h.symm

private theorem proj₂_inv (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f) (hbot : E ⊓ F = ⊥)
    (hEQ : E ≤ Q) (hFQ : F ≤ Q) {q : G} (hq : q ∈ Q) :
    proj₂ hEF q⁻¹ = (proj₂ hEF q)⁻¹ := by
  classical
  have h₁ : proj₁ hEF q ∈ E := proj₁_mem hEF hq
  have h₂ : proj₂ hEF q ∈ F := proj₂_mem hEF hq
  have hcomm : (proj₁ hEF q)⁻¹ * (proj₂ hEF q)⁻¹ =
      (proj₂ hEF q)⁻¹ * (proj₁ hEF q)⁻¹ :=
    hQcomm _ (Q.inv_mem (hEQ h₁)) _ (Q.inv_mem (hFQ h₂))
  have hdec : q⁻¹ = (proj₁ hEF q)⁻¹ * (proj₂ hEF q)⁻¹ := by
    calc q⁻¹ = (proj₁ hEF q * proj₂ hEF q)⁻¹ := by rw [proj₁_mul_proj₂ hEF hq]
      _ = (proj₂ hEF q)⁻¹ * (proj₁ hEF q)⁻¹ := by rw [mul_inv_rev]
      _ = (proj₁ hEF q)⁻¹ * (proj₂ hEF q)⁻¹ := hcomm.symm
  have h := proj₂_eq_of_decomp hEF hbot (Q.inv_mem hq)
    (E.inv_mem h₁) (F.inv_mem h₂) hdec
  exact h.symm

end Projection

private noncomputable def qPart
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o) (x : G) : G := by
  classical
  exact if hx : x ∈ Subgroup.centralizer (Q : Set G) then
    Classical.choose
      (hCQ x fun q hq => (Subgroup.mem_centralizer_iff.mp hx q hq).symm)
  else 1

private theorem qPart_mem_and_spec
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {x : G} (hx : x ∈ Subgroup.centralizer (Q : Set G)) :
    qPart hCQ x ∈ Q ∧ ∃ o ∈ O, x = qPart hCQ x * o := by
  classical
  unfold qPart
  rw [dif_pos hx]
  exact Classical.choose_spec
    (hCQ x fun q hq => (Subgroup.mem_centralizer_iff.mp hx q hq).symm)

private theorem qPart_eq_of_mem (hQ : IsPGroup 2 Q)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {x q o : G} (hx : x ∈ Subgroup.centralizer (Q : Set G))
    (hq : q ∈ Q) (ho : o ∈ O) (h : x = q * o) : q = qPart hCQ x := by
  classical
  have hqP : qPart hCQ x ∈ Q := (qPart_mem_and_spec hCQ hx).1
  obtain ⟨o', ho', hspec⟩ := (qPart_mem_and_spec hCQ hx).2
  have hEq : q * o = qPart hCQ x * o' := h.symm.trans hspec
  have hcalc : q⁻¹ * qPart hCQ x = o * o'⁻¹ := by
    calc q⁻¹ * qPart hCQ x
        = q⁻¹ * (qPart hCQ x * o') * o'⁻¹ := by group
      _ = q⁻¹ * (q * o) * o'⁻¹ := by rw [← hEq]
      _ = o * o'⁻¹ := by group
  have hmem : q⁻¹ * qPart hCQ x ∈ Q ⊓ O := by
    refine Subgroup.mem_inf.mpr ⟨Q.mul_mem (Q.inv_mem hq) hqP, ?_⟩
    rw [hcalc]
    exact O.mul_mem ho (O.inv_mem ho')
  have hone : q⁻¹ * qPart hCQ x = 1 :=
    eq_one_of_mem_Q_inf_O hQ hO hmem.1 hmem.2
  exact inv_mul_eq_one.mp hone

private theorem qPart_eq_one_of_mem_O (hQ : IsPGroup 2 Q)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {x : G} (hx : x ∈ O) : qPart hCQ x = 1 := by
  have hxcent : x ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (((hO x).mp hx).1 q hq).symm
  have h := qPart_eq_of_mem hQ hO hCQ hxcent (Q.one_mem) hx (by simp)
  exact h.symm

private theorem qPart_one (hQ : IsPGroup 2 Q)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o) : qPart hCQ (1 : G) = 1 := by
  classical
  have h := qPart_eq_of_mem hQ hO hCQ (Subgroup.one_mem _) (Q.one_mem) (O.one_mem)
    (by simp : (1 : G) = 1 * 1)
  exact h.symm

private theorem qPart_mul (hQ : IsPGroup 2 Q)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {x y : G} (hx : x ∈ Subgroup.centralizer (Q : Set G))
    (hy : y ∈ Subgroup.centralizer (Q : Set G)) :
    qPart hCQ (x * y) = qPart hCQ x * qPart hCQ y := by
  classical
  have hxy : x * y ∈ Subgroup.centralizer (Q : Set G) :=
    (Subgroup.centralizer (Q : Set G)).mul_mem hx hy
  have hqx : qPart hCQ x ∈ Q := (qPart_mem_and_spec hCQ hx).1
  have hqy : qPart hCQ y ∈ Q := (qPart_mem_and_spec hCQ hy).1
  obtain ⟨ox, hox, hxeq⟩ := (qPart_mem_and_spec hCQ hx).2
  obtain ⟨oy, hoy, hyeq⟩ := (qPart_mem_and_spec hCQ hy).2
  have hcomm : ox * qPart hCQ y = qPart hCQ y * ox :=
    ((hO ox).mp hox).1 _ hqy
  have hdecomp : x * y = (qPart hCQ x * qPart hCQ y) * (ox * oy) := by
    calc x * y = (qPart hCQ x * ox) * (qPart hCQ y * oy) := by
          rw [← hxeq, ← hyeq]
      _ = qPart hCQ x * (ox * qPart hCQ y) * oy := by group
      _ = qPart hCQ x * (qPart hCQ y * ox) * oy := by rw [hcomm]
      _ = (qPart hCQ x * qPart hCQ y) * (ox * oy) := by group
  exact (qPart_eq_of_mem hQ hO hCQ hxy (Q.mul_mem hqx hqy) (O.mul_mem hox hoy)
    hdecomp).symm

private theorem qPart_inv (hQ : IsPGroup 2 Q)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {x : G} (hx : x ∈ Subgroup.centralizer (Q : Set G)) :
    qPart hCQ x⁻¹ = (qPart hCQ x)⁻¹ := by
  classical
  have hxinv : x⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
    (Subgroup.centralizer (Q : Set G)).inv_mem hx
  have hxy : x * x⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
    (Subgroup.centralizer (Q : Set G)).mul_mem hx hxinv
  have hmul : qPart hCQ (x * x⁻¹) = qPart hCQ x * qPart hCQ x⁻¹ :=
    qPart_mul hQ hO hCQ hx hxinv
  have hone : qPart hCQ (x * x⁻¹) = 1 := by
    rw [mul_inv_cancel, qPart_one hQ hO hCQ]
  have hprod : qPart hCQ x * qPart hCQ x⁻¹ = 1 := by rw [← hmul, hone]
  exact mul_eq_one_iff_eq_inv'.mp hprod

private theorem conj_mem_centralizer {n x : G}
    (hn : n ∈ Subgroup.normalizer (Q : Set G))
    (hx : x ∈ Subgroup.centralizer (Q : Set G)) :
    n * x * n⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : n⁻¹ * q * n ∈ Q := (Subgroup.mem_normalizer_iff''.mp hn q).mp hq
  have hxq := Subgroup.mem_centralizer_iff.mp hx (n⁻¹ * q * n) hq'
  calc q * (n * x * n⁻¹) = n * ((n⁻¹ * q * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * q * n)) * n⁻¹ := by rw [hxq]
    _ = (n * x * n⁻¹) * q := by group

private theorem conj_mem_O
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    {n o : G} (hn : n ∈ Subgroup.normalizer (Q : Set G)) (ho : o ∈ O) :
    n * o * n⁻¹ ∈ O := by
  have hoc : o ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (((hO o).mp ho).1 q hq).symm
  rw [hO]
  refine ⟨?_, ?_⟩
  · intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (conj_mem_centralizer hn hoc) q hq).symm
  · have hord : orderOf (n * o * n⁻¹) = orderOf o := by
      have h := MulEquiv.orderOf_eq (MulAut.conj n) o
      rwa [MulAut.conj_apply] at h
    rw [hord]
    exact ((hO o).mp ho).2

private theorem qPart_conj (hQ : IsPGroup 2 Q)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {n x : G} (hn : n ∈ Subgroup.normalizer (Q : Set G))
    (hx : x ∈ Subgroup.centralizer (Q : Set G)) :
    qPart hCQ (n * x * n⁻¹) = n * qPart hCQ x * n⁻¹ := by
  classical
  have hq : qPart hCQ x ∈ Q := (qPart_mem_and_spec hCQ hx).1
  obtain ⟨o, ho, hxeq⟩ := (qPart_mem_and_spec hCQ hx).2
  have hqQ : n * qPart hCQ x * n⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hn (qPart hCQ x)).mp hq
  have hoO : n * o * n⁻¹ ∈ O := conj_mem_O hO hn ho
  have hdec : n * x * n⁻¹ = (n * qPart hCQ x * n⁻¹) * (n * o * n⁻¹) := by
    conv_lhs => rw [hxeq]
    group
  exact (qPart_eq_of_mem hQ hO hCQ (conj_mem_centralizer hn hx) hqQ hoO hdec).symm

private theorem P₁_le_normalizer_Q
    (hE : ∀ q ∈ Q, ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₂, q = e₁ * e₂)
    (hE₁ : E₁ ≤ Q) (hE₂ : E₂ ≤ Q)
    (h₁₁ : ∀ x ∈ P₁, ∀ e ∈ E₁, x * e * x⁻¹ ∈ E₁)
    (h₁₂ : ∀ x ∈ P₁, ∀ e ∈ E₂, x * e = e * x) :
    P₁ ≤ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.le_set_normalizer_iff]
  intro p hp q hq
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := hE q hq
  have h1 : p * e₁ * p⁻¹ ∈ E₁ := h₁₁ p hp e₁ he₁
  have h2 : p * e₂ * p⁻¹ = e₂ := by
    calc p * e₂ * p⁻¹ = (p * e₂) * p⁻¹ := rfl
      _ = (e₂ * p) * p⁻¹ := by rw [h₁₂ p hp e₂ he₂]
      _ = e₂ := by group
  have hprod : p * (e₁ * e₂) * p⁻¹ = (p * e₁ * p⁻¹) * (p * e₂ * p⁻¹) := by
    group
  rw [hprod, h2]
  exact Q.mul_mem (hE₁ h1) (hE₂ he₂)

private theorem P₂_le_normalizer_Q
    (hE : ∀ q ∈ Q, ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₂, q = e₁ * e₂)
    (hE₁ : E₁ ≤ Q) (hE₂ : E₂ ≤ Q)
    (h₂₁ : ∀ y ∈ P₂, ∀ e ∈ E₁, y * e = e * y)
    (h₂₂ : ∀ y ∈ P₂, ∀ e ∈ E₂, y * e * y⁻¹ ∈ E₂) :
    P₂ ≤ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.le_set_normalizer_iff]
  intro p hp q hq
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := hE q hq
  have h1 : p * e₁ * p⁻¹ = e₁ := by
    calc p * e₁ * p⁻¹ = (p * e₁) * p⁻¹ := rfl
      _ = (e₁ * p) * p⁻¹ := by rw [h₂₁ p hp e₁ he₁]
      _ = e₁ := by group
  have h2 : p * e₂ * p⁻¹ ∈ E₂ := h₂₂ p hp e₂ he₂
  have hprod : p * (e₁ * e₂) * p⁻¹ = (p * e₁ * p⁻¹) * (p * e₂ * p⁻¹) := by
    group
  rw [hprod, h1]
  exact Q.mul_mem (hE₁ he₁) (hE₂ h2)

private theorem commutator_mem_centralizer
    {E F U V : Subgroup G}
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f)
    (hUF : ∀ u ∈ U, ∀ f ∈ F, u * f = f * u)
    (hVE : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v)
    (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ U ⊓ V)
    {u v : G} (hu : u ∈ U) (hv : v ∈ V) :
    u * v * u⁻¹ * v⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  have hβ : u * v * u⁻¹ * v⁻¹ ∈ U ⊓ V := hcomm u hu v hv
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨e, he, f, hf, rfl⟩ := hEF q hq
  have huf : (u * v * u⁻¹ * v⁻¹) * f = f * (u * v * u⁻¹ * v⁻¹) :=
    hUF _ hβ.1 f hf
  have hve : (u * v * u⁻¹ * v⁻¹) * e = e * (u * v * u⁻¹ * v⁻¹) :=
    hVE _ hβ.2 e he
  calc (e * f) * (u * v * u⁻¹ * v⁻¹)
      = e * (f * (u * v * u⁻¹ * v⁻¹)) := by group
    _ = e * ((u * v * u⁻¹ * v⁻¹) * f) := by rw [huf]
    _ = (e * (u * v * u⁻¹ * v⁻¹)) * f := by group
    _ = ((u * v * u⁻¹ * v⁻¹) * e) * f := by rw [hve]
    _ = (u * v * u⁻¹ * v⁻¹) * (e * f) := by group

private theorem proj₂_qPart_commutator_eq_one
    (hQ : IsPGroup 2 Q)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    {E F U V : Subgroup G}
    (hEF : ∀ q ∈ Q, ∃ e ∈ E, ∃ f ∈ F, q = e * f)
    (hbot : E ⊓ F = ⊥) (hEQ : E ≤ Q) (hFQ : F ≤ Q)
    (hUQ : U ≤ Subgroup.normalizer (Q : Set G))
    (hUE : U ≤ Subgroup.normalizer (E : Set G))
    (hUF : ∀ u ∈ U, ∀ f ∈ F, u * f = f * u)
    (hVE : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v)
    (hUgen : U ≤ Subgroup.closure {u : G | u ∈ U ∧ Odd (orderOf u)})
    (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ U ⊓ V)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {v : G} (hv : v ∈ V) {u : G} (hu : u ∈ U) :
    proj₂ hEF (qPart hCQ (u * v * u⁻¹ * v⁻¹)) = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : G → G := fun a => proj₂ hEF (qPart hCQ (a * v * a⁻¹ * v⁻¹))
  have hf_mul : ∀ a ∈ U, ∀ a' ∈ U, f (a * a') = f a * f a' := by
    intro a ha a' ha'
    have hβa : a * v * a⁻¹ * v⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
      commutator_mem_centralizer hEF hUF hVE hcomm ha hv
    have hβa' : a' * v * a'⁻¹ * v⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
      commutator_mem_centralizer hEF hUF hVE hcomm ha' hv
    have hconj : a * (a' * v * a'⁻¹ * v⁻¹) * a⁻¹ ∈
        Subgroup.centralizer (Q : Set G) := conj_mem_centralizer (hUQ ha) hβa'
    have hβeq : (a * a') * v * (a * a')⁻¹ * v⁻¹ =
        (a * (a' * v * a'⁻¹ * v⁻¹) * a⁻¹) * (a * v * a⁻¹ * v⁻¹) := by
      group
    have hq₁ : qPart hCQ (a * (a' * v * a'⁻¹ * v⁻¹) * a⁻¹) =
        a * qPart hCQ (a' * v * a'⁻¹ * v⁻¹) * a⁻¹ :=
      qPart_conj hQ hO hCQ (hUQ ha) hβa'
    have hq₂ : qPart hCQ ((a * (a' * v * a'⁻¹ * v⁻¹) * a⁻¹) *
          (a * v * a⁻¹ * v⁻¹)) =
        qPart hCQ (a * (a' * v * a'⁻¹ * v⁻¹) * a⁻¹) *
          qPart hCQ (a * v * a⁻¹ * v⁻¹) :=
      qPart_mul hQ hO hCQ hconj hβa
    have hq₁Q : qPart hCQ (a * (a' * v * a'⁻¹ * v⁻¹) * a⁻¹) ∈ Q :=
      (qPart_mem_and_spec hCQ hconj).1
    have hq₂Q : qPart hCQ (a * v * a⁻¹ * v⁻¹) ∈ Q :=
      (qPart_mem_and_spec hCQ hβa).1
    calc f (a * a')
        = proj₂ hEF (qPart hCQ ((a * a') * v * (a * a')⁻¹ * v⁻¹)) := by
            simp only [f]
      _ = proj₂ hEF (qPart hCQ ((a * (a' * v * a'⁻¹ * v⁻¹) * a⁻¹) *
            (a * v * a⁻¹ * v⁻¹))) := by rw [hβeq]
      _ = proj₂ hEF (qPart hCQ (a * (a' * v * a'⁻¹ * v⁻¹) * a⁻¹) *
            qPart hCQ (a * v * a⁻¹ * v⁻¹)) := by rw [hq₂]
      _ = proj₂ hEF (a * qPart hCQ (a' * v * a'⁻¹ * v⁻¹) * a⁻¹ *
            qPart hCQ (a * v * a⁻¹ * v⁻¹)) := by rw [hq₁]
      _ = proj₂ hEF (a * qPart hCQ (a' * v * a'⁻¹ * v⁻¹) * a⁻¹) *
            proj₂ hEF (qPart hCQ (a * v * a⁻¹ * v⁻¹)) := by
            have hq₁mem : a * qPart hCQ (a' * v * a'⁻¹ * v⁻¹) * a⁻¹ ∈ Q := by
              rw [← hq₁]
              exact hq₁Q
            exact proj₂_mul hQcomm hEF hbot hEQ hFQ hq₁mem hq₂Q
      _ = proj₂ hEF (qPart hCQ (a' * v * a'⁻¹ * v⁻¹)) *
            proj₂ hEF (qPart hCQ (a * v * a⁻¹ * v⁻¹)) := by
            rw [proj₂_conj hEF hbot hUQ hUE hUF ha
              (qPart_mem_and_spec hCQ hβa').1]
      _ = f a * f a' := by
            have hswap := hQcomm
              (proj₂ hEF (qPart hCQ (a' * v * a'⁻¹ * v⁻¹)))
              (hFQ (proj₂_mem hEF (qPart_mem_and_spec hCQ hβa').1))
              (proj₂ hEF (qPart hCQ (a * v * a⁻¹ * v⁻¹)))
              (hFQ (proj₂_mem hEF (qPart_mem_and_spec hCQ hβa).1))
            simpa only [f] using hswap
  have hf_one : f 1 = 1 := by
    have hβ : (1 : G) * v * (1 : G)⁻¹ * v⁻¹ = 1 := by group
    change proj₂ hEF (qPart hCQ ((1 : G) * v * (1 : G)⁻¹ * v⁻¹)) = 1
    rw [hβ, qPart_one hQ hO hCQ, proj₂_one hEF hbot]
  have hf_odd : ∀ a ∈ U, Odd (orderOf a) → f a = 1 := by
    intro a ha haodd
    have hfaF : f a ∈ F :=
      proj₂_mem hEF (qPart_mem_and_spec hCQ
        (commutator_mem_centralizer hEF hUF hVE hcomm ha hv)).1
    have hpow : ∀ n : ℕ, (f a) ^ n = f (a ^ n) := by
      intro n
      induction n with
      | zero => simpa using hf_one.symm
      | succ n ih =>
          calc (f a) ^ (n + 1) = (f a) ^ n * f a := pow_succ _ _
            _ = f (a ^ n) * f a := by rw [ih]
            _ = f (a ^ n * a) :=
                (hf_mul (a ^ n) (U.pow_mem ha n) a ha).symm
            _ = f (a ^ (n + 1)) := by rw [pow_succ]
    have hfa_pow : (f a) ^ orderOf a = 1 := by
      rw [hpow (orderOf a), pow_orderOf_eq_one, hf_one]
    have hdvd : orderOf (f a) ∣ orderOf a := orderOf_dvd_of_pow_eq_one hfa_pow
    have hFp : IsPGroup 2 F := hQ.to_le hFQ
    obtain ⟨k, hk⟩ := hFp.exists_orderOf_eq_pow ⟨f a, hfaF⟩
    have hk' : orderOf (f a) = 2 ^ k := by
      simpa only [Subgroup.orderOf_mk] using hk
    have hodd2 : Odd (2 ^ k) := by
      rw [← hk']
      exact haodd.of_dvd_nat hdvd
    have hk0 : k = 0 := by
      by_contra hne
      exact (Nat.not_odd_iff_even.mpr
        (by rw [Nat.even_pow]; exact ⟨even_two, hne⟩)) hodd2
    exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])
  have hUle : Subgroup.closure {a : G | a ∈ U ∧ Odd (orderOf a)} ≤ U :=
    (Subgroup.closure_le U).mpr fun a ha => ha.1
  have hf_all : ∀ a ∈ U, f a = 1 := by
    intro a ha
    have hmem := hUgen ha
    induction hmem using Subgroup.closure_induction with
    | mem b hb => exact hf_odd b hb.1 hb.2
    | one => exact hf_one
    | mul b c hb hc ihb ihc =>
        rw [hf_mul b (hUle hb) c (hUle hc), ihb (hUle hb), ihc (hUle hc),
          mul_one]
    | inv b hb ihb =>
        have hmul : f (b * b⁻¹) = f b * f b⁻¹ :=
          hf_mul b (hUle hb) b⁻¹ (U.inv_mem (hUle hb))
        have hone : f b * f b⁻¹ = 1 := by
          rw [← hmul, mul_inv_cancel, hf_one]
        have hinv : f b⁻¹ = (f b)⁻¹ := mul_eq_one_iff_eq_inv'.mp hone
        rw [hinv, ihb (hUle hb), inv_one]
  exact hf_all u hu

theorem commutator_mem_of_complementary_actions
    (hQ : IsPGroup 2 Q)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hE₁ : E₁ ≤ Q) (hE₂ : E₂ ≤ Q)
    (hE : ∀ q ∈ Q, ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₂, q = e₁ * e₂)
    (hE12 : E₁ ⊓ E₂ = ⊥)
    (h₁₂ : ∀ x ∈ P₁, ∀ e ∈ E₂, x * e = e * x)
    (h₁₁ : ∀ x ∈ P₁, ∀ e ∈ E₁, x * e * x⁻¹ ∈ E₁)
    (h₂₁ : ∀ y ∈ P₂, ∀ e ∈ E₁, y * e = e * y)
    (h₂₂ : ∀ y ∈ P₂, ∀ e ∈ E₂, y * e * y⁻¹ ∈ E₂)
    (hP : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y * x⁻¹ * y⁻¹ ∈ P₁ ⊓ P₂)
    (hP₁ : P₁ ≤ Subgroup.closure {x : G | x ∈ P₁ ∧ Odd (orderOf x)})
    (hP₂ : P₂ ≤ Subgroup.closure {x : G | x ∈ P₂ ∧ Odd (orderOf x)})
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {x y : G} (hx : x ∈ P₁) (hy : y ∈ P₂) :
    x * y * x⁻¹ * y⁻¹ ∈ O := by
  classical
  have hUE : P₁ ≤ Subgroup.normalizer (E₁ : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    exact h₁₁
  have hUQ : P₁ ≤ Subgroup.normalizer (Q : Set G) :=
    P₁_le_normalizer_Q hE hE₁ hE₂ h₁₁ h₁₂
  have hβ_cent : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
    commutator_mem_centralizer hE h₁₂ h₂₁ hP hx hy
  have h₂ : proj₂ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) = 1 :=
    proj₂_qPart_commutator_eq_one hQ hQcomm hE hE12 hE₁ hE₂ hUQ hUE h₁₂ h₂₁ hP₁ hP
      hO hCQ (v := y) hy (u := x) hx
  let hEswap : ∀ q ∈ Q, ∃ e ∈ E₂, ∃ f ∈ E₁, q = e * f := fun q hq => by
    obtain ⟨e₁, he₁, e₂, he₂, hqeq⟩ := hE q hq
    exact ⟨e₂, he₂, e₁, he₁, by rw [hqeq, hQcomm e₁ (hE₁ he₁) e₂ (hE₂ he₂)]⟩
  have hE12swap : E₂ ⊓ E₁ = ⊥ := by rw [inf_comm]; exact hE12
  have hVQ : P₂ ≤ Subgroup.normalizer (Q : Set G) :=
    P₂_le_normalizer_Q hE hE₁ hE₂ h₂₁ h₂₂
  have hVE : P₂ ≤ Subgroup.normalizer (E₂ : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    exact h₂₂
  have hcomm₂ : ∀ u ∈ P₂, ∀ v ∈ P₁, u * v * u⁻¹ * v⁻¹ ∈ P₂ ⊓ P₁ := by
    intro u hu v hv
    have hmem : u * v * u⁻¹ * v⁻¹ ∈ P₁ ⊓ P₂ := by
      have h := (P₁ ⊓ P₂).inv_mem (hP v hv u hu)
      rwa [show (v * u * v⁻¹ * u⁻¹)⁻¹ = u * v * u⁻¹ * v⁻¹ by group] at h
    simpa [inf_comm] using hmem
  have hgen₂ : proj₂ hEswap (qPart hCQ (y * x * y⁻¹ * x⁻¹)) = 1 :=
    proj₂_qPart_commutator_eq_one hQ hQcomm hEswap hE12swap hE₂ hE₁ hVQ hVE h₂₁ h₁₂
      hP₂ hcomm₂ hO hCQ (v := x) hx (u := y) hy
  have hqβ : qPart hCQ (x * y * x⁻¹ * y⁻¹) ∈ Q :=
    (qPart_mem_and_spec hCQ hβ_cent).1
  have hgen₂' : proj₂ hEswap (qPart hCQ (x * y * x⁻¹ * y⁻¹)) = 1 := by
    have hgen₂'' : proj₂ hEswap (qPart hCQ ((x * y * x⁻¹ * y⁻¹)⁻¹)) = 1 := by
      simpa only [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group]
        using hgen₂
    have hinv : proj₂ hEswap (qPart hCQ ((x * y * x⁻¹ * y⁻¹)⁻¹)) =
        (proj₂ hEswap (qPart hCQ (x * y * x⁻¹ * y⁻¹)))⁻¹ := by
      rw [qPart_inv hQ hO hCQ hβ_cent]
      exact proj₂_inv hQcomm hEswap hE12swap hE₂ hE₁ hqβ
    rw [hinv] at hgen₂''
    exact inv_eq_one.mp hgen₂''
  have hswap_eq : proj₂ hEswap (qPart hCQ (x * y * x⁻¹ * y⁻¹)) =
      proj₁ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) := by
    have hdec : qPart hCQ (x * y * x⁻¹ * y⁻¹) =
        proj₂ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) *
          proj₁ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) := by
      calc qPart hCQ (x * y * x⁻¹ * y⁻¹)
          = proj₁ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) *
              proj₂ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) :=
            (proj₁_mul_proj₂ hE hqβ).symm
        _ = proj₂ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) *
              proj₁ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) :=
            hQcomm _ (hE₁ (proj₁_mem hE hqβ)) _ (hE₂ (proj₂_mem hE hqβ))
    exact (proj₂_eq_of_decomp hEswap hE12swap hqβ
      (proj₂_mem hE hqβ) (proj₁_mem hE hqβ) hdec).symm
  have h₁ : proj₁ hE (qPart hCQ (x * y * x⁻¹ * y⁻¹)) = 1 := by
    rw [← hswap_eq]
    exact hgen₂'
  have hqE₁ : qPart hCQ (x * y * x⁻¹ * y⁻¹) ∈ E₁ := by
    have hdec := proj₁_mul_proj₂ hE hqβ
    rw [h₂, mul_one] at hdec
    rw [← hdec]
    exact proj₁_mem hE hqβ
  have hqE₂ : qPart hCQ (x * y * x⁻¹ * y⁻¹) ∈ E₂ := by
    have hdec := proj₁_mul_proj₂ hE hqβ
    rw [h₁, one_mul] at hdec
    rw [← hdec]
    exact proj₂_mem hE hqβ
  have hq_one : qPart hCQ (x * y * x⁻¹ * y⁻¹) = 1 := by
    have hmem : qPart hCQ (x * y * x⁻¹ * y⁻¹) ∈ E₁ ⊓ E₂ :=
      Subgroup.mem_inf.mpr ⟨hqE₁, hqE₂⟩
    have hmem' : qPart hCQ (x * y * x⁻¹ * y⁻¹) ∈ (⊥ : Subgroup G) := by
      simpa [hE12] using hmem
    simpa using hmem'
  obtain ⟨o, ho, hβeq⟩ := (qPart_mem_and_spec hCQ hβ_cent).2
  rw [hq_one, one_mul] at hβeq
  rw [hβeq]
  exact ho

private theorem conj_qPart_eq_of_commutator_mem_O (hQ : IsPGroup 2 Q)
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    {n z : G} (hn : n ∈ Subgroup.normalizer (Q : Set G))
    (hz : z ∈ Subgroup.centralizer (Q : Set G))
    (hβ : n * z * n⁻¹ * z⁻¹ ∈ O) :
    n * qPart hCQ z * n⁻¹ = qPart hCQ z := by
  classical
  have hzn : n * z * n⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
    conj_mem_centralizer hn hz
  have hmul : qPart hCQ (n * z * n⁻¹ * z⁻¹) =
      qPart hCQ (n * z * n⁻¹) * qPart hCQ (z⁻¹) :=
    qPart_mul hQ hO hCQ hzn ((Subgroup.centralizer (Q : Set G)).inv_mem hz)
  have hconj : qPart hCQ (n * z * n⁻¹) = n * qPart hCQ z * n⁻¹ :=
    qPart_conj hQ hO hCQ hn hz
  have hinv : qPart hCQ (z⁻¹) = (qPart hCQ z)⁻¹ := qPart_inv hQ hO hCQ hz
  have hqβ : qPart hCQ (n * z * n⁻¹ * z⁻¹) = 1 :=
    qPart_eq_one_of_mem_O hQ hO hCQ hβ
  rw [hmul, hconj, hinv] at hqβ
  exact mul_inv_eq_one.mp hqβ

theorem odd_card_inf_of_complementary_actions
    (hQ : IsPGroup 2 Q)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hE₁ : E₁ ≤ Q) (hE₂ : E₂ ≤ Q)
    (hE : ∀ q ∈ Q, ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₂, q = e₁ * e₂)
    (hE12 : E₁ ⊓ E₂ = ⊥)
    (h₁₂ : ∀ x ∈ P₁, ∀ e ∈ E₂, x * e = e * x)
    (h₁₁ : ∀ x ∈ P₁, ∀ e ∈ E₁, x * e * x⁻¹ ∈ E₁)
    (h₂₁ : ∀ y ∈ P₂, ∀ e ∈ E₁, y * e = e * y)
    (h₂₂ : ∀ y ∈ P₂, ∀ e ∈ E₂, y * e * y⁻¹ ∈ E₂)
    (hP : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y * x⁻¹ * y⁻¹ ∈ P₁ ⊓ P₂)
    (hP₁ : P₁ ≤ Subgroup.closure {x : G | x ∈ P₁ ∧ Odd (orderOf x)})
    (hP₂ : P₂ ≤ Subgroup.closure {x : G | x ∈ P₂ ∧ Odd (orderOf x)})
    (hO : ∀ x, x ∈ O ↔ (∀ q ∈ Q, x * q = q * x) ∧ Odd (orderOf x))
    (hCQ : ∀ x, (∀ q ∈ Q, x * q = q * x) →
      ∃ q ∈ Q, ∃ o ∈ O, x = q * o)
    (hC₁ : ∀ e ∈ E₁, (∀ x ∈ P₁, x * e * x⁻¹ = e) → e = 1)
    (hC₂ : ∀ e ∈ E₂, (∀ y ∈ P₂, y * e * y⁻¹ = e) → e = 1) :
    Odd (Nat.card ↥(P₁ ⊓ P₂)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUE : P₁ ≤ Subgroup.normalizer (E₁ : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    exact h₁₁
  have hUQ : P₁ ≤ Subgroup.normalizer (Q : Set G) :=
    P₁_le_normalizer_Q hE hE₁ hE₂ h₁₁ h₁₂
  have hVQ : P₂ ≤ Subgroup.normalizer (Q : Set G) :=
    P₂_le_normalizer_Q hE hE₁ hE₂ h₂₁ h₂₂
  have hVE : P₂ ≤ Subgroup.normalizer (E₂ : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    exact h₂₂
  have hz_cent : ∀ z ∈ P₁ ⊓ P₂, z ∈ Subgroup.centralizer (Q : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := hE q hq
    have h1 : z * e₁ = e₁ * z := h₂₁ z hz.2 e₁ he₁
    have h2 : z * e₂ = e₂ * z := h₁₂ z hz.1 e₂ he₂
    calc (e₁ * e₂) * z = e₁ * (e₂ * z) := by group
      _ = e₁ * (z * e₂) := by rw [h2]
      _ = (e₁ * z) * e₂ := by group
      _ = (z * e₁) * e₂ := by rw [h1]
      _ = z * (e₁ * e₂) := by group
  let hEswap : ∀ q ∈ Q, ∃ e ∈ E₂, ∃ f ∈ E₁, q = e * f := fun q hq => by
    obtain ⟨e₁, he₁, e₂, he₂, hqeq⟩ := hE q hq
    exact ⟨e₂, he₂, e₁, he₁, by rw [hqeq, hQcomm e₁ (hE₁ he₁) e₂ (hE₂ he₂)]⟩
  have hE12swap : E₂ ⊓ E₁ = ⊥ := by rw [inf_comm]; exact hE12
  have hswap₁ : ∀ q ∈ Q, proj₁ hEswap q = proj₂ hE q := by
    intro q hq
    have hdec : q = proj₂ hE q * proj₁ hE q := by
      calc q = proj₁ hE q * proj₂ hE q := (proj₁_mul_proj₂ hE hq).symm
        _ = proj₂ hE q * proj₁ hE q :=
            hQcomm _ (hE₁ (proj₁_mem hE hq)) _ (hE₂ (proj₂_mem hE hq))
    exact (proj₁_eq_of_decomp hEswap hE12swap hq
      (proj₂_mem hE hq) (proj₁_mem hE hq) hdec).symm
  have hz_qPart_one : ∀ z ∈ P₁ ⊓ P₂, qPart hCQ z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.centralizer (Q : Set G) := hz_cent z hz
    have hq : qPart hCQ z ∈ Q := (qPart_mem_and_spec hCQ hzc).1
    have hP₁q : ∀ x ∈ P₁, x * qPart hCQ z * x⁻¹ = qPart hCQ z := by
      intro x hx
      exact conj_qPart_eq_of_commutator_mem_O hQ hO hCQ (hUQ hx) hzc
        (commutator_mem_of_complementary_actions hQ hQcomm hE₁ hE₂ hE hE12 h₁₂ h₁₁
          h₂₁ h₂₂ hP hP₁ hP₂ hO hCQ hx hz.2)
    have hP₂q : ∀ y ∈ P₂, y * qPart hCQ z * y⁻¹ = qPart hCQ z := by
      intro y hy
      have hβ' : z * y * z⁻¹ * y⁻¹ ∈ O :=
        commutator_mem_of_complementary_actions hQ hQcomm hE₁ hE₂ hE hE12 h₁₂ h₁₁
          h₂₁ h₂₂ hP hP₁ hP₂ hO hCQ hz.1 hy
      have hβ : y * z * y⁻¹ * z⁻¹ ∈ O := by
        have h := O.inv_mem hβ'
        rwa [show (z * y * z⁻¹ * y⁻¹)⁻¹ = y * z * y⁻¹ * z⁻¹ by group] at h
      exact conj_qPart_eq_of_commutator_mem_O hQ hO hCQ (hVQ hy) hzc hβ
    have he₁ : proj₁ hE (qPart hCQ z) = 1 := by
      refine hC₁ (proj₁ hE (qPart hCQ z)) (proj₁_mem hE hq) ?_
      intro x hx
      have hconj := proj₁_conj hE hE12 hUQ hUE h₁₂ hx hq
      rw [hP₁q x hx] at hconj
      exact hconj.symm
    have he₂ : proj₂ hE (qPart hCQ z) = 1 := by
      refine hC₂ (proj₂ hE (qPart hCQ z)) (proj₂_mem hE hq) ?_
      intro y hy
      have hconj := proj₁_conj hEswap hE12swap hVQ hVE h₂₁ hy hq
      rw [hP₂q y hy, hswap₁ _ hq] at hconj
      exact hconj.symm
    have hdec := proj₁_mul_proj₂ hE hq
    rw [he₁, he₂, one_mul] at hdec
    exact hdec.symm
  have hzodd : ∀ z ∈ P₁ ⊓ P₂, Odd (orderOf z) := by
    intro z hz
    have hzc : z ∈ Subgroup.centralizer (Q : Set G) := hz_cent z hz
    obtain ⟨o, ho, hzeq⟩ := (qPart_mem_and_spec hCQ hzc).2
    rw [hz_qPart_one z hz, one_mul] at hzeq
    rw [hzeq]
    exact ((hO o).mp ho).2
  by_contra hodd
  have heven : Even (Nat.card ↥(P₁ ⊓ P₂)) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P₁ ⊓ P₂)) 2 heven.two_dvd
  have hwodd : Odd (orderOf (w : G)) := hzodd (w : G) w.2
  have hwG : orderOf (w : G) = 2 := by
    rw [Subgroup.orderOf_coe, hw]
  rw [hwG] at hwodd
  exact (Nat.not_odd_iff_even.mpr (by norm_num : Even 2)) hwodd
