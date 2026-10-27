module

public import CFSG.GH74.GLS.C3.Layer2.FinModel
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup

section Aux

variable {n : ℕ} {C : Type*} [Group C]

private theorem eq_one_of_mem_K_of_mem_Q (hn : 5 ≤ n) {K Q : Subgroup C}
    (eK : K ≃* alternatingGroup (Fin n)) (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k) {k : C}
    (hk : k ∈ K) (hkQ : k ∈ Q) : k = 1 := by
  have hc : eK ⟨k, hk⟩ ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨⟨k', hk'⟩, rfl⟩ := eK.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg eK (Subtype.ext (hKQ k' hk' k hkQ))
  rw [alternatingGroup.center_eq_bot (by simp; omega)] at hc
  have h1 : eK ⟨k, hk⟩ = eK 1 := by rw [map_one]; exact Subgroup.mem_bot.mp hc
  exact congrArg Subtype.val (eK.injective h1)

private theorem sign_psi_eq_one_of_mem_K (hn : 5 ≤ n) {K : Subgroup C}
    (eK : K ≃* alternatingGroup (Fin n)) (ψ : C →* Perm (Fin n)) {k : C} (hk : k ∈ K) :
    sign (ψ k) = 1 := by
  let χ : alternatingGroup (Fin n) →* ℤˣ :=
    (sign.comp ψ).comp (K.subtype.comp eK.symm.toMonoidHom)
  have hle : commutator (alternatingGroup (Fin n)) ≤ χ.ker :=
    Abelianization.commutator_subset_ker χ
  rw [commutator_alternatingGroup_eq_top (by simpa using hn)] at hle
  have h1 : χ (eK ⟨k, hk⟩) = 1 := MonoidHom.mem_ker.mp (hle (Subgroup.mem_top _))
  simpa [χ] using h1

private theorem exists_mem_K_psi_eq (hn : 5 ≤ n) [Finite C] {K Q : Subgroup C}
    (eK : K ≃* alternatingGroup (Fin n)) (ψ : C →* Perm (Fin n)) (hker : ψ.ker = Q)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k) {σ : Perm (Fin n)} (hσ : sign σ = 1) :
    ∃ k ∈ K, ψ k = σ := by
  have hinj : Function.Injective (ψ.comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : (k : C) ∈ Q := by rw [← hker]; exact hk
    exact Subtype.ext (eq_one_of_mem_K_of_mem_Q hn eK hKQ k.2 hk')
  have hle : (ψ.comp K.subtype).range ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨k, rfl⟩
    exact mem_alternatingGroup.mpr (sign_psi_eq_one_of_mem_K hn eK ψ k.2)
  have hcard : Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (ψ.comp K.subtype).range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr eK.toEquiv]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hσ' : σ ∈ alternatingGroup (Fin n) := mem_alternatingGroup.mpr hσ
  rw [← heq] at hσ'
  obtain ⟨k, hk⟩ := hσ'
  exact ⟨k, k.2, hk⟩

private theorem card_eq_four_mul_factorial [Finite C] (ψ : C →* Perm (Fin n)) {Q : Subgroup C}
    (hker : ψ.ker = Q) (hrange : ψ.range = ⊤) (hQcard : Nat.card Q = 4) :
    Nat.card C = 4 * n.factorial := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have h2 : Nat.card (C ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have h3 : Nat.card ψ.range = n.factorial := by
    rw [hrange, Subgroup.card_top, Nat.card_perm]; simp
  rw [h1, h2, h3, hker, hQcard]; ring

private structure KFacts {n : ℕ} {C : Type*} [Group C] (K Q : Subgroup C)
    (ψ : C →* Perm (Fin n)) : Prop where
  inter : ∀ k ∈ K, k ∈ Q → k = 1
  even : ∀ k ∈ K, sign (ψ k) = 1
  surj : ∀ σ : Perm (Fin n), sign σ = 1 → ∃ k ∈ K, ψ k = σ

private theorem exists_decomp {K Q : Subgroup C} {ψ : C →* Perm (Fin n)} (hker : ψ.ker = Q)
    (KF : KFacts K Q ψ) {g : C} (hg : sign (ψ g) = -1) (c : C) :
    ∃ q ∈ Q, ∃ k ∈ K, c = q * k ∨ c = q * (k * g) := by
  have key : ∀ d : C, sign (ψ d) = 1 → ∃ q ∈ Q, ∃ k ∈ K, d = q * k := by
    intro d hd
    obtain ⟨k, hk, hψ⟩ := KF.surj (ψ d) hd
    refine ⟨d * k⁻¹, ?_, k, hk, by simp⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hψ, mul_inv_cancel]
  rcases Int.units_eq_one_or (sign (ψ c)) with h | h
  · obtain ⟨q, hq, k, hk, rfl⟩ := key c h
    exact ⟨q, hq, k, hk, Or.inl rfl⟩
  · obtain ⟨q, hq, k, hk, hc⟩ := key (c * g⁻¹) (by simp [h, hg])
    exact ⟨q, hq, k, hk, Or.inr (by rw [← mul_assoc, ← hc]; simp)⟩

private def qFour (x q : C) : Fin 4 → C := ![1, x, q, q * x]

@[simp] private theorem qFour_zero (x q : C) : qFour x q 0 = 1 := rfl
@[simp] private theorem qFour_one (x q : C) : qFour x q 1 = x := rfl
@[simp] private theorem qFour_two (x q : C) : qFour x q 2 = q := rfl
@[simp] private theorem qFour_three (x q : C) : qFour x q 3 = q * x := rfl

private theorem qFour_mem {Q : Subgroup C} {x q : C} (hx : x ∈ Q) (hq : q ∈ Q) (i : Fin 4) :
    qFour x q i ∈ Q := by
  fin_cases i
  · exact Q.one_mem
  · exact hx
  · exact hq
  · exact Q.mul_mem hq hx

private theorem qFour_injective {x q : C} (hx1 : x ≠ 1) (hq1 : q ≠ 1) (hqx : q ≠ x)
    (hxx : x * x = 1) : Function.Injective (qFour x q) := by
  have h01 : (1 : C) ≠ x := hx1.symm
  have h02 : (1 : C) ≠ q := hq1.symm
  have h03 : (1 : C) ≠ q * x := by
    intro h
    apply hqx
    have : q = x⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [this]
    exact inv_eq_of_mul_eq_one_right hxx
  have h12 : x ≠ q := hqx.symm
  have h13 : x ≠ q * x := by
    intro h
    apply hq1
    exact mul_eq_right.mp h.symm
  have h23 : q ≠ q * x := by
    intro h
    apply hx1
    exact mul_eq_left.mp h.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp only [qFour] at hij; simp_all)

private theorem mem_Q_cases [Finite C] {Q : Subgroup C} (hQcard : Nat.card Q = 4) {x q : C}
    (hx : x ∈ Q) (hq : q ∈ Q) (hx1 : x ≠ 1) (hq1 : q ≠ 1) (hqx : q ≠ x) (hxx : x * x = 1)
    {r : C} (hr : r ∈ Q) : r = 1 ∨ r = x ∨ r = q ∨ r = q * x := by
  have hinj := qFour_injective hx1 hq1 hqx hxx
  let φ : Fin 4 → Q := fun i => ⟨qFour x q i, qFour_mem hx hq i⟩
  have hφ : Function.Injective φ := fun i j h => hinj (congrArg Subtype.val h)
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).2 ⟨hφ, by rw [hQcard]; simp⟩
  obtain ⟨i, hi⟩ := hbij.2 ⟨r, hr⟩
  have hi' : qFour x q i = r := congrArg Subtype.val hi
  fin_cases i
  · exact Or.inl hi'.symm
  · exact Or.inr (Or.inl hi'.symm)
  · exact Or.inr (Or.inr (Or.inl hi'.symm))
  · exact Or.inr (Or.inr (Or.inr hi'.symm))

private theorem exists_f [Finite C] {K Q : Subgroup C} [Q.Normal] {ψ : C →* Perm (Fin n)}
    (hn : 5 ≤ n) (hker : ψ.ker = Q) (hsurj : Function.Surjective ψ) (KF : KFacts K Q ψ)
    (hQcard : Nat.card Q = 4) (hQe : ∀ q ∈ Q, q ^ 2 = 1)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k) (hQab : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q)
    {x : C} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hxc : ∀ c : C, c * x = x * c)
    (hnt : ∃ c : C, ∃ q ∈ Q, c * q ≠ q * c) :
    ∃ f q : C, q ∈ Q ∧ q ≠ 1 ∧ q ≠ x ∧ f * f = 1 ∧ sign (ψ f) = -1 ∧ f * q = q * x * f := by
  have hxx : x * x = 1 := by simpa [pow_two] using hQe x hxQ
  obtain ⟨g₀, hg₀⟩ := hsurj (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
  have hg₀s : sign (ψ g₀) = -1 := by
    rw [hg₀]; exact sign_swap (by simp [Fin.ext_iff])
  obtain ⟨q, hqQ, hnc⟩ : ∃ q ∈ Q, g₀ * q ≠ q * g₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, q, hq, hcq⟩ := hnt
    obtain ⟨q', hq', k, hk, hc | hc⟩ := exists_decomp hker KF hg₀s c
    · apply hcq
      rw [hc]
      exact Commute.mul_left (show Commute q' q from hQab q' hq' q hq)
        (show Commute k q from hKQ k hk q hq)
    · apply hcq
      rw [hc]
      exact Commute.mul_left (show Commute q' q from hQab q' hq' q hq)
        (Commute.mul_left (show Commute k q from hKQ k hk q hq)
          (show Commute g₀ q from hcon q hq))
  have hq1 : q ≠ 1 := by
    rintro rfl
    exact hnc (by simp)
  have hqx : q ≠ x := by
    rintro rfl
    exact hnc (hxc g₀)
  have hqq : q * q = 1 := by simpa [pow_two] using hQe q hqQ
  have hψq : ψ q = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hqQ
  have h5 : g₀ * q = q * x * g₀ := by
    have hmem : g₀ * q * g₀⁻¹ ∈ Q := Subgroup.Normal.conj_mem inferInstance q hqQ g₀
    rcases mem_Q_cases hQcard hxQ hqQ hx1 hq1 hqx hxx hmem with h | h | h | h
    · exfalso
      apply hq1
      have : g₀ * q = g₀ := by
        calc g₀ * q = g₀ * q * g₀⁻¹ * g₀ := by simp
          _ = 1 * g₀ := by rw [h]
          _ = g₀ := one_mul _
      exact mul_eq_left.mp this
    · exfalso
      apply hqx
      have h1 : g₀ * q = x * g₀ := by
        calc g₀ * q = g₀ * q * g₀⁻¹ * g₀ := by simp
          _ = x * g₀ := by rw [h]
      have h' : g₀ * q = g₀ * x := by rw [h1, hxc]
      exact mul_left_cancel h'
    · exfalso
      apply hnc
      calc g₀ * q = g₀ * q * g₀⁻¹ * g₀ := by simp
        _ = q * g₀ := by rw [h]
    · calc g₀ * q = g₀ * q * g₀⁻¹ * g₀ := by simp
        _ = q * x * g₀ := by rw [h]
  have hg₀₂ : g₀ * g₀ ∈ Q := by
    rw [← hker, MonoidHom.mem_ker, map_mul, hg₀]
    exact swap_mul_self _ _
  have h6 : g₀ * g₀ = 1 ∨ g₀ * g₀ = x := by
    rcases mem_Q_cases hQcard hxQ hqQ hx1 hq1 hqx hxx hg₀₂ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      apply hnc
      rw [← h]
      exact (mul_assoc _ _ _).symm
    · exfalso
      apply hx1
      have hcomm : g₀ * (q * x) = q * x * g₀ := by
        rw [← h]
        exact (mul_assoc _ _ _).symm
      have h' : q * x * g₀ * x = q * x * g₀ * 1 := by
        calc q * x * g₀ * x = g₀ * q * x := by rw [h5]
          _ = g₀ * (q * x) := mul_assoc _ _ _
          _ = q * x * g₀ := hcomm
          _ = q * x * g₀ * 1 := (mul_one _).symm
      exact mul_left_cancel h'
  rcases h6 with h6 | h6
  · exact ⟨g₀, q, hqQ, hq1, hqx, h6, hg₀s, h5⟩
  · refine ⟨g₀ * q, q, hqQ, hq1, hqx, ?_, ?_, ?_⟩
    · calc g₀ * q * (g₀ * q) = g₀ * q * g₀ * q := (mul_assoc _ _ _).symm
        _ = q * x * g₀ * g₀ * q := by rw [h5]
        _ = q * x * (g₀ * g₀) * q := by rw [mul_assoc (q * x) g₀ g₀]
        _ = q * x * x * q := by rw [h6]
        _ = q * (x * x) * q := by rw [mul_assoc q x x]
        _ = q * q := by rw [hxx, mul_one]
        _ = 1 := hqq
    · rw [map_mul, hψq, mul_one]
      exact hg₀s
    · calc g₀ * q * q = (q * x * g₀) * q := by rw [h5]
        _ = q * x * (g₀ * q) := mul_assoc _ _ _

private theorem invol_mul_cancel {f : C} (hf : f * f = 1) (y : C) : f * (f * y) = y := by
  rw [← mul_assoc, hf, one_mul]

private theorem invol_conj_mem {K : Subgroup C} [K.Normal] {f : C} (hf : f * f = 1) {k : C}
    (hk : k ∈ K) : f * k * f ∈ K := by
  have := Subgroup.Normal.conj_mem inferInstance k hk f
  rwa [inv_eq_of_mul_eq_one_right hf] at this

private def rSub (K : Subgroup C) [K.Normal] (f : C) (hf : f * f = 1) : Subgroup C where
  carrier := {c | c ∈ K ∨ c * f ∈ K}
  one_mem' := Or.inl K.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (K.mul_mem ha hb)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact K.mul_mem ha hb
    · refine Or.inr ?_
      have : a * b * f = (a * f) * (f * b * f) := by
        simp only [mul_assoc, invol_mul_cancel hf]
      rw [this]
      exact K.mul_mem ha (invol_conj_mem hf hb)
    · refine Or.inl ?_
      have : a * b = (a * f) * (f * (b * f) * f) := by
        simp only [mul_assoc, invol_mul_cancel hf, hf, mul_one]
      rw [this]
      exact K.mul_mem ha (invol_conj_mem hf hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (K.inv_mem ha)
    · refine Or.inr ?_
      have h1 : f * a⁻¹ = (a * f)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hf]
      have : a⁻¹ * f = f * (f * a⁻¹) * f := by
        simp only [invol_mul_cancel hf]
      rw [this, h1]
      exact invol_conj_mem hf (K.inv_mem ha)

private theorem mem_rSub {K : Subgroup C} [K.Normal] {f : C} {hf : f * f = 1} {c : C} :
    c ∈ rSub K f hf ↔ c ∈ K ∨ c * f ∈ K := Iff.rfl

private noncomputable def cosetPerm (R : Subgroup C) (s : Fin 4 → C)
    (hb : Function.Bijective fun i => (QuotientGroup.mk (s i) : C ⧸ R)) : C →* Perm (Fin 4) :=
  ((Equiv.ofBijective _ hb).symm.permCongrHom : Perm (C ⧸ R) ≃* Perm (Fin 4)).toMonoidHom.comp
    (MulAction.toPermHom C (C ⧸ R))

private theorem cosetPerm_apply (R : Subgroup C) (s : Fin 4 → C)
    (hb : Function.Bijective fun i => (QuotientGroup.mk (s i) : C ⧸ R)) (c : C) (i : Fin 4) :
    cosetPerm R s hb c i =
      (Equiv.ofBijective _ hb).symm (c • (QuotientGroup.mk (s i) : C ⧸ R)) :=
  rfl

private theorem cosetPerm_spec (R : Subgroup C) (s : Fin 4 → C)
    (hb : Function.Bijective fun i => (QuotientGroup.mk (s i) : C ⧸ R)) (c : C) (i : Fin 4) :
    (QuotientGroup.mk (s (cosetPerm R s hb c i)) : C ⧸ R) = QuotientGroup.mk (c * s i) := by
  have h := (Equiv.ofBijective _ hb).apply_symm_apply (c • (QuotientGroup.mk (s i) : C ⧸ R))
  rw [← cosetPerm_apply] at h
  exact h

private theorem cosetPerm_eq_of_mul (R : Subgroup C) (s : Fin 4 → C)
    (hb : Function.Bijective fun i => (QuotientGroup.mk (s i) : C ⧸ R)) {c r : C} (hr : r ∈ R)
    {i j : Fin 4} (h : c * s i = s j * r) : cosetPerm R s hb c i = j := by
  apply hb.1
  show (QuotientGroup.mk (s (cosetPerm R s hb c i)) : C ⧸ R) = QuotientGroup.mk (s j)
  rw [cosetPerm_spec, h]
  exact QuotientGroup.eq.mpr (by simpa using R.inv_mem hr)

private theorem coset_bijective {Q R : Subgroup C} {s : Fin 4 → C} (hmem : ∀ i, s i ∈ Q)
    (hinj : Function.Injective s) (hsurj : ∀ r ∈ Q, ∃ i, s i = r)
    (hRQ : ∀ r ∈ R, r ∈ Q → r = 1) (hdec : ∀ c : C, ∃ q ∈ Q, ∃ r ∈ R, c = q * r) :
    Function.Bijective fun i => (QuotientGroup.mk (s i) : C ⧸ R) := by
  constructor
  · intro i j hij
    have h := QuotientGroup.eq.mp hij
    have h1 : (s i)⁻¹ * s j = 1 := hRQ _ h (Q.mul_mem (Q.inv_mem (hmem i)) (hmem j))
    exact hinj (inv_mul_eq_one.mp h1)
  · intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨q, hq, r, hr, rfl⟩ := hdec c
    obtain ⟨i, rfl⟩ := hsurj q hq
    refine ⟨i, ?_⟩
    apply QuotientGroup.eq.mpr
    simpa using hr

private theorem perm_fin4_ext {σ τ : Perm (Fin 4)} (h0 : σ 0 = τ 0) (h1 : σ 1 = τ 1)
    (h2 : σ 2 = τ 2) (h3 : σ 3 = τ 3) : σ = τ := by
  refine Equiv.ext fun i => ?_
  fin_cases i
  exacts [h0, h1, h2, h3]

private theorem sign_swap_mul_swap {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) :
    sign (swap a b * swap c d) = 1 := by
  rw [Perm.sign_mul, sign_swap hab, sign_swap hcd]
  decide

private theorem exists_delta_of_R [Finite C] {K Q R : Subgroup C} {ψ : C →* Perm (Fin n)}
    (hker : ψ.ker = Q) (KF : KFacts K Q ψ) (hQcard : Nat.card Q = 4)
    (hQe : ∀ q ∈ Q, q ^ 2 = 1) (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k)
    {x : C} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hxc : ∀ c : C, c * x = x * c)
    {f q : C} (hqQ : q ∈ Q) (hq1 : q ≠ 1) (hqx : q ≠ x)
    (hsf : sign (ψ f) = -1) (hfq : f * q = q * x * f)
    (hKR : ∀ k ∈ K, k ∈ R) (hfR : f ∈ R) (hRQ : ∀ r ∈ R, r ∈ Q → r = 1)
    (hdec : ∀ c : C, ∃ q ∈ Q, ∃ r ∈ R, c = q * r) :
    ∃ δ : C →* Perm (Fin 4), δ x = x4 ∧ (∀ c, sign (ψ c) = sign (δ c)) ∧
      ∀ c, ψ c = 1 → δ c = 1 → c = 1 := by
  have hxx : x * x = 1 := by simpa [pow_two] using hQe x hxQ
  have hqq : q * q = 1 := by simpa [pow_two] using hQe q hqQ
  have hsmem : ∀ i, qFour x q i ∈ Q := qFour_mem hxQ hqQ
  have hsinj : Function.Injective (qFour x q) := qFour_injective hx1 hq1 hqx hxx
  have hssurj : ∀ r ∈ Q, ∃ i, qFour x q i = r := by
    intro r hr
    rcases mem_Q_cases hQcard hxQ hqQ hx1 hq1 hqx hxx hr with h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  have hb := coset_bijective hsmem hsinj hssurj hRQ hdec
  have hψQ : ∀ r ∈ Q, ψ r = 1 := fun r hr => by rw [← MonoidHom.mem_ker, hker]; exact hr
  have hδx : cosetPerm R (qFour x q) hb x = x4 := by
    have h0 : cosetPerm R (qFour x q) hb x 0 = 1 :=
      cosetPerm_eq_of_mul R _ hb R.one_mem (by simp)
    have h1 : cosetPerm R (qFour x q) hb x 1 = 0 :=
      cosetPerm_eq_of_mul R _ hb R.one_mem (by simp [hxx])
    have h2 : cosetPerm R (qFour x q) hb x 2 = 3 :=
      cosetPerm_eq_of_mul R _ hb R.one_mem (by simp [hxc q])
    have h3 : cosetPerm R (qFour x q) hb x 3 = 2 := cosetPerm_eq_of_mul R _ hb R.one_mem (by
      simp only [qFour_three, qFour_two, mul_one]
      rw [← mul_assoc, ← hxc q, mul_assoc, hxx, mul_one])
    exact perm_fin4_ext (h0.trans (by decide)) (h1.trans (by decide)) (h2.trans (by decide))
      (h3.trans (by decide))
  have hδq : cosetPerm R (qFour x q) hb q = swap 0 2 * swap 1 3 := by
    have h0 : cosetPerm R (qFour x q) hb q 0 = 2 :=
      cosetPerm_eq_of_mul R _ hb R.one_mem (by simp)
    have h1 : cosetPerm R (qFour x q) hb q 1 = 3 :=
      cosetPerm_eq_of_mul R _ hb R.one_mem (by simp)
    have h2 : cosetPerm R (qFour x q) hb q 2 = 0 :=
      cosetPerm_eq_of_mul R _ hb R.one_mem (by simp [hqq])
    have h3 : cosetPerm R (qFour x q) hb q 3 = 1 := cosetPerm_eq_of_mul R _ hb R.one_mem (by
      simp only [qFour_three, qFour_one, mul_one]
      rw [← mul_assoc, hqq, one_mul])
    exact perm_fin4_ext (h0.trans (by decide)) (h1.trans (by decide)) (h2.trans (by decide))
      (h3.trans (by decide))
  have hδf : cosetPerm R (qFour x q) hb f = swap 2 3 := by
    have h0 : cosetPerm R (qFour x q) hb f 0 = 0 := cosetPerm_eq_of_mul R _ hb hfR (by simp)
    have h1 : cosetPerm R (qFour x q) hb f 1 = 1 := cosetPerm_eq_of_mul R _ hb hfR (hxc f)
    have h2 : cosetPerm R (qFour x q) hb f 2 = 3 := cosetPerm_eq_of_mul R _ hb hfR hfq
    have h3 : cosetPerm R (qFour x q) hb f 3 = 2 := cosetPerm_eq_of_mul R _ hb hfR (by
      simp only [qFour_three, qFour_two]
      rw [← mul_assoc, hfq, mul_assoc (q * x) f x, hxc f, ← mul_assoc, mul_assoc q x x, hxx,
        mul_one])
    exact perm_fin4_ext (h0.trans (by decide)) (h1.trans (by decide)) (h2.trans (by decide))
      (h3.trans (by decide))
  have hδK : ∀ k ∈ K, cosetPerm R (qFour x q) hb k = 1 := fun k hk =>
    Equiv.ext fun i => cosetPerm_eq_of_mul R _ hb (hKR k hk) (hKQ k hk _ (hsmem i))
  have hsx : sign x4 = 1 := sign_swap_mul_swap (by decide) (by decide)
  have hsignQ : ∀ r ∈ Q, sign (cosetPerm R (qFour x q) hb r) = 1 := by
    intro r hr
    rcases mem_Q_cases hQcard hxQ hqQ hx1 hq1 hqx hxx hr with h | h | h | h
    · rw [h, map_one, map_one]
    · rw [h, hδx]
      exact hsx
    · rw [h, hδq]
      exact sign_swap_mul_swap (by decide) (by decide)
    · rw [h, map_mul, hδq, hδx, Perm.sign_mul, hsx, sign_swap_mul_swap (by decide) (by decide)]
      rfl
  have hsδf : sign (cosetPerm R (qFour x q) hb f) = -1 := by
    rw [hδf]
    exact sign_swap (by decide)
  have hsign : ∀ c, sign (ψ c) = sign (cosetPerm R (qFour x q) hb c) := by
    intro c
    obtain ⟨q', hq', k, hk, hc | hc⟩ := exists_decomp hker KF hsf c
    · rw [hc]
      simp [map_mul, hψQ q' hq', KF.even k hk, hδK k hk, hsignQ q' hq']
    · rw [hc]
      simp [map_mul, hψQ q' hq', KF.even k hk, hδK k hk, hsignQ q' hq', hsf, hsδf]
  have hinj : ∀ c, ψ c = 1 → cosetPerm R (qFour x q) hb c = 1 → c = 1 := by
    intro c hψ hδ
    have hcQ : c ∈ Q := by rw [← hker]; exact hψ
    have h := cosetPerm_spec R (qFour x q) hb c 0
    rw [hδ, Perm.one_apply] at h
    have h' := QuotientGroup.eq.mp h
    simp at h'
    exact hRQ c h' hcQ
  exact ⟨cosetPerm R (qFour x q) hb, hδx, hsign, hinj⟩

private theorem exists_delta [Finite C] {K Q : Subgroup C} [K.Normal] {ψ : C →* Perm (Fin n)}
    (hker : ψ.ker = Q) (KF : KFacts K Q ψ) (hQcard : Nat.card Q = 4)
    (hQe : ∀ q ∈ Q, q ^ 2 = 1) (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k)
    {x : C} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hxc : ∀ c : C, c * x = x * c)
    {f q : C} (hqQ : q ∈ Q) (hq1 : q ≠ 1) (hqx : q ≠ x) (hff : f * f = 1)
    (hsf : sign (ψ f) = -1) (hfq : f * q = q * x * f) :
    ∃ δ : C →* Perm (Fin 4), δ x = x4 ∧ (∀ c, sign (ψ c) = sign (δ c)) ∧
      ∀ c, ψ c = 1 → δ c = 1 → c = 1 := by
  refine exists_delta_of_R (R := rSub K f hff) hker KF hQcard hQe hKQ hxQ hx1 hxc hqQ hq1 hqx hsf
    hfq (fun k hk => mem_rSub.mpr (Or.inl hk))
    (mem_rSub.mpr (Or.inr (by rw [hff]; exact K.one_mem))) ?_ ?_
  · intro r hr hrQ
    rcases mem_rSub.mp hr with hr | hr
    · exact KF.inter r hr hrQ
    · exfalso
      have h1 := KF.even _ hr
      have hψr : ψ r = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hrQ
      rw [map_mul, hψr, one_mul, hsf] at h1
      exact absurd h1 (by decide)
  · intro c
    obtain ⟨q', hq', k, hk, hc | hc⟩ := exists_decomp hker KF hsf c
    · exact ⟨q', hq', k, mem_rSub.mpr (Or.inl hk), hc⟩
    · refine ⟨q', hq', k * f, mem_rSub.mpr (Or.inr ?_), hc⟩
      rw [mul_assoc, hff, mul_one]
      exact hk

private theorem exists_mulEquiv_of_delta [Finite C] {ψ : C →* Perm (Fin n)}
    {δ : C →* Perm (Fin 4)} {x : C} (hxc : ∀ c : C, c * x = x * c) (hδx : δ x = x4)
    (hsign : ∀ c, sign (ψ c) = sign (δ c)) (hinj : ∀ c, ψ c = 1 → δ c = 1 → c = 1)
    (hcard : Nat.card C = 4 * n.factorial) :
    ∃ ι : C ≃* Fgrp n, ∀ c, ((ι c : Fgrp n) : Amb n) = (ψ c, δ c) := by
  have hmem : ∀ c, (ψ.prod δ) c ∈ Fgrp n := by
    intro c
    refine ⟨?_, hsign c⟩
    show δ c * x4 = x4 * δ c
    rw [← hδx, ← map_mul, ← map_mul, hxc c]
  have hι₀inj : Function.Injective ((ψ.prod δ).codRestrict (Fgrp n) hmem) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have h1 : (ψ.prod δ) c = 1 := congrArg Subtype.val hc
    have h2 := Prod.ext_iff.mp h1
    exact hinj c h2.1 h2.2
  have hbij : Function.Bijective ((ψ.prod δ).codRestrict (Fgrp n) hmem) :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨hι₀inj, by rw [hcard, card_Fgrp]⟩
  exact ⟨MulEquiv.ofBijective _ hbij, fun c => rfl⟩

end Aux

theorem exists_mulEquiv_fgrp {n : ℕ} (hn : 5 ≤ n) {C : Type*} [Group C] [Finite C]
    (K Q : Subgroup C) [K.Normal] [Q.Normal] (eK : K ≃* alternatingGroup (Fin n))
    (ψ : C →* Perm (Fin n)) (hker : ψ.ker = Q) (hrange : ψ.range = ⊤)
    (hQcard : Nat.card Q = 4) (hQe : ∀ q ∈ Q, q ^ 2 = 1) (hQab : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k)
    {x : C} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hxc : ∀ c : C, c * x = x * c)
    (hnt : ∃ c : C, ∃ q ∈ Q, c * q ≠ q * c) :
    ∃ ι : C ≃* Fgrp n, ((ι x : Fgrp n) : Amb n) = x0 n ∧
      ∀ c : C, ((ι c : Fgrp n) : Amb n).1 = ψ c := by
  have KF : KFacts K Q ψ :=
    ⟨fun k hk hkQ => eq_one_of_mem_K_of_mem_Q hn eK hKQ hk hkQ,
      fun k hk => sign_psi_eq_one_of_mem_K hn eK ψ hk,
      fun σ hσ => exists_mem_K_psi_eq hn eK ψ hker hKQ hσ⟩
  have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hrange
  obtain ⟨f, q, hqQ, hq1, hqx, hff, hsf, hfq⟩ :=
    exists_f hn hker hsurj KF hQcard hQe hKQ hQab hxQ hx1 hxc hnt
  obtain ⟨δ, hδx, hsign, hinj⟩ :=
    exists_delta hker KF hQcard hQe hKQ hxQ hx1 hxc hqQ hq1 hqx hff hsf hfq
  obtain ⟨ι, hι⟩ := exists_mulEquiv_of_delta hxc hδx hsign hinj
    (card_eq_four_mul_factorial ψ hker hrange hQcard)
  refine ⟨ι, ?_, fun c => by rw [hι c]⟩
  have hψx : ψ x = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hxQ
  rw [hι x, hψx, hδx]
  rfl

end CFSG.GH74.GLS.C3.Layer2.Model
