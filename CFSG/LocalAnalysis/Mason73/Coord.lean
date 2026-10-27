module

public import CFSG.CGT.Stroth77.L4Sylow.Model

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv

variable {n : ℕ}

abbrev pv (π : Perm (Fin 4)) (e : Fin 4 → ZMod (2 ^ n)) : Fin 4 → ZMod (2 ^ n) :=
  fun i => e (π⁻¹ i)

theorem pv_one (e : Fin 4 → ZMod (2 ^ n)) : pv 1 e = e := rfl

theorem pv_mul (π σ : Perm (Fin 4)) (e : Fin 4 → ZMod (2 ^ n)) :
    pv (π * σ) e = pv π (pv σ e) := by
  funext i
  simp [pv, mul_inv_rev, Perm.mul_apply]

theorem pv_add (π : Perm (Fin 4)) (e f : Fin 4 → ZMod (2 ^ n)) :
    pv π (e + f) = pv π e + pv π f := rfl

theorem sum_pv (π : Perm (Fin 4)) (e : Fin 4 → ZMod (2 ^ n)) : ∑ i, pv π e i = ∑ i, e i :=
  Equiv.sum_comp π⁻¹ e

@[expose] def IsConst (e : Fin 4 → ZMod (2 ^ n)) : Prop := ∀ i j, e i = e j

theorem isConst_pv_iff (π : Perm (Fin 4)) (e : Fin 4 → ZMod (2 ^ n)) :
    IsConst (pv π e) ↔ IsConst e := by
  constructor
  · intro h i j
    have := h (π i) (π j)
    simpa [pv] using this
  · intro h i j
    exact h _ _

@[expose] def sgnH (π : Fin81.R0) : ZMod (2 ^ n) :=
  Multiplicative.toAdd (signZ n (Perm.sign (π : Perm (Fin 4))))

@[expose] def detSum (d : Fin 4 → ZMod (2 ^ n)) (π : Fin81.R0) : Prop := ∑ i, d i + sgnH π = 0

abbrev hat (d : Fin 4 → ZMod (2 ^ n)) (π : Fin81.R0) : L4Hat n := ⟨Multiplicative.ofAdd d, π⟩

theorem hat_mul (d e : Fin 4 → ZMod (2 ^ n)) (π σ : Fin81.R0) :
    hat d π * hat e σ = hat (d + pv (π : Perm (Fin 4)) e) (π * σ) := rfl

theorem hat_mem_L4P {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} :
    hat d π ∈ L4P n ↔ detSum d π := by
  rw [mem_L4P, ← Multiplicative.toAdd.injective.eq_iff, detL4_apply]
  rfl

theorem hat_left (a : L4Hat n) : hat (Multiplicative.toAdd a.left) a.right = a := rfl

instance instFiniteL4Hat : Finite (L4Hat n) :=
  Nat.finite_of_card_ne_zero (by rw [card_L4Hat]; positivity)

instance instFiniteL4Model : Finite (L4Model n) := inferInstance

@[expose] def el (d : Fin 4 → ZMod (2 ^ n)) (π : Fin81.R0) (h : detSum d π) : L4Model n :=
  QuotientGroup.mk ⟨hat d π, hat_mem_L4P.2 h⟩

theorem detSum_mul {d e : Fin 4 → ZMod (2 ^ n)} {π σ : Fin81.R0} (h : detSum d π)
    (h' : detSum e σ) : detSum (d + pv (π : Perm (Fin 4)) e) (π * σ) := by
  have := (L4P n).mul_mem (hat_mem_L4P.2 h) (hat_mem_L4P.2 h')
  rw [hat_mul] at this
  exact hat_mem_L4P.1 this

theorem el_mul {d e : Fin 4 → ZMod (2 ^ n)} {π σ : Fin81.R0} (h : detSum d π)
    (h' : detSum e σ) :
    el d π h * el e σ h' = el (d + pv (π : Perm (Fin 4)) e) (π * σ) (detSum_mul h h') := rfl

theorem exists_eq_el (g : L4Model n) :
    ∃ (d : Fin 4 → ZMod (2 ^ n)) (π : Fin81.R0) (h : detSum d π), g = el d π h := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨Multiplicative.toAdd a.left, a.right, hat_mem_L4P.1 ha, rfl⟩

theorem detSum_zero_one : detSum (0 : Fin 4 → ZMod (2 ^ n)) 1 := by
  simp [detSum, sgnH, signZ]

theorem el_zero_one : el (0 : Fin 4 → ZMod (2 ^ n)) 1 detSum_zero_one = 1 := rfl

theorem el_eq_el_iff (hn : 2 ≤ n) {d e : Fin 4 → ZMod (2 ^ n)} {π σ : Fin81.R0}
    (h : detSum d π) (h' : detSum e σ) :
    el d π h = el e σ h' ↔ π = σ ∧ IsConst (e - d) := by
  rw [el, el, QuotientGroup.eq, mem_zpowers_cL4 hn]
  have hinv : (hat d π)⁻¹ * hat e σ =
      hat (pv ((π : Perm (Fin 4))⁻¹) (e - d)) (π⁻¹ * σ) := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, toAdd_mul, toAdd_inv,
        Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
      rw [toAdd_actL4, toAdd_actL4]
      simp only [toAdd_ofAdd, Pi.neg_apply, pv, Pi.sub_apply, toAdd_inv,
        SemidirectProduct.inv_right, InvMemClass.coe_inv, inv_inv]
      ring
    · rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hinv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (isConst_pv_iff _ _).1 fun i j => h2 i j⟩
    have : π⁻¹ * σ = 1 := h1
    exact (inv_mul_eq_one.mp this)
  · rintro ⟨rfl, h2⟩
    exact ⟨inv_mul_cancel π, fun i j => (isConst_pv_iff _ _).2 h2 i j⟩

@[expose] def piP : L4P n →* Fin81.R0 :=
  (SemidirectProduct.rightHom).comp (L4P n).subtype

theorem zpowers_cL4_le_ker_piP : Subgroup.zpowers (cL4 n) ≤ (piP (n := n)).ker := by
  rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
  rfl

@[expose] def piT : L4Model n →* Fin81.R0 :=
  QuotientGroup.lift _ piP zpowers_cL4_le_ker_piP

theorem piT_el {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π) : piT (el d π h) = π :=
  rfl

@[expose] def A (n : ℕ) : Subgroup (L4Model n) := (piT (n := n)).ker

theorem mem_A_iff {g : L4Model n} : g ∈ A n ↔ piT g = 1 := MonoidHom.mem_ker

theorem el_mem_A {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π) :
    el d π h ∈ A n ↔ π = 1 := by
  rw [mem_A_iff, piT_el]

theorem detSum_one_iff {d : Fin 4 → ZMod (2 ^ n)} : detSum d 1 ↔ ∑ i, d i = 0 := by
  simp [detSum, sgnH, signZ]

theorem A_comm {g g' : L4Model n} (hg : g ∈ A n) (hg' : g' ∈ A n) : g * g' = g' * g := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  obtain ⟨e, σ, h', rfl⟩ := exists_eq_el g'
  rw [el_mem_A] at hg hg'
  subst hg hg'
  rw [el_mul, el_mul]
  congr 1
  simp only [OneMemClass.coe_one, pv_one]
  exact add_comm d e

theorem exists_detSum (π : Fin81.R0) : ∃ d : Fin 4 → ZMod (2 ^ n), detSum d π := by
  refine ⟨Pi.single 0 (-sgnH π), ?_⟩
  simp [detSum]

theorem piT_surjective : Function.Surjective (piT (n := n)) := by
  intro π
  obtain ⟨d, h⟩ := exists_detSum (n := n) π
  exact ⟨el d π h, rfl⟩

theorem card_A (hn : 2 ≤ n) : Nat.card (A n) = 2 ^ (3 * n - 2) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (piT_surjective (n := n))
  rw [card_L4Model hn, Fin81.card_R0] at h
  have h2 : 2 ^ (3 * n + 1) = 2 ^ (3 * n - 2) * 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

end CFSG.LocalAnalysis.Mason73
