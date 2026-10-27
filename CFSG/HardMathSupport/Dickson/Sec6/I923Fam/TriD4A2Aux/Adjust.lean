module

public import CFSG.GH74.GLS.SP.GlueDefs

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped Pointwise

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

variable {X : Type*} [Group X] {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem conjBy_eq_of_mem_H (R : RGD2 n H r₁ r₂ U root) {a : X} (ha : a ∈ H) {j : ℤ}
    (hj : IsRoot n j) : conjBy a (root j) = root j := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro h
    have := R.invariant j hj a⁻¹ (H.inv_mem ha) _ h
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at this
  · intro h
    exact R.invariant j hj a ha x h

theorem conjBy_inv_mul_eq (R : RGD2 n H r₁ r₂ U root) {a : X} (ha : a ∈ H) (r : X) {j : ℤ}
    (hj : IsRoot n j) : conjBy (r * a)⁻¹ (root j) = conjBy r⁻¹ (root j) := by
  rw [mul_inv_rev, conjBy_mul, conjBy_eq_of_mem_H R (H.inv_mem ha) hj]

theorem exists_lift_mem {S : Subgroup X} {A B : Subgroup X} (hA : A ≠ ⊥) (hAS : A ≤ S)
    (hBS : B ≤ S) {r : X}
    (hr : ∀ y ∈ A, y ≠ 1 → y ∈ (B : Set X) * (H : Set X) * {r} * (B : Set X)) :
    ∃ h ∈ H, h * r ∈ S := by
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨z, hz, x', hx', hyz⟩ := Set.mem_mul.1 (hr y hy hy1')
  obtain ⟨w, hw, rr, hrr, hzw⟩ := Set.mem_mul.1 hz
  obtain ⟨x, hx, h, hh, hwx⟩ := Set.mem_mul.1 hw
  rw [Set.mem_singleton_iff] at hrr
  subst hrr
  refine ⟨h, hh, ?_⟩
  have e : h * rr = x⁻¹ * y * x'⁻¹ := by
    rw [← hyz, ← hzw, ← hwx]
    group
  rw [e]
  exact S.mul_mem (S.mul_mem (S.inv_mem (hBS hx)) (hAS hy)) (S.inv_mem (hBS hx'))

theorem rank_adjust {S : Subgroup X} {A B : Subgroup X} (hAS : A ≤ S) (hBS : B ≤ S) {r a : X}
    (ha : a ∈ H) (hS : a * r ∈ S)
    (hr : ∀ y ∈ A, y ≠ 1 → y ∈ (B : Set X) * (H : Set X) * {r} * (B : Set X)) :
    ∀ y ∈ A, y ≠ 1 → y ∈ (B : Set X) * ((H ⊓ S : Subgroup X) : Set X) * {a * r} * (B : Set X) := by
  intro y hy hy1
  obtain ⟨z, hz, x', hx', hyz⟩ := Set.mem_mul.1 (hr y hy hy1)
  obtain ⟨w, hw, rr, hrr, hzw⟩ := Set.mem_mul.1 hz
  obtain ⟨x, hx, h, hh, hwx⟩ := Set.mem_mul.1 hw
  rw [Set.mem_singleton_iff] at hrr
  subst hrr
  have hy' : y = x * (h * a⁻¹) * (a * rr) * x' := by
    rw [← hyz, ← hzw, ← hwx]
    group
  have hmem : h * a⁻¹ ∈ S := by
    have e : h * a⁻¹ = x⁻¹ * y * x'⁻¹ * (a * rr)⁻¹ := by
      rw [hy']
      group
    rw [e]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.inv_mem (hBS hx)) (hAS hy)) (S.inv_mem (hBS hx')))
      (S.inv_mem hS)
  refine Set.mem_mul.2 ⟨x * (h * a⁻¹) * (a * rr), ?_, x', hx', hy'.symm⟩
  refine Set.mem_mul.2 ⟨x * (h * a⁻¹), ?_, a * rr, Set.mem_singleton _, rfl⟩
  exact Set.mem_mul.2 ⟨x, hx, h * a⁻¹, ⟨H.mul_mem hh (H.inv_mem ha), hmem⟩, rfl⟩


theorem w_pow_conj_mem (R : RGD2 n H r₁ r₂ U root) (k : ℕ) {c : X} (hc : c ∈ H) :
    (r₁ * r₂) ^ k * c * ((r₁ * r₂) ^ k)⁻¹ ∈ H := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    have e : (r₁ * r₂) ^ (k + 1) * c * ((r₁ * r₂) ^ (k + 1))⁻¹ =
        r₁ * (r₂ * ((r₁ * r₂) ^ k * c * ((r₁ * r₂) ^ k)⁻¹) * r₂⁻¹) * r₁⁻¹ := by
      rw [pow_succ']
      generalize (r₁ * r₂) ^ k = wk
      group
    rw [e]
    exact R.conj_H₁ _ (R.conj_H₂ _ ih)

theorem adjust_pow_eq (R : RGD2 n H r₁ r₂ U root) {a b : X} (ha : a ∈ H) (hb : b ∈ H) (k : ℕ) :
    ∃ h ∈ H, ((r₁ * a) * (r₂ * b)) ^ k = h * (r₁ * r₂) ^ k := by
  have hc₀ : r₁ * (a * (r₂ * b * r₂⁻¹)) * r₁⁻¹ ∈ H :=
    R.conj_H₁ _ (H.mul_mem ha (R.conj_H₂ b hb))
  induction k with
  | zero => exact ⟨1, H.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨h, hh, hk⟩ := ih
    refine ⟨h * ((r₁ * r₂) ^ k * (r₁ * (a * (r₂ * b * r₂⁻¹)) * r₁⁻¹) * ((r₁ * r₂) ^ k)⁻¹),
      H.mul_mem hh (w_pow_conj_mem R k hc₀), ?_⟩
    rw [pow_succ, hk, pow_succ]
    have e : (r₁ * a) * (r₂ * b) =
        (r₁ * (a * (r₂ * b * r₂⁻¹)) * r₁⁻¹) * (r₁ * r₂) := by group
    rw [e]
    generalize (r₁ * r₂) ^ k = wk
    group

theorem isRoot_pos {n : ℕ} {k : ℤ} (h1 : 1 ≤ k) (h2 : k ≤ n) : IsRoot n k :=
  ⟨by omega, by omega⟩

theorem isRoot_neg {n : ℕ} {k : ℤ} (h1 : 1 ≤ k) (h2 : k ≤ n) : IsRoot n (-k) :=
  ⟨by omega, by omega⟩

theorem rgd2_adjust (R : RGD2 n H r₁ r₂ U root) (S : Subgroup X) [S.Normal]
    (hroot : ∀ i, IsRoot n i → root i ≤ S) :
    ∃ a ∈ H, ∃ b ∈ H, r₁ * a ∈ S ∧ r₂ * b ∈ S ∧
      RGD2 n (H ⊓ S) (r₁ * a) (r₂ * b) U root := by
  have h3 := R.three_le
  have hI1 : IsRoot n 1 := isRoot_pos le_rfl (by omega)
  have hIn : IsRoot n n := isRoot_pos (by omega) le_rfl
  have hIm1 : IsRoot n (-1) := by simpa using isRoot_neg (n := n) (k := 1) le_rfl (by omega)
  have hImn : IsRoot n (-(n : ℤ)) := isRoot_neg (by omega) le_rfl
  have hU : U ≤ S := by
    intro u hu
    have : u ∈ chainProd root (intList 1 n) := by rw [← R.carrier_eq]; exact hu
    exact chainProd_subset root S (intList 1 n) (fun k hk => hroot k (isRoot_pos
      (mem_intList_iff.1 hk).1 (mem_intList_iff.1 hk).2)) this
  obtain ⟨h₁, hh₁, hS₁⟩ := exists_lift_mem (S := S) (R.ne_bot _ hIm1) (hroot _ hIm1)
    (hroot _ hI1) R.rank₁
  obtain ⟨h₂, hh₂, hS₂⟩ := exists_lift_mem (S := S) (R.ne_bot _ hImn) (hroot _ hImn)
    (hroot _ hIn) R.rank₂
  set a : X := r₁⁻¹ * h₁ * r₁ with ha_def
  set b : X := r₂⁻¹ * h₂ * r₂ with hb_def
  have haH : a ∈ H := by
    have := R.conj_H₁' hh₁
    exact this
  have hbH : b ∈ H := R.conj_H₂' hh₂
  have e₁ : r₁ * a = h₁ * r₁ := by rw [ha_def]; group
  have e₂ : r₂ * b = h₂ * r₂ := by rw [hb_def]; group
  have hr₁S : r₁ * a ∈ S := by rw [e₁]; exact hS₁
  have hr₂S : r₂ * b ∈ S := by rw [e₂]; exact hS₂
  refine ⟨a, haH, b, hbH, hr₁S, hr₂S, ?_⟩
  refine ⟨R.three_le, fun x hx y hy => R.comm_H x hx.1 y hy.1, R.nilpotent, ?_, ?_, ?_, ?_, ?_,
    ?_, R.ne_bot, fun i hi h hh x hx => R.invariant i hi h hh.1 x hx, R.carrier_eq, R.unique,
    R.reverse_eq, R.subgroup, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h' hh'
    refine ⟨?_, S.mul_mem (S.mul_mem hr₁S hh'.2) (S.inv_mem hr₁S)⟩
    have e : r₁ * a * h' * (r₁ * a)⁻¹ = r₁ * (a * h' * a⁻¹) * r₁⁻¹ := by group
    rw [e]
    exact R.conj_H₁ _ (H.mul_mem (H.mul_mem haH hh'.1) (H.inv_mem haH))
  ·
    intro h' hh'
    refine ⟨?_, S.mul_mem (S.mul_mem hr₂S hh'.2) (S.inv_mem hr₂S)⟩
    have e : r₂ * b * h' * (r₂ * b)⁻¹ = r₂ * (b * h' * b⁻¹) * r₂⁻¹ := by group
    rw [e]
    exact R.conj_H₂ _ (H.mul_mem (H.mul_mem hbH hh'.1) (H.inv_mem hbH))
  ·
    refine ⟨?_, S.mul_mem hr₁S hr₁S⟩
    have e : r₁ * a * (r₁ * a) = (r₁ * a * r₁⁻¹) * (r₁ * r₁) * a := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (R.conj_H₁ a haH) R.sq₁) haH
  ·
    refine ⟨?_, S.mul_mem hr₂S hr₂S⟩
    have e : r₂ * b * (r₂ * b) = (r₂ * b * r₂⁻¹) * (r₂ * r₂) * b := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (R.conj_H₂ b hbH) R.sq₂) hbH
  ·
    refine ⟨?_, S.pow_mem (S.mul_mem hr₁S hr₂S) n⟩
    obtain ⟨h, hh, he⟩ := adjust_pow_eq R haH hbH n
    rw [he]
    exact H.mul_mem hh R.pow
  ·
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ U ⊓ H := ⟨hx.1, hx.2.1⟩
    rw [R.U_inf_H] at this
    exact this
  ·
    obtain ⟨a1, a2, a3⟩ := R.act₁
    refine ⟨?_, ?_, fun i hi1 hi2 => ?_⟩
    · rw [conjBy_inv_mul_eq R haH r₁ hI1]; exact a1
    · rw [conjBy_inv_mul_eq R haH r₁ hIm1]; exact a2
    · obtain ⟨b1, b2⟩ := a3 i hi1 hi2
      refine ⟨?_, ?_⟩
      · rw [conjBy_inv_mul_eq R haH r₁ (isRoot_pos (by omega) hi2)]; exact b1
      · rw [conjBy_inv_mul_eq R haH r₁ (isRoot_neg (by omega) hi2)]; exact b2
  ·
    obtain ⟨a1, a2, a3⟩ := R.act₂
    refine ⟨?_, ?_, fun i hi1 hi2 => ?_⟩
    · rw [conjBy_inv_mul_eq R hbH r₂ hIn]; exact a1
    · rw [conjBy_inv_mul_eq R hbH r₂ hImn]; exact a2
    · obtain ⟨b1, b2⟩ := a3 i hi1 hi2
      refine ⟨?_, ?_⟩
      · rw [conjBy_inv_mul_eq R hbH r₂ (isRoot_pos hi1 (by omega))]; exact b1
      · rw [conjBy_inv_mul_eq R hbH r₂ (isRoot_neg hi1 (by omega))]; exact b2
  ·
    intro x hx hneg
    exact R.meet_one x (sup_le_sup_right inf_le_left U hx) hneg
  ·
    rw [e₁]
    exact rank_adjust (hroot _ hIm1) (hroot _ hI1) hh₁ hS₁ R.rank₁
  ·
    rw [e₂]
    exact rank_adjust (hroot _ hImn) (hroot _ hIn) hh₂ hS₂ R.rank₂

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
