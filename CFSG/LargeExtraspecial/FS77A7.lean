module

public import CFSG.LargeExtraspecial.FS77Core
public import CFSG.LargeExtraspecial.FS77Orth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

@[expose] noncomputable def emb6 (e : Fin 6 → V) : V6 →ₗ[ZMod 2] V :=
  Fintype.linearCombination (ZMod 2) e

theorem emb6_apply (e : Fin 6 → V) (v : V6) :
    emb6 e v = v 0 • e 0 + v 1 • e 1 + v 2 • e 2 + v 3 • e 3 + v 4 • e 4 + v 5 • e 5 := by
  rw [emb6, Fintype.linearCombination_apply, Fin.sum_univ_six]

section Sextuple

variable {e : Fin 6 → V} (hq : ∀ i, q (e i) = orthQv6 i)
  (hB : ∀ i j, polar q (e i) (e j) = orthBm6 i j)

include hB in
theorem polar_emb6_basis (v : V6) (j : Fin 6) :
    polar q (emb6 e v) (e j) = polar6 v (Pi.single j 1) := by
  rw [emb6_apply]
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hB, smul_eq_mul]
  fin_cases j <;> simp [orthBm6, polar6]

include hB in
theorem polar_emb6 (v w : V6) : polar q (emb6 e v) (emb6 e w) = polar6 v w := by
  conv_lhs => rw [emb6_apply e w]
  simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, polar_emb6_basis hB,
    smul_eq_mul]
  simp only [polar6, Pi.single_apply]
  simp
  ring

include hq hB in
theorem q_emb6 (v : V6) : q (emb6 e v) = q6 v := by
  rw [emb6_apply]
  simp only [QuadraticMap.map_add (⇑q), QuadraticMap.map_smul, QuadraticMap.polar_add_left,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hq, hB, smul_eq_mul]
  simp [orthQv6, orthBm6, q6]
  linear_combination Core.zmod2_mul_self (v 4) + Core.zmod2_mul_self (v 5)

end Sextuple

@[expose] def sVec : Fin 3 → V6 :=
  ![Pi.single 2 1, Pi.single 0 1 + Pi.single 2 1, Pi.single 0 1]

@[expose] def uVec : Fin 3 → V6 :=
  ![Pi.single 0 1 + Pi.single 5 1, Pi.single 4 1, Pi.single 4 1 + Pi.single 5 1]

@[expose] def eich6 (s u v : V6) : V6 := v + polar6 v s • u - (polar6 v u + q6 u * polar6 v s) • s

theorem eich6_eq_tLin (k : Fin 3) (v : V6) : eich6 (sVec k) (uVec k) v = tLin k v := by
  revert v
  fin_cases k <;> decide +kernel

theorem q6_sVec (k : Fin 3) : q6 (sVec k) = 0 := by
  fin_cases k <;> decide +kernel

theorem polar6_sVec_uVec (k : Fin 3) : polar6 (sVec k) (uVec k) = 0 := by
  fin_cases k <;> decide +kernel

@[expose] noncomputable def tEich (e : Fin 6 → V) (k : Fin 3) : V ≃ₗ[ZMod 2] V :=
  eichler q (emb6 e (sVec k)) (emb6 e (uVec k))

@[expose] noncomputable def tEichProd (e : Fin 6 → V) : List (Fin 3) → V ≃ₗ[ZMod 2] V
  | [] => 1
  | k :: ks => tEich (q := q) e k * tEichProd e ks

section Sextuple

variable {e : Fin 6 → V} (hq : ∀ i, q (e i) = orthQv6 i)
  (hB : ∀ i j, polar q (e i) (e j) = orthBm6 i j)

include hq hB in
theorem q_emb6_sVec (k : Fin 3) : q (emb6 e (sVec k)) = 0 := by
  rw [q_emb6 hq hB, q6_sVec]

include hB in
theorem polar_emb6_sVec_uVec (k : Fin 3) :
    polar q (emb6 e (sVec k)) (emb6 e (uVec k)) = 0 := by
  rw [polar_emb6 hB, polar6_sVec_uVec]

include hq hB in
theorem tEich_emb6 (k : Fin 3) (v : V6) :
    tEich (q := q) e k (emb6 e v) = emb6 e (tLin k v) := by
  rw [tEich, eichler_apply (q_emb6_sVec hq hB k) (polar_emb6_sVec_uVec hB k), polar_emb6 hB,
    polar_emb6 hB, q_emb6 hq hB, ← eich6_eq_tLin, eich6, map_sub, map_add, map_smul, map_smul]

theorem polar_emb6_right_of_perp {x : V} (hx : ∀ i, polar q x (e i) = 0) (w : V6) :
    polar q x (emb6 e w) = 0 := by
  rw [emb6_apply]
  simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hx, smul_zero, add_zero]

theorem tEich_of_perp (k : Fin 3) {x : V} (hx : ∀ i, polar q x (e i) = 0) :
    tEich (q := q) e k x = x :=
  eichler_apply_of_polar_eq_zero (polar_emb6_right_of_perp hx _) (polar_emb6_right_of_perp hx _)

include hq hB in
theorem tEichProd_emb6 (ω : List (Fin 3)) (v : V6) :
    tEichProd (q := q) e ω (emb6 e v) = emb6 e (tComp ω v) := by
  induction ω with
  | nil => rfl
  | cons k ks ih => rw [tEichProd, LinearEquiv.mul_apply, ih, tEich_emb6 hq hB]; rfl

theorem tEichProd_of_perp (ω : List (Fin 3)) {x : V} (hx : ∀ i, polar q x (e i) = 0) :
    tEichProd (q := q) e ω x = x := by
  induction ω with
  | nil => rfl
  | cons k ks ih => rw [tEichProd, LinearEquiv.mul_apply, ih, tEich_of_perp k hx]

@[expose] def partner : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

theorem polar6_single (c : V6) (j : Fin 6) : polar6 c (Pi.single j 1) = c (partner j) := by
  fin_cases j <;> simp [polar6, partner]

theorem partner_partner (j : Fin 6) : partner (partner j) = j := by
  fin_cases j <;> rfl

include hB in
theorem exists_decomp (x : V) :
    ∃ c : V6, ∃ y : V, x = emb6 e c + y ∧ ∀ i, polar q y (e i) = 0 := by
  refine ⟨fun i => polar q x (e (partner i)), x - emb6 e (fun i => polar q x (e (partner i))),
    by abel, fun j => ?_⟩
  rw [QuadraticMap.polar_sub_left, polar_emb6_basis hB, polar6_single, partner_partner, sub_self]

include hq hB in
theorem tEichProd_eq_one (ω : List (Fin 3)) (hω : ∀ v, tComp ω v = v) :
    tEichProd (q := q) e ω = 1 := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨c, y, rfl, hy⟩ := exists_decomp hB x
  rw [map_add, tEichProd_emb6 hq hB, hω, tEichProd_of_perp ω hy]
  rfl

end Sextuple

end CFSG.LargeExtraspecial.FS77
