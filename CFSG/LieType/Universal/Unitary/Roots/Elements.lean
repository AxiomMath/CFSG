module

public import CFSG.LieType.Universal.Unitary.Roots.Monomial

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.Universal.SpecialLinear

variable {F : Type*} [Field F] {n : ℕ}

theorem rev_ne_rev_rev {b : Fin n} (hb : b ≠ Fin.rev b) : Fin.rev b ≠ Fin.rev (Fin.rev b) := by
  rw [Fin.rev_rev]
  exact hb.symm

theorem swap_apply_rev (x y s : Fin n) :
    Equiv.swap x y (Fin.rev s) = Fin.rev (Equiv.swap (Fin.rev x) (Fin.rev y) s) := by
  have := Fin.rev_injective.swap_apply (Fin.rev x) (Fin.rev y) s
  rwa [Fin.rev_rev, Fin.rev_rev] at this

theorem swap_rev_comm (b s : Fin n) :
    Equiv.swap b (Fin.rev b) (Fin.rev s) = Fin.rev (Equiv.swap b (Fin.rev b) s) := by
  rw [swap_apply_rev, Fin.rev_rev, Equiv.swap_comm]

theorem swap_mul_swap_comm {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  have hca := hac.symm
  have hda := had.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  refine Equiv.ext fun t => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hta : t = a
  · subst hta
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, *]
  by_cases htb : t = b
  · subst htb
    simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, *]
  by_cases htc : t = c
  · subst htc
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, *]
  by_cases htd : t = d
  · subst htd
    simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, *]
  simp only [Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, *]

theorem swap_mul_swap_rev_comm {a b : Fin n} (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b)
    (hba : b ≠ Fin.rev a) (s : Fin n) :
    (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) (Fin.rev s) =
      Fin.rev ((Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) s) := by
  have hab' : a ≠ Fin.rev b := fun h => hba (by rw [h, Fin.rev_rev])
  rw [Equiv.Perm.mul_apply, swap_apply_rev (Fin.rev a), Fin.rev_rev, Fin.rev_rev, swap_apply_rev,
    ← Equiv.Perm.mul_apply, swap_mul_swap_comm (Ne.symm ha) (Ne.symm hba) (Ne.symm hab')
      (Ne.symm hb)]

theorem swap_mul_swap_rev_mul_self {a b : Fin n} (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b)
    (hba : b ≠ Fin.rev a) :
    Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b) *
      (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) = 1 := by
  have hab' : a ≠ Fin.rev b := fun h => hba (by rw [h, Fin.rev_rev])
  have hc := swap_mul_swap_comm ha hab' hba hb
  rw [mul_assoc, ← mul_assoc (Equiv.swap (Fin.rev a) (Fin.rev b)), ← hc, mul_assoc,
    Equiv.swap_mul_self, mul_one, Equiv.swap_mul_self]

variable {σ : F ≃+* F}

theorem shortSign_unitary (hσ : ∀ c, σ (σ c) = c) {a b : Fin n} (hab : a ≠ b)
    (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {c : F} (hc : c ≠ 0)
    (s : Fin n) : σ (shortSign σ a b c s) * shortSign σ a b c (Fin.rev s) = 1 := by
  have h1 : Fin.rev a ≠ Fin.rev b := fun h => hab (Fin.rev_injective h)
  have h2 : a ≠ Fin.rev b := fun h => hba (by rw [h, Fin.rev_rev])
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hab' := hab.symm
  have ha' := ha.symm
  have hb' := hb.symm
  have hba' := hba.symm
  have h1' := h1.symm
  have h2' := h2.symm
  by_cases hsa : s = a
  · subst hsa
    simp only [shortSign, ite_true, ite_false, map_neg, map_inv₀, *]
    field_simp
  by_cases hsb : s = b
  · subst hsb
    simp only [shortSign, ite_true, ite_false, *]
    field_simp
  by_cases hsa' : s = Fin.rev a
  · subst hsa'
    simp only [shortSign, ite_true, ite_false, map_neg, Fin.rev_rev, *]
    field_simp
  by_cases hsb' : s = Fin.rev b
  · subst hsb'
    simp only [shortSign, ite_true, ite_false, map_inv₀, Fin.rev_rev, *]
    field_simp
  have e1 : Fin.rev s ≠ a := fun h => hsa' (by rw [← h, Fin.rev_rev])
  have e2 : Fin.rev s ≠ b := fun h => hsb' (by rw [← h, Fin.rev_rev])
  have e3 : Fin.rev s ≠ Fin.rev a := fun h => hsa (Fin.rev_injective h)
  have e4 : Fin.rev s ≠ Fin.rev b := fun h => hsb (Fin.rev_injective h)
  simp only [shortSign, ite_false, map_one, mul_one, *]

theorem longSign_unitary {b : Fin n} (hb : b ≠ Fin.rev b) {z : F} (hz : z + σ z = 0)
    (hz0 : z ≠ 0) (s : Fin n) : σ (longSign b z s) * longSign b z (Fin.rev s) = 1 := by
  have hσz : σ z = -z := by linear_combination hz
  have hb' := hb.symm
  by_cases hsb : s = b
  · subst hsb
    simp only [longSign, ite_true, ite_false, map_neg, map_inv₀, *]
    field_simp
  by_cases hsb' : s = Fin.rev b
  · subst hsb'
    simp only [longSign, ite_true, ite_false, Fin.rev_rev, *]
    field_simp
  have e1 : Fin.rev s ≠ b := fun h => hsb' (by rw [← h, Fin.rev_rev])
  have e2 : Fin.rev s ≠ Fin.rev b := fun h => hsb (Fin.rev_injective h)
  simp only [longSign, ite_false, map_one, mul_one, *]

variable (σ) (hσ : ∀ c, σ (σ c) = c)

noncomputable def shortWeyl {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (c : F) : SU σ n :=
  rootHom σ hσ hab ha hb (Multiplicative.ofAdd c) *
    rootHom σ hσ hab.symm hb ha (Multiplicative.ofAdd (-c⁻¹)) *
      rootHom σ hσ hab ha hb (Multiplicative.ofAdd c)

theorem shortWeyl_def {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b)
    (c : F) : shortWeyl σ hσ hab ha hb c =
      rootHom σ hσ hab ha hb (Multiplicative.ofAdd c) *
        rootHom σ hσ hab.symm hb ha (Multiplicative.ofAdd (-c⁻¹)) *
          rootHom σ hσ hab ha hb (Multiplicative.ofAdd c) :=
  (rfl)

theorem coe_shortWeyl {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b)
    (hba : b ≠ Fin.rev a) {c : F} (hc : c ≠ 0) :
    ((shortWeyl σ hσ hab ha hb c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      signedPerm (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) (shortSign σ a b c) := by
  simp only [shortWeyl, Subgroup.coe_mul, Units.val_mul, coe_rootHom, toAdd_ofAdd]
  exact rootMatrix_weyl hab ha hb hba hc

omit hσ in
theorem neg_inv_add_map_eq_zero {z : F} (hz : z + σ z = 0) : -z⁻¹ + σ (-z⁻¹) = 0 := by
  have hσz : σ z = -z := by linear_combination hz
  rw [map_neg, map_inv₀, hσz, inv_neg, neg_neg, neg_add_cancel]

noncomputable def longWeyl {b : Fin n} (hb : b ≠ Fin.rev b) (z : traceZero σ) : SU σ n :=
  longRootHom σ hb (Multiplicative.ofAdd z) *
    longRootHom σ (rev_ne_rev_rev hb)
      (Multiplicative.ofAdd ⟨-(z : F)⁻¹, neg_inv_add_map_eq_zero σ z.2⟩) *
      longRootHom σ hb (Multiplicative.ofAdd z)

omit hσ in
theorem longWeyl_def {b : Fin n} (hb : b ≠ Fin.rev b) (z : traceZero σ) :
    longWeyl σ hb z = longRootHom σ hb (Multiplicative.ofAdd z) *
      longRootHom σ (rev_ne_rev_rev hb)
        (Multiplicative.ofAdd ⟨-(z : F)⁻¹, neg_inv_add_map_eq_zero σ z.2⟩) *
        longRootHom σ hb (Multiplicative.ofAdd z) :=
  (rfl)

omit hσ in
theorem coe_longWeyl {b : Fin n} (hb : b ≠ Fin.rev b) {z : traceZero σ} (hz : (z : F) ≠ 0) :
    ((longWeyl σ hb z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      signedPerm (Equiv.swap b (Fin.rev b)) (longSign b (z : F)) := by
  simp only [longWeyl, Subgroup.coe_mul, Units.val_mul, coe_longRootHom, toAdd_ofAdd]
  exact longRootMatrix_weyl hb hz

@[expose] def shortTorusFun (a b : Fin n) (c : F) (s : Fin n) : F :=
  if s = a then c else if s = b then c⁻¹ else if s = Fin.rev a then (σ c)⁻¹
    else if s = Fin.rev b then σ c else 1

noncomputable def shortTorus {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (c : F) : SU σ n :=
  shortWeyl σ hσ hab ha hb c * shortWeyl σ hσ hab ha hb (-1)

theorem shortTorus_def {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b)
    (c : F) : shortTorus σ hσ hab ha hb c =
      shortWeyl σ hσ hab ha hb c * shortWeyl σ hσ hab ha hb (-1) :=
  (rfl)

theorem coe_shortTorus {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b)
    (hba : b ≠ Fin.rev a) {c : F} (hc : c ≠ 0) :
    ((shortTorus σ hσ hab ha hb c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (shortTorusFun σ a b c) := by
  rw [shortTorus, Subgroup.coe_mul, Units.val_mul, coe_shortWeyl σ hσ hab ha hb hba hc,
    coe_shortWeyl σ hσ hab ha hb hba (neg_ne_zero.mpr one_ne_zero), signedPerm_mul_signedPerm,
    swap_mul_swap_rev_mul_self ha hb hba, signedPerm_one]
  congr 1
  funext s
  have h1 : Fin.rev a ≠ Fin.rev b := fun h => hab (Fin.rev_injective h)
  have h2 : a ≠ Fin.rev b := fun h => hba (by rw [h, Fin.rev_rev])
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hab' := hab.symm
  have ha' := ha.symm
  have hb' := hb.symm
  have hba' := hba.symm
  have h1' := h1.symm
  have h2' := h2.symm
  by_cases hsa : s = a
  · subst hsa
    simp only [shortSign, shortTorusFun, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, ite_true, ite_false, *]
    simp
  by_cases hsb : s = b
  · subst hsb
    simp only [shortSign, shortTorusFun, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, ite_true, ite_false, *]
    simp
  by_cases hsa' : s = Fin.rev a
  · subst hsa'
    simp only [shortSign, shortTorusFun, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, ite_true, ite_false, *]
    simp
  by_cases hsb' : s = Fin.rev b
  · subst hsb'
    simp only [shortSign, shortTorusFun, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne, ne_eq, not_false_eq_true, ite_true, ite_false, *]
    simp
  simp only [shortSign, shortTorusFun, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, ne_eq,
    not_false_eq_true, ite_false, mul_one, *]

@[expose] def longTorusFun (b : Fin n) (e : F) (s : Fin n) : F :=
  if s = b then e else if s = Fin.rev b then e⁻¹ else 1

omit hσ in
theorem mul_add_map_mul_eq_zero {e : F} (he : σ e = e) {z : F} (hz : z + σ z = 0) :
    e * z + σ (e * z) = 0 := by
  rw [map_mul, he, ← mul_add, hz, mul_zero]

noncomputable def longTorus {b : Fin n} (hb : b ≠ Fin.rev b) (ζ : traceZero σ) {e : F}
    (he : σ e = e) : SU σ n :=
  longWeyl σ hb ⟨e * ζ, mul_add_map_mul_eq_zero σ he ζ.2⟩ * longWeyl σ hb (-ζ)

omit hσ in
theorem longTorus_def {b : Fin n} (hb : b ≠ Fin.rev b) (ζ : traceZero σ) {e : F}
    (he : σ e = e) : longTorus σ hb ζ he =
      longWeyl σ hb ⟨e * ζ, mul_add_map_mul_eq_zero σ he ζ.2⟩ * longWeyl σ hb (-ζ) :=
  (rfl)

omit hσ in
theorem coe_longTorus {b : Fin n} (hb : b ≠ Fin.rev b) {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    {e : F} (he : σ e = e) (he0 : e ≠ 0) :
    ((longTorus σ hb ζ he : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (longTorusFun b e) := by
  rw [longTorus, Subgroup.coe_mul, Units.val_mul, coe_longWeyl σ hb (mul_ne_zero he0 hζ),
    coe_longWeyl σ hb (neg_ne_zero.mpr hζ), signedPerm_mul_signedPerm, Equiv.swap_mul_self,
    signedPerm_one]
  congr 1
  funext s
  have hb' := hb.symm
  by_cases hsb : s = b
  · subst hsb
    simp only [longSign, longTorusFun, Equiv.swap_apply_left, ite_true, ite_false,
      AddSubgroup.coe_neg, *]
    field_simp
  by_cases hsb' : s = Fin.rev b
  · subst hsb'
    simp only [longSign, longTorusFun, Equiv.swap_apply_right, ite_true, ite_false,
      AddSubgroup.coe_neg, *]
    field_simp
  simp only [longSign, longTorusFun, Equiv.swap_apply_of_ne_of_ne hsb hsb', ite_false, mul_one, *]

end CFSG.LieType.Universal.Unitary
