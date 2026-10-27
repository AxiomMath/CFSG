module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.Universal.SpecialLinear

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

theorem rootMatrix_mulVec (i j : Fin n) (c : F) (v : Fin n → F) :
    rootMatrix σ i j c *ᵥ v =
      v + Pi.single i (c * v j) - Pi.single (Fin.rev j) (σ c * v (Fin.rev i)) := by
  rw [rootMatrix, sub_mulVec, add_mulVec, one_mulVec, single_mulVec, single_mulVec]
  rfl

theorem longRootMatrix_mulVec (i : Fin n) (c : F) (v : Fin n → F) :
    longRootMatrix i c *ᵥ v = v + Pi.single i (c * v (Fin.rev i)) := by
  rw [longRootMatrix, add_mulVec, one_mulVec, single_mulVec]
  rfl

theorem heisenbergMatrix_mulVec (i k : Fin n) (a b : F) (v : Fin n → F) :
    heisenbergMatrix σ i k a b *ᵥ v =
      v + Pi.single i (a * v k) - Pi.single k (σ a * v (Fin.rev i)) +
        Pi.single i (b * v (Fin.rev i)) := by
  rw [heisenbergMatrix, add_mulVec, sub_mulVec, add_mulVec, one_mulVec, single_mulVec,
    single_mulVec, single_mulVec]
  rfl

omit σ in
theorem signedPerm_mulVec_single (π : Equiv.Perm (Fin n)) (d : Fin n → F) (s : Fin n) (c : F) :
    signedPerm π d *ᵥ Pi.single s c = Pi.single (π s) (d s * c) := by
  funext r
  rw [mulVec_single]
  simp [signedPerm_apply, Pi.single_apply, col]

omit σ in
theorem eq_signedPerm_of_mulVec_single {M : Matrix (Fin n) (Fin n) F} (π : Equiv.Perm (Fin n))
    (d : Fin n → F) (h : ∀ s, M *ᵥ Pi.single s 1 = Pi.single (π s) (d s)) :
    M = signedPerm π d := by
  refine ext_of_mulVec_single fun s => ?_
  rw [h, signedPerm_mulVec_single, mul_one]

omit σ in
theorem signedPerm_mul_single_eq (π : Equiv.Perm (Fin n)) {d : Fin n → F} (i j : Fin n)
    (hd : d j ≠ 0) (c : F) :
    signedPerm π d * single i j c = single (π i) (π j) (d i * c * (d j)⁻¹) * signedPerm π d := by
  rw [signedPerm_mul_single, single_mul_signedPerm, Equiv.symm_apply_apply,
    inv_mul_cancel_right₀ hd]

variable {σ}

theorem ne_zero_of_unitary {d : Fin n → F} (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (s : Fin n) :
    d s ≠ 0 := by
  intro h
  have := hd (Fin.rev s)
  rw [Fin.rev_rev, h, mul_zero] at this
  exact zero_ne_one this

theorem map_eq_inv_of_unitary {d : Fin n → F} (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    (s : Fin n) : σ (d s) = (d (Fin.rev s))⁻¹ :=
  eq_inv_of_mul_eq_one_left (hd s)

theorem signedPerm_mul_rootMatrix {π : Equiv.Perm (Fin n)}
    (hπ : ∀ s, π (Fin.rev s) = Fin.rev (π s)) {d : Fin n → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (i j : Fin n) (c : F) :
    signedPerm π d * rootMatrix σ i j c =
      rootMatrix σ (π i) (π j) (d i * c * (d j)⁻¹) * signedPerm π d := by
  have h0 := ne_zero_of_unitary hd
  rw [rootMatrix, rootMatrix, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul,
    Matrix.add_mul, Matrix.one_mul, signedPerm_mul_single_eq π i j (h0 j),
    signedPerm_mul_single_eq π _ _ (h0 _), hπ, hπ, map_mul, map_mul, map_inv₀,
    map_eq_inv_of_unitary hd, map_eq_inv_of_unitary hd]
  congr 3
  field_simp [h0 (Fin.rev i), h0 (Fin.rev j)]

theorem signedPerm_mul_longRootMatrix {π : Equiv.Perm (Fin n)}
    (hπ : ∀ s, π (Fin.rev s) = Fin.rev (π s)) {d : Fin n → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (i : Fin n) (c : F) :
    signedPerm π d * longRootMatrix i c =
      longRootMatrix (π i) (d i * c * (d (Fin.rev i))⁻¹) * signedPerm π d := by
  have h0 := ne_zero_of_unitary hd
  rw [longRootMatrix, longRootMatrix, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
    Matrix.one_mul, signedPerm_mul_single_eq π _ _ (h0 _), hπ]

theorem mul_mem_traceZero_of_unitary {d : Fin n → F} (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    (i : Fin n) {c : F} (hc : c + σ c = 0) :
    d i * c * (d (Fin.rev i))⁻¹ + σ (d i * c * (d (Fin.rev i))⁻¹) = 0 := by
  have h0 := ne_zero_of_unitary hd
  have hσc : σ c = -c := by linear_combination hc
  rw [map_mul, map_mul, map_inv₀, map_eq_inv_of_unitary hd, map_eq_inv_of_unitary hd,
    Fin.rev_rev, hσc]
  field_simp [h0 i, h0 (Fin.rev i)]
  ring

theorem signedPerm_mul_heisenbergMatrix {π : Equiv.Perm (Fin n)}
    (hπ : ∀ s, π (Fin.rev s) = Fin.rev (π s)) {d : Fin n → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (i : Fin n) {k : Fin n} (hk : Fin.rev k = k)
    (hπk : π k = k) (a b : F) :
    signedPerm π d * heisenbergMatrix σ i k a b =
      heisenbergMatrix σ (π i) k (d i * a * (d k)⁻¹) (d i * b * (d (Fin.rev i))⁻¹) *
        signedPerm π d := by
  have h0 := ne_zero_of_unitary hd
  rw [heisenbergMatrix, heisenbergMatrix, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_add,
    Matrix.mul_one, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul,
    signedPerm_mul_single_eq π _ _ (h0 _), signedPerm_mul_single_eq π _ _ (h0 _),
    signedPerm_mul_single_eq π _ _ (h0 _), hπ, hπk, map_mul, map_mul, map_inv₀,
    map_eq_inv_of_unitary hd, map_eq_inv_of_unitary hd, hk]
  congr 3
  field_simp [h0 (Fin.rev i), h0 k]

theorem heisenberg_rel_of_unitary {d : Fin n → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (i : Fin n) {k : Fin n} (hk : Fin.rev k = k)
    {a b : F} (hab : b + σ b + σ a * a = 0) :
    d i * b * (d (Fin.rev i))⁻¹ + σ (d i * b * (d (Fin.rev i))⁻¹) +
      σ (d i * a * (d k)⁻¹) * (d i * a * (d k)⁻¹) = 0 := by
  have h0 := ne_zero_of_unitary hd
  simp only [map_mul, map_inv₀, map_eq_inv_of_unitary hd, Fin.rev_rev, hk]
  have hσb : σ b = -b - σ a * a := by linear_combination hab
  rw [hσb]
  field_simp [h0 i, h0 (Fin.rev i), h0 k]
  ring

theorem signedPerm_congr {π π' : Equiv.Perm (Fin n)} {d d' : Fin n → F} (hπ : ∀ s, π s = π' s)
    (hd : ∀ s, d s = d' s) : signedPerm π d = signedPerm π' d' := by
  rw [Equiv.ext hπ, funext hd]

theorem signedPerm_comm_of_disjoint {π₁ π₂ : Equiv.Perm (Fin n)} {d₁ d₂ : Fin n → F}
    (P₁ P₂ : Fin n → Prop) (h₁ : ∀ s, ¬P₁ s → π₁ s = s ∧ d₁ s = 1)
    (h₂ : ∀ s, ¬P₂ s → π₂ s = s ∧ d₂ s = 1) (h₁' : ∀ s, P₁ s → P₁ (π₁ s))
    (h₂' : ∀ s, P₂ s → P₂ (π₂ s)) (hdisj : ∀ s, P₁ s → ¬P₂ s) :
    signedPerm π₁ d₁ * signedPerm π₂ d₂ = signedPerm π₂ d₂ * signedPerm π₁ d₁ := by
  rw [signedPerm_mul_signedPerm, signedPerm_mul_signedPerm]
  refine signedPerm_congr (fun s => ?_) (fun s => ?_)
  · simp only [Equiv.Perm.mul_apply]
    by_cases hs : P₁ s
    · rw [(h₂ s (hdisj s hs)).1, (h₂ _ (hdisj _ (h₁' s hs))).1]
    · rw [(h₁ s hs).1]
      by_cases hs' : P₂ s
      · rw [(h₁ _ fun h => hdisj _ h (h₂' s hs')).1]
      · rw [(h₂ s hs').1, (h₁ s hs).1]
  · by_cases hs : P₁ s
    · rw [(h₂ s (hdisj s hs)).1, (h₂ s (hdisj s hs)).2, (h₂ _ (hdisj _ (h₁' s hs))).2, mul_one,
        one_mul]
    · rw [(h₁ s hs).1, (h₁ s hs).2]
      by_cases hs' : P₂ s
      · rw [(h₁ _ fun h => hdisj _ h (h₂' s hs')).2, one_mul, mul_one]
      · rw [(h₂ s hs').1, (h₂ s hs').2, (h₁ s hs).2]

local macro "mono_simp" : tactic => `(tactic| simp only [rootMatrix_mulVec, longRootMatrix_mulVec,
  heisenbergMatrix_mulVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply, Pi.single_zero, ite_true,
  ite_false, mul_zero, mul_one, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero,
  Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
  Equiv.swap_apply_of_ne_of_ne, Fin.rev_rev, ne_eq, not_false_eq_true, *])

local macro "vec_ext" : tactic => `(tactic| (
    funext r
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> simp_all <;> field_simp))

variable (σ) in
@[expose] def shortSign (a b : Fin n) (c : F) (s : Fin n) : F :=
  if s = a then -c⁻¹ else if s = b then c else if s = Fin.rev a then -σ c
    else if s = Fin.rev b then (σ c)⁻¹ else 1

theorem rootMatrix_weyl {a b : Fin n} (hab : a ≠ b)
    (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {c : F} (hc : c ≠ 0) :
    rootMatrix σ a b c * rootMatrix σ b a (-c⁻¹) * rootMatrix σ a b c =
      signedPerm (Equiv.swap a b * Equiv.swap (Fin.rev a) (Fin.rev b)) (shortSign σ a b c) := by
  have h1 : Fin.rev a ≠ Fin.rev b := fun h => hab (Fin.rev_injective h)
  have h2 : a ≠ Fin.rev b := fun h => hba (by rw [h, Fin.rev_rev])
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hab' := hab.symm
  have ha' := ha.symm
  have hb' := hb.symm
  have hba' := hba.symm
  have h1' := h1.symm
  have h2' := h2.symm
  refine eq_signedPerm_of_mulVec_single _ _ fun s => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  by_cases hsa : s = a
  · subst hsa
    mono_simp
    simp only [shortSign, ite_true]
    vec_ext
  by_cases hsb : s = b
  · subst hsb
    mono_simp
    simp only [shortSign, ite_true, ite_false, hsa]
    vec_ext
  by_cases hsa' : s = Fin.rev a
  · subst hsa'
    mono_simp
    simp only [shortSign]
    mono_simp
    vec_ext
  by_cases hsb' : s = Fin.rev b
  · subst hsb'
    mono_simp
    simp only [shortSign]
    mono_simp
    vec_ext
  have e1 : a ≠ s := Ne.symm hsa
  have e2 : b ≠ s := Ne.symm hsb
  have e3 : Fin.rev a ≠ s := Ne.symm hsa'
  have e4 : Fin.rev b ≠ s := Ne.symm hsb'
  mono_simp
  simp only [shortSign]
  mono_simp

@[expose] def longSign (b : Fin n) (z : F) (s : Fin n) : F :=
  if s = b then -z⁻¹ else if s = Fin.rev b then z else 1

theorem longRootMatrix_weyl {b : Fin n} (hb : b ≠ Fin.rev b) {z : F} (hz : z ≠ 0) :
    longRootMatrix b z * longRootMatrix (Fin.rev b) (-z⁻¹) * longRootMatrix b z =
      signedPerm (Equiv.swap b (Fin.rev b)) (longSign b z) := by
  have hb' := hb.symm
  refine eq_signedPerm_of_mulVec_single _ _ fun s => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  by_cases hsb : s = b
  · subst hsb
    mono_simp
    simp only [longSign, ite_true]
    vec_ext
  by_cases hsb' : s = Fin.rev b
  · subst hsb'
    mono_simp
    simp only [longSign]
    mono_simp
    vec_ext
  have e1 : b ≠ s := Ne.symm hsb
  have e2 : Fin.rev b ≠ s := Ne.symm hsb'
  mono_simp
  simp only [longSign]
  mono_simp

variable (σ) in
@[expose] def heisSign (i k : Fin n) (b : F) (s : Fin n) : F :=
  if s = i then (σ b)⁻¹ else if s = k then -σ b * b⁻¹ else if s = Fin.rev i then b else 1

theorem heisenbergMatrix_weyl (hσ : ∀ c, σ (σ c) = c) {i k : Fin n} (hi : i ≠ Fin.rev i)
    (hik : i ≠ k) (hk : Fin.rev k = k) {a b : F} (hab : b + σ b + σ a * a = 0) (hb : b ≠ 0) :
    heisenbergMatrix σ (Fin.rev i) k (-a * (σ b)⁻¹) (σ b)⁻¹ * heisenbergMatrix σ i k a b *
        heisenbergMatrix σ (Fin.rev i) k (-a * b⁻¹) (σ b)⁻¹ =
      signedPerm (Equiv.swap i (Fin.rev i)) (heisSign σ i k b) := by
  have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hb
  have hi' := hi.symm
  have hik' := hik.symm
  have h1 : Fin.rev i ≠ k := fun h => hik (by rw [← Fin.rev_rev i, h, hk])
  have h1' := h1.symm
  have K : 1 + a * (σ a * (σ b)⁻¹) + b * (σ b)⁻¹ = 0 := by
    field_simp
    linear_combination hab
  refine eq_signedPerm_of_mulVec_single _ _ fun s => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  by_cases hsi : s = i
  · subst hsi
    mono_simp
    simp only [heisSign, ite_true, map_mul, map_neg, map_inv₀]
    funext r
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> simp_all
  by_cases hsk : s = k
  · subst hsk
    mono_simp
    simp only [heisSign, ite_true, map_mul, map_neg, map_inv₀]
    mono_simp
    funext r
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> first | (exfalso; simp_all; done) | skip
    all_goals field_simp
    all_goals first | ring1 | linear_combination hab | linear_combination -a * hab
  by_cases hsi' : s = Fin.rev i
  · subst hsi'
    mono_simp
    simp only [heisSign, ite_true, map_mul, map_neg, map_inv₀]
    mono_simp
    funext r
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> first | (exfalso; simp_all; done) | skip
    all_goals field_simp
    all_goals first | ring1 | linear_combination hab
  have e1 : i ≠ s := Ne.symm hsi
  have e2 : k ≠ s := Ne.symm hsk
  have e3 : Fin.rev i ≠ s := Ne.symm hsi'
  mono_simp
  simp only [heisSign]
  mono_simp

end CFSG.LieType.Universal.Unitary
