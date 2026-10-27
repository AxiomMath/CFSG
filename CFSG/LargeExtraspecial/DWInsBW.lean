module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LargeExtraspecial.DW.Insp

open Module CFSG.RankThree.OrthogonalInvolutions

section Ring

variable {R : Type*} [CommRing R]

@[expose] def tri (x : R) : R := 1 + x + x ^ 2

theorem tri_mul_self (h2 : (2 : R) = 0) {x : R} (hx : x ^ 3 = 1) : tri x * tri x = tri x := by
  unfold tri
  linear_combination x * hx + (x ^ 3 + x ^ 2 + x) * h2

theorem mul_tri {x : R} (hx : x ^ 3 = 1) : x * tri x = tri x := by
  unfold tri
  linear_combination hx

theorem tri_mul_of_mul_eq (h2 : (2 : R) = 0) {x s : R} (hx : x * s = s) : tri x * s = s := by
  unfold tri
  linear_combination (2 + x) * hx + s * h2

variable {A B : R}

theorem tri_mul_tri_ab (hA : A ^ 3 = 1) : tri A * tri (A * B) = tri A * tri B := by
  unfold tri
  linear_combination (B + B ^ 2 + A * B ^ 2) * hA

theorem tri_mul_tri_ab2 (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) :
    tri A * tri (A * B ^ 2) = tri A * tri B := by
  unfold tri
  linear_combination (B ^ 2 + B ^ 4 + A * B ^ 4) * hA + (B + A * B + A ^ 2 * B) * hB

theorem tri_b_mul_tri_ab (hB : B ^ 3 = 1) : tri B * tri (A * B) = tri A * tri B := by
  unfold tri
  linear_combination (A + A ^ 2 + A ^ 2 * B) * hB

theorem tri_b_mul_tri_ab2 (hB : B ^ 3 = 1) : tri B * tri (A * B ^ 2) = tri A * tri B := by
  unfold tri
  linear_combination (A + A * B + A ^ 2 + A ^ 2 * B + A ^ 2 * B ^ 2 + A ^ 2 * B ^ 3) * hB

theorem tri_ab_mul_tri_ab2 (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) :
    tri (A * B) * tri (A * B ^ 2) = tri A * tri B := by
  unfold tri
  linear_combination (B ^ 4 + B ^ 5 + A * B ^ 6) * hA +
    (B + B ^ 2 + A + A * B ^ 3 + A ^ 2 + A ^ 2 * B) * hB

theorem tri_sum (h2 : (2 : R) = 0) (hB : B ^ 3 = 1) :
    tri A + tri B + tri (A * B) + tri (A * B ^ 2) = 1 + tri A * tri B := by
  unfold tri
  linear_combination (A ^ 2 * B) * hB + h2

theorem pow_three_ab (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) : (A * B) ^ 3 = 1 := by
  rw [mul_pow, hA, hB, one_mul]

theorem pow_three_ab2 (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) : (A * B ^ 2) ^ 3 = 1 := by
  rw [mul_pow, hA, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hB, one_pow, one_mul]

theorem orth_of (h2 : (2 : R) = 0) {P s tx ty : R} (hP : P * P = P) (hs : s * s = s)
    (hxs : tx * s = s) (hys : ty * s = s) (hxy : tx * ty = s) :
    P * (tx + s) * (P * (ty + s)) = 0 := by
  linear_combination (tx * ty + tx * s + ty * s + s * s) * hP + P * hxy + P * hxs + P * hys +
    P * hs + (2 * P * s) * h2

theorem orth0_of (h2 : (2 : R) = 0) {P s tx : R} (hP : P * P = P) (hs : s * s = s)
    (hxs : tx * s = s) : P * s * (P * (tx + s)) = 0 := by
  linear_combination (s * tx + s * s) * hP + P * hxs + P * hs + (P * s) * h2

theorem idem_of (h2 : (2 : R) = 0) {P s tx : R} (hP : P * P = P) (hs : s * s = s)
    (hxs : tx * s = s) (hxx : tx * tx = tx) : P * (tx + s) * (P * (tx + s)) = P * (tx + s) := by
  linear_combination (tx + s) ^ 2 * hP + P * hxx + (2 * P) * hxs + P * hs + (P * s) * h2

theorem idem0_of {P s : R} (hP : P * P = P) (hs : s * s = s) : P * s * (P * s) = P * s := by
  linear_combination s ^ 2 * hP + P * hs

end Ring

section Rank

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

@[expose] noncomputable def rk (f : Module.End (ZMod 2) V) : ℕ :=
  finrank (ZMod 2) (LinearMap.range f)

theorem rk_add {P Q : Module.End (ZMod 2) V} (hP : P * P = P) (hQP : Q * P = 0)
    (hPQ : P * Q = 0) (hQ : Q * Q = Q) : rk (P + Q) = rk P + rk Q := by
  have hsup : LinearMap.range (P + Q) = LinearMap.range P ⊔ LinearMap.range Q := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, rfl⟩
        refine ⟨P v, ?_⟩
        rw [LinearMap.add_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, hP, hQP,
          LinearMap.zero_apply, add_zero]
      · rintro _ ⟨v, rfl⟩
        refine ⟨Q v, ?_⟩
        rw [LinearMap.add_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, hQ, hPQ,
          LinearMap.zero_apply, zero_add]
  have hinf : LinearMap.range P ⊓ LinearMap.range Q = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨v, rfl⟩, ⟨w, hw⟩⟩
    have e1 : P v = P (P v) := by rw [← Module.End.mul_apply, hP]
    rw [Submodule.mem_bot, e1, ← hw, ← Module.End.mul_apply, hPQ, LinearMap.zero_apply]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range P) (LinearMap.range Q)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  exact h

variable {R : Type*} [CommRing R]

theorem rk_map_add (φ : R →+* Module.End (ZMod 2) V) {x y : R} (hx : x * x = x)
    (hy : y * y = y) (hxy : x * y = 0) : rk (φ (x + y)) = rk (φ x) + rk (φ y) := by
  rw [map_add]
  exact rk_add (by rw [← map_mul, hx]) (by rw [← map_mul, mul_comm, hxy, map_zero])
    (by rw [← map_mul, hxy, map_zero]) (by rw [← map_mul, hy])

theorem idem_add {x y : R} (hx : x * x = x) (hy : y * y = y) (hxy : x * y = 0) :
    (x + y) * (x + y) = x + y := by
  linear_combination hx + hy + 2 * hxy

theorem orth_add {x y z : R} (hxz : x * z = 0) (hyz : y * z = 0) : (x + y) * z = 0 := by
  rw [add_mul, hxz, hyz, add_zero]

theorem bw2 (φ : R →+* Module.End (ZMod 2) V) (h2 : (2 : R) = 0) {A B P : R}
    (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) (hP : P * P = P) :
    rk (φ (P * tri A)) + rk (φ (P * tri B)) + rk (φ (P * tri (A * B))) +
        rk (φ (P * tri (A * B ^ 2))) = rk (φ P) + 3 * rk (φ (P * (tri A * tri B))) := by
  set s := tri A * tri B with hs_def
  have hAB := pow_three_ab hA hB
  have hAB2 := pow_three_ab2 hA hB
  have iA := tri_mul_self h2 hA
  have iB := tri_mul_self h2 hB
  have iAB := tri_mul_self h2 hAB
  have iAB2 := tri_mul_self h2 hAB2
  have hss : s * s = s := by
    rw [hs_def]
    linear_combination (tri B * tri B) * iA + tri A * iB
  have hAs : A * s = s := by rw [hs_def, ← mul_assoc, mul_tri hA]
  have hBs : B * s = s := by rw [hs_def, mul_left_comm, mul_tri hB]
  have hABs : A * B * s = s := by rw [mul_assoc, hBs, hAs]
  have hAB2s : A * B ^ 2 * s = s := by rw [pow_two, mul_assoc, mul_assoc, hBs, hBs, hAs]
  have tAs := tri_mul_of_mul_eq h2 hAs
  have tBs := tri_mul_of_mul_eq h2 hBs
  have tABs := tri_mul_of_mul_eq h2 hABs
  have tAB2s := tri_mul_of_mul_eq h2 hAB2s
  have hsum := tri_sum (A := A) h2 hB
  have key : ∀ tx : R, tx * tx = tx → tx * s = s →
      rk (φ (P * tx)) = rk (φ (P * s)) + rk (φ (P * (tx + s))) := fun tx hxx hxs => by
    rw [show P * tx = P * s + P * (tx + s) by linear_combination (-(P * s)) * h2]
    exact rk_map_add φ (idem0_of hP hss) (idem_of h2 hP hss hxs hxx) (orth0_of h2 hP hss hxs)
  have hPsum : P = P * s + P * (tri A + s) + P * (tri B + s) + P * (tri (A * B) + s) +
      P * (tri (A * B ^ 2) + s) := by
    linear_combination (-P) * hsum + (-3 * P * s) * h2
  have i0 := idem0_of hP hss
  have i1 := idem_of h2 hP hss tAs iA
  have i2 := idem_of h2 hP hss tBs iB
  have i3 := idem_of h2 hP hss tABs iAB
  have i4 := idem_of h2 hP hss tAB2s iAB2
  have o01 := orth0_of h2 hP hss tAs
  have o02 := orth0_of h2 hP hss tBs
  have o03 := orth0_of h2 hP hss tABs
  have o04 := orth0_of h2 hP hss tAB2s
  have o12 := orth_of h2 hP hss tAs tBs rfl
  have o13 := orth_of h2 hP hss tAs tABs (tri_mul_tri_ab hA)
  have o14 := orth_of h2 hP hss tAs tAB2s (tri_mul_tri_ab2 hA hB)
  have o23 := orth_of h2 hP hss tBs tABs (tri_b_mul_tri_ab hB)
  have o24 := orth_of h2 hP hss tBs tAB2s (tri_b_mul_tri_ab2 hB)
  have o34 := orth_of h2 hP hss tABs tAB2s (tri_ab_mul_tri_ab2 hA hB)
  have j1 := idem_add i0 i1 o01
  have j2 := idem_add j1 i2 (orth_add o02 o12)
  have j3 := idem_add j2 i3 (orth_add (orth_add o03 o13) o23)
  have r1 := rk_map_add φ i0 i1 o01
  have r2 := rk_map_add φ j1 i2 (orth_add o02 o12)
  have r3 := rk_map_add φ j2 i3 (orth_add (orth_add o03 o13) o23)
  have r4 := rk_map_add φ j3 i4 (orth_add (orth_add (orth_add o04 o14) o24) o34)
  rw [← hPsum] at r4
  rw [key _ iA tAs, key _ iB tBs, key _ iAB tABs, key _ iAB2 tAB2s]
  omega

end Rank


section Aut3

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

@[expose] noncomputable def rc (g : V ≃ₗ[ZMod 2] V) : ℕ := finrank (ZMod 2) (commSpace g)

omit [FiniteDimensional (ZMod 2) V] in
theorem add_self_vec' (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

omit [FiniteDimensional (ZMod 2) V] in
theorem range_tri {f : Module.End (ZMod 2) V} (hf : f ^ 3 = 1) :
    LinearMap.range (1 + f + f ^ 2) = LinearMap.ker (f - 1) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply]
    have : (f - 1) * (1 + f + f ^ 2) = f ^ 3 - 1 := by noncomm_ring
    rw [this, hf, sub_self, LinearMap.zero_apply]
  · intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    refine ⟨v, ?_⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, pow_two,
      Module.End.mul_apply, hv, hv, add_self_vec', zero_add]

theorem rk_tri_add_rc {g : V ≃ₗ[ZMod 2] V} (hg : (g : Module.End (ZMod 2) V) ^ 3 = 1) :
    rk (1 + (g : Module.End (ZMod 2) V) + (g : Module.End (ZMod 2) V) ^ 2) + rc g =
      finrank (ZMod 2) V := by
  rw [rk, range_tri hg, rc, add_comm]
  exact finrank_commSpace_add_finrank_fixSpace g

theorem pow_three_mul {G : Type*} [CommMonoid G] {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    (x * y) ^ 3 = 1 := by
  rw [mul_pow, hx, hy, one_mul]

theorem pow_three_pow {G : Type*} [Monoid G] {x : G} (hx : x ^ 3 = 1) (k : ℕ) :
    (x ^ k) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]

omit [FiniteDimensional (ZMod 2) V] in
theorem coe_mul_end (x y : V ≃ₗ[ZMod 2] V) :
    ((x * y : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V) = (x : Module.End (ZMod 2) V) * y :=
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem coe_pow_end (x : V ≃ₗ[ZMod 2] V) (k : ℕ) :
    ((x ^ k : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V) = (x : Module.End (ZMod 2) V) ^ k :=
  map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom x k

theorem rk_tri_map {R : Type*} [CommRing R] (φ : R →+* Module.End (ZMod 2) V) {X : R}
    {g : V ≃ₗ[ZMod 2] V} (hX : φ X = g) (h3 : X ^ 3 = 1) :
    rk (φ (tri X)) + rc g = finrank (ZMod 2) V := by
  have e : φ (tri X) = 1 + (g : Module.End (ZMod 2) V) + (g : Module.End (ZMod 2) V) ^ 2 := by
    rw [tri, map_add, map_add, map_one, map_pow, hX]
  rw [e]
  refine rk_tri_add_rc ?_
  rw [← hX, ← map_pow, h3, map_one]

omit [FiniteDimensional (ZMod 2) V] in
theorem rk_one : rk (1 : Module.End (ZMod 2) V) = finrank (ZMod 2) V := by
  rw [rk, Module.End.one_eq_id, LinearMap.range_id, finrank_top]

theorem bw2_one {R : Type*} [CommRing R] (φ : R →+* Module.End (ZMod 2) V) (h2 : (2 : R) = 0)
    {A B : R} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) :
    rk (φ (tri A)) + rk (φ (tri B)) + rk (φ (tri (A * B))) + rk (φ (tri (A * B ^ 2))) =
      finrank (ZMod 2) V + 3 * rk (φ (tri A * tri B)) := by
  have h := bw2 φ h2 hA hB (P := 1) (mul_one 1)
  simp only [one_mul] at h
  rwa [map_one, rk_one] at h

theorem rk_tri_mul_le {R : Type*} [CommRing R] (φ : R →+* Module.End (ZMod 2) V) (x y : R) :
    rk (φ (x * y)) ≤ rk (φ y) := by
  rw [rk, rk, mul_comm, map_mul, Module.End.mul_eq_comp]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

theorem bw_arith {n f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
    r12 r13 tA tB tAB tAB2 s1 s2 : ℕ} (i1 : f1 + r1 = n) (i2 : f2 + r2 = n) (i3 : f3 + r3 = n)
    (i4 : f4 + r4 = n) (i5 : f5 + r5 = n) (i6 : f6 + r6 = n) (i7 : f7 + r7 = n)
    (i8 : f8 + r8 = n) (i9 : f9 + r9 = n) (i10 : f10 + r10 = n) (i11 : f11 + r11 = n)
    (i12 : f12 + r12 = n) (i13 : f13 + r13 = n) (b1 : f10 + f11 + f12 + f13 = n + 3 * s1)
    (b2 : f1 + f10 + f2 + f3 = n + 3 * tA) (b3 : f1 + f11 + f4 + f5 = n + 3 * tB)
    (b4 : f1 + f12 + f6 + f7 = n + 3 * tAB) (b5 : f1 + f13 + f8 + f9 = n + 3 * tAB2)
    (b6 : tA + tB + tAB + tAB2 = f1 + 3 * s2) (hle : s2 ≤ s1) :
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = 2 * (r10 + r11 + r12 + r13) + 9 * (s1 - s2) := by
  have key : r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + 9 * s2 =
      2 * (r10 + r11 + r12 + r13) + 9 * s1 := by
    zify at i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 b1 b2 b3 b4 b5 b6 ⊢
    linear_combination i1 + i2 + i3 + i4 + i5 + i6 + i7 + i8 + i9 - 2 * (i10 + i11 + i12 + i13) +
      3 * b1 - b2 - b3 - b4 - b5 - 3 * b6
  generalize r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = L at key ⊢
  generalize 2 * (r10 + r11 + r12 + r13) = M at key ⊢
  omega

theorem bw_line_of_ring {R : Type*} [CommRing R] (φ : R →+* Module.End (ZMod 2) V)
    (h2 : (2 : R) = 0) {A B C : R} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) (hC : C ^ 3 = 1)
    {a b c : V ≃ₗ[ZMod 2] V} (hφA : φ A = a) (hφB : φ B = b) (hφC : φ C = c) :
    ∃ k : ℕ, rc c + rc (c * a) + rc (c * a ^ 2) + rc (c * b) + rc (c * b ^ 2) +
        rc (c * (a * b)) + rc (c * (a * b) ^ 2) + rc (c * (a * b ^ 2)) +
        rc (c * (a * b ^ 2) ^ 2) = 2 * (rc a + rc b + rc (a * b) + rc (a * b ^ 2)) + 9 * k := by
  have hAB := pow_three_mul hA hB
  have hAB2 := pow_three_mul hA (pow_three_pow hB 2)
  have i1 := rk_tri_map φ hφC hC
  have i2 := rk_tri_map φ (X := C * A) (g := c * a) (by rw [map_mul, hφC, hφA, coe_mul_end])
    (pow_three_mul hC hA)
  have i3 := rk_tri_map φ (X := C * A ^ 2) (g := c * a ^ 2)
    (by rw [map_mul, map_pow, hφC, hφA, coe_mul_end, coe_pow_end])
    (pow_three_mul hC (pow_three_pow hA 2))
  have i4 := rk_tri_map φ (X := C * B) (g := c * b) (by rw [map_mul, hφC, hφB, coe_mul_end])
    (pow_three_mul hC hB)
  have i5 := rk_tri_map φ (X := C * B ^ 2) (g := c * b ^ 2)
    (by rw [map_mul, map_pow, hφC, hφB, coe_mul_end, coe_pow_end])
    (pow_three_mul hC (pow_three_pow hB 2))
  have i6 := rk_tri_map φ (X := C * (A * B)) (g := c * (a * b))
    (by rw [map_mul, map_mul, hφC, hφA, hφB, coe_mul_end, coe_mul_end]) (pow_three_mul hC hAB)
  have i7 := rk_tri_map φ (X := C * (A * B) ^ 2) (g := c * (a * b) ^ 2)
    (by rw [map_mul, map_pow, map_mul, hφC, hφA, hφB, coe_mul_end, coe_pow_end, coe_mul_end])
    (pow_three_mul hC (pow_three_pow hAB 2))
  have i8 := rk_tri_map φ (X := C * (A * B ^ 2)) (g := c * (a * b ^ 2))
    (by rw [map_mul, map_mul, map_pow, hφC, hφA, hφB, coe_mul_end, coe_mul_end, coe_pow_end])
    (pow_three_mul hC hAB2)
  have i9 := rk_tri_map φ (X := C * (A * B ^ 2) ^ 2) (g := c * (a * b ^ 2) ^ 2)
    (by rw [map_mul, map_pow, map_mul, map_pow, hφC, hφA, hφB, coe_mul_end, coe_pow_end,
      coe_mul_end, coe_pow_end]) (pow_three_mul hC (pow_three_pow hAB2 2))
  have i10 := rk_tri_map φ hφA hA
  have i11 := rk_tri_map φ hφB hB
  have i12 := rk_tri_map φ (X := A * B) (g := a * b) (by rw [map_mul, hφA, hφB, coe_mul_end]) hAB
  have i13 := rk_tri_map φ (X := A * B ^ 2) (g := a * b ^ 2)
    (by rw [map_mul, map_pow, hφA, hφB, coe_mul_end, coe_pow_end]) hAB2
  have b1 := bw2_one φ h2 hA hB
  have b2 := bw2_one φ h2 hC hA
  have b3 := bw2_one φ h2 hC hB
  have b4 := bw2_one φ h2 hC hAB
  have b5 := bw2_one φ h2 hC hAB2
  have b6 := bw2 φ h2 hA hB (P := tri C) (tri_mul_self h2 hC)
  have hle := rk_tri_mul_le φ (tri C) (tri A * tri B)
  exact ⟨_, bw_arith i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 b1 b2 b3 b4 b5 b6 hle⟩

theorem bw_line (a b c : V ≃ₗ[ZMod 2] V) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) :
    ∃ k : ℕ, rc c + rc (c * a) + rc (c * a ^ 2) + rc (c * b) + rc (c * b ^ 2) +
        rc (c * (a * b)) + rc (c * (a * b) ^ 2) + rc (c * (a * b ^ 2)) +
        rc (c * (a * b ^ 2) ^ 2) = 2 * (rc a + rc b + rc (a * b) + rc (a * b ^ 2)) + 9 * k := by
  let S : Set (Module.End (ZMod 2) V) :=
    {(a : Module.End (ZMod 2) V), (b : Module.End (ZMod 2) V), (c : Module.End (ZMod 2) V)}
  have hι : ∀ x y : V ≃ₗ[ZMod 2] V, x * y = y * x →
      Commute (x : Module.End (ZMod 2) V) (y : Module.End (ZMod 2) V) := fun x y h => by
    change (x : Module.End (ZMod 2) V) * y = (y : Module.End (ZMod 2) V) * x
    rw [← coe_mul_end, h, coe_mul_end]
  have hcomm : S.Pairwise Commute := by
    intro x hx y hy _
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact hι _ _ hab | exact (hι _ _ hab).symm
      | exact hι _ _ hac | exact (hι _ _ hac).symm
      | exact hι _ _ hbc | exact (hι _ _ hbc).symm
  have hmc := Algebra.isMulCommutative_adjoin (ZMod 2) hcomm
  let _ : CommRing (Algebra.adjoin (ZMod 2) S) :=
    { (inferInstance : Ring (Algebra.adjoin (ZMod 2) S)) with
      mul_comm := fun x y => hmc.is_comm.comm x y }
  let φ : Algebra.adjoin (ZMod 2) S →+* Module.End (ZMod 2) V :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  have hinj : Function.Injective φ := Subtype.val_injective
  have h2 : (2 : Algebra.adjoin (ZMod 2) S) = 0 := by
    apply hinj
    rw [map_ofNat, map_zero, show (2 : Module.End (ZMod 2) V) = 1 + 1 from one_add_one_eq_two.symm]
    ext v
    rw [LinearMap.add_apply, Module.End.one_apply, add_self_vec']
    rfl
  let A : Algebra.adjoin (ZMod 2) S := ⟨a, Algebra.subset_adjoin (by simp [S])⟩
  let B : Algebra.adjoin (ZMod 2) S := ⟨b, Algebra.subset_adjoin (by simp [S])⟩
  let C : Algebra.adjoin (ZMod 2) S := ⟨c, Algebra.subset_adjoin (by simp [S])⟩
  have hA : A ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    change (a : Module.End (ZMod 2) V) ^ 3 = 1
    rw [← coe_pow_end, ha]
    rfl)
  have hB : B ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    change (b : Module.End (ZMod 2) V) ^ 3 = 1
    rw [← coe_pow_end, hb]
    rfl)
  have hC : C ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    change (c : Module.End (ZMod 2) V) ^ 3 = 1
    rw [← coe_pow_end, hc]
    rfl)
  exact bw_line_of_ring φ h2 hA hB hC rfl rfl rfl

end Aut3


section RC

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem fixSpace_inv (g : V ≃ₗ[ZMod 2] V) : fixSpace g⁻¹ = fixSpace g := by
  ext v
  rw [mem_fixSpace, mem_fixSpace]
  constructor
  · intro h
    calc g v = g (g⁻¹ v) := by rw [h]
      _ = v := by rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
  · intro h
    calc g⁻¹ v = g⁻¹ (g v) := by rw [h]
      _ = v := by rw [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]

theorem rc_inv (g : V ≃ₗ[ZMod 2] V) : rc g⁻¹ = rc g := by
  have h1 := finrank_commSpace_add_finrank_fixSpace g
  have h2 := finrank_commSpace_add_finrank_fixSpace g⁻¹
  rw [fixSpace_inv] at h2
  rw [rc, rc]
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_conj (x g : V ≃ₗ[ZMod 2] V) :
    commSpace (x * g * x⁻¹) = (commSpace g).map (x : V →ₗ[ZMod 2] V) := by
  have hx : ∀ v, x (x⁻¹ v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
  have hx' : ∀ v, x⁻¹ (x v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]
  ext w
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨g (x⁻¹ v) - x⁻¹ v, sub_mem_commSpace g _, ?_⟩
    rw [LinearEquiv.coe_coe, map_sub, hx, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
    refine ⟨x v, ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx', LinearEquiv.coe_coe, map_sub]

omit [FiniteDimensional (ZMod 2) V] in
theorem rc_conj (x g : V ≃ₗ[ZMod 2] V) : rc (x * g * x⁻¹) = rc g := by
  rw [rc, rc, commSpace_conj, LinearEquiv.finrank_map_eq]

theorem rc_mul_le (g h : V ≃ₗ[ZMod 2] V) : rc (g * h) ≤ rc g + rc h := by
  have hle : commSpace (g * h) ≤ commSpace g ⊔ commSpace h := by
    intro w hw
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
    have e : (g * h) v - v = (g (h v) - h v) + (h v - v) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [e]
    exact Submodule.add_mem_sup (sub_mem_commSpace g _) (sub_mem_commSpace h _)
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rc_pos {g : V ≃ₗ[ZMod 2] V} (hg : g ≠ 1) : 0 < rc g :=
  one_le_finrank_commSpace hg

theorem rc_sq {g : V ≃ₗ[ZMod 2] V} (hg : g ^ 3 = 1) : rc (g ^ 2) = rc g := by
  have : g ^ 2 = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hg]
  rw [this, rc_inv]

end RC

end CFSG.LargeExtraspecial.DW.Insp
