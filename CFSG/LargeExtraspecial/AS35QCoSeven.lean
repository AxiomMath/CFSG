module

public import CFSG.LargeExtraspecial.AS35QCoFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

namespace Seven

structure Hyp (q : QuadraticForm (ZMod 2) V) (x : V ≃ₗ[ZMod 2] V) : Prop where
  nondeg : q.polarBilin.Nondegenerate
  dim : finrank (ZMod 2) V = 8
  isom : ∀ v, q (x v) = q v
  pow : x ^ 7 = 1
  ne_one : x ≠ 1

abbrev eX (x : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V := x.toLinearMap

@[expose] def pA (x : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V := eX x ^ 3 + eX x + 1

@[expose] def pB (x : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V := eX x ^ 3 + eX x ^ 2 + 1

omit [FiniteDimensional (ZMod 2) V] in
theorem two_eq_zero_end : (2 : Module.End (ZMod 2) V) = 0 := by
  ext v
  rw [show (2 : Module.End (ZMod 2) V) = 1 + 1 from one_add_one_eq_two.symm, LinearMap.add_apply,
    Module.End.one_apply, LinearMap.zero_apply, ← two_nsmul, two_nsmul_eq_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem eX_pow (x : V ≃ₗ[ZMod 2] V) (k : ℕ) : eX x ^ k = eX (x ^ k) :=
  (map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom x k).symm

omit [FiniteDimensional (ZMod 2) V] in
theorem eX_pow_apply (x : V ≃ₗ[ZMod 2] V) (k : ℕ) (v : V) : (eX x ^ k) v = (x ^ k) v := by
  rw [eX_pow]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem eX_pow_seven {x : V ≃ₗ[ZMod 2] V} (h : x ^ 7 = 1) : eX x ^ 7 = 1 := by
  rw [eX_pow, h]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem bezout (x : V ≃ₗ[ZMod 2] V) : eX x * pA x + (eX x + 1) * pB x = 1 := by
  have e : eX x * pA x + (eX x + 1) * pB x =
      1 + 2 * (eX x ^ 4 + eX x ^ 3 + eX x ^ 2 + eX x) := by
    unfold pA pB
    noncomm_ring
  rw [e, two_eq_zero_end, zero_mul, add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem inv_mod_pA (x : V ≃ₗ[ZMod 2] V) : (eX x + 1) * (eX x ^ 2 + eX x) = 1 + pA x := by
  have e : (eX x + 1) * (eX x ^ 2 + eX x) = 1 + pA x + 2 * (eX x ^ 2 - 1) := by
    unfold pA
    noncomm_ring
  rw [e, two_eq_zero_end, zero_mul, add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem inv_mod_pB (x : V ≃ₗ[ZMod 2] V) : (eX x + 1) * eX x ^ 2 = 1 + pB x := by
  have e : (eX x + 1) * eX x ^ 2 = 1 + pB x + 2 * (-1) := by
    unfold pB
    noncomm_ring
  rw [e, two_eq_zero_end, zero_mul, add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem pA_pB_sub_one {x : V ≃ₗ[ZMod 2] V} (h : x ^ 7 = 1) :
    pA x * pB x * (eX x - 1) = 0 := by
  have e : pA x * pB x * (eX x - 1) = eX x ^ 7 - 1 + 2 * (eX x ^ 4 - eX x ^ 3) := by
    unfold pA pB
    noncomm_ring
  rw [e, eX_pow_seven h, two_eq_zero_end, zero_mul, add_zero, sub_self]

omit [FiniteDimensional (ZMod 2) V] in
theorem commute_pA {x : V ≃ₗ[ZMod 2] V} {c : Module.End (ZMod 2) V} (h : Commute c (eX x)) :
    Commute c (pA x) :=
  ((h.pow_right 3).add_right h).add_right (Commute.one_right c)

omit [FiniteDimensional (ZMod 2) V] in
theorem commute_pB {x : V ≃ₗ[ZMod 2] V} {c : Module.End (ZMod 2) V} (h : Commute c (eX x)) :
    Commute c (pB x) :=
  ((h.pow_right 3).add_right (h.pow_right 2)).add_right (Commute.one_right c)

omit [FiniteDimensional (ZMod 2) V] in
theorem pow_four_mul_pA {x : V ≃ₗ[ZMod 2] V} (h : x ^ 7 = 1) :
    eX x ^ 4 * pA x = eX x ^ 4 + eX x ^ 5 + 1 := by
  have e : eX x ^ 4 * pA x = eX x ^ 4 + eX x ^ 5 + eX x ^ 7 := by
    unfold pA
    noncomm_ring
  rw [e, eX_pow_seven h]

omit [FiniteDimensional (ZMod 2) V] in
theorem pow_four_mul_pB {x : V ≃ₗ[ZMod 2] V} (h : x ^ 7 = 1) :
    eX x ^ 4 * pB x = eX x ^ 4 + eX x ^ 6 + 1 := by
  have e : eX x ^ 4 * pB x = eX x ^ 4 + eX x ^ 6 + eX x ^ 7 := by
    unfold pB
    noncomm_ring
  rw [e, eX_pow_seven h]

variable {q : QuadraticForm (ZMod 2) V} {x : V ≃ₗ[ZMod 2] V}

namespace Hyp

variable (hx : Hyp q x)
include hx

omit [FiniteDimensional (ZMod 2) V] in
theorem isom_pow (k : ℕ) (v : V) : q ((x ^ k) v) = q v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, hx.isom, ih]

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_pow (k : ℕ) (u v : V) :
    QuadraticMap.polar q ((x ^ k) u) ((x ^ k) v) = QuadraticMap.polar q u v := by
  simp only [QuadraticMap.polar, ← map_add, hx.isom_pow]

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_pow_right {k : ℕ} (hk : k ≤ 7) (u v : V) :
    QuadraticMap.polar q u ((x ^ k) v) = QuadraticMap.polar q ((x ^ (7 - k)) u) v := by
  rw [← hx.polar_pow k ((x ^ (7 - k)) u) v, ← LinearEquiv.mul_apply, ← pow_add,
    Nat.add_sub_cancel' hk, hx.pow]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_pB_right (u v : V) :
    QuadraticMap.polar q u (pB x v) = QuadraticMap.polar q ((eX x ^ 4 * pA x) u) v := by
  rw [pow_four_mul_pA hx.pow]
  simp only [pB, LinearMap.add_apply, Module.End.one_apply, eX_pow_apply]
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, QuadraticMap.polar_add_left,
    QuadraticMap.polar_add_left, hx.polar_pow_right (by norm_num : 3 ≤ 7),
    hx.polar_pow_right (by norm_num : 2 ≤ 7)]

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_pA_right (u v : V) :
    QuadraticMap.polar q u (pA x v) = QuadraticMap.polar q ((eX x ^ 4 * pB x) u) v := by
  rw [pow_four_mul_pB hx.pow]
  have e1 : (eX x) v = (x ^ 1) v := by rw [pow_one]; rfl
  simp only [pA, LinearMap.add_apply, Module.End.one_apply, eX_pow_apply]
  rw [e1, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, QuadraticMap.polar_add_left,
    QuadraticMap.polar_add_left, hx.polar_pow_right (by norm_num : 3 ≤ 7),
    hx.polar_pow_right (by norm_num : 1 ≤ 7)]

end Hyp

abbrev kA (x : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V := LinearMap.ker (pA x)

abbrev kB (x : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V := LinearMap.ker (pB x)

omit [FiniteDimensional (ZMod 2) V] in
theorem three_smul_eq (v : V) : v + v + v = v := by
  rw [← two_nsmul, two_nsmul_eq_zero, zero_add]

omit [FiniteDimensional (ZMod 2) V] in
theorem pow_apply_of_fixed {v : V} (hx1 : x v = v) (k : ℕ) : (x ^ k) v = v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, hx1, ih]

omit [FiniteDimensional (ZMod 2) V] in
theorem kA_inf_fixSpace : kA x ⊓ fixSpace x = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hA, hF⟩ := Submodule.mem_inf.mp hv
  have hx1 : x v = v := mem_fixSpace.mp hF
  have h0 : pA x v = 0 := hA
  have e1 : (eX x) v = (x ^ 1) v := by rw [pow_one]; rfl
  rw [pA, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, eX_pow_apply, e1,
    pow_apply_of_fixed hx1, pow_apply_of_fixed hx1, three_smul_eq] at h0
  exact (Submodule.mem_bot _).mpr h0

omit [FiniteDimensional (ZMod 2) V] in
theorem kB_inf_fixSpace : kB x ⊓ fixSpace x = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hB, hF⟩ := Submodule.mem_inf.mp hv
  have hx1 : x v = v := mem_fixSpace.mp hF
  have h0 : pB x v = 0 := hB
  rw [pB, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, eX_pow_apply,
    eX_pow_apply, pow_apply_of_fixed hx1, pow_apply_of_fixed hx1, three_smul_eq] at h0
  exact (Submodule.mem_bot _).mpr h0

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_commSpace_of_eq {w v : V} (h : (eX x + 1) w = v) : v ∈ commSpace x := by
  refine mem_commSpace.mpr ⟨w, ?_⟩
  rw [← h, LinearMap.add_apply, Module.End.one_apply, sub_eq_add_neg, neg_eq_self']
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem kA_le_commSpace : kA x ≤ commSpace x := by
  intro a ha
  have h0 : pA x a = 0 := ha
  apply mem_commSpace_of_eq (w := (eX x ^ 2 + eX x) a)
  rw [← Module.End.mul_apply, inv_mod_pA, LinearMap.add_apply, Module.End.one_apply, h0,
    add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem kB_le_commSpace : kB x ≤ commSpace x := by
  intro b hb
  have h0 : pB x b = 0 := hb
  apply mem_commSpace_of_eq (w := (eX x ^ 2) b)
  rw [← Module.End.mul_apply, inv_mod_pB, LinearMap.add_apply, Module.End.one_apply, h0,
    add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_le_sup (h7 : x ^ 7 = 1) : commSpace x ≤ kA x ⊔ kB x := by
  intro w hw
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
  have hk : (pA x * pB x) (x u - u) = 0 := by
    have e := congrArg (fun T : Module.End (ZMod 2) V => T u) (pA_pB_sub_one h7)
    simp only [LinearMap.zero_apply] at e
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at e
    exact e
  have e := congrArg (fun T : Module.End (ZMod 2) V => T (x u - u)) (bezout x)
  simp only [LinearMap.add_apply, Module.End.one_apply] at e
  rw [← e, add_comm]
  refine Submodule.add_mem_sup ?_ ?_
  · change pA x (((eX x + 1) * pB x) (x u - u)) = 0
    rw [← Module.End.mul_apply, show pA x * ((eX x + 1) * pB x) =
      (eX x + 1) * (pA x * pB x) by unfold pA pB; noncomm_ring, Module.End.mul_apply, hk,
      map_zero]
  · change pB x ((eX x * pA x) (x u - u)) = 0
    rw [← Module.End.mul_apply, show pB x * (eX x * pA x) = eX x * (pA x * pB x) by
      unfold pA pB; noncomm_ring, Module.End.mul_apply, hk, map_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem eX_mul (c d : V ≃ₗ[ZMod 2] V) : eX (c * d) = eX c * eX d :=
  map_mul LinearEquiv.automorphismGroup.toLinearMapMonoidHom c d

omit [FiniteDimensional (ZMod 2) V] in
theorem commute_eX {c : V ≃ₗ[ZMod 2] V} (h : c * x = x * c) : Commute (eX c) (eX x) := by
  change eX c * eX x = eX x * eX c
  rw [← eX_mul, ← eX_mul, h]

omit [FiniteDimensional (ZMod 2) V] in
theorem kA_invariant {c : V ≃ₗ[ZMod 2] V} (h : c * x = x * c) : ∀ u ∈ kA x, c u ∈ kA x := by
  intro u hu
  change pA x (eX c u) = 0
  rw [← Module.End.mul_apply, ← (commute_pA (commute_eX h)).eq, Module.End.mul_apply]
  change c (pA x u) = 0
  rw [show pA x u = 0 from hu, map_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem kB_invariant {c : V ≃ₗ[ZMod 2] V} (h : c * x = x * c) : ∀ u ∈ kB x, c u ∈ kB x := by
  intro u hu
  change pB x (eX c u) = 0
  rw [← Module.End.mul_apply, ← (commute_pB (commute_eX h)).eq, Module.End.mul_apply]
  change c (pB x u) = 0
  rw [show pB x u = 0 from hu, map_zero]

namespace Hyp

variable (hx : Hyp q x)
include hx

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_kA {a a' : V} (ha : a ∈ kA x) (ha' : a' ∈ kA x) :
    QuadraticMap.polar q a a' = 0 := by
  have h0 : pA x a = 0 := ha
  have h0' : pA x a' = 0 := ha'
  have e := congrArg (fun T : Module.End (ZMod 2) V => T a') (bezout x)
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, h0', map_zero, zero_add,
    Module.End.one_apply] at e
  have hc : Commute (eX x + 1) (eX x) := (Commute.refl (eX x)).add_left (Commute.one_left _)
  have e' : pB x ((eX x + 1) a') = a' := by
    rw [← Module.End.mul_apply, ← (commute_pB hc).eq, Module.End.mul_apply, e]
  rw [← e', hx.polar_pB_right, Module.End.mul_apply, h0, map_zero,
    QuadraticMap.polar_zero_left]

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_kB {b b' : V} (hb : b ∈ kB x) (hb' : b' ∈ kB x) :
    QuadraticMap.polar q b b' = 0 := by
  have h0 : pB x b = 0 := hb
  have h0' : pB x b' = 0 := hb'
  have e := congrArg (fun T : Module.End (ZMod 2) V => T b') (bezout x)
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, h0', map_zero, add_zero,
    Module.End.one_apply] at e
  have e' : pA x ((eX x) b') = b' := by
    rw [← Module.End.mul_apply, ← (commute_pA (Commute.refl (eX x))).eq, Module.End.mul_apply, e]
  rw [← e', hx.polar_pA_right, Module.End.mul_apply, h0, map_zero,
    QuadraticMap.polar_zero_left]

theorem le_orthogonal {U : Submodule (ZMod 2) V} (hU : U ≤ commSpace x)
    (hiso : ∀ a ∈ U, ∀ a' ∈ U, QuadraticMap.polar q a a' = 0) :
    U ≤ LinearMap.BilinForm.orthogonal q.polarBilin (U ⊔ fixSpace x) := by
  intro a ha
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  obtain ⟨a', ha', f, hf, rfl⟩ := Submodule.mem_sup.mp hn
  have hperp : a ∈ LinearMap.BilinForm.orthogonal q.polarBilin (fixSpace x) := by
    rw [← commSpace_eq_orthogonal hx.nondeg hx.isom]
    exact hU ha
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hperp
  have h1 : QuadraticMap.polar q f a = 0 := hperp f hf
  change QuadraticMap.polar q (a' + f) a = 0
  rw [QuadraticMap.polar_add_left, hiso a' ha' a ha, h1, add_zero]

theorem two_mul_finrank_le {U : Submodule (ZMod 2) V} (hU : U ≤ commSpace x)
    (hiso : ∀ a ∈ U, ∀ a' ∈ U, QuadraticMap.polar q a a' = 0) (hUF : U ⊓ fixSpace x = ⊥) :
    2 * finrank (ZMod 2) U + finrank (ZMod 2) (fixSpace x) ≤ 8 := by
  have h1 := Submodule.finrank_mono (hx.le_orthogonal hU hiso)
  rw [LinearMap.BilinForm.finrank_orthogonal hx.nondeg, finrank_sup_of_inf_eq_bot hUF,
    hx.dim] at h1
  have h2 : finrank (ZMod 2) U + finrank (ZMod 2) (fixSpace x) ≤ 8 := by
    have := Submodule.finrank_le (U ⊔ fixSpace x)
    rw [finrank_sup_of_inf_eq_bot hUF, hx.dim] at this
    exact this
  omega

theorem finrank_fixSpace : finrank (ZMod 2) (fixSpace x) = 2 ∧ finrank (ZMod 2) (kA x) = 3 ∧
    finrank (ZMod 2) (kB x) = 3 := by
  have hA := hx.two_mul_finrank_le kA_le_commSpace (fun _ ha _ ha' => hx.polar_kA ha ha')
    kA_inf_fixSpace
  have hB := hx.two_mul_finrank_le kB_le_commSpace (fun _ hb _ hb' => hx.polar_kB hb hb')
    kB_inf_fixSpace
  have hsum := Submodule.finrank_mono (commSpace_le_sup hx.pow)
  have hsup := Submodule.finrank_add_le_finrank_add_finrank (kA x) (kB x)
  have hcf := finrank_commSpace_add_finrank_fixSpace x
  rw [hx.dim] at hcf
  have hA3 : finrank (ZMod 2) (kA x) % 3 = 0 := by
    have := mod_three_of_pow_seven hx.pow (W := kA x) (fun u hu =>
      kA_invariant (c := x) rfl u hu)
    rw [kA_inf_fixSpace, finrank_bot] at this
    exact this
  have hF3 : finrank (ZMod 2) (fixSpace x) % 3 = 2 := by
    have := mod_three_of_pow_seven hx.pow (W := ⊤) (fun _ _ => Submodule.mem_top)
    rw [top_inf_eq, finrank_top, hx.dim] at this
    omega
  have hF8 : finrank (ZMod 2) (fixSpace x) ≠ 8 := by
    intro h
    apply hx.ne_one
    apply Frame.fixSpace_eq_top_iff.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [h, hx.dim]
  omega

theorem fixSpace_sup_commSpace : fixSpace x ⊔ commSpace x = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_sup_of_inf_eq_bot (fixSpace_inf_commSpace (n := 7) ⟨3, rfl⟩ hx.pow), add_comm,
    finrank_commSpace_add_finrank_fixSpace]

theorem le_fixSpace_of_comm {c : V ≃ₗ[ZMod 2] V} (hcx : c * x = x * c)
    (hc : c * c = 1 ∨ c ^ 3 = 1) {U : Submodule (ZMod 2) V} (hUx : ∀ u ∈ U, x u ∈ U)
    (hUc : ∀ u ∈ U, c u ∈ U) (hUF : U ⊓ fixSpace x = ⊥) (hU3 : finrank (ZMod 2) U = 3) :
    U ≤ fixSpace c := by
  set W := U ⊓ fixSpace c with hWdef
  have hWx : ∀ w ∈ W, x w ∈ W := fun w hw => Submodule.mem_inf.mpr
    ⟨hUx w (Submodule.mem_inf.mp hw).1, apply_mem_fixSpace hcx.symm (Submodule.mem_inf.mp hw).2⟩
  have h3 : finrank (ZMod 2) W % 3 = 0 := by
    have := mod_three_of_pow_seven hx.pow hWx
    have hbot : W ⊓ fixSpace x = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans hUF.le)
    rw [hbot, finrank_bot] at this
    exact this
  have hle : finrank (ZMod 2) W ≤ 3 := hU3 ▸ Submodule.finrank_mono inf_le_left
  have hpos : 0 < finrank (ZMod 2) W := by
    rcases hc with hc2 | hc3
    · have hne : U ≠ ⊥ := by
        rintro rfl
        rw [finrank_bot] at hU3
        exact absurd hU3 (by norm_num)
      obtain ⟨a, haU, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hcc : ∀ v, c (c v) = v := fun v => by
        rw [← LinearEquiv.mul_apply, hc2]
        rfl
      by_cases hca : c a = a
      · exact Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨⟨a, Submodule.mem_inf.mpr ⟨haU, mem_fixSpace.mpr hca⟩⟩,
            fun h => ha0 (congrArg Subtype.val h)⟩
      · refine Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨⟨c a + a, Submodule.mem_inf.mpr ⟨U.add_mem (hUc a haU) haU, mem_fixSpace.mpr ?_⟩⟩,
            fun h => hca ?_⟩
        · rw [map_add, hcc, add_comm]
        · have h' : c a + a = 0 := congrArg Subtype.val h
          exact (eq_neg_of_add_eq_zero_left h').trans (neg_eq_self' a)
    · have := mod_two_of_pow_three hc3 hUc
      rw [hU3] at this
      change 3 % 2 = finrank (ZMod 2) ↥W % 2 at this
      omega
  have hW3 : finrank (ZMod 2) W = 3 := by omega
  have hWU : W = U := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hW3, hU3])
  rw [← hWU]
  exact inf_le_right

theorem commSpace_le_fixSpace_of_comm {c : V ≃ₗ[ZMod 2] V} (hcx : c * x = x * c)
    (hc : c * c = 1 ∨ c ^ 3 = 1) : commSpace x ≤ fixSpace c := by
  obtain ⟨-, hA3, hB3⟩ := hx.finrank_fixSpace
  have hxx : x * x = x * x := rfl
  refine (commSpace_le_sup hx.pow).trans (sup_le ?_ ?_)
  · exact hx.le_fixSpace_of_comm hcx hc (kA_invariant hxx) (kA_invariant hcx)
      kA_inf_fixSpace hA3
  · exact hx.le_fixSpace_of_comm hcx hc (kB_invariant hxx) (kB_invariant hcx)
      kB_inf_fixSpace hB3

theorem commSpace_le_fixSpace {c : V ≃ₗ[ZMod 2] V} (hcx : c * x = x * c)
    (hc : c * c = 1 ∨ c ^ 3 = 1) : commSpace c ≤ fixSpace x := by
  intro w hw
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
  have hv : v ∈ fixSpace x ⊔ commSpace x := by
    rw [hx.fixSpace_sup_commSpace]
    exact Submodule.mem_top
  obtain ⟨f, hf, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
  have hcu : c u = u := mem_fixSpace.mp (hx.commSpace_le_fixSpace_of_comm hcx hc hu)
  rw [map_add, hcu, add_sub_add_right_eq_sub]
  exact (fixSpace x).sub_mem (apply_mem_fixSpace hcx hf) hf

end Hyp

end Seven

end CFSG.LargeExtraspecial.AS35QCo
