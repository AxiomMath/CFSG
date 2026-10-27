module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem natCard_submodule [FiniteDimensional (ZMod 2) V] (W : Submodule (ZMod 2) V) :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem two_pow_modEq [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime]
    {g : V ≃ₗ[ZMod 2] V} (hg : g ^ p = 1) {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, g w ∈ W) :
    2 ^ finrank (ZMod 2) W ≡ 2 ^ finrank (ZMod 2) ↥(W ⊓ fixSpace g) [MOD p] := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype W := Fintype.ofFinite W
  let f : Function.End W := fun w => ⟨g w, hW w w.2⟩
  have hfp : ∀ k : ℕ, ∀ w : W, ((f ^ k) w : V) = (g ^ k) w := by
    intro k
    induction k with
    | zero => intro w; rfl
    | succ k ih =>
      intro w
      rw [pow_succ', pow_succ', LinearEquiv.mul_apply]
      exact congrArg g (ih w)
  have hf : f ^ p ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one, hfp, hg]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  rw [← Nat.card_eq_fintype_card, natCard_submodule] at h
  convert h using 1
  rw [← natCard_submodule, Fintype.card_eq_nat_card]
  apply Nat.card_congr
  exact {
    toFun := fun x => ⟨⟨x.1, (Submodule.mem_inf.mp x.2).1⟩, by
      change f _ = _
      apply Subtype.ext
      exact mem_fixSpace.mp (Submodule.mem_inf.mp x.2).2⟩
    invFun := fun x => ⟨x.1.1, Submodule.mem_inf.mpr ⟨x.1.2, mem_fixSpace.mpr
      (congrArg Subtype.val (x.2 : f x.1 = x.1))⟩⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl }

theorem two_pow_mod_three (a : ℕ) : 2 ^ a % 3 = 2 ^ (a % 2) % 3 := by
  conv_lhs => rw [← Nat.div_add_mod a 2, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_mod_five (a : ℕ) : 2 ^ a % 5 = 2 ^ (a % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod a 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_mod_seven (a : ℕ) : 2 ^ a % 7 = 2 ^ (a % 3) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem mod_two_of_pow_three [FiniteDimensional (ZMod 2) V] {g : V ≃ₗ[ZMod 2] V}
    (hg : g ^ 3 = 1) {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, g w ∈ W) :
    finrank (ZMod 2) W % 2 = finrank (ZMod 2) ↥(W ⊓ fixSpace g) % 2 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := two_pow_modEq hg hW
  unfold Nat.ModEq at h
  rw [two_pow_mod_three, two_pow_mod_three (finrank (ZMod 2) ↥(W ⊓ fixSpace g))] at h
  have h1 := Nat.mod_lt (finrank (ZMod 2) W) (show 0 < 2 by norm_num)
  have h2 := Nat.mod_lt (finrank (ZMod 2) ↥(W ⊓ fixSpace g)) (show 0 < 2 by norm_num)
  interval_cases (finrank (ZMod 2) W % 2) <;>
    interval_cases (finrank (ZMod 2) ↥(W ⊓ fixSpace g) % 2) <;> simp_all

theorem mod_four_of_pow_five [FiniteDimensional (ZMod 2) V] {g : V ≃ₗ[ZMod 2] V}
    (hg : g ^ 5 = 1) {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, g w ∈ W) :
    finrank (ZMod 2) W % 4 = finrank (ZMod 2) ↥(W ⊓ fixSpace g) % 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := two_pow_modEq hg hW
  unfold Nat.ModEq at h
  rw [two_pow_mod_five, two_pow_mod_five (finrank (ZMod 2) ↥(W ⊓ fixSpace g))] at h
  have h1 := Nat.mod_lt (finrank (ZMod 2) W) (show 0 < 4 by norm_num)
  have h2 := Nat.mod_lt (finrank (ZMod 2) ↥(W ⊓ fixSpace g)) (show 0 < 4 by norm_num)
  interval_cases (finrank (ZMod 2) W % 4) <;>
    interval_cases (finrank (ZMod 2) ↥(W ⊓ fixSpace g) % 4) <;> simp_all

theorem mod_three_of_pow_seven [FiniteDimensional (ZMod 2) V] {g : V ≃ₗ[ZMod 2] V}
    (hg : g ^ 7 = 1) {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, g w ∈ W) :
    finrank (ZMod 2) W % 3 = finrank (ZMod 2) ↥(W ⊓ fixSpace g) % 3 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := two_pow_modEq hg hW
  unfold Nat.ModEq at h
  rw [two_pow_mod_seven, two_pow_mod_seven (finrank (ZMod 2) ↥(W ⊓ fixSpace g))] at h
  have h1 := Nat.mod_lt (finrank (ZMod 2) W) (show 0 < 3 by norm_num)
  have h2 := Nat.mod_lt (finrank (ZMod 2) ↥(W ⊓ fixSpace g)) (show 0 < 3 by norm_num)
  interval_cases (finrank (ZMod 2) W % 3) <;>
    interval_cases (finrank (ZMod 2) ↥(W ⊓ fixSpace g) % 3) <;> simp_all

theorem two_nsmul_eq_zero (v : V) : (2 : ℕ) • v = 0 := by
  rw [two_nsmul, ← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem odd_nsmul_eq {n : ℕ} (hn : Odd n) (v : V) : n • v = v := by
  obtain ⟨m, rfl⟩ := hn
  have h : (2 * m) • v = 0 := by rw [mul_comm, mul_nsmul, two_nsmul_eq_zero]
  rw [add_nsmul, one_nsmul, h, zero_add]

theorem fixSpace_inf_commSpace {g : V ≃ₗ[ZMod 2] V} {n : ℕ} (hn : Odd n) (hg : g ^ n = 1) :
    fixSpace g ⊓ commSpace g = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvf, hvc⟩ := Submodule.mem_inf.mp hv
  obtain ⟨w, hw⟩ := mem_commSpace.mp hvc
  rw [mem_fixSpace] at hvf
  have hgw : g w = w + v := by rw [← hw]; abel
  have key : ∀ k : ℕ, (g ^ k) w = w + k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, hvf, hgw,
        add_nsmul, one_nsmul]; abel
  have h := key n
  rw [hg, odd_nsmul_eq hn] at h
  have h' : w = w + v := h
  rw [left_eq_add] at h'
  rw [h', Submodule.mem_bot]

variable [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem fixSpace_le_orthogonal {g : V ≃ₗ[ZMod 2] V} (hg : ∀ v, q (g v) = q v) :
    fixSpace g ≤ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace g) := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hu
  rw [mem_fixSpace] at hv
  change QuadraticMap.polar q (g w - w) v = 0
  rw [QuadraticMap.polar_sub_left]
  nth_rewrite 1 [← hv]
  have : QuadraticMap.polar q (g w) (g v) = QuadraticMap.polar q w v := by
    simp only [QuadraticMap.polar, ← map_add, hg]
  rw [this, sub_self]

theorem fixSpace_eq_orthogonal (hq : q.polarBilin.Nondegenerate) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ v, q (g v) = q v) :
    fixSpace g = LinearMap.BilinForm.orthogonal q.polarBilin (commSpace g) := by
  refine Submodule.eq_of_le_of_finrank_eq (fixSpace_le_orthogonal hg) ?_
  rw [LinearMap.BilinForm.finrank_orthogonal hq]
  have := finrank_commSpace_add_finrank_fixSpace g
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem polarBilin_isRefl (q : QuadraticForm (ZMod 2) V) : q.polarBilin.IsRefl :=
  (QuadraticMap.isSymm_polarBilin q).isRefl

theorem commSpace_eq_orthogonal (hq : q.polarBilin.Nondegenerate) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ v, q (g v) = q v) :
    commSpace g = LinearMap.BilinForm.orthogonal q.polarBilin (fixSpace g) := by
  rw [fixSpace_eq_orthogonal hq hg,
    LinearMap.BilinForm.orthogonal_orthogonal hq (polarBilin_isRefl q)]

theorem commSpace_le_fixSpace_swap (hq : q.polarBilin.Nondegenerate) {g h : V ≃ₗ[ZMod 2] V}
    (hg : ∀ v, q (g v) = q v) (hh : ∀ v, q (h v) = q v) (hle : commSpace g ≤ fixSpace h) :
    commSpace h ≤ fixSpace g := by
  rw [commSpace_eq_orthogonal hq hh, fixSpace_eq_orthogonal hq hg]
  exact LinearMap.BilinForm.orthogonal_le hle

section Invariance

omit [FiniteDimensional (ZMod 2) V]

theorem apply_mem_fixSpace {g k : V ≃ₗ[ZMod 2] V} (h : g * k = k * g) {v : V}
    (hv : v ∈ fixSpace k) : g v ∈ fixSpace k := by
  rw [mem_fixSpace] at hv ⊢
  rw [← LinearEquiv.mul_apply, ← h, LinearEquiv.mul_apply, hv]

theorem apply_mem_commSpace {g k : V ≃ₗ[ZMod 2] V} (h : g * k = k * g) {v : V}
    (hv : v ∈ commSpace k) : g v ∈ commSpace k := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  refine mem_commSpace.mpr ⟨g w, ?_⟩
  rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, h]

theorem fixSpace_conj (P g : V ≃ₗ[ZMod 2] V) :
    fixSpace (P * g * P⁻¹) = (fixSpace g).map (P : V →ₗ[ZMod 2] V) := by
  ext v
  rw [Submodule.mem_map, mem_fixSpace]
  constructor
  · intro h
    refine ⟨P⁻¹ v, ?_, ?_⟩
    · rw [mem_fixSpace]
      have := congrArg (P⁻¹ : V ≃ₗ[ZMod 2] V) h
      simpa [LinearEquiv.mul_apply] using this
    · simp
  · rintro ⟨w, hw, rfl⟩
    rw [mem_fixSpace] at hw
    simp [LinearEquiv.mul_apply, hw]

theorem commSpace_conj (P g : V ≃ₗ[ZMod 2] V) :
    commSpace (P * g * P⁻¹) = (commSpace g).map (P : V →ₗ[ZMod 2] V) := by
  ext v
  rw [Submodule.mem_map, mem_commSpace]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨g (P⁻¹ w) - P⁻¹ w, sub_mem_commSpace _ _, ?_⟩
    simp [LinearEquiv.mul_apply]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, rfl⟩ := mem_commSpace.mp hw
    refine ⟨P x, ?_⟩
    simp [LinearEquiv.mul_apply]

theorem one_apply' (v : V) : (1 : V ≃ₗ[ZMod 2] V) v = v := rfl

theorem neg_eq_self' (v : V) : -v = v :=
  neg_eq_of_add_eq_zero_left (by rw [← two_nsmul]; exact two_nsmul_eq_zero v)

theorem mul_inv_apply (g : V ≃ₗ[ZMod 2] V) (v : V) : g (g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel, one_apply']

theorem inv_mul_apply (g : V ≃ₗ[ZMod 2] V) (v : V) : g⁻¹ (g v) = v := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel, one_apply']

theorem fixSpace_inv (g : V ≃ₗ[ZMod 2] V) : fixSpace g⁻¹ = fixSpace g := by
  ext v
  rw [mem_fixSpace, mem_fixSpace]
  constructor
  · intro h
    have := congrArg g h
    rw [mul_inv_apply] at this
    exact this.symm
  · intro h
    have := congrArg (g⁻¹ : V ≃ₗ[ZMod 2] V) h
    rw [inv_mul_apply] at this
    exact this.symm

theorem commSpace_inv (g : V ≃ₗ[ZMod 2] V) : commSpace g⁻¹ = commSpace g := by
  ext v
  rw [mem_commSpace, mem_commSpace]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨g⁻¹ w, by rw [mul_inv_apply, ← neg_sub, neg_eq_self']⟩
  · rintro ⟨w, rfl⟩
    exact ⟨g w, by rw [inv_mul_apply, ← neg_sub, neg_eq_self']⟩

end Invariance

section OrderThree

omit [FiniteDimensional (ZMod 2) V]

theorem pow_three_apply {g : V ≃ₗ[ZMod 2] V} (hg : g ^ 3 = 1) (v : V) : g (g (g v)) = v := by
  have := congrArg (fun h : V ≃ₗ[ZMod 2] V => h v) hg
  simpa [pow_succ, LinearEquiv.mul_apply] using this

theorem sq_add_add_eq_zero {g : V ≃ₗ[ZMod 2] V} (hg : g ^ 3 = 1) {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, g u ∈ U) (hfree : U ⊓ fixSpace g = ⊥) {u : V} (hu : u ∈ U) :
    g (g u) + g u + u = 0 := by
  have hmem : g (g u) + g u + u ∈ U ⊓ fixSpace g := by
    refine Submodule.mem_inf.mpr ⟨U.add_mem (U.add_mem (hU _ (hU _ hu)) (hU _ hu)) hu, ?_⟩
    rw [mem_fixSpace, map_add, map_add, pow_three_apply hg]
    abel
  rw [hfree, Submodule.mem_bot] at hmem
  exact hmem

theorem le_sup_fix_comm {g : V ≃ₗ[ZMod 2] V} (hg : g ^ 3 = 1) {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, g u ∈ U) : U ≤ (U ⊓ fixSpace g) ⊔ (U ⊓ commSpace g) := by
  intro u hu
  have h1 : u + g u + g (g u) ∈ U ⊓ fixSpace g := by
    refine Submodule.mem_inf.mpr ⟨U.add_mem (U.add_mem hu (hU _ hu)) (hU _ (hU _ hu)), ?_⟩
    rw [mem_fixSpace, map_add, map_add, pow_three_apply hg]
    abel
  have h2 : g u + g (g u) ∈ U ⊓ commSpace g := by
    refine Submodule.mem_inf.mpr ⟨U.add_mem (hU _ hu) (hU _ (hU _ hu)), ?_⟩
    refine mem_commSpace.mpr ⟨g u, ?_⟩
    rw [sub_eq_add_neg, neg_eq_self', add_comm]
  have e : u = (u + g u + g (g u)) + (g u + g (g u)) := by
    have h := two_nsmul_eq_zero (g u + g (g u))
    rw [two_nsmul] at h
    calc u = u + ((g u + g (g u)) + (g u + g (g u))) := by rw [h, add_zero]
      _ = (u + g u + g (g u)) + (g u + g (g u)) := by abel
  rw [e]
  exact Submodule.add_mem_sup h1 h2

theorem le_fixSpace_of_inf_commSpace {g : V ≃ₗ[ZMod 2] V} (hg : g ^ 3 = 1)
    {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, g u ∈ U) (h : U ⊓ commSpace g = ⊥) :
    U ≤ fixSpace g := by
  intro u hu
  have := le_sup_fix_comm hg hU hu
  rw [h, sup_bot_eq] at this
  exact (Submodule.mem_inf.mp this).2

theorem eq_add_of_add_add {a b c : V} (h : a + b + c = 0) : a = b + c := by
  have h2 := two_nsmul_eq_zero (b + c)
  rw [two_nsmul] at h2
  calc a = a + b + c + (b + c) := by rw [add_assoc a b c, add_assoc, h2, add_zero]
    _ = b + c := by rw [h, zero_add]

theorem split_aux {A B : V ≃ₗ[ZMod 2] V} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hc : ∀ v, A (B v) = B (A v)) {x : V} (hAx : A (A x) = A x + x) (hBx : B (B x) = B x + x)
    (hABx : A (A (B x)) = A (B x) + B x) :
    A (B (B (A (B x) + A (B (A (B x)))))) = A (B x) + A (B (A (B x))) := by
  have h3A := pow_three_apply hA
  have h3B := pow_three_apply hB
  have hc' : ∀ v, B (A v) = A (B v) := fun v => (hc v).symm
  have t1 : A (B (B (A (B x)))) = A (A x) := by
    simp only [hc', h3B]
  have t2 : A (B (B (A (B (A (B x)))))) = B x := by
    simp only [hc', h3A, h3B]
  have t3 : A (B (A (B x))) = A (B x) + B x + (A x + x) := by
    rw [← hc (B x), hBx, map_add, map_add, hABx, hAx]
  rw [map_add, map_add, map_add, t1, t2, t3, hAx]
  have h2 := two_nsmul_eq_zero (A (B x))
  rw [two_nsmul] at h2
  calc A x + x + B x = A x + x + B x + (A (B x) + A (B x)) := by rw [h2, add_zero]
    _ = A (B x) + (A (B x) + B x + (A x + x)) := by abel

theorem le_sup_split {A B : V ≃ₗ[ZMod 2] V} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hAB : A * B = B * A) {U : Submodule (ZMod 2) V} (hUA : ∀ u ∈ U, A u ∈ U)
    (hUB : ∀ u ∈ U, B u ∈ U) (hfA : U ⊓ fixSpace A = ⊥) (hfB : U ⊓ fixSpace B = ⊥) :
    U ≤ (U ⊓ fixSpace (A * B)) ⊔ (U ⊓ fixSpace (A * B * B)) := by
  have hc : ∀ v, A (B v) = B (A v) := fun v => by
    rw [← LinearEquiv.mul_apply, hAB, LinearEquiv.mul_apply]
  intro x hx
  have hAx := eq_add_of_add_add (sq_add_add_eq_zero hA hUA hfA hx)
  have hBx := eq_add_of_add_add (sq_add_add_eq_zero hB hUB hfB hx)
  have hABx := eq_add_of_add_add (sq_add_add_eq_zero hA hUA hfA (hUB _ hx))
  have hc' : ∀ v, B (A v) = A (B v) := fun v => (hc v).symm
  have hC3 : ∀ v, A (B (A (B (A (B v))))) = v := fun v => by
    simp only [hc', pow_three_apply hA, pow_three_apply hB]
  set y := A (B x) with hy
  have h1 : x + y + A (B y) ∈ U ⊓ fixSpace (A * B) := by
    refine Submodule.mem_inf.mpr ⟨U.add_mem (U.add_mem hx (hUA _ (hUB _ hx)))
      (hUA _ (hUB _ (hUA _ (hUB _ hx)))), ?_⟩
    rw [mem_fixSpace, LinearEquiv.mul_apply, map_add, map_add, map_add, map_add, hy, hC3]
    abel
  have h2 : y + A (B y) ∈ U ⊓ fixSpace (A * B * B) := by
    refine Submodule.mem_inf.mpr ⟨U.add_mem (hUA _ (hUB _ hx))
      (hUA _ (hUB _ (hUA _ (hUB _ hx)))), ?_⟩
    rw [mem_fixSpace, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact split_aux hA hB hc hAx hBx hABx
  have e : x = (x + y + A (B y)) + (y + A (B y)) := by
    have h := two_nsmul_eq_zero (y + A (B y))
    rw [two_nsmul] at h
    calc x = x + ((y + A (B y)) + (y + A (B y))) := by rw [h, add_zero]
      _ = (x + y + A (B y)) + (y + A (B y)) := by abel
  rw [e]
  exact Submodule.add_mem_sup h1 h2

theorem inf_split_eq_bot {A B : V ≃ₗ[ZMod 2] V} {U : Submodule (ZMod 2) V}
    (hfB : U ⊓ fixSpace B = ⊥) :
    (U ⊓ fixSpace (A * B)) ⊓ (U ⊓ fixSpace (A * B * B)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  obtain ⟨hvU, h1⟩ := Submodule.mem_inf.mp hv1
  have h2 := (Submodule.mem_inf.mp hv2).2
  rw [mem_fixSpace, LinearEquiv.mul_apply] at h1
  rw [mem_fixSpace, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h2
  have hB : B v = v := by
    have := h2.trans h1.symm
    exact B.injective (A.injective this)
  have hmem : v ∈ U ⊓ fixSpace B := Submodule.mem_inf.mpr ⟨hvU, mem_fixSpace.mpr hB⟩
  rw [hfB, Submodule.mem_bot] at hmem
  exact hmem

end OrderThree

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_map_equiv (P : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (W.map (P : V →ₗ[ZMod 2] V)) = finrank (ZMod 2) W :=
  LinearEquiv.finrank_map_eq P W

theorem finrank_le_of_map_le (P : V ≃ₗ[ZMod 2] V) {W W' : Submodule (ZMod 2) V}
    (h : ∀ w ∈ W, P w ∈ W') : finrank (ZMod 2) W ≤ finrank (ZMod 2) W' := by
  rw [← finrank_map_equiv P W]
  apply Submodule.finrank_mono
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

theorem even_finrank_of_free {g : V ≃ₗ[ZMod 2] V} (hg : g ^ 3 = 1) {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, g w ∈ W) (hfree : W ⊓ fixSpace g = ⊥) : Even (finrank (ZMod 2) W) := by
  have h := mod_two_of_pow_three hg hW
  rw [hfree, finrank_bot] at h
  exact Nat.even_iff.mpr h

theorem finrank_sup_of_inf_eq_bot {U U' : Submodule (ZMod 2) V} (h : U ⊓ U' = ⊥) :
    finrank (ZMod 2) ↥(U ⊔ U') = finrank (ZMod 2) U + finrank (ZMod 2) U' := by
  have := Submodule.finrank_sup_add_finrank_inf_eq U U'
  rw [h, finrank_bot, add_zero] at this
  exact this

theorem finrank_split {A B S : V ≃ₗ[ZMod 2] V} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hAB : A * B = B * A) {U : Submodule (ZMod 2) V} (hUA : ∀ u ∈ U, A u ∈ U)
    (hUB : ∀ u ∈ U, B u ∈ U) (hfA : U ⊓ fixSpace A = ⊥) (hfB : U ⊓ fixSpace B = ⊥)
    (hSA : S * A = A * S) (hSB : S * B = B * B * S) (hS2 : S * S = 1)
    (hUS : ∀ u ∈ U, S u ∈ U) :
    finrank (ZMod 2) U = 2 * finrank (ZMod 2) ↥(U ⊓ fixSpace (A * B)) ∧
      Even (finrank (ZMod 2) ↥(U ⊓ fixSpace (A * B))) := by
  have h3B := pow_three_apply hB
  have hBS : ∀ v, B (S v) = S (B (B v)) := fun v => by
    have e1 : S (B (S v)) = B (B v) := by
      rw [← LinearEquiv.mul_apply S B, hSB, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        ← LinearEquiv.mul_apply S S, hS2, one_apply']
    have := congrArg S e1
    rwa [← LinearEquiv.mul_apply S S, hS2, one_apply'] at this
  have hSA' : ∀ v, S (A v) = A (S v) := fun v => by
    rw [← LinearEquiv.mul_apply, hSA, LinearEquiv.mul_apply]
  have hSB' : ∀ v, S (B v) = B (B (S v)) := fun v => by
    rw [← LinearEquiv.mul_apply, hSB, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have h12 : ∀ w ∈ U ⊓ fixSpace (A * B), S w ∈ U ⊓ fixSpace (A * B * B) := by
    intro w hw
    obtain ⟨hwU, hwf⟩ := Submodule.mem_inf.mp hw
    rw [mem_fixSpace, LinearEquiv.mul_apply] at hwf
    refine Submodule.mem_inf.mpr ⟨hUS w hwU, ?_⟩
    rw [mem_fixSpace, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hBS w, hBS (B (B w)),
      h3B (B w), ← hSA' (B w), hwf]
  have h21 : ∀ w ∈ U ⊓ fixSpace (A * B * B), S w ∈ U ⊓ fixSpace (A * B) := by
    intro w hw
    obtain ⟨hwU, hwf⟩ := Submodule.mem_inf.mp hw
    rw [mem_fixSpace, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hwf
    refine Submodule.mem_inf.mpr ⟨hUS w hwU, ?_⟩
    rw [mem_fixSpace, LinearEquiv.mul_apply, hBS w, ← hSA' (B (B w)), hwf]
  have hd := le_antisymm (finrank_le_of_map_le S h12) (finrank_le_of_map_le S h21)
  have hsup : U = (U ⊓ fixSpace (A * B)) ⊔ (U ⊓ fixSpace (A * B * B)) :=
    le_antisymm (le_sup_split hA hB hAB hUA hUB hfA hfB) (sup_le inf_le_left inf_le_left)
  have hdim : finrank (ZMod 2) U = finrank (ZMod 2) ↥(U ⊓ fixSpace (A * B)) +
      finrank (ZMod 2) ↥(U ⊓ fixSpace (A * B * B)) := by
    conv_lhs => rw [hsup]
    exact finrank_sup_of_inf_eq_bot (inf_split_eq_bot hfB)
  refine ⟨by rw [hdim, ← hd]; ring, ?_⟩
  apply even_finrank_of_free hA
  · intro w hw
    obtain ⟨hwU, hwf⟩ := Submodule.mem_inf.mp hw
    refine Submodule.mem_inf.mpr ⟨hUA w hwU, apply_mem_fixSpace ?_ hwf⟩
    rw [← mul_assoc, mul_assoc A B A, ← hAB, ← mul_assoc]
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    have : v ∈ U ⊓ fixSpace A := Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hv1).1, hv2⟩
    rwa [hfA] at this

end CFSG.LargeExtraspecial.AS35QCo
