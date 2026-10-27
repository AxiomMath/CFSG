module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L5Std
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.QuasithinUnique.A5.Kc3L5

open Matrix

theorem fixedAdd_invariant {Vg : Subgroup Gl} {a : Gl} (ha : a ∈ Subgroup.normalizer (Vg : Set Gl))
    {c : W} (hc : c ∈ fixedAdd (Vg : Set Gl)) : act a c ∈ fixedAdd (Vg : Set Gl) := by
  intro v hv
  have h1 : a⁻¹ * v * a ∈ Vg := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem ha) v).1 hv
    simpa using this
  have h2 : act (a⁻¹ * v * a) c = c := hc (a⁻¹ * v * a) h1
  calc act v (act a c) = act (v * a) c := (act_mul v a c).symm
    _ = act (a * (a⁻¹ * v * a)) c := by congr 1; group
    _ = act a (act (a⁻¹ * v * a) c) := act_mul _ _ _
    _ = act a c := by rw [h2]

theorem num_card_cases {n : ℕ} (hk : ∃ k : ℕ, k ≤ 5 ∧ n = 2 ^ k)
    (h : n ≡ 1 [MOD 5] ∨ n ≡ 2 [MOD 5]) : n = 1 ∨ n = 2 ∨ n = 16 ∨ n = 32 := by
  obtain ⟨k, hk, rfl⟩ := hk
  interval_cases k <;> simp [Nat.ModEq] at h ⊢

theorem eq_one_or_two_of_dvd {n : ℕ} (h : n ∣ 2) : n = 1 ∨ n = 2 :=
  (Nat.dvd_prime Nat.prime_two).1 h

theorem fixed_mod_five {Vg : Subgroup Gl} {x : Gl} (hx5 : orderOf x = 5)
    (hxN : x ∈ Subgroup.normalizer (Vg : Set Gl)) :
    Nat.card (fixedAdd (Vg : Set Gl)) ≡
      Nat.card ↥(fixedAdd (Vg : Set Gl) ⊓ fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl))
        [MOD 5] ∧
    Nat.card ↥(fixedAdd (Vg : Set Gl) ⊓
      fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl)) ∣ 2 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P : Subgroup Gl := Subgroup.zpowers x with hP
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [hP, Nat.card_zpowers, hx5]; norm_num)
  have hPN : P ≤ Subgroup.normalizer (Vg : Set Gl) := (Subgroup.zpowers_le).2 hxN
  have hinv : ∀ a ∈ P, ∀ c ∈ fixedAdd (Vg : Set Gl), act a c ∈ fixedAdd (Vg : Set Gl) :=
    fun a ha c hc => fixedAdd_invariant (hPN ha) hc
  refine ⟨card_modEq_fixed (p := 5) P hP5 _ hinv, ?_⟩
  have h1 := AddSubgroup.card_dvd_of_le (inf_le_right : fixedAdd (Vg : Set Gl) ⊓
    fixedAdd (P : Set Gl) ≤ fixedAdd (P : Set Gl))
  rwa [card_fix_five hx5] at h1

theorem card_fixedAdd_cases {Vg : Subgroup Gl} (hV2 : IsPGroup 2 Vg) (hV16 : Nat.card Vg = 16)
    {x : Gl} (hx5 : orderOf x = 5) (hxN : x ∈ Subgroup.normalizer (Vg : Set Gl)) :
    Nat.card (fixedAdd (Vg : Set Gl)) = 2 ∨ Nat.card (fixedAdd (Vg : Set Gl)) = 16 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hmod, hdvd⟩ := fixed_mod_five hx5 hxN
  have hcases : Nat.card (fixedAdd (Vg : Set Gl)) ≡ 1 [MOD 5] ∨
      Nat.card (fixedAdd (Vg : Set Gl)) ≡ 2 [MOD 5] := by
    rcases eq_one_or_two_of_dvd hdvd with h | h
    · left; rw [h] at hmod; exact hmod
    · right; rw [h] at hmod; exact hmod
  have h4 := num_card_cases (card_eq_pow _) hcases
  have heven : Nat.card (fixedAdd (Vg : Set Gl)) ≠ 1 := by
    have h2 := card_modEq_fixed (p := 2) Vg hV2 ⊤ (fun _ _ _ _ => AddSubgroup.mem_top _)
    rw [AddSubgroup.card_top, card_W, top_inf_eq] at h2
    intro h1
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hne : Nat.card (fixedAdd (Vg : Set Gl)) ≠ 32 := by
    intro h32
    have htop : fixedAdd (Vg : Set Gl) = ⊤ := by
      rw [← AddSubgroup.card_eq_iff_eq_top, h32, card_W]
    have hbot : Vg = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      refine eq_one_of_act_eq v fun w => ?_
      have hw : w ∈ fixedAdd (Vg : Set Gl) := by rw [htop]; trivial
      exact hw v hv
    rw [hbot, Subgroup.card_bot] at hV16
    omega
  omega

theorem exists_conj_U0 {Vg : Subgroup Gl} (hV16 : Nat.card Vg = 16)
    (h16 : Nat.card (fixedAdd (Vg : Set Gl)) = 16) :
    ∃ τ : Gl, Vg.map (MulAut.conj τ).toMonoidHom = U0 := by
  obtain ⟨τ, hτ⟩ := exists_conj_M0 _ h16
  refine ⟨τ, ?_⟩
  have hle : Vg.map (MulAut.conj τ).toMonoidHom ≤ U0 := by
    rintro _ ⟨v, hv, rfl⟩ z hz
    have hw : act τ⁻¹ z ∈ fixedAdd (Vg : Set Gl) := by
      rw [hτ]
      have : act τ (act τ⁻¹ z) = z := by rw [← act_mul, mul_inv_cancel, act_one]
      rw [this]
      exact hz
    have h1 : act v (act τ⁻¹ z) = act τ⁻¹ z := hw v hv
    have h2 : act τ (act τ⁻¹ z) = z := by rw [← act_mul, mul_inv_cancel, act_one]
    show act (τ * v * τ⁻¹) z = z
    rw [act_mul, act_mul, h1, h2]
  have hcard : Nat.card U0 ≤ Nat.card (Vg.map (MulAut.conj τ).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective, hV16]
    exact card_U0_le
  exact Subgroup.eq_of_le_of_card_ge hle hcard

@[expose] def dualGl (g : Gl) : Gl :=
  ⟨((g⁻¹ : Gl) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ, by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one], by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem dualGl_mul (g h : Gl) : dualGl (g * h) = dualGl g * dualGl h := by
  apply Units.ext
  simp [dualGl, _root_.mul_inv_rev, Matrix.transpose_mul]

theorem dualGl_dualGl (g : Gl) : dualGl (dualGl g) = g := by
  apply Units.ext
  simp [dualGl]

@[expose] def dualEquiv : Gl ≃* Gl where
  toFun := dualGl
  invFun := dualGl
  left_inv := dualGl_dualGl
  right_inv := dualGl_dualGl
  map_mul' := dualGl_mul

@[expose] def dot (a b : W) : ZMod 2 := ∑ i, a i * b i

theorem dot_add (a b c : W) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_act_dual (g : Gl) (w u : W) : dot (act (dualGl g) w) u = dot w (act g⁻¹ u) := by
  have h1 : dot (act (dualGl g) w) u = (act (dualGl g) w) ⬝ᵥ u := rfl
  have h2 : dot w (act g⁻¹ u) = w ⬝ᵥ (act g⁻¹ u) := rfl
  rw [h1, h2]
  simp [act, dualGl, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem act_sub (g : Gl) (a b : W) : act g (a - b) = act g a - act g b := by
  simp [act, Matrix.mulVec_sub]

theorem dot_sub (a b c : W) : dot a (b - c) = dot a b - dot a c := by
  simp only [dot, Pi.sub_apply, mul_sub]
  exact Finset.sum_sub_distrib _ _

theorem dot_single (a : W) (i : Fin 5) : dot a (Pi.single i 1) = a i := by
  simp [dot, Pi.single_apply]

theorem exists_orth : ∀ a : W, a ≠ 0 → ∃ w : W, w ≠ 0 ∧ dot a w = 0 := by
  decide +kernel

theorem fixed_zpowers_iff {x : Gl} {u : W} :
    (∀ g ∈ (Subgroup.zpowers x : Subgroup Gl), act g u = u) ↔ act x u = u := by
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    clear hg
    induction n using Int.induction_on with
    | zero => simp [act_one]
    | succ n ih =>
      rw [_root_.zpow_add_one, act_mul, h, ih]
    | pred n ih =>
      have h1 : act x⁻¹ u = u := by
        have := congrArg (act x⁻¹) h
        rw [← act_mul, inv_mul_cancel, act_one] at this
        exact this.symm
      rw [_root_.zpow_sub_one, act_mul, h1, ih]

theorem exists_fixed_vector {Vg : Subgroup Gl} {x : Gl} (hx5 : orderOf x = 5)
    (hxN : x ∈ Subgroup.normalizer (Vg : Set Gl))
    (h2 : Nat.card (fixedAdd (Vg : Set Gl)) = 2) :
    ∃ c : W, c ≠ 0 ∧ c ∈ fixedAdd (Vg : Set Gl) ∧
      c ∈ fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl) := by
  classical
  obtain ⟨hmod, hdvd⟩ := fixed_mod_five hx5 hxN
  rw [h2] at hmod
  have hinf : Nat.card ↥(fixedAdd (Vg : Set Gl) ⊓
      fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl)) = 2 := by
    rcases eq_one_or_two_of_dvd hdvd with h | h
    · rw [h] at hmod
      exact absurd hmod (by decide)
    · exact h
  have heq : fixedAdd (Vg : Set Gl) ⊓ fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl) =
      fixedAdd (Vg : Set Gl) :=
    AddSubgroup.eq_of_le_of_card_ge inf_le_left (by rw [hinf, h2])
  have hne : ∃ c ∈ fixedAdd (Vg : Set Gl), c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : fixedAdd (Vg : Set Gl) = ⊥ := by
      rw [AddSubgroup.eq_bot_iff_forall]
      exact hcon
    rw [hbot, AddSubgroup.card_bot] at h2
    omega
  obtain ⟨c, hc, hc0⟩ := hne
  refine ⟨c, hc0, hc, ?_⟩
  have : c ∈ fixedAdd (Vg : Set Gl) ⊓ fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl) := by
    rw [heq]; exact hc
  exact (AddSubgroup.mem_inf.1 this).2

@[expose] def hyper (a : W) : AddSubgroup W where
  carrier := {w | dot a w = 0}
  add_mem' := by
    intro b c hb hc
    have hb' : dot a b = 0 := hb
    have hc' : dot a c = 0 := hc
    show dot a (b + c) = 0
    rw [dot_add, hb', hc']
    rfl
  zero_mem' := by
    show dot a 0 = 0
    simp [dot]
  neg_mem' := by
    intro b hb
    have hb' : dot a b = 0 := hb
    show dot a (-b) = 0
    rw [W_neg, hb']

theorem dual_data {Vg : Subgroup Gl} (hV2 : IsPGroup 2 Vg) (hV16 : Nat.card Vg = 16) {x : Gl}
    (hx5 : orderOf x = 5) (hxN : x ∈ Subgroup.normalizer (Vg : Set Gl)) :
    IsPGroup 2 (Vg.map dualEquiv.toMonoidHom) ∧ Nat.card (Vg.map dualEquiv.toMonoidHom) = 16 ∧
      orderOf (dualEquiv x) = 5 ∧
      dualEquiv x ∈ Subgroup.normalizer ((Vg.map dualEquiv.toMonoidHom : Subgroup Gl) : Set Gl) := by
  refine ⟨hV2.map dualEquiv.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective dualEquiv.injective, hV16]
  · rw [MulEquiv.orderOf_eq, hx5]
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have hmap : ∀ z : Gl, z ∈ Vg.map dualEquiv.toMonoidHom ↔ dualEquiv.symm z ∈ Vg :=
      fun z => Subgroup.mem_map_equiv
    rw [hmap, hmap]
    have e : dualEquiv.symm (dualEquiv x * y * (dualEquiv x)⁻¹) =
        x * dualEquiv.symm y * x⁻¹ := by
      simp [map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 hxN _

theorem W_sub_eq_zero {a b : W} : a - b = 0 ↔ a = b := sub_eq_zero

theorem not_both_two {Vg : Subgroup Gl} (hV2 : IsPGroup 2 Vg) (hV16 : Nat.card Vg = 16) {x : Gl}
    (hx5 : orderOf x = 5) (hxN : x ∈ Subgroup.normalizer (Vg : Set Gl))
    (h2 : Nat.card (fixedAdd (Vg : Set Gl)) = 2)
    (h2' : Nat.card (fixedAdd ((Vg.map dualEquiv.toMonoidHom : Subgroup Gl) : Set Gl)) = 2) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hV2', hV16', hx5', hxN'⟩ := dual_data hV2 hV16 hx5 hxN
  obtain ⟨c, hc0, hcV, hcx⟩ := exists_fixed_vector hx5 hxN h2
  obtain ⟨c', hc'0, hc'V, hc'x⟩ := exists_fixed_vector hx5' hxN' h2'
  have hc'v : ∀ v ∈ Vg, ∀ u : W, dot c' (act v u) = dot c' u := by
    intro v hv u
    have hmem : dualGl v⁻¹ ∈ ((Vg.map dualEquiv.toMonoidHom : Subgroup Gl) : Set Gl) :=
      Subgroup.mem_map.2 ⟨v⁻¹, inv_mem hv, rfl⟩
    have h1 : act (dualGl v⁻¹) c' = c' := hc'V _ hmem
    have h3 : dot (act (dualGl v⁻¹) c') u = dot c' (act (v⁻¹)⁻¹ u) := dot_act_dual _ _ _
    rw [h1, inv_inv] at h3
    exact h3.symm
  have hc'x' : ∀ u : W, dot c' (act x u) = dot c' u := by
    intro u
    have hmem : dualGl x⁻¹ ∈ ((Subgroup.zpowers (dualEquiv x) : Subgroup Gl) : Set Gl) := by
      have : dualGl x⁻¹ = (dualEquiv x)⁻¹ := map_inv dualEquiv x
      rw [this]
      exact inv_mem (Subgroup.mem_zpowers _)
    have h1 : act (dualGl x⁻¹) c' = c' := hc'x _ hmem
    have h3 : dot (act (dualGl x⁻¹) c') u = dot c' (act (x⁻¹)⁻¹ u) := dot_act_dual _ _ _
    rw [h1, inv_inv] at h3
    exact h3.symm
  have hcz : dot c' c = 0 := by
    have hHinv : ∀ a ∈ Vg, ∀ w ∈ hyper c', act a w ∈ hyper c' := by
      intro a ha w hw
      show dot c' (act a w) = 0
      rw [hc'v a ha]
      exact hw
    have hmod := card_modEq_fixed (p := 2) Vg hV2 (hyper c') hHinv
    have hne : Nat.card (hyper c') ≠ 1 := by
      intro h1
      obtain ⟨w, hw0, hw⟩ := exists_orth c' hc'0
      have hbot : hyper c' = ⊥ := by
        rw [AddSubgroup.eq_bot_iff_forall]
        intro y hy
        have := Nat.card_eq_one_iff_unique.1 h1
        exact congrArg Subtype.val (this.1.elim ⟨y, hy⟩ ⟨0, (hyper c').zero_mem⟩)
      have : w ∈ hyper c' := hw
      rw [hbot, AddSubgroup.mem_bot] at this
      exact hw0 this
    obtain ⟨k, hk5, hk⟩ := card_eq_pow (hyper c')
    have hk0 : k ≠ 0 := fun h0 => hne (by rw [hk, h0]; rfl)
    have heven : 2 ∣ Nat.card (hyper c') := by
      rw [hk]; exact dvd_pow_self 2 hk0
    have hdv : Nat.card ↥(hyper c' ⊓ fixedAdd (Vg : Set Gl)) ∣ 2 := by
      have := AddSubgroup.card_dvd_of_le (inf_le_right : hyper c' ⊓ fixedAdd (Vg : Set Gl) ≤
        fixedAdd (Vg : Set Gl))
      rwa [h2] at this
    have hev2 : 2 ∣ Nat.card ↥(hyper c' ⊓ fixedAdd (Vg : Set Gl)) := by
      rw [Nat.ModEq] at hmod
      omega
    have heq : Nat.card ↥(hyper c' ⊓ fixedAdd (Vg : Set Gl)) = 2 := by
      rcases eq_one_or_two_of_dvd hdv with h | h
      · rw [h] at hev2; omega
      · exact h
    have hinfeq : hyper c' ⊓ fixedAdd (Vg : Set Gl) = fixedAdd (Vg : Set Gl) :=
      AddSubgroup.eq_of_le_of_card_ge inf_le_right (by rw [heq, h2])
    have : c ∈ hyper c' ⊓ fixedAdd (Vg : Set Gl) := by rw [hinfeq]; exact hcV
    exact (AddSubgroup.mem_inf.1 this).1
  let δ : W →+ W := AddMonoidHom.mk' (fun u => act x u - u) (by
    intro a b
    funext i
    have := congrFun (act_add x a b) i
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    rw [this]
    ring)
  have hδ : ∀ u, δ u = act x u - u := fun u => rfl
  have hker : δ.ker = fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl) := by
    ext u
    rw [AddMonoidHom.mem_ker, hδ, W_sub_eq_zero]
    exact (fixed_zpowers_iff (x := x) (u := u)).symm
  have hkerc : Nat.card δ.ker = 2 := by rw [hker]; exact card_fix_five hx5
  have hD16 : Nat.card δ.range = 16 := by
    have := AddSubgroup.card_ker_mul_card_range δ
    rw [hkerc, card_W] at this
    omega
  have hDinv : ∀ g ∈ (Subgroup.zpowers x : Subgroup Gl), ∀ d ∈ δ.range, act g d ∈ δ.range := by
    rintro g hg _ ⟨u, rfl⟩
    refine ⟨act g u, ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hcomm : x ^ n * x = x * x ^ n := (Commute.zpow_left (Commute.refl x) n).eq
    rw [hδ, hδ, act_sub, ← act_mul, ← act_mul, hcomm]
  have hP5 : IsPGroup 5 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx5]; norm_num)
  have hmodD := card_modEq_fixed (p := 5) (Subgroup.zpowers x) hP5 δ.range hDinv
  have hdvD : Nat.card ↥(δ.range ⊓ fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl)) ∣ 2 := by
    have := AddSubgroup.card_dvd_of_le (inf_le_right : δ.range ⊓
      fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl) ≤
      fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl))
    rwa [card_fix_five hx5] at this
  have hcD : c ∉ δ.range := by
    intro hcDm
    have h1 : Nat.card ↥(δ.range ⊓ fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl)) = 1 := by
      rcases eq_one_or_two_of_dvd hdvD with h | h
      · exact h
      · rw [hD16, h] at hmodD
        exact absurd hmodD (by decide)
    have hbot : δ.range ⊓ fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl) = ⊥ := by
      rw [AddSubgroup.eq_bot_iff_forall]
      intro y hy
      have := Nat.card_eq_one_iff_unique.1 h1
      exact congrArg Subtype.val (this.1.elim ⟨y, hy⟩ ⟨0, AddSubgroup.zero_mem _⟩)
    have hcin : c ∈ δ.range ⊓ fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl) :=
      AddSubgroup.mem_inf.2 ⟨hcDm, hcx⟩
    rw [hbot, AddSubgroup.mem_bot] at hcin
    exact hc0 hcin
  have hvanD : ∀ w ∈ δ.range, dot c' w = 0 := by
    rintro _ ⟨u, rfl⟩
    rw [hδ, dot_sub, hc'x' u]
    exact sub_self _
  have hall : ∀ w : W, dot c' w = 0 := by
    intro w
    by_cases hw : w ∈ δ.range
    · exact hvanD w hw
    · have hwc : w + c ∈ δ.range := add_mem_of_not_mem δ.range hD16 hw hcD
      have := hvanD _ hwc
      rw [dot_add, hcz] at this
      simpa using this
  apply hc'0
  funext i
  have := hall (Pi.single i 1)
  rw [dot_single] at this
  exact this

theorem exists_equiv_U0 {Vg : Subgroup Gl} (hV2 : IsPGroup 2 Vg) (hV16 : Nat.card Vg = 16)
    {x : Gl} (hx5 : orderOf x = 5) (hxN : x ∈ Subgroup.normalizer (Vg : Set Gl)) :
    ∃ θ : Gl ≃* Gl, Vg.map θ.toMonoidHom = U0 := by
  rcases card_fixedAdd_cases hV2 hV16 hx5 hxN with h2 | h16
  · obtain ⟨hV2', hV16', hx5', hxN'⟩ := dual_data hV2 hV16 hx5 hxN
    rcases card_fixedAdd_cases hV2' hV16' hx5' hxN' with h2' | h16'
    · exact (not_both_two hV2 hV16 hx5 hxN h2 h2').elim
    · obtain ⟨τ, hτ⟩ := exists_conj_U0 hV16' h16'
      refine ⟨dualEquiv.trans (MulAut.conj τ), ?_⟩
      rw [Subgroup.map_map] at hτ
      exact hτ
  · obtain ⟨τ, hτ⟩ := exists_conj_U0 hV16 h16
    exact ⟨MulAut.conj τ, hτ⟩

@[expose] def Good (Vg : Subgroup Gl) : Prop :=
  (∀ g : Gl, (∀ v ∈ Vg, g * v = v * g) → g ∈ Vg) ∧
    ∃ A : Subgroup Gl, A ≤ Subgroup.normalizer (Vg : Set Gl) ∧ Nat.card A = 16 ∧
      ∀ a ∈ A, (∀ v ∈ Vg, a * v * a⁻¹ = v) → a = 1

theorem good_U0 : Good U0 := ⟨mem_U0_of_centralizes, exists_A⟩

theorem good_of_map (θ : Gl ≃* Gl) {Vg : Subgroup Gl} (h : Good (Vg.map θ.toMonoidHom)) :
    Good Vg := by
  obtain ⟨h1, A₁, hA₁N, hA₁c, hA₁f⟩ := h
  have hmem : ∀ z : Gl, z ∈ Vg.map θ.toMonoidHom ↔ θ.symm z ∈ Vg :=
    fun z => Subgroup.mem_map_equiv
  refine ⟨fun g hg => ?_, A₁.map θ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · have : θ g ∈ Vg.map θ.toMonoidHom := by
      apply h1
      intro u hu
      rw [hmem] at hu
      have h2 := congrArg θ (hg (θ.symm u) hu)
      simpa [map_mul] using h2
    rw [hmem, MulEquiv.symm_apply_apply] at this
    exact this
  · rintro _ ⟨a₁, ha₁, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have h3 := Subgroup.mem_normalizer_iff.1 (hA₁N ha₁) (θ v)
    rw [hmem, hmem] at h3
    simpa [map_mul, map_inv] using h3
  · rw [Subgroup.card_map_of_injective θ.symm.injective]
    exact hA₁c
  · rintro _ ⟨a₁, ha₁, rfl⟩ hcomm
    have : a₁ = 1 := by
      apply hA₁f a₁ ha₁
      intro u hu
      rw [hmem] at hu
      have h2 := congrArg θ (hcomm (θ.symm u) hu)
      simpa [map_mul, map_inv] using h2
    show θ.symm a₁ = 1
    rw [this, map_one]

theorem good_of_data {Vg : Subgroup Gl} (hV2 : IsPGroup 2 Vg) (hV16 : Nat.card Vg = 16)
    {x : Gl} (hx5 : orderOf x = 5) (hxN : x ∈ Subgroup.normalizer (Vg : Set Gl)) : Good Vg := by
  obtain ⟨θ, hθ⟩ := exists_equiv_U0 hV2 hV16 hx5 hxN
  refine good_of_map θ ?_
  rw [hθ]
  exact good_U0

end CFSG.QuasithinUnique.A5.Kc3L5
