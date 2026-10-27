module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.RankThree.Native.DerivedGenerators

public section


attribute [-instance] CFSG.RankThree.Native.fact_prime_five
namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

section Abstract

variable {K R : Type} [Group K] [Group R]

theorem u5_conj_central {u : K} (hu : ∀ g : K, g * u = u * g) (X : K) : u * X * u⁻¹ = X := by
  rw [← hu X]
  group

theorem u5_conj_by_central {u : K} (hu : ∀ g : K, g * u = u * g) (g : K) : g * u * g⁻¹ = u := by
  rw [hu g]
  group

theorem u5_comm_central_mul {u v : K} (hu : ∀ g : K, g * u = u * g) (hv : ∀ g : K, g * v = v * g)
    (a b : K) : (u * a) * (v * b) * (u * a)⁻¹ * (v * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  calc (u * a) * (v * b) * (u * a)⁻¹ * (v * b)⁻¹
      = u * (a * v * b * a⁻¹) * u⁻¹ * b⁻¹ * v⁻¹ := by group
    _ = (a * v * b * a⁻¹) * b⁻¹ * v⁻¹ := by rw [u5_conj_central hu]
    _ = a * (v * (b * a⁻¹ * b⁻¹) * v⁻¹) := by group
    _ = a * (b * a⁻¹ * b⁻¹) := by rw [u5_conj_central hv]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem u5_comm_of_lifts (φ : K →* R)
    (hc : ∀ z : K, φ z = 1 → z ∈ Subgroup.center K) {x y n : K}
    (hxy : φ x * φ y = φ y * φ x) (hn1 : φ (n * x * n⁻¹) = φ y) (hn2 : φ (n * y * n⁻¹) = φ x)
    (hx5 : φ x ^ 5 = 1) (hy5 : φ y ^ 5 = 1) : x * y = y * x := by
  set z : K := x * y * x⁻¹ * y⁻¹ with hz_def
  have hz1 : φ z = 1 := by
    rw [hz_def, map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
    group
  have hzc : ∀ g : K, g * z = z * g := fun g => Subgroup.mem_center_iff.1 (hc z hz1) g
  have hφw1 : φ (n * x * n⁻¹ * y⁻¹) = 1 := by
    rw [map_mul φ (n * x * n⁻¹) y⁻¹, map_inv, hn1, mul_inv_cancel]
  have hφw2 : φ (n * y * n⁻¹ * x⁻¹) = 1 := by
    rw [map_mul φ (n * y * n⁻¹) x⁻¹, map_inv, hn2, mul_inv_cancel]
  set w1 : K := n * x * n⁻¹ * y⁻¹ with hw1_def
  set w2 : K := n * y * n⁻¹ * x⁻¹ with hw2_def
  have hw1c : ∀ g : K, g * w1 = w1 * g := fun g => Subgroup.mem_center_iff.1 (hc w1 hφw1) g
  have hw2c : ∀ g : K, g * w2 = w2 * g := fun g => Subgroup.mem_center_iff.1 (hc w2 hφw2) g
  have e1 : n * x * n⁻¹ = w1 * y := by rw [hw1_def]; group
  have e2 : n * y * n⁻¹ = w2 * x := by rw [hw2_def]; group
  have hconj : n * z * n⁻¹ = z⁻¹ := by
    have h1 : n * z * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) * (n * x * n⁻¹)⁻¹ * (n * y * n⁻¹)⁻¹ := by
      rw [hz_def]; group
    rw [h1, e1, e2, u5_comm_central_mul hw1c hw2c, hz_def]
    group
  have hzz : z * z = 1 := by
    have h2 : n * z * n⁻¹ = z := by rw [hzc n]; group
    rw [h2] at hconj
    calc z * z = z * z⁻¹ := by rw [← hconj]
      _ = 1 := mul_inv_cancel z
  have hzpow : ∀ j : ℕ, ∀ g : K, g * z ^ j = z ^ j * g := fun j g =>
    Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ (hc z hz1) j) g
  have hind : ∀ k : ℕ, x ^ k * y * (x ^ k)⁻¹ = z ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * y * (x ^ (k + 1))⁻¹ = x * (x ^ k * y * (x ^ k)⁻¹) * x⁻¹ := by
            rw [pow_succ']; group
        _ = x * (z ^ k * y) * x⁻¹ := by rw [ih]
        _ = (x * z ^ k * x⁻¹) * (x * y * x⁻¹) := by group
        _ = z ^ k * (z * y) := by
            rw [u5_conj_by_central (hzpow k) x, show x * y * x⁻¹ = z * y by rw [hz_def]; group]
        _ = z ^ (k + 1) * y := by rw [pow_succ]; group
  have hx5c : ∀ g : K, g * x ^ 5 = x ^ 5 * g := by
    intro g
    refine Subgroup.mem_center_iff.1 (hc (x ^ 5) ?_) g
    rw [map_pow, hx5]
  have hz5 : z ^ 5 = 1 := by
    have h5 := hind 5
    rw [u5_conj_central hx5c] at h5
    have : z ^ 5 * y = 1 * y := by rw [← h5, one_mul]
    exact mul_right_cancel this
  have hz1' : z = 1 := by
    have h2 : z ^ 2 = 1 := by rw [sq]; exact hzz
    have := (pow_gcd_eq_one (a := z)).2 ⟨hz5, h2⟩
    simpa using this
  rw [hz_def] at hz1'
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hz1', one_mul]

end Abstract

section Counting

variable {K R : Type} [Group K] [Group R] [Finite K]

theorem u5_exists_elemAbelian (φ : K →* R) (hker : ∀ z : K, φ z = 1 ↔ z ∈ Subgroup.center K)
    (P : Subgroup K) (hPz : Subgroup.center K ≤ P)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hP5 : ∀ x ∈ P, φ x ^ 5 = 1)
    (hcard : 5 ^ 5 ≤ Nat.card (φ.comp P.subtype).range) :
    ∃ Ω : Subgroup K, Ω ≤ P ∧ IsElemAbelian 5 Ω ∧ 5 ^ 5 ≤ Nat.card Ω := by
  letI : CommGroup P := { (inferInstance : Group P) with
    mul_comm := fun a b => Subtype.ext (hPc a a.2 b b.2) }
  set f : P →* P := powMonoidHom 5 with hf
  set ψ : P →* R := φ.comp P.subtype with hψ
  have ha : Nat.card f.ker * Nat.card f.range = Nat.card P := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index f.ker
  have hd : Nat.card ψ.ker * Nat.card ψ.range = Nat.card P := by
    rw [← Subgroup.index_ker ψ]
    exact Subgroup.card_mul_index ψ.ker
  have hkerψ : ψ.ker = (Subgroup.center K).subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, MonoidHom.comp_apply,
      Subgroup.coe_subtype, hker]
  have hkerψcard : Nat.card ψ.ker = Nat.card (Subgroup.center K) := by
    rw [hkerψ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPz).toEquiv
  have hfp : ∀ p : P, ((f p : P) : K) = (p : K) ^ 5 := fun p => by
    rw [hf, powMonoidHom_apply, Subgroup.coe_pow]
  have hfim : Nat.card f.range ≤ Nat.card (Subgroup.center K) := by
    have hmap : Nat.card (f.range.map P.subtype) = Nat.card f.range :=
      Subgroup.card_map_of_injective Subtype.val_injective
    rw [← hmap]
    apply Subgroup.card_le_of_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hx
    apply (hker _).1
    show φ ((f p : P) : K) = 1
    rw [hfp p, map_pow, hP5 p p.2]
  have hZpos : 0 < Nat.card (Subgroup.center K) := Nat.card_pos
  have hmain : Nat.card ψ.range ≤ Nat.card f.ker := by
    have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card f.ker * Nat.card f.range := by
      rw [hd, ha]
    rw [hkerψcard] at h1
    have h2 : Nat.card f.ker * Nat.card f.range ≤
        Nat.card f.ker * Nat.card (Subgroup.center K) := Nat.mul_le_mul_left _ hfim
    have h3 : Nat.card (Subgroup.center K) * Nat.card ψ.range ≤
        Nat.card (Subgroup.center K) * Nat.card f.ker := by
      rw [h1, mul_comm (Nat.card (Subgroup.center K))]
      exact h2
    exact Nat.le_of_mul_le_mul_left h3 hZpos
  have hΩP : f.ker.map P.subtype ≤ P := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  refine ⟨f.ker.map P.subtype, hΩP, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · exact Subtype.ext (hPc a.1 (hΩP a.2) b.1 (hΩP b.2))
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hy1 : f y = 1 := hy
    have := congrArg (fun z : P => (z : K)) hy1
    simp only [Subgroup.coe_one] at this
    rw [hfp y] at this
    exact this
  · rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact le_trans hcard hmain

end Counting

section TwoLocal

variable {K R : Type} [Group K] [Group R] [Finite K]

theorem u5_exists_twoLocal (φ : K →* R) (hker : ∀ z : K, φ z = 1 ↔ z ∈ Subgroup.center K)
    (t : K) (ht2 : φ t ^ 2 = 1) (ht1 : φ t ≠ 1) :
    ∃ Q : Subgroup K, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      ∀ x : K, Commute (φ x) (φ t) → x ∈ Subgroup.normalizer (Q : Set K) := by
  set W : Subgroup K := (Subgroup.zpowers (φ t)).comap φ with hW_def
  have hWmem : ∀ w : K, w ∈ W ↔ φ w ∈ Subgroup.zpowers (φ t) := fun w => Iff.rfl
  have hWform : ∀ w ∈ W, ∃ z ∈ Subgroup.center K, ∃ j : ℤ, w = z * t ^ j := by
    intro w hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 ((hWmem w).1 hw)
    refine ⟨w * t ^ (-j), ?_, j, by group⟩
    rw [← hker, map_mul, map_zpow, ← hj, ← zpow_add, add_neg_cancel, zpow_zero]
  have hcomm_t : ∀ w ∈ W, Commute w t := by
    intro w hw
    obtain ⟨z, hz, j, rfl⟩ := hWform w hw
    exact Commute.mul_left (Subgroup.mem_center_iff.1 hz t).symm ((Commute.refl t).zpow_left j)
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    obtain ⟨z2, hz2, j2, rfl⟩ := hWform b hb
    have hab : Commute a (t ^ j2) := (hcomm_t a ha).zpow_right j2
    calc a * (z2 * t ^ j2) = (a * z2) * t ^ j2 := by group
      _ = (z2 * a) * t ^ j2 := by rw [Subgroup.mem_center_iff.1 hz2 a]
      _ = z2 * (a * t ^ j2) := by group
      _ = z2 * (t ^ j2 * a) := by rw [hab.eq]
      _ = (z2 * t ^ j2) * a := by group
  let Q : Subgroup K :=
    { carrier := {w | w ∈ W ∧ ∃ n : ℕ, w ^ 2 ^ n = 1}
      mul_mem' := by
        rintro a b ⟨ha, m, hm⟩ ⟨hb, n, hn⟩
        have ha' : a ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, hm, one_pow]
        have hb' : b ^ 2 ^ (m + n) = 1 := by rw [add_comm, pow_add, pow_mul, hn, one_pow]
        have hcab : Commute a b := hWcomm a ha b hb
        refine ⟨W.mul_mem ha hb, m + n, ?_⟩
        rw [hcab.mul_pow, ha', hb', one_mul]
      one_mem' := ⟨W.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, m, hm⟩
        exact ⟨W.inv_mem ha, m, by rw [inv_pow, hm, inv_one]⟩ }
  have hQmem : ∀ w : K, w ∈ Q ↔ w ∈ W ∧ ∃ n : ℕ, w ^ 2 ^ n = 1 := fun w => Iff.rfl
  obtain ⟨a, m, hm_odd, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
  have hφs : φ (t ^ m) = φ t := by
    obtain ⟨k, rfl⟩ := hm_odd
    rw [map_pow, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hsQ : t ^ m ∈ Q := by
    refine (hQmem _).2 ⟨(hWmem _).2 ?_, a, ?_⟩
    · rw [hφs]
      exact Subgroup.mem_zpowers _
    · rw [← pow_mul, mul_comm, ← ho, pow_orderOf_eq_one]
  have hsne : t ^ m ≠ 1 := by
    intro h
    apply ht1
    rw [← hφs, h, map_one]
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro h
    apply hsne
    have := hsQ
    rw [h, Subgroup.mem_bot] at this
    exact this
  · intro g
    obtain ⟨n, hn⟩ := ((hQmem g.1).1 g.2).2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · intro x hx
    have hconjQ : ∀ y : K, Commute (φ y) (φ t) → ∀ h ∈ Q, y * h * y⁻¹ ∈ Q := by
      intro y hy h hh
      obtain ⟨hhW, n, hn⟩ := (hQmem h).1 hh
      refine (hQmem _).2 ⟨(hWmem _).2 ?_, n, ?_⟩
      · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 ((hWmem h).1 hhW)
        rw [map_mul, map_mul, map_inv, ← hj, (hy.zpow_right j).eq, mul_inv_cancel_right]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
      · rw [conj_pow, hn, mul_one, mul_inv_cancel]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconjQ x hx h hh, fun hh => ?_⟩
    have hx' : Commute (φ x⁻¹) (φ t) := by
      rw [map_inv]
      exact hx.inv_left
    have := hconjQ x⁻¹ hx' _ hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rw [e] at this
    exact this

end TwoLocal

section Mat

variable {F : Type} [Field F] {d : ℕ}

theorem u5_pow_mod (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (m : ℕ) : ζ ^ (m % 5) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 5, pow_add, pow_mul, h5, one_pow, mul_one]

@[expose] def u5Chi (ζ : Fˣ) (h5 : ζ ^ 5 = 1) : Multiplicative (ZMod 5) →* Fˣ where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, ZMod.val_add, u5_pow_mod ζ h5, pow_add]

theorem u5Chi_pow_five (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (x : Multiplicative (ZMod 5)) :
    u5Chi ζ h5 x ^ 5 = 1 := by
  rw [u5Chi, MonoidHom.coe_mk, OneHom.coe_mk, ← pow_mul, mul_comm, pow_mul, h5, one_pow]

theorem u5Chi_eq_one (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (hζ : orderOf ζ = 5) (x : Multiplicative (ZMod 5)) :
    u5Chi ζ h5 x = 1 ↔ x = 1 := by
  have key : ζ ^ (Multiplicative.toAdd x).val = 1 ↔ 5 ∣ (Multiplicative.toAdd x).val := by
    rw [← orderOf_dvd_iff_pow_eq_one, hζ]
  rw [u5Chi, MonoidHom.coe_mk, OneHom.coe_mk, key]
  constructor
  · intro h
    have h0 : (Multiplicative.toAdd x).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt _)
    rw [ZMod.val_eq_zero] at h0
    exact (toAdd_eq_zero.1 h0).symm ▸ rfl
  · rintro rfl
    simp

@[expose] def u5Diag (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (u : Fin d → Multiplicative (ZMod 5)) : GL (Fin d) F where
  val := Matrix.diagonal fun i => ((u5Chi ζ h5 (u i) : Fˣ) : F)
  inv := Matrix.diagonal fun i => (((u5Chi ζ h5 (u i))⁻¹ : Fˣ) : F)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp

@[expose] def u5Torus (ζ : Fˣ) (h5 : ζ ^ 5 = 1) : (Fin d → Multiplicative (ZMod 5)) →* GL (Fin d) F where
  toFun := u5Diag ζ h5
  map_one' := Units.ext (by simp [u5Diag])
  map_mul' u v := Units.ext (by simp [u5Diag, Matrix.diagonal_mul_diagonal])

theorem u5Torus_val (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (u : Fin d → Multiplicative (ZMod 5)) :
    ((u5Torus ζ h5 u : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal fun i => ((u5Chi ζ h5 (u i) : Fˣ) : F) := rfl

theorem u5Torus_det (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (u : Fin d → Multiplicative (ZMod 5)) :
    (((u5Torus ζ h5 u : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)).det =
      ∏ i, ((u5Chi ζ h5 (u i) : Fˣ) : F) := by
  rw [u5Torus_val, Matrix.det_diagonal]

end Mat

section Swap

variable {F : Type} [Field F] {d : ℕ}

@[expose] def u5Swap (i j : Fin d) : GL (Fin d) F := Matrix.GeneralLinearGroup.swap F i j

theorem u5Swap_val (i j : Fin d) :
    ((u5Swap (F := F) i j : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.swap F i j := rfl

theorem u5Swap_inv (i j : Fin d) : (u5Swap (F := F) i j)⁻¹ = u5Swap i j := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  simp only [Units.val_mul, Units.val_one, u5Swap_val, Matrix.swap_mul_self]

theorem u5_swap_mul_apply (i j : Fin d) (g : Matrix (Fin d) (Fin d) F) (a b : Fin d) :
    (Matrix.swap F i j * g) a b = g (Equiv.swap i j a) b := by
  by_cases ha : a = i
  · subst ha
    simp [Matrix.swap_mul_apply_left]
  · by_cases hb : a = j
    · subst hb
      simp [Matrix.swap_mul_apply_right]
    · rw [Matrix.swap_mul_of_ne ha hb, Equiv.swap_apply_of_ne_of_ne ha hb]

theorem u5_mul_swap_apply (i j : Fin d) (g : Matrix (Fin d) (Fin d) F) (a b : Fin d) :
    (g * Matrix.swap F i j) a b = g a (Equiv.swap i j b) := by
  by_cases hb : b = i
  · subst hb
    simp [Matrix.mul_swap_apply_left]
  · by_cases hb' : b = j
    · subst hb'
      simp [Matrix.mul_swap_apply_right]
    · rw [Matrix.mul_swap_of_ne hb hb', Equiv.swap_apply_of_ne_of_ne hb hb']

theorem u5_swap_sandwich (i j : Fin d) (g : Matrix (Fin d) (Fin d) F) (a b : Fin d) :
    (Matrix.swap F i j * g * Matrix.swap F i j) a b = g (Equiv.swap i j a) (Equiv.swap i j b) := by
  rw [u5_mul_swap_apply, u5_swap_mul_apply]

theorem u5Swap_conj (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (i j : Fin d)
    (u : Fin d → Multiplicative (ZMod 5)) :
    u5Swap i j * u5Torus ζ h5 u * u5Swap i j = u5Torus ζ h5 (u ∘ Equiv.swap i j) := by
  apply Units.ext
  ext a b
  simp only [Units.val_mul, u5Swap_val, u5Torus_val,
    u5_swap_sandwich, Matrix.diagonal_apply, Function.comp_apply, Equiv.apply_eq_iff_eq]

theorem swap_map_eq (g : F → F) (h0 : g 0 = 0) (h1 : g 1 = 1) (i j : Fin d) :
    (Matrix.swap F i j).map g = Matrix.swap F i j := by
  ext a b
  rw [Matrix.map_apply]
  unfold Matrix.swap
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp [h0, h1]

end Swap

section Membership

variable {F : Type} [Field F] {d : ℕ}

theorem u5_pow4_fix (c : F) (hc : c ^ 5 = 1) : c ^ (2 ^ 2) * c = 1 := by
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← pow_succ]
  exact hc

theorem u5Torus_mem (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (u : Fin d → Multiplicative (ZMod 5))
    (hu : ∏ i, u5Chi ζ h5 (u i) = 1) : u5Torus ζ h5 u ∈ StatedSU d (2 ^ 2) F := by
  unfold StatedSU
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [u5Torus_det, ← Units.coe_prod, hu, Units.val_one]
  · rw [u5Torus_val, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h := congrArg (fun x : Fˣ => (x : F)) (u5Chi_pow_five ζ h5 (u i))
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
    exact u5_pow4_fix _ h

theorem u5Swap_mem (hneg : (-1 : F) = 1) (i j : Fin d) (hij : i ≠ j) :
    u5Swap i j ∈ StatedSU d (2 ^ 2) F := by
  unfold StatedSU
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [u5Swap_val]
    show ((Equiv.swap i j).permMatrix F).det = 1
    rw [Matrix.det_permutation, Equiv.Perm.sign_swap hij]
    simp [hneg]
  · rw [u5Swap_val, swap_map_eq (fun x : F => x ^ (2 ^ 2)) (by simp) (by simp) i j,
      Matrix.transpose_swap, Matrix.swap_mul_self]

end Membership

section Gens

variable {F : Type} [Field F] {d : ℕ} [NeZero d]

theorem u5_pow5_chi (x : Multiplicative (ZMod 5)) : x ^ 5 = 1 := by revert x; decide

theorem u5_val2 (hd : 8 ≤ d) : ((2 : Fin d) : ℕ) = 2 := by
  show (2 : ℕ) % d = 2
  exact Nat.mod_eq_of_lt (by omega)

theorem u5_val1 (hd : 8 ≤ d) : ((1 : Fin d) : ℕ) = 1 := by
  show (1 : ℕ) % d = 1
  exact Nat.mod_eq_of_lt (by omega)

theorem u5_ne_two_zero (hd : 8 ≤ d) : (0 : Fin d) ≠ 2 := fun h => by
  have := congrArg Fin.val h; rw [u5_val2 hd, Fin.val_zero] at this; omega

theorem u5_ne_two_one (hd : 8 ≤ d) : (1 : Fin d) ≠ 2 := fun h => by
  have := congrArg Fin.val h; rw [u5_val2 hd, u5_val1 hd] at this; omega

@[expose] def u5Idx (j : Fin 5) : Fin d := Fin.ofNat d ((j : ℕ) + 3)

theorem u5Idx_val (hd : 8 ≤ d) (j : Fin 5) : ((u5Idx j : Fin d) : ℕ) = (j : ℕ) + 3 := by
  show ((j : ℕ) + 3) % d = (j : ℕ) + 3
  exact Nat.mod_eq_of_lt (by omega)

theorem u5Idx_inj (hd : 8 ≤ d) {j k : Fin 5} (h : u5Idx (d := d) j = u5Idx k) : j = k := by
  have := congrArg (fun x : Fin d => (x : ℕ)) h
  simp only [u5Idx_val hd] at this
  exact Fin.ext (by omega)

theorem u5Idx_ne_two (hd : 8 ≤ d) (j : Fin 5) : u5Idx (d := d) j ≠ 2 := by
  intro h
  have := congrArg (fun x : Fin d => (x : ℕ)) h
  rw [u5Idx_val hd, u5_val2 hd] at this
  omega

theorem u5Idx_ne_zero (hd : 8 ≤ d) (j : Fin 5) : u5Idx (d := d) j ≠ 0 := by
  intro h
  have := congrArg (fun x : Fin d => (x : ℕ)) h
  rw [u5Idx_val hd, Fin.val_zero] at this
  omega

theorem u5Idx_ne_one (hd : 8 ≤ d) (j : Fin 5) : u5Idx (d := d) j ≠ 1 := by
  intro h
  have := congrArg (fun x : Fin d => (x : ℕ)) h
  rw [u5Idx_val hd, u5_val1 hd] at this
  omega

@[expose] def u5Gen (j : Fin 5) : Fin d → Multiplicative (ZMod 5) :=
  Pi.mulSingle (u5Idx j) (Multiplicative.ofAdd 1) *
    (Pi.mulSingle (2 : Fin d) (Multiplicative.ofAdd 1))⁻¹

theorem u5Gen_at (hd : 8 ≤ d) (j k : Fin 5) :
    u5Gen (d := d) j (u5Idx k) = if j = k then Multiplicative.ofAdd 1 else 1 := by
  have h2 := u5Idx_ne_two (d := d) hd k
  simp only [u5Gen, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_apply, h2, if_false, inv_one,
    mul_one]
  by_cases hjk : j = k
  · subst hjk; simp
  · have : u5Idx (d := d) j ≠ u5Idx k := fun h => hjk (u5Idx_inj hd h)
    simp [this, Ne.symm this, hjk]

theorem u5Gen_zero (hd : 8 ≤ d) (j : Fin 5) : u5Gen (d := d) j 0 = 1 := by
  simp [u5Gen, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_apply, (u5Idx_ne_zero hd j).symm,
    u5_ne_two_zero hd]

theorem u5Gen_one (hd : 8 ≤ d) (j : Fin 5) : u5Gen (d := d) j 1 = 1 := by
  simp [u5Gen, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_apply, (u5Idx_ne_one hd j).symm,
    u5_ne_two_one hd]

theorem u5Gen_swap (hd : 8 ≤ d) {j k : Fin 5} (hjk : j ≠ k) :
    u5Gen (d := d) j ∘ Equiv.swap (u5Idx j) (u5Idx k) = u5Gen k := by
  have hne : u5Idx (d := d) j ≠ u5Idx k := fun h => hjk (u5Idx_inj hd h)
  funext i
  simp only [Function.comp_apply]
  by_cases hi : i = u5Idx j
  · subst hi
    rw [Equiv.swap_apply_left, u5Gen_at hd, u5Gen_at hd]
    simp [hjk, Ne.symm hjk]
  · by_cases hi' : i = u5Idx k
    · subst hi'
      rw [Equiv.swap_apply_right, u5Gen_at hd, u5Gen_at hd]
      simp [hjk]
    · rw [Equiv.swap_apply_of_ne_of_ne hi hi']
      simp [u5Gen, Pi.mulSingle_apply, hi, hi']

theorem u5Gen_swap01 (hd : 8 ≤ d) (j : Fin 5) :
    u5Gen (d := d) j ∘ Equiv.swap (0 : Fin d) 1 = u5Gen j := by
  funext i
  simp only [Function.comp_apply]
  by_cases h0 : i = 0
  · subst h0
    rw [Equiv.swap_apply_left, u5Gen_one hd, u5Gen_zero hd]
  · by_cases h1 : i = 1
    · subst h1
      rw [Equiv.swap_apply_right, u5Gen_zero hd, u5Gen_one hd]
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]

theorem u5Gen_pow5 (hd : 8 ≤ d) (j : Fin 5) : u5Gen (d := d) j ^ 5 = 1 := by
  funext i
  simp [u5Gen, u5_pow5_chi]

end Gens

section Exp

variable {F : Type} [Field F] {d : ℕ} [NeZero d]

@[expose] def u5Prod (ζ : Fˣ) (h5 : ζ ^ 5 = 1) : (Fin d → Multiplicative (ZMod 5)) →* Fˣ where
  toFun u := ∏ i, u5Chi ζ h5 (u i)
  map_one' := by simp
  map_mul' u v := by simp [Finset.prod_mul_distrib]

abbrev u5E1 (ζ : Fˣ) (h5 : ζ ^ 5 = 1) : Subgroup (Fin d → Multiplicative (ZMod 5)) :=
  (u5Prod (d := d) ζ h5).ker

@[expose] def u5Tau (ζ : Fˣ) (h5 : ζ ^ 5 = 1) : u5E1 (F := F) (d := d) ζ h5 →* StatedSU d (2 ^ 2) F where
  toFun u := ⟨u5Torus ζ h5 u.1, u5Torus_mem ζ h5 u.1 (MonoidHom.mem_ker.1 u.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

@[expose] def u5Phi (ζ : Fˣ) (h5 : ζ ^ 5 = 1) :
    u5E1 (F := F) (d := d) ζ h5 →* StatedProj (StatedSU d (2 ^ 2) F) :=
  (QuotientGroup.mk' _).comp (u5Tau ζ h5)

theorem u5Phi_eq_one_iff (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (u : u5E1 (F := F) (d := d) ζ h5) :
    u5Phi ζ h5 u = 1 ↔
      ∃ c : Fˣ, u5Torus ζ h5 u.1 = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  unfold u5Phi
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  show u5Torus ζ h5 u.1 ∈ StatedScalars (Fin d) F ↔ _
  rw [StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

theorem u5Torus_entry (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (u : Fin d → Multiplicative (ZMod 5)) (c : Fˣ)
    (h : u5Torus ζ h5 u = Matrix.GeneralLinearGroup.scalar (Fin d) c) (i : Fin d) :
    u5Chi ζ h5 (u i) = c := by
  have := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) i i) h
  simp only [u5Torus_val, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_mk,
    OneHom.coe_mk, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at this
  exact Units.ext (by simpa using this)

theorem u5Phi_injOn (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (hζ : orderOf ζ = 5)
    (X Y : u5E1 (F := F) (d := d) ζ h5) (hX0 : X.1 0 = 1) (hY0 : Y.1 0 = 1)
    (h : u5Phi ζ h5 X = u5Phi ζ h5 Y) : X = Y := by
  have h1 : u5Phi ζ h5 (X⁻¹ * Y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (u5Phi_eq_one_iff ζ h5 _).1 h1
  have hall : ∀ i, u5Chi ζ h5 ((X⁻¹ * Y).1 i) = c := fun i => u5Torus_entry ζ h5 _ c hc i
  have hc1 : c = 1 := by
    have := hall 0
    simpa [hX0, hY0] using this.symm
  have hXY : X⁻¹ * Y = 1 := by
    apply Subtype.ext
    funext i
    have := hall i
    rw [hc1] at this
    exact (u5Chi_eq_one ζ h5 hζ _).1 this
  exact inv_mul_eq_one.1 hXY

end Exp

section Words

variable {F : Type} [Field F] {d : ℕ} [NeZero d]

theorem u5_prod_gen (j : Fin 5) : ∏ i, u5Gen (d := d) j i = 1 := by
  simp [u5Gen, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pi_mulSingle']

theorem u5_gen_mem (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (j : Fin 5) :
    u5Gen (d := d) j ∈ u5E1 (F := F) ζ h5 := by
  show ∏ i, u5Chi ζ h5 (u5Gen j i) = 1
  rw [← map_prod, u5_prod_gen, map_one]

@[expose] def u5G (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (j : Fin 5) : u5E1 (F := F) (d := d) ζ h5 :=
  ⟨u5Gen j, u5_gen_mem ζ h5 j⟩

theorem u5_ofAdd_one_pow (x : ZMod 5) : Multiplicative.ofAdd (1 : ZMod 5) ^ x.val =
    Multiplicative.ofAdd x := by
  rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]

@[expose] def u5Xv (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (v : Fin 5 → ZMod 5) :
    u5E1 (F := F) (d := d) ζ h5 :=
  u5G ζ h5 0 ^ (v 0).val * u5G ζ h5 1 ^ (v 1).val * u5G ζ h5 2 ^ (v 2).val *
    u5G ζ h5 3 ^ (v 3).val * u5G ζ h5 4 ^ (v 4).val

theorem u5Xv_coord (hd : 8 ≤ d) (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (v : Fin 5 → ZMod 5) (k : Fin 5) :
    (u5Xv (F := F) (d := d) ζ h5 v).1 (u5Idx k) = Multiplicative.ofAdd (v k) := by
  fin_cases k <;> simp [u5Xv, u5G, u5Gen_at hd, u5_ofAdd_one_pow]

theorem u5Xv_zero (hd : 8 ≤ d) (ζ : Fˣ) (h5 : ζ ^ 5 = 1) (v : Fin 5 → ZMod 5) :
    (u5Xv (F := F) (d := d) ζ h5 v).1 0 = 1 := by
  simp [u5Xv, u5G, u5Gen_zero hd]

theorem u5Xv_inj (hd : 8 ≤ d) (ζ : Fˣ) (h5 : ζ ^ 5 = 1) {v w : Fin 5 → ZMod 5}
    (h : u5Xv (F := F) (d := d) ζ h5 v = u5Xv (F := F) (d := d) ζ h5 w) : v = w := by
  funext k
  have := congrArg (fun X : u5E1 (F := F) (d := d) ζ h5 => X.1 (u5Idx k)) h
  simp only [u5Xv_coord hd] at this
  exact Multiplicative.ofAdd.injective this

end Words

section Assembly

variable {K R : Type} [Group K] [Group R] [Finite K]

theorem u5_comm_closure (S : Set K) (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).2 fun s hs => Subgroup.mem_centralizer_iff.2 fun h hh => hS h hh s hs
  intro x hx y hy
  have hxS : ∀ s ∈ S, s * x = x * s := fun s hs => Subgroup.mem_centralizer_iff.1 (h1 hx) s hs
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer ({x} : Set K) :=
    (Subgroup.closure_le _).2 fun s hs => Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (hxS s hs).symm
  exact Subgroup.mem_centralizer_iff.1 (h2 hy) x rfl

theorem u5_exp_le (E : Subgroup K) (k : ℕ) (hk : Nat.card E = 5 ^ k) : k ≤ Nat.card K := by
  have h1 : k < 5 ^ k := Nat.lt_pow_self (by norm_num)
  have h2 := Subgroup.card_le_card_group E
  omega

theorem u5_le_pRank (H E : Subgroup K) (hEH : E ≤ H) (hE : IsElemAbelian 5 E) (k : ℕ)
    (hk : Nat.card E = 5 ^ k) : k ≤ CFSG.Open.pRank 5 H := by
  unfold CFSG.Open.pRank
  exact le_csSup ⟨Nat.card K, fun _ ⟨E', _, _, hE'⟩ => u5_exp_le E' _ hE'⟩ ⟨E, hEH, hE, hk⟩

theorem u5_pRank_le (H : Subgroup K) : CFSG.Open.pRank 5 H ≤ Nat.card K := by
  unfold CFSG.Open.pRank
  exact csSup_le' fun _ ⟨E, _, _, hE⟩ => u5_exp_le E _ hE

theorem u5_le_twoLocal (H : Subgroup K) (hH : CFSG.Open.IsTwoLocal H) (k : ℕ)
    (hk : k ≤ CFSG.Open.pRank 5 H) : k ≤ CFSG.Open.twoLocalPrimeRank 5 K :=
  le_trans hk (le_csSup ⟨Nat.card K, fun _ ⟨H', _, hr⟩ => hr ▸ u5_pRank_le H'⟩ ⟨H, hH, rfl⟩)

theorem u5_five_pow (Ω : Subgroup K) (hΩ : IsElemAbelian 5 Ω) (h : 5 ^ 5 ≤ Nat.card Ω) :
    ∃ k, 5 ≤ k ∧ Nat.card Ω = 5 ^ k := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : IsPGroup 5 Ω := fun g => ⟨1, Subtype.ext (by simpa using hΩ.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  refine ⟨k, ?_, hk⟩
  by_contra hlt
  have hlt' : k < 5 := by omega
  have := Nat.pow_lt_pow_right (by norm_num : 1 < 5) hlt'
  omega

theorem u5_main_abstract (φ : K →* R)
    (hker : ∀ z : K, φ z = 1 ↔ z ∈ Subgroup.center K) (t : K) (ht2 : φ t ^ 2 = 1)
    (ht1 : φ t ≠ 1) (g : Fin 5 → K) (hg5 : ∀ j, φ (g j) ^ 5 = 1)
    (hgt : ∀ j, Commute (φ (g j)) (φ t))
    (hgc : ∀ j j', φ (g j) * φ (g j') = φ (g j') * φ (g j))
    (hsw : ∀ j j', j ≠ j' → ∃ n : K, φ (n * g j * n⁻¹) = φ (g j') ∧ φ (n * g j' * n⁻¹) = φ (g j))
    (hinj : ∀ v w : Fin 5 → ZMod 5,
      φ (g 0 ^ (v 0).val * g 1 ^ (v 1).val * g 2 ^ (v 2).val * g 3 ^ (v 3).val * g 4 ^ (v 4).val) =
      φ (g 0 ^ (w 0).val * g 1 ^ (w 1).val * g 2 ^ (w 2).val * g 3 ^ (w 3).val *
        g 4 ^ (w 4).val) → v = w) :
    5 ≤ CFSG.Open.twoLocalPrimeRank 5 K := by
  obtain ⟨Q, hQ1, hQ2, hQ3⟩ := u5_exists_twoLocal φ hker t ht2 ht1
  have hc : ∀ z : K, φ z = 1 → z ∈ Subgroup.center K := fun z hz => (hker z).1 hz
  set S : Set K := Set.range g ∪ (Subgroup.center K : Set K) with hS_def
  have hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    rcases ha with ⟨j, rfl⟩ | ha <;> rcases hb with ⟨j', rfl⟩ | hb
    · by_cases hjj : j = j'
      · rw [hjj]
      · obtain ⟨n, hn1, hn2⟩ := hsw j j' hjj
        exact u5_comm_of_lifts φ hc (hgc j j') hn1 hn2 (hg5 j) (hg5 j')
    · exact Subgroup.mem_center_iff.1 hb (g j)
    · exact (Subgroup.mem_center_iff.1 ha (g j')).symm
    · exact Subgroup.mem_center_iff.1 hb a
  set P : Subgroup K := Subgroup.closure S with hP_def
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := u5_comm_closure S hSc
  have hPz : Subgroup.center K ≤ P := fun z hz => Subgroup.subset_closure (Or.inr hz)
  have hP5 : ∀ x ∈ P, φ x ^ 5 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨j, rfl⟩ | hz
      · exact hg5 j
      · rw [(hker x).2 hz, one_pow]
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hcom : Commute (φ x) (φ y) := by
        show φ x * φ y = φ y * φ x
        rw [← map_mul, ← map_mul, hPc x hx y hy]
      rw [map_mul, (hcom.mul_pow 5), ihx, ihy, one_mul]
    | inv x hx ihx => rw [map_inv, inv_pow, ihx, inv_one]
  have hPN : P ≤ Subgroup.normalizer (Q : Set K) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro a (⟨j, rfl⟩ | ha)
    · exact hQ3 (g j) (hgt j)
    · refine Subgroup.mem_normalizer_iff.2 fun h => ?_
      have hah : a * h * a⁻¹ = h := by rw [← Subgroup.mem_center_iff.1 ha h, mul_inv_cancel_right]
      rw [hah]
  have hXP : ∀ v : Fin 5 → ZMod 5, g 0 ^ (v 0).val * g 1 ^ (v 1).val * g 2 ^ (v 2).val *
      g 3 ^ (v 3).val * g 4 ^ (v 4).val ∈ P := by
    intro v
    have hm : ∀ j, g j ∈ P := fun j => Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
    exact P.mul_mem (P.mul_mem (P.mul_mem (P.mul_mem (P.pow_mem (hm 0) _)
      (P.pow_mem (hm 1) _)) (P.pow_mem (hm 2) _)) (P.pow_mem (hm 3) _)) (P.pow_mem (hm 4) _)
  have hcard : 5 ^ 5 ≤ Nat.card (φ.comp P.subtype).range := by
    haveI : Finite (φ.comp P.subtype).range :=
      (Set.finite_range (φ.comp P.subtype)).to_subtype
    let f : (Fin 5 → ZMod 5) → (φ.comp P.subtype).range := fun v =>
      ⟨φ _, ⟨⟨_, hXP v⟩, rfl⟩⟩
    have hf : Function.Injective f := fun v w h => hinj v w (congrArg Subtype.val h)
    have h1 := Nat.card_le_card_of_injective f hf
    have h2 : Nat.card (Fin 5 → ZMod 5) = 5 ^ 5 := by simp [Nat.card_fun]
    omega
  obtain ⟨Ω, hΩP, hΩab, hΩcard⟩ := u5_exists_elemAbelian φ hker P hPz hPc hP5 hcard
  have hΩN : Ω ≤ Subgroup.normalizer (Q : Set K) := hΩP.trans hPN
  obtain ⟨k, hk5, hkcard⟩ := u5_five_pow Ω hΩab hΩcard
  have hpR := u5_le_pRank _ Ω hΩN hΩab k hkcard
  exact u5_le_twoLocal _ ⟨Q, hQ1, hQ2, rfl⟩ 5 (hk5.trans hpR)

end Assembly

section Main

theorem u5Swap_comm {F : Type} [Field F] {d : ℕ} [NeZero d] (i j : Fin d) :
    u5Swap (F := F) i j = u5Swap j i :=
  Units.ext (by rw [u5Swap_val, u5Swap_val, Matrix.swap_comm])

theorem u5Swap_sq {F : Type} [Field F] {d : ℕ} [NeZero d] (i j : Fin d) :
    u5Swap (F := F) i j * u5Swap i j = 1 := by
  have := mul_inv_cancel (u5Swap (F := F) i j)
  rwa [u5Swap_inv] at this

theorem u5_gen_comm_swap01 {F : Type} [Field F] {d : ℕ} [NeZero d] (hd : 8 ≤ d) (ζ : Fˣ)
    (h5 : ζ ^ 5 = 1) (j : Fin 5) :
    u5Swap (F := F) (d := d) 0 1 * u5Torus ζ h5 (u5Gen j) =
      u5Torus ζ h5 (u5Gen j) * u5Swap (F := F) (d := d) 0 1 := by
  have h := u5Swap_conj ζ h5 (F := F) (d := d) 0 1 (u5Gen j)
  rw [u5Gen_swap01 hd j] at h
  have h' := congrArg (· * u5Swap (F := F) (d := d) 0 1) h
  simp only [mul_assoc, u5Swap_sq, mul_one] at h'
  exact h'

theorem u5_conj_gen {F : Type} [Field F] {d : ℕ} [NeZero d] (hd : 8 ≤ d) (ζ : Fˣ)
    (h5 : ζ ^ 5 = 1) {i j : Fin 5} (hij : i ≠ j) :
    u5Swap (F := F) (d := d) (u5Idx i) (u5Idx j) * u5Torus ζ h5 (u5Gen i) *
      (u5Swap (F := F) (d := d) (u5Idx i) (u5Idx j))⁻¹ = u5Torus ζ h5 (u5Gen j) := by
  rw [u5Swap_inv, u5Swap_conj, u5Gen_swap hd hij]

theorem u5_swap_not_scalar {F : Type} [Field F] {d : ℕ} [NeZero d] (i j : Fin d) (hij : i ≠ j)
    (c : Fˣ) (h : u5Swap (F := F) i j = Matrix.GeneralLinearGroup.scalar (Fin d) c) : False := by
  have h2 : (Matrix.swap F i j) i j = 1 := by
    have e := u5_swap_mul_apply i j (1 : Matrix (Fin d) (Fin d) F) i j
    rw [mul_one, Matrix.one_apply, Equiv.swap_apply_left, if_pos rfl] at e
    exact e
  have h3 : ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) i j = 0 := by
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  have key : (u5Swap (F := F) i j : Matrix (Fin d) (Fin d) F) i j =
      ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j :=
    by rw [h]
  rw [u5Swap_val, h2, h3] at key
  exact one_ne_zero key

theorem u5RankAt_holds : U5RankAt := by
  intro K _ _ r hr hM
  have hX := CFSG.StandardType.largeEvenMarking_exists_markedModel hM
  obtain ⟨lab, hl, R, hRg, I, F', θ, hs, hna, hPlab, hmR⟩ := hX
  have hlab : lab = ⟨.twA, 5 * r - 1, 2⟩ := hPlab
  subst hlab
  have hMod := CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hmR
  have hLM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU (5 * r - 1 + 1) 2 2 := hMod
  have hsc : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSU (5 * r - 1 + 1) 2 2 := by
    rcases hLM with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals omega
  obtain ⟨-, F, hFi, hFf, hF, ⟨e⟩⟩ := hsc
  have hd8 : 8 ≤ 5 * r - 1 + 1 := by omega
  generalize 5 * r - 1 + 1 = d at e hd8
  haveI : NeZero d := ⟨by omega⟩
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have h16 : Fintype.card F = 2 ^ 4 := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨p, hpc, n, hp, hpn⟩ := FiniteField.card' F
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 ^ 4 := by
      rw [← h16, hpn]
      exact dvd_pow_self p (by exact_mod_cast n.ne_zero)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  haveI : CharP F 2 := hpc
  have hneg : (-1 : F) = 1 := CharTwo.neg_eq 1
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5card : 5 ∣ Fintype.card Fˣ := by
    rw [Fintype.card_units, h16]
    norm_num
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card 5 h5card
  have h5 : ζ ^ 5 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  obtain ⟨φ, hφ⟩ : ∃ φ : K →* StatedProj (StatedSU d (2 ^ 2) F),
      ∀ z : K, φ z = e (QuotientGroup.mk z) :=
    ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)), fun z => rfl⟩
  have hker : ∀ z : K, φ z = 1 ↔ z ∈ Subgroup.center K := by
    intro z
    rw [hφ, map_eq_one_iff e (MulEquiv.injective e), QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) x
    exact ⟨z, by rw [hφ]; rfl⟩
  have h01 : (0 : Fin d) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_zero, u5_val1 hd8] at this
    omega
  set ρ := QuotientGroup.mk' ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ 2) F))
    with hρ
  let sw : (i j : Fin d) → i ≠ j → StatedSU d (2 ^ 2) F := fun i j hij =>
    ⟨u5Swap i j, u5Swap_mem hneg i j hij⟩
  obtain ⟨t, ht⟩ := hsurj (ρ (sw 0 1 h01))
  have ht2 : φ t ^ 2 = 1 := by
    rw [ht, ← map_pow, ← map_one ρ]
    congr 1
    apply Subtype.ext
    show u5Swap (F := F) 0 1 ^ 2 = 1
    rw [sq]
    exact u5Swap_sq 0 1
  have ht1 : φ t ≠ 1 := by
    rw [ht]
    intro h
    obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 (by
      have h' := (QuotientGroup.eq_one_iff _).1 h
      rw [Subgroup.mem_subgroupOf, StatedScalars] at h'
      exact h')
    exact u5_swap_not_scalar 0 1 h01 c hc.symm
  obtain ⟨g, hg⟩ : ∃ g : Fin 5 → K, ∀ j, φ (g j) = u5Phi ζ h5 (u5G ζ h5 j) :=
    ⟨fun j => (hsurj (u5Phi ζ h5 (u5G ζ h5 j))).choose,
      fun j => (hsurj _).choose_spec⟩
  have hΦ : ∀ X : u5E1 (F := F) (d := d) ζ h5, u5Phi ζ h5 X = ρ (u5Tau ζ h5 X) :=
    fun X => rfl
  have hgt : ∀ j, Commute (φ (g j)) (φ t) := by
    intro j
    rw [hg j, ht, hΦ]
    have hc : Commute (u5Tau ζ h5 (u5G ζ h5 j)) (sw 0 1 h01) :=
      Subtype.ext (u5_gen_comm_swap01 hd8 ζ h5 j).symm
    exact hc.map ρ
  have hgc : ∀ j j', φ (g j) * φ (g j') = φ (g j') * φ (g j) := by
    intro j j'
    rw [hg j, hg j', ← map_mul, ← map_mul, mul_comm]
  have hg5 : ∀ j, φ (g j) ^ 5 = 1 := by
    intro j
    rw [hg j, ← map_pow]
    have h1 : u5G ζ h5 j ^ 5 = 1 := Subtype.ext (by simpa [u5G] using u5Gen_pow5 hd8 j)
    rw [h1, map_one]
  have hsw : ∀ j j', j ≠ j' → ∃ n : K, φ (n * g j * n⁻¹) = φ (g j') ∧
      φ (n * g j' * n⁻¹) = φ (g j) := by
    intro j j' hjj
    have hij : u5Idx (d := d) j ≠ u5Idx j' := fun h => hjj (u5Idx_inj hd8 h)
    obtain ⟨n, hn⟩ := hsurj (ρ (sw (u5Idx j) (u5Idx j') hij))
    refine ⟨n, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hn, hg j, hg j', hΦ, hΦ]
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (u5_conj_gen hd8 ζ h5 hjj)
    · rw [map_mul, map_mul, map_inv, hn, hg j, hg j', hΦ, hΦ]
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      have hc := u5_conj_gen hd8 ζ h5 (Ne.symm hjj)
      rw [u5Swap_comm (u5Idx j') (u5Idx j)] at hc
      exact Subtype.ext hc
  have hinj : ∀ v w : Fin 5 → ZMod 5,
      φ (g 0 ^ (v 0).val * g 1 ^ (v 1).val * g 2 ^ (v 2).val * g 3 ^ (v 3).val *
        g 4 ^ (v 4).val) =
      φ (g 0 ^ (w 0).val * g 1 ^ (w 1).val * g 2 ^ (w 2).val * g 3 ^ (w 3).val *
        g 4 ^ (w 4).val) → v = w := by
    intro v w h
    have hφX : ∀ v : Fin 5 → ZMod 5, φ (g 0 ^ (v 0).val * g 1 ^ (v 1).val * g 2 ^ (v 2).val *
        g 3 ^ (v 3).val * g 4 ^ (v 4).val) = u5Phi ζ h5 (u5Xv (F := F) (d := d) ζ h5 v) := by
      intro v
      simp only [u5Xv, map_mul, map_pow, hg]
    rw [hφX, hφX] at h
    exact u5Xv_inj hd8 ζ h5 (u5Phi_injOn ζ h5 hζ _ _ (u5Xv_zero hd8 ζ h5 v)
      (u5Xv_zero hd8 ζ h5 w) h)
  exact u5_main_abstract φ hker t ht2 ht1 g hg5 hgt hgc hsw hinj

end Main

end CFSG.LocalAnalysis.GLTheoremA
