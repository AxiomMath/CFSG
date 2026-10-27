module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightFin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightOrb
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.QuasithinUnique.Setup.X1.Tight

section Kap

variable {V : Type} [CommGroup V]

@[expose] def kap (v : Fin 5 → V) (n : ℕ) : V :=
  ∏ k : Fin 5, if n.testBit k.val then v k else 1

theorem kap_zero (v : Fin 5 → V) : kap v 0 = 1 := by simp [kap]

theorem kap_xor {v : Fin 5 → V} (hv : ∀ k, v k * v k = 1) (m n : ℕ) :
    kap v (m ^^^ n) = kap v m * kap v n := by
  unfold kap
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor]
  cases h1 : m.testBit k.val <;> cases h2 : n.testBit k.val <;> simp [hv k]

theorem kap_self {v : Fin 5 → V} (hv : ∀ k, v k * v k = 1) (n : ℕ) :
    kap v n * kap v n = 1 := by
  rw [← kap_xor hv, Nat.xor_self, kap_zero]

theorem kap_two_pow (v : Fin 5 → V) (k : Fin 5) : kap v (2 ^ k.val) = v k := by
  unfold kap
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    have : ¬ (k.val = j.val) := fun h => hj (Fin.ext h.symm)
    simp [this]
  · simp

theorem xor_lt32 {m n : ℕ} (hm : m < 32) (hn : n < 32) : m ^^^ n < 32 := by
  have := Nat.xor_lt_two_pow (n := 5) (x := m) (y := n) (by simpa using hm) (by simpa using hn)
  simpa using this

theorem app5_lt32 {f : ℕ → ℕ} (hf : ∀ k < 5, f k < 32) (n : ℕ) : app5 f n < 32 := by
  have h : ∀ (b : Bool) (k : ℕ), k < 5 → (if b then f k else 0) < 32 := fun b k hk => by
    cases b <;> simp [hf k hk]
  unfold app5
  exact xor_lt32 (xor_lt32 (xor_lt32 (xor_lt32 (h _ 0 (by norm_num)) (h _ 1 (by norm_num)))
    (h _ 2 (by norm_num))) (h _ 3 (by norm_num))) (h _ 4 (by norm_num))

theorem kap_app5 {v : Fin 5 → V} (hv : ∀ k, v k * v k = 1) (f : ℕ → ℕ) (n : ℕ) :
    kap v (app5 f n) = ∏ k : Fin 5, if n.testBit k.val then kap v (f k.val) else 1 := by
  have h : ∀ (b : Bool) (m : ℕ), kap v (if b then m else 0) = if b then kap v m else 1 := by
    intro b m
    cases b <;> simp [kap_zero]
  unfold app5
  simp only [kap_xor hv, h, Fin.prod_univ_five]
  simp

theorem kap_surj {v : Fin 5 → V} (hv : ∀ k, v k * v k = 1)
    (hgen : Subgroup.closure (Set.range v) = ⊤) (x : V) : ∃ n < 32, kap v n = x := by
  let H : Subgroup V :=
    { carrier := {x | ∃ n < 32, kap v n = x}
      one_mem' := ⟨0, by norm_num, kap_zero v⟩
      mul_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
        exact ⟨m ^^^ n, xor_lt32 hm hn, kap_xor hv m n⟩
      inv_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨m, hm, (inv_eq_of_mul_eq_one_right (kap_self hv m)).symm⟩ }
  have hle : Subgroup.closure (Set.range v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨2 ^ k.val, by
      have : k.val < 5 := k.2
      calc 2 ^ k.val < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) this
        _ = 32 := by norm_num, kap_two_pow v k⟩
  have : x ∈ H := hle (by rw [hgen]; exact Subgroup.mem_top x)
  exact this

theorem kap_inj [Finite V] {v : Fin 5 → V} (hv : ∀ k, v k * v k = 1)
    (hgen : Subgroup.closure (Set.range v) = ⊤) (hcard : Nat.card V = 32) {m n : ℕ}
    (hm : m < 32) (hn : n < 32) (h : kap v m = kap v n) : m = n := by
  let F : Fin 32 → V := fun n => kap v n.val
  have hsurj : Function.Surjective F := fun x => by
    obtain ⟨n, hn, hx⟩ := kap_surj hv hgen x
    exact ⟨⟨n, hn⟩, hx⟩
  have hbij : Function.Bijective F :=
    hsurj.bijective_of_nat_card_le (by simp [hcard])
  have := hbij.1 (a₁ := ⟨m, hm⟩) (a₂ := ⟨n, hn⟩) h
  simpa using this

theorem hom_kap {v : Fin 5 → V} (hv : ∀ k, v k * v k = 1) (φ : V →* V) (f : ℕ → ℕ)
    (hf : ∀ k : Fin 5, kap v (f k.val) = φ (v k)) (n : ℕ) :
    φ (kap v n) = kap v (app5 f n) := by
  rw [kap_app5 hv, kap, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · exact (hf k).symm
  · exact map_one φ

theorem card_range_eq [Finite V] {v : Fin 5 → V} (hv : ∀ k, v k * v k = 1)
    (hgen : Subgroup.closure (Set.range v) = ⊤) (hcard : Nat.card V = 32) (φ : V →* V)
    (f : ℕ → ℕ) (hf : ∀ k : Fin 5, kap v (f k.val) = φ (v k)) (hlt : ∀ k < 5, f k < 32) :
    Nat.card φ.range = imgCard f := by
  have hφ := hom_kap hv φ f hf
  have hrange : (φ.range : Set V) =
      (fun n => kap v n) '' (((Finset.range 32).image (app5 f) : Finset ℕ) : Set ℕ) := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_image, Finset.coe_image,
      Finset.coe_range, Set.mem_Iio]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨n, hn, rfl⟩ := kap_surj hv hgen y
      exact ⟨app5 f n, ⟨n, hn, rfl⟩, (hφ n).symm⟩
    · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      exact ⟨kap v n, hφ n⟩
  have hinj : Set.InjOn (fun n => kap v n)
      (((Finset.range 32).image (app5 f) : Finset ℕ) : Set ℕ) := by
    intro m hm n hn h
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hm hn
    obtain ⟨m', -, rfl⟩ := hm
    obtain ⟨n', -, rfl⟩ := hn
    exact kap_inj hv hgen hcard (app5_lt32 hlt m') (app5_lt32 hlt n') h
  calc Nat.card φ.range = (φ.range : Set V).ncard := (Nat.card_coe_set_eq _)
    _ = ((((Finset.range 32).image (app5 f) : Finset ℕ) : Set ℕ)).ncard := by
        rw [hrange]; exact hinj.ncard_image
    _ = imgCard f := Set.ncard_coe_finset _

theorem rotn_lt32 (m n : ℕ) : rotn m n < 32 ∨ 32 ≤ n := by
  induction m with
  | zero => exact lt_or_ge n 32
  | succ m ih =>
    rcases ih with h | h
    · left
      exact app5_lt32 (fun k hk => by
        simp only [shiftC]
        calc 2 ^ ((k + 1) % 5) < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt _ (by norm_num))
          _ = 32 := by norm_num) _
    · right; exact h

theorem rotn_lt32' {m n : ℕ} (hn : n < 32) : rotn m n < 32 := by
  rcases rotn_lt32 m n with h | h
  · exact h
  · omega

theorem dbC_lt32 (k : ℕ) : dbC k < 32 := by
  simp only [dbC]
  calc 2 ^ ((2 * k) % 5) < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt _ (by norm_num))
    _ = 32 := by norm_num

end Kap

section GCoords

variable {V : Type} [CommGroup V]

structure GCoords (γ : MulAut V) where
  v : Fin 5 → V
  hgen : Subgroup.closure (Set.range v) = ⊤
  hγ : ∀ k : Fin 5, γ (v k) = v (k + 1)

variable {γ : MulAut V}

theorem fin5_add_one_val : ∀ k : Fin 5, (k + 1 : Fin 5).val = (k.val + 1) % 5 := by decide

theorem fin5_two_mul_val : ∀ k : Fin 5, (2 * k : Fin 5).val = (2 * k.val) % 5 := by decide

theorem hom_kap_aut {v : Fin 5 → V} (hv : ∀ k, v k * v k = 1) (φ : MulAut V) (f : ℕ → ℕ)
    (hf : ∀ k : Fin 5, kap v (f k.val) = φ (v k)) (n : ℕ) :
    φ (kap v n) = kap v (app5 f n) :=
  hom_kap hv φ.toMonoidHom f hf n

theorem GCoords.kap_shiftC (C : GCoords γ) (k : Fin 5) :
    kap C.v (shiftC k.val) = γ (C.v k) := by
  have : shiftC k.val = 2 ^ (k + 1 : Fin 5).val := by
    rw [fin5_add_one_val]; rfl
  rw [this, kap_two_pow, C.hγ]

theorem GCoords.map_kap (C : GCoords γ) (hV : ∀ x : V, x * x = 1) (n : ℕ) :
    γ (kap C.v n) = kap C.v (app5 shiftC n) :=
  hom_kap_aut (fun _ => hV _) γ shiftC (fun k => C.kap_shiftC k) n

theorem GCoords.pow_kap (C : GCoords γ) (hV : ∀ x : V, x * x = 1) (m n : ℕ) :
    (γ ^ m) (kap C.v n) = kap C.v (rotn m n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, ih, C.map_kap hV]
    rfl

theorem GCoords.inj [Finite V] (C : GCoords γ) (hV : ∀ x : V, x * x = 1) (hcard : Nat.card V = 32) {m n : ℕ}
    (hm : m < 32) (hn : n < 32) (h : kap C.v m = kap C.v n) : m = n :=
  kap_inj (fun _ => hV _) C.hgen hcard hm hn h

theorem GCoords.surj (C : GCoords γ) (hV : ∀ x : V, x * x = 1) (x : V) : ∃ n < 32, kap C.v n = x :=
  kap_surj (fun _ => hV _) C.hgen x

theorem pow_mod_five (h5 : γ ^ 5 = 1) (m : ℕ) : γ ^ m = γ ^ (m % 5) := by
  conv_lhs => rw [← Nat.div_add_mod m 5, pow_add, pow_mul, h5, one_pow, one_mul]

@[expose] def GCoords.ofOrb (h5 : γ ^ 5 = 1) (u : V) (hu : Subgroup.closure
    (Set.range fun k : Fin 5 => (γ ^ (k : ℕ)) u) = ⊤) : GCoords γ where
  v k := (γ ^ (k : ℕ)) u
  hgen := hu
  hγ k := by
    show γ ((γ ^ (k : ℕ)) u) = (γ ^ ((k + 1 : Fin 5) : ℕ)) u
    rw [fin5_add_one_val, ← pow_mod_five h5, pow_succ', MulAut.mul_apply]

end GCoords

section Coords

variable {V : Type} [CommGroup V] [Finite V]

structure Coords (γ δ : MulAut V) extends GCoords γ where
  hδ : ∀ k : Fin 5, δ (v k) = v (2 * k)

omit [Finite V] in
theorem delta_pow (γ δ : MulAut V) (h : δ * γ * δ⁻¹ = γ ^ 2) (k : ℕ) :
    δ * γ ^ k = γ ^ (2 * k) * δ := by
  have h1 : δ * γ = γ ^ 2 * δ := by
    rw [← h]; group
  induction k with
  | zero => simp
  | succ k ih =>
    calc δ * γ ^ (k + 1) = (δ * γ ^ k) * γ := by rw [pow_succ, mul_assoc]
      _ = γ ^ (2 * k) * (δ * γ) := by rw [ih, mul_assoc]
      _ = γ ^ (2 * (k + 1)) * δ := by rw [h1, ← mul_assoc, ← pow_add]; congr 2

theorem iterate_app5_lt32 {f : ℕ → ℕ} (hf : ∀ k < 5, f k < 32) (m n : ℕ) (hn : n < 32) :
    (app5 f)^[m] n < 32 := by
  induction m generalizing n with
  | zero => exact hn
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (app5_lt32 hf n)

theorem exists_coords
    (hV : ∀ x : V, x * x = 1) (hcard : Nat.card V = 32) (γ δ : MulAut V)
    (h5 : γ ^ 5 = 1) (h1 : γ ≠ 1) (hδ4 : δ ^ 4 = 1) (hδγ : δ * γ * δ⁻¹ = γ ^ 2) :
    Nonempty (Coords γ δ) := by
  obtain ⟨u0, hu0⟩ := exists_cyclic_generator hcard γ h5 h1
  let C0 : GCoords γ := GCoords.ofOrb h5 u0 hu0
  obtain ⟨w, hw, hwk⟩ := C0.surj hV (δ u0)
  have hδv : ∀ k : Fin 5, δ (C0.v k) = kap C0.v (dwC w k.val) := by
    intro k
    show δ ((γ ^ (k : ℕ)) u0) = _
    have := delta_pow γ δ hδγ k
    calc δ ((γ ^ (k : ℕ)) u0) = (δ * γ ^ (k : ℕ)) u0 := rfl
      _ = (γ ^ (2 * (k : ℕ)) * δ) u0 := by rw [this]
      _ = (γ ^ (2 * (k : ℕ))) (δ u0) := rfl
      _ = (γ ^ (2 * (k : ℕ))) (kap C0.v w) := by rw [hwk]
      _ = kap C0.v (rotn (2 * (k : ℕ)) w) := C0.pow_kap hV _ _
  have hδk : ∀ n, δ (kap C0.v n) = kap C0.v (app5 (dwC w) n) :=
    hom_kap_aut (fun _ => hV _) δ (dwC w) (fun k => (hδv k).symm)
  have hlt : ∀ k < 5, dwC w k < 32 := fun k _ => rotn_lt32' hw
  have hδpow : ∀ m n, (δ ^ m) (kap C0.v n) = kap C0.v ((app5 (dwC w))^[m] n) := by
    intro m
    induction m with
    | zero => intro n; rfl
    | succ m ih =>
      intro n
      rw [pow_succ', MulAut.mul_apply, ih, hδk, Function.iterate_succ_apply']
  have hord : ∀ k < 5, app5 (dwC w) (app5 (dwC w) (app5 (dwC w) (app5 (dwC w) (2 ^ k)))) = 2 ^ k := by
    intro k hk
    have h4 := hδpow 4 (2 ^ k)
    rw [hδ4, show (1 : MulAut V) (kap C0.v (2 ^ k)) = kap C0.v (2 ^ k) from rfl] at h4
    have hk2 : 2 ^ k < 32 := by
      calc 2 ^ k < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) hk
        _ = 32 := by norm_num
    exact (C0.inj hV hcard (iterate_app5_lt32 hlt 4 _ hk2) hk2 h4.symm)
  obtain ⟨x, hx, hcyc, hfix⟩ := rebase_fin w hw hord
  have hδu : δ (kap C0.v x) = kap C0.v x := by rw [hδk, hfix]
  have hγu : ∀ k : ℕ, (γ ^ k) (kap C0.v x) = kap C0.v (rotn k x) := fun k => C0.pow_kap hV k x
  have hcyc' : ∀ z < 32, ∃ e < 32, app5 (fun k => rotn k x) e = z := by
    intro z hz
    unfold cycOK at hcyc
    have := List.all_eq_true.1 hcyc z (List.mem_range.2 hz)
    obtain ⟨e, he, hez⟩ := List.any_eq_true.1 this
    exact ⟨e, List.mem_range.1 he, beq_iff_eq.1 hez⟩
  have hgen : Subgroup.closure (Set.range fun k : Fin 5 => (γ ^ (k : ℕ)) (kap C0.v x)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, rfl⟩ := C0.surj hV y
    obtain ⟨e, he, rfl⟩ := hcyc' z hz
    rw [kap_app5 (fun _ => hV _)]
    refine Subgroup.prod_mem _ fun k _ => ?_
    split_ifs
    · rw [← hγu]
      exact Subgroup.subset_closure ⟨k, rfl⟩
    · exact Subgroup.one_mem _
  refine ⟨{ GCoords.ofOrb h5 (kap C0.v x) hgen with hδ := fun k => ?_ }⟩
  show δ ((γ ^ (k : ℕ)) (kap C0.v x)) = (γ ^ ((2 * k : Fin 5) : ℕ)) (kap C0.v x)
  have := delta_pow γ δ hδγ k
  calc δ ((γ ^ (k : ℕ)) (kap C0.v x)) = (δ * γ ^ (k : ℕ)) (kap C0.v x) := rfl
    _ = (γ ^ (2 * (k : ℕ)) * δ) (kap C0.v x) := by rw [this]
    _ = (γ ^ (2 * (k : ℕ))) (δ (kap C0.v x)) := rfl
    _ = (γ ^ (2 * (k : ℕ))) (kap C0.v x) := by rw [hδu]
    _ = (γ ^ ((2 * k : Fin 5) : ℕ)) (kap C0.v x) := by rw [fin5_two_mul_val, ← pow_mod_five h5]

end Coords

section Final

variable {V : Type} [CommGroup V]

theorem th0C_lt32 {x y : ℕ} (hx : x < 32) (hy : y < 32) (k : ℕ) : th0C x y k < 32 := by
  have hD : ∀ n, n < 32 → app5 dbC n < 32 := fun n _ => app5_lt32 (fun k _ => dbC_lt32 k) n
  unfold th0C
  split_ifs
  · exact hx
  · exact hy
  · exact hD _ hy
  · exact hD _ (hD _ (hD _ hy))
  · exact hD _ (hD _ hy)

theorem thC_lt32 {x y : ℕ} (hx : x < 32) (hy : y < 32) (i k : ℕ) : thC x y i k < 32 :=
  rotn_lt32' (th0C_lt32 hx hy _)

theorem thC_zero {x y : ℕ} {k : ℕ} (hk : k < 5) : thC x y 0 k = th0C x y k := by
  have h : (k + 5 - 0 % 5) % 5 = k := by omega
  simp only [thC, rotn, h]

theorem thC_succ (x y : ℕ) {n k : ℕ} (hn : n < 4) (hk : k < 5) :
    thC x y (n + 1) k = app5 shiftC (thC x y n ((k + 4) % 5)) := by
  have h : (k + 5 - (n + 1) % 5) % 5 = ((k + 4) % 5 + 5 - n % 5) % 5 := by omega
  simp only [thC, rotn, h]

theorem fin5_sub_one_val : ∀ k : Fin 5, (k - 1 : Fin 5).val = (k.val + 4) % 5 := by decide

omit [CommGroup V] in
theorem fin5_two_mul_two : (2 * 2 : Fin 5) = 4 := by decide

omit [CommGroup V] in
theorem fin5_two_mul_four : (2 * 4 : Fin 5) = 3 := by decide

variable [Finite V]

omit [Finite V] in
theorem Coords.kap_dbC {γ δ : MulAut V} (C : Coords γ δ) (k : Fin 5) :
    kap C.v (dbC k.val) = δ (C.v k) := by
  have : dbC k.val = 2 ^ (2 * k : Fin 5).val := by
    rw [fin5_two_mul_val]; rfl
  rw [this, kap_two_pow, C.hδ]

omit [Finite V] in
theorem Coords.map_kap {γ δ : MulAut V} (C : Coords γ δ) (hV : ∀ x : V, x * x = 1) (n : ℕ) :
    δ (kap C.v n) = kap C.v (app5 dbC n) :=
  hom_kap_aut (fun _ => hV _) δ dbC (fun k => C.kap_dbC k) n

omit [Finite V] in
theorem Coords.inv_v {γ δ : MulAut V} (C : Coords γ δ) (k : Fin 5) :
    γ⁻¹ (C.v k) = C.v (k - 1) := by
  have h := C.hγ (k - 1)
  rw [sub_add_cancel] at h
  rw [← h]
  exact MulAut.inv_apply_self V γ _

theorem afc2
    (hV : ∀ x : V, x * x = 1) (hcard : Nat.card V = 32) (γ δ : MulAut V)
    (h5 : γ ^ 5 = 1) (h1 : γ ≠ 1) (hδ4 : δ ^ 4 = 1) (hδγ : δ * γ * δ⁻¹ = γ ^ 2)
    (Θ : Fin 5 → (V →* V))
    (hΘc : ∀ (i : Fin 5) (x : V), Θ (i + 1) x = γ (Θ i (γ⁻¹ x)))
    (hinj : Function.Injective (Θ 0))
    (hΘδ : ∀ x, Θ 0 (δ x) = δ (Θ 0 x))
    (hsum : ∀ x, Θ 0 x * Θ 1 x * Θ 2 x * Θ 3 x * Θ 4 x = x)
    (hr1 : 16 ≤ Nat.card (Θ 0 * Θ 1).range)
    (hr2 : 16 ≤ Nat.card (Θ 0 * Θ 1 * Θ 2 * Θ 3).range) : False := by
  obtain ⟨C⟩ := exists_coords hV hcard γ δ h5 h1 hδ4 hδγ
  have hv : ∀ k, C.v k * C.v k = 1 := fun _ => hV _
  have hex : ∀ k : Fin 5, ∃ n < 32, kap C.v n = Θ 0 (C.v k) := fun k => C.surj hV _
  choose g hg hgk using hex
  have hrel : ∀ k : Fin 5, g (2 * k) = app5 dbC (g k) := by
    intro k
    have h := hΘδ (C.v k)
    rw [C.hδ] at h
    rw [← hgk, ← hgk, C.map_kap hV] at h
    exact C.inj hV hcard (hg _) (app5_lt32 (fun k _ => dbC_lt32 k) _) h
  have hg0 : g 0 = 0 ∨ g 0 = 1 ∨ g 0 = 30 ∨ g 0 = 31 := by
    have := hrel 0
    simp only [mul_zero] at this
    exact fix_dbC _ (hg 0) this.symm
  have e2 : g 2 = app5 dbC (g 1) := by simpa using hrel 1
  have e4 : g 4 = app5 dbC (g 2) := by
    have := hrel 2
    rwa [fin5_two_mul_two] at this
  have e3 : g 3 = app5 dbC (g 4) := by
    have := hrel 4
    rwa [fin5_two_mul_four] at this
  have hG : ∀ k : Fin 5, g k = th0C (g 0) (g 1) k.val := by
    intro k
    fin_cases k
    · simp [th0C]
    · simp [th0C]
    · simpa [th0C] using e2
    · simp only [th0C]
      simp [e3, e4, e2]
    · simp only [th0C]
      simp [e4, e2]
  have hx0 : g 0 < 32 := hg 0
  have hy : g 1 < 32 := hg 1
  have hcol : ∀ (n : ℕ) (hn : n < 5) (k : Fin 5),
      Θ ⟨n, hn⟩ (C.v k) = kap C.v (thC (g 0) (g 1) n k.val) := by
    intro n
    induction n with
    | zero =>
      intro hn k
      rw [thC_zero k.2, ← hG k]
      exact (hgk k).symm
    | succ n ih =>
      intro hn k
      have hn4 : n < 4 := by omega
      have hΘ := hΘc ⟨n, by omega⟩ (C.v k)
      have hfin : (⟨n, by omega⟩ + 1 : Fin 5) = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        simp only [Fin.val_add]
        omega
      rw [hfin] at hΘ
      rw [hΘ, C.inv_v, ih (by omega) (k - 1), C.toGCoords.map_kap hV, thC_succ _ _ hn4 k.2,
        fin5_sub_one_val]
  have h0 : ∀ k : Fin 5, Θ 0 (C.v k) = kap C.v (thC (g 0) (g 1) 0 k.val) := fun k =>
    hcol 0 (by norm_num) k
  have h1' : ∀ k : Fin 5, Θ 1 (C.v k) = kap C.v (thC (g 0) (g 1) 1 k.val) := fun k =>
    hcol 1 (by norm_num) k
  have h2' : ∀ k : Fin 5, Θ 2 (C.v k) = kap C.v (thC (g 0) (g 1) 2 k.val) := fun k =>
    hcol 2 (by norm_num) k
  have h3' : ∀ k : Fin 5, Θ 3 (C.v k) = kap C.v (thC (g 0) (g 1) 3 k.val) := fun k =>
    hcol 3 (by norm_num) k
  have h4' : ∀ k : Fin 5, Θ 4 (C.v k) = kap C.v (thC (g 0) (g 1) 4 k.val) := fun k =>
    hcol 4 (by norm_num) k
  have hT : ∀ i k, thC (g 0) (g 1) i k < 32 := fun i k => thC_lt32 hx0 hy i k
  have hsumk : ∀ k : Fin 5, thC (g 0) (g 1) 0 k.val ^^^ thC (g 0) (g 1) 1 k.val ^^^
      thC (g 0) (g 1) 2 k.val ^^^ thC (g 0) (g 1) 3 k.val ^^^ thC (g 0) (g 1) 4 k.val =
      2 ^ k.val := by
    intro k
    have h := hsum (C.v k)
    rw [h0 k, h1' k, h2' k, h3' k, h4' k, ← kap_two_pow C.v k, ← kap_xor hv, ← kap_xor hv,
      ← kap_xor hv, ← kap_xor hv] at h
    refine C.inj hV hcard ?_ ?_ h
    · exact xor_lt32 (xor_lt32 (xor_lt32 (xor_lt32 (hT _ _) (hT _ _)) (hT _ _)) (hT _ _)) (hT _ _)
    · calc 2 ^ k.val < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) k.2
        _ = 32 := by norm_num
  have hbij : Nat.card (Θ 0).range = 32 := by
    rw [← hcard]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hr0 : imgCard (th0C (g 0) (g 1)) = 32 := by
    have := card_range_eq hv C.hgen hcard (Θ 0) (th0C (g 0) (g 1))
      (fun k => by rw [← hG k]; exact hgk k) (fun k _ => th0C_lt32 hx0 hy k)
    rw [← this]
    exact hbij
  have hr1' : 16 ≤ imgCard (fun k => thC (g 0) (g 1) 0 k ^^^ thC (g 0) (g 1) 1 k) := by
    have := card_range_eq hv C.hgen hcard (Θ 0 * Θ 1)
      (fun k => thC (g 0) (g 1) 0 k ^^^ thC (g 0) (g 1) 1 k)
      (fun k => by rw [kap_xor hv, MonoidHom.mul_apply, h0 k, h1' k])
      (fun k _ => xor_lt32 (hT _ _) (hT _ _))
    rw [← this]
    exact hr1
  have hr2' : 16 ≤ imgCard (fun k => thC (g 0) (g 1) 0 k ^^^ thC (g 0) (g 1) 1 k ^^^
      thC (g 0) (g 1) 2 k ^^^ thC (g 0) (g 1) 3 k) := by
    have := card_range_eq hv C.hgen hcard (Θ 0 * Θ 1 * Θ 2 * Θ 3)
      (fun k => thC (g 0) (g 1) 0 k ^^^ thC (g 0) (g 1) 1 k ^^^
        thC (g 0) (g 1) 2 k ^^^ thC (g 0) (g 1) 3 k)
      (fun k => by
        rw [kap_xor hv, kap_xor hv, kap_xor hv, MonoidHom.mul_apply, MonoidHom.mul_apply,
          MonoidHom.mul_apply, h0 k, h1' k, h2' k, h3' k])
      (fun k _ => xor_lt32 (xor_lt32 (xor_lt32 (hT _ _) (hT _ _)) (hT _ _)) (hT _ _))
    rw [← this]
    exact hr2
  have hgood : good (g 0) (g 1) = true := by
    unfold good
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.mem_range]
    refine ⟨⟨⟨?_, hr0⟩, hr1'⟩, hr2'⟩
    intro k hk
    exact hsumk ⟨k, hk⟩
  have hfalse := good_false (g 0) (by rcases hg0 with h | h | h | h <;> simp [h]) (g 1) hy
  rw [hgood] at hfalse
  exact Bool.noConfusion hfalse

end Final

end CFSG.QuasithinUnique.Setup.X1.Tight
