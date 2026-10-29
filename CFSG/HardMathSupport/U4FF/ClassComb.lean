module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.U4FF

@[expose] def locM : Bool → Bool → Bool → ℕ
  | false, false, false => 1
  | true, false, false => 4
  | false, false, true => 4
  | false, true, false => 6
  | true, false, true => 14
  | true, true, false => 20
  | false, true, true => 20
  | true, true, true => 64

@[expose] def locF1 : Bool → Bool → Bool → ℕ
  | false, false, false => 1
  | true, false, false => 2
  | false, false, true => 2
  | false, true, false => 2
  | true, false, true => 2
  | true, true, false => 2
  | false, true, true => 2
  | true, true, true => 0

structure Lbl (n : ℕ) where
  a : Fin n → Bool
  b : Fin n → Bool
  c : Fin n → Bool

namespace Lbl

variable {n : ℕ}

@[expose] def ZeroAt (l : Lbl n) (i : Fin n) : Prop :=
  l.a i = false ∧ l.b i = false ∧ l.c i = false

@[expose] def IsZero (l : Lbl n) : Prop :=
  ∀ i, l.ZeroAt i

@[expose] def dim (l : Lbl n) : ℕ :=
  ∏ i, locM (l.a i) (l.b i) (l.c i)

@[expose] def fix1 (l : Lbl n) : ℕ :=
  ∏ i, locF1 (l.a i) (l.b i) (l.c i)

@[expose] def rk1 (l : Lbl n) : ℕ :=
  (l.dim - l.fix1) / 2

@[expose] def bitA [NeZero n] (l : Lbl n) (j : ℕ) : Bool :=
  if h : j % (2 * n) < n then l.a ⟨j % (2 * n), h⟩
  else l.c ⟨j % (2 * n) - n, by
    have h2 : j % (2 * n) < 2 * n := Nat.mod_lt _ (by have := NeZero.pos n; omega)
    omega⟩

@[expose] def bitB [NeZero n] (l : Lbl n) (j : ℕ) : Bool :=
  l.b ⟨j % n, Nat.mod_lt _ (NeZero.pos n)⟩

@[expose] def RotInv [NeZero n] (l : Lbl n) (d : ℕ) : Prop :=
  ∀ j : ℕ, l.bitA (j + d) = l.bitA j ∧ l.bitB (j + d) = l.bitB j

@[expose] def SingleN (l : Lbl n) : Prop :=
  ∃ i₀ : Fin n, (∀ i, i ≠ i₀ → l.ZeroAt i) ∧ l.b i₀ = false ∧
    ((l.a i₀ = true ∧ l.c i₀ = false) ∨ (l.a i₀ = false ∧ l.c i₀ = true))

@[expose] def SingleO (l : Lbl n) : Prop :=
  ∃ i₀ : Fin n, (∀ i, i ≠ i₀ → l.ZeroAt i) ∧ l.a i₀ = false ∧ l.b i₀ = true ∧ l.c i₀ = false

theorem bitA_eq_a [NeZero n] (l : Lbl n) (i : Fin n) (j : ℕ) (hj : j % (2 * n) = i.val) :
    l.bitA j = l.a i := by
  have h : j % (2 * n) < n := by rw [hj]; exact i.isLt
  unfold bitA
  rw [dif_pos h]
  congr 1
  exact Fin.ext hj

theorem bitA_eq_c [NeZero n] (l : Lbl n) (i : Fin n) (j : ℕ) (hj : j % (2 * n) = i.val + n) :
    l.bitA j = l.c i := by
  have h : ¬ j % (2 * n) < n := by rw [hj]; omega
  unfold bitA
  rw [dif_neg h]
  congr 1
  apply Fin.ext
  show j % (2 * n) - n = i.val
  omega

theorem bitB_eq [NeZero n] (l : Lbl n) (i : Fin n) (j : ℕ) (hj : j % n = i.val) :
    l.bitB j = l.b i := by
  unfold bitB
  congr 1
  exact Fin.ext hj

theorem bitA_add_period [NeZero n] (l : Lbl n) (j q : ℕ) :
    l.bitA (j + 2 * n * q) = l.bitA j := by
  have h : (j + 2 * n * q) % (2 * n) = j % (2 * n) := Nat.add_mul_mod_self_left j (2 * n) q
  unfold bitA
  simp only [h]

theorem bitA_lo [NeZero n] (l : Lbl n) (i : Fin n) : l.bitA i.val = l.a i :=
  l.bitA_eq_a i i.val (Nat.mod_eq_of_lt (by have := i.isLt; omega))

theorem bitA_hi [NeZero n] (l : Lbl n) (i : Fin n) : l.bitA (i.val + n) = l.c i :=
  l.bitA_eq_c i (i.val + n) (Nat.mod_eq_of_lt (by have := i.isLt; omega))

theorem bitA_pair [NeZero n] (l : Lbl n) (i : Fin n) (j : ℕ) (hj : j % n = i.val) :
    (l.bitA j = l.a i ∧ l.bitA (j + n) = l.c i) ∨ (l.bitA j = l.c i ∧ l.bitA (j + n) = l.a i) := by
  have hn : 0 < n := NeZero.pos n
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 2 * n ∧ j = r + 2 * n * q :=
    ⟨j / (2 * n), j % (2 * n), Nat.mod_lt _ (by omega), (Nat.mod_add_div j (2 * n)).symm⟩
  have hmod : (r + 2 * n * q) % n = r % n := by
    rw [show 2 * n * q = n * (2 * q) by ring]
    exact Nat.add_mul_mod_self_left r n (2 * q)
  rw [l.bitA_add_period r q, show r + 2 * n * q + n = (r + n) + 2 * n * q by ring,
    l.bitA_add_period (r + n) q]
  rcases lt_or_ge r n with hrn | hrn
  · have hi : i = ⟨r, hrn⟩ := Fin.ext (by
      show i.val = r
      rw [← hj, hmod, Nat.mod_eq_of_lt hrn])
    subst hi
    left
    exact ⟨l.bitA_eq_a ⟨r, hrn⟩ r (Nat.mod_eq_of_lt hr),
      l.bitA_eq_c ⟨r, hrn⟩ (r + n) (Nat.mod_eq_of_lt (by omega))⟩
  · have hi : i.val = r - n := by
      rw [← hj, hmod, Nat.mod_eq_sub_mod hrn, Nat.mod_eq_of_lt (show r - n < n by omega)]
    right
    refine ⟨l.bitA_eq_c i r (by rw [Nat.mod_eq_of_lt hr]; omega), ?_⟩
    rw [show r + n = (r - n) + 2 * n * 1 by omega, l.bitA_add_period (r - n) 1]
    exact l.bitA_eq_a i (r - n) (by rw [hi]; exact Nat.mod_eq_of_lt (show r - n < 2 * n by omega))

theorem zeroAt_iff [NeZero n] (l : Lbl n) (i : Fin n) (j : ℕ) (hj : j % n = i.val) :
    l.ZeroAt i ↔ (l.bitA j = false ∧ l.bitA (j + n) = false ∧ l.bitB j = false) := by
  rw [l.bitB_eq i j hj]
  unfold ZeroAt
  rcases l.bitA_pair i j hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

end Lbl

theorem locM_ge_four : ∀ x y z : Bool, ¬ (x = false ∧ y = false ∧ z = false) →
    4 ≤ locM x y z := by
  decide

theorem locM_ge_six : ∀ x y z : Bool, x = z → ¬ (x = false ∧ y = false ∧ z = false) →
    6 ≤ locM x y z := by
  decide

theorem locF1_le_two : ∀ x y z : Bool, locF1 x y z ≤ 2 := by
  decide

theorem locF1_le_locM : ∀ x y z : Bool, locF1 x y z ≤ locM x y z := by
  decide

theorem locM_mod_two : ∀ x y z : Bool, locM x y z % 2 = locF1 x y z % 2 := by
  decide

theorem four_pow_ge (k : ℕ) (hk : 3 ≤ k) : 12 * k + 2 ^ k ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    have h2k : 0 ≤ 2 ^ k := Nat.zero_le _
    linarith

theorem dvd_of_add_mod_eq' (p d m : ℕ) (hp : p < m) (h : (p + d) % m = p) : m ∣ d := by
  have h1 : (p + d) % m = p % m := by rw [h, Nat.mod_eq_of_lt hp]
  have h2 := Nat.sub_mod_eq_zero_of_mod_eq h1
  rw [Nat.add_sub_cancel_left] at h2
  exact Nat.dvd_of_mod_eq_zero h2

namespace Lbl

variable {n : ℕ}

theorem fix1_le_dim (l : Lbl n) : l.fix1 ≤ l.dim := by
  unfold fix1 dim
  exact Finset.prod_le_prod (fun i _ => locF1_le_locM _ _ _)

theorem dim_mod_two (l : Lbl n) : l.dim % 2 = l.fix1 % 2 := by
  unfold dim fix1
  rw [Finset.prod_nat_mod (Finset.univ) 2 (fun i => locM (l.a i) (l.b i) (l.c i)),
    Finset.prod_nat_mod (Finset.univ) 2 (fun i => locF1 (l.a i) (l.b i) (l.c i))]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => locM_mod_two _ _ _)

theorem two_mul_rk1 (l : Lbl n) : 2 * l.rk1 = l.dim - l.fix1 := by
  have h1 := l.fix1_le_dim
  have h2 := l.dim_mod_two
  unfold rk1
  omega

theorem dim_sub_fix1_mod_two (l : Lbl n) : (l.dim - l.fix1) % 2 = 0 := by
  have h1 := l.fix1_le_dim
  have h2 := l.dim_mod_two
  omega

theorem dim_ge_pow (l : Lbl n) (P : Finset (Fin n)) (hP : ∀ i, i ∈ P ↔ ¬ l.ZeroAt i)
    (c : ℕ) (hc : ∀ i ∈ P, c ≤ locM (l.a i) (l.b i) (l.c i)) : c ^ P.card ≤ l.dim := by
  classical
  have hprod : ∏ i : Fin n, (if i ∈ P then c else 1) = c ^ P.card := by
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [← hprod]
  unfold dim
  refine Finset.prod_le_prod (fun i _ => ?_)
  by_cases hi : i ∈ P
  · rw [if_pos hi]
    exact hc i hi
  · rw [if_neg hi]
    have hz : l.ZeroAt i := by
      by_contra h
      exact hi ((hP i).2 h)
    obtain ⟨h1, h2, h3⟩ := hz
    simp [h1, h2, h3, locM]

theorem fix1_le_pow (l : Lbl n) (P : Finset (Fin n)) (hP : ∀ i, i ∈ P ↔ ¬ l.ZeroAt i)
    (e : ℕ) (hc : ∀ i ∈ P, locF1 (l.a i) (l.b i) (l.c i) ≤ e) : l.fix1 ≤ e ^ P.card := by
  classical
  have hprod : ∏ i : Fin n, (if i ∈ P then e else 1) = e ^ P.card := by
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [← hprod]
  unfold fix1
  refine Finset.prod_le_prod (fun i _ => ?_)
  by_cases hi : i ∈ P
  · rw [if_pos hi]
    exact hc i hi
  · rw [if_neg hi]
    have hz : l.ZeroAt i := by
      by_contra h
      exact hi ((hP i).2 h)
    obtain ⟨h1, h2, h3⟩ := hz
    simp [h1, h2, h3, locF1]

theorem orbit_nz [NeZero n] (l : Lbl n) {d : ℕ} (hinv : l.RotInv d) (i₀ : Fin n)
    (hi₀ : ¬ l.ZeroAt i₀) (t : ℕ) :
    ¬ l.ZeroAt ⟨(i₀.val + t * d) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
  have hstep : ∀ j : ℕ,
      (l.bitA (j + d) = false ∧ l.bitA (j + d + n) = false ∧ l.bitB (j + d) = false) ↔
        (l.bitA j = false ∧ l.bitA (j + n) = false ∧ l.bitB j = false) := by
    intro j
    have h1 := (hinv j).1
    have h2 := (hinv (j + n)).1
    have h3 := (hinv j).2
    rw [show j + d + n = j + n + d by ring, h1, h2, h3]
  have hbase : ¬ (l.bitA i₀.val = false ∧ l.bitA (i₀.val + n) = false ∧
      l.bitB i₀.val = false) := by
    rw [← l.zeroAt_iff i₀ i₀.val (Nat.mod_eq_of_lt i₀.isLt)]
    exact hi₀
  have hgen : ∀ t : ℕ, ¬ (l.bitA (i₀.val + t * d) = false ∧
      l.bitA (i₀.val + t * d + n) = false ∧ l.bitB (i₀.val + t * d) = false) := by
    intro t
    induction t with
    | zero => simpa using hbase
    | succ t ih =>
      rw [show i₀.val + (t + 1) * d = i₀.val + t * d + d by ring, hstep]
      exact ih
  intro hz
  exact hgen t ((l.zeroAt_iff ⟨(i₀.val + t * d) % n, Nat.mod_lt _ (NeZero.pos n)⟩
    (i₀.val + t * d) rfl).1 hz)

theorem singleN_bitA_true [NeZero n] (l : Lbl n) (i₀ : Fin n)
    (hz : ∀ i, i ≠ i₀ → l.ZeroAt i) (j : ℕ) (hj : l.bitA j = true) :
    (j % (2 * n) = i₀.val ∧ l.a i₀ = true) ∨ (j % (2 * n) = i₀.val + n ∧ l.c i₀ = true) := by
  have hn : 0 < n := NeZero.pos n
  rcases lt_or_ge (j % (2 * n)) n with h | h
  · rw [l.bitA_eq_a ⟨j % (2 * n), h⟩ j rfl] at hj
    by_cases hr : (⟨j % (2 * n), h⟩ : Fin n) = i₀
    · exact Or.inl ⟨congrArg Fin.val hr, by rw [← hr]; exact hj⟩
    · exfalso
      obtain ⟨h1, -, -⟩ := hz _ hr
      rw [h1] at hj
      exact Bool.false_ne_true hj
  · obtain ⟨i₁, hi₁⟩ : ∃ i₁ : Fin n, i₁.val = j % (2 * n) - n :=
      ⟨⟨j % (2 * n) - n, by have := Nat.mod_lt j (show 2 * n > 0 by omega); omega⟩, rfl⟩
    rw [l.bitA_eq_c i₁ j (by omega)] at hj
    by_cases hr : i₁ = i₀
    · have hv : i₀.val = j % (2 * n) - n := by rw [← hr]; exact hi₁
      exact Or.inr ⟨by omega, by rw [← hr]; exact hj⟩
    · exfalso
      obtain ⟨-, -, h3⟩ := hz _ hr
      rw [h3] at hj
      exact Bool.false_ne_true hj

theorem SingleN.two_mul_dvd [NeZero n] {l : Lbl n} (hl : l.SingleN) {d : ℕ}
    (hinv : l.RotInv d) : 2 * n ∣ d := by
  obtain ⟨i₀, hz, -, hac⟩ := hl
  have hi₀ := i₀.isLt
  rcases hac with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · have hp : l.bitA i₀.val = true := by rw [l.bitA_lo i₀]; exact ha
    have h1 : l.bitA (i₀.val + d) = true := by rw [(hinv i₀.val).1]; exact hp
    rcases singleN_bitA_true l i₀ hz _ h1 with ⟨h2, -⟩ | ⟨-, h3⟩
    · exact dvd_of_add_mod_eq' _ d _ (by omega) h2
    · rw [hc] at h3
      exact absurd h3 (by decide)
  · have hp : l.bitA (i₀.val + n) = true := by rw [l.bitA_hi i₀]; exact hc
    have h1 : l.bitA (i₀.val + n + d) = true := by rw [(hinv (i₀.val + n)).1]; exact hp
    rcases singleN_bitA_true l i₀ hz _ h1 with ⟨-, h2⟩ | ⟨h3, -⟩
    · rw [ha] at h2
      exact absurd h2 (by decide)
    · exact dvd_of_add_mod_eq' _ d _ (by omega) h3

theorem SingleO.dvd [NeZero n] {l : Lbl n} (hl : l.SingleO) {d : ℕ}
    (hinv : l.RotInv d) : n ∣ d := by
  obtain ⟨i₀, hz, -, hb, -⟩ := hl
  have hbit : ∀ j : ℕ, l.bitB j = true → j % n = i₀.val := by
    intro j hj
    by_contra hne
    have hne' : (⟨j % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) ≠ i₀ :=
      fun h => hne (congrArg Fin.val h)
    obtain ⟨-, h2, -⟩ := hz _ hne'
    unfold bitB at hj
    rw [h2] at hj
    exact Bool.false_ne_true hj
  have h1 : l.bitB (i₀.val + d) = true := by
    rw [(hinv i₀.val).2, l.bitB_eq i₀ i₀.val (Nat.mod_eq_of_lt i₀.isLt)]
    exact hb
  exact dvd_of_add_mod_eq' _ d _ i₀.isLt (hbit _ h1)

theorem a_eq_c_of_two_mul [NeZero n] (l : Lbl n) {d : ℕ} (hinv : l.RotInv d) (h2 : n ∣ 2 * d)
    (hnd : ¬ n ∣ d) (i : Fin n) : l.a i = l.c i := by
  obtain ⟨m, hm⟩ := h2
  have hpar : ∀ j : ℕ, l.bitA (j + 2 * d) = l.bitA j := by
    intro j
    rw [show j + 2 * d = (j + d) + d by ring, (hinv (j + d)).1, (hinv j).1]
  rcases Nat.even_or_odd m with ⟨q, hq⟩ | ⟨q, hq⟩
  · exfalso
    apply hnd
    refine ⟨q, ?_⟩
    have h3 : 2 * d = 2 * (n * q) := by rw [hm, hq]; ring
    omega
  · have hd2 : 2 * d = n + 2 * n * q := by rw [hm, hq]; ring
    have hper : ∀ j : ℕ, l.bitA (j + n) = l.bitA j := by
      intro j
      have e1 : l.bitA (j + 2 * d) = l.bitA (j + n) := by
        rw [show j + 2 * d = (j + n) + 2 * n * q by omega]
        exact l.bitA_add_period (j + n) q
      rw [← e1, hpar j]
    rw [← l.bitA_lo i, ← l.bitA_hi i, hper]

end Lbl

theorem exists_orbit_card {n : ℕ} [NeZero n] (P : Finset (Fin n)) {d : ℕ}
    (i₀ : Fin n)
    (hP : ∀ t : ℕ, (⟨(i₀.val + t * d) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) ∈ P) :
    ∃ y : ℕ, 0 < y ∧ y ≤ P.card ∧ n ∣ y * d := by
  have hex : ∃ t : ℕ, 0 < t ∧ n ∣ t * d := ⟨n, NeZero.pos n, dvd_mul_right n d⟩
  obtain ⟨y, hy⟩ : ∃ y, Nat.find hex = y := ⟨_, rfl⟩
  have hspec := Nat.find_spec hex
  rw [hy] at hspec
  have hmin : ∀ t, t < y → ¬ (0 < t ∧ n ∣ t * d) := fun t ht => by
    rw [← hy] at ht
    exact Nat.find_min hex ht
  refine ⟨y, hspec.1, ?_, hspec.2⟩
  have key : ∀ s t : ℕ, s < t → t < y → (i₀.val + s * d) % n ≠ (i₀.val + t * d) % n := by
    intro s t hst hty hcon
    apply hmin (t - s) (by omega)
    refine ⟨by omega, ?_⟩
    have hmod : s * d ≡ t * d [MOD n] := Nat.ModEq.add_left_cancel' i₀.val hcon
    have hle : s * d ≤ t * d := Nat.mul_le_mul_right d hst.le
    have hdvd := (Nat.modEq_iff_dvd' hle).1 hmod
    rwa [← Nat.sub_mul] at hdvd
  have hinj : Set.InjOn
      (fun t : ℕ => (⟨(i₀.val + t * d) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n))
      (Finset.range y : Set ℕ) := by
    intro s hs t ht hst
    have hs' : s < y := Finset.mem_range.1 hs
    have ht' : t < y := Finset.mem_range.1 ht
    have hv : (i₀.val + s * d) % n = (i₀.val + t * d) % n := congrArg Fin.val hst
    rcases lt_trichotomy s t with h | h | h
    · exact absurd hv (key s t h ht')
    · exact h
    · exact absurd hv.symm (key t s h hs')
  have hcard := Finset.card_le_card_of_injOn
    (fun t : ℕ => (⟨(i₀.val + t * d) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n))
    (by intro t _; exact hP t) hinj
  simpa using hcard

theorem case_one {n : ℕ} [NeZero n] (l : Lbl n) {d : ℕ} (hd : 0 < d) (i₀ : Fin n)
    (hz : ∀ i, i ≠ i₀ → l.ZeroAt i) (hnz : ¬ l.ZeroAt i₀) (hdvd : n ∣ d) :
    l.SingleN ∨ l.SingleO ∨ 6 * n ≤ d * l.rk1 := by
  have hdim : l.dim = locM (l.a i₀) (l.b i₀) (l.c i₀) := by
    unfold Lbl.dim
    apply Finset.prod_eq_single i₀
    · intro i _ hne
      obtain ⟨h1, h2, h3⟩ := hz i hne
      simp [h1, h2, h3, locM]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hfix : l.fix1 = locF1 (l.a i₀) (l.b i₀) (l.c i₀) := by
    unfold Lbl.fix1
    apply Finset.prod_eq_single i₀
    · intro i _ hne
      obtain ⟨h1, h2, h3⟩ := hz i hne
      simp [h1, h2, h3, locF1]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hn : n ≤ d := Nat.le_of_dvd hd hdvd
  obtain ⟨x, hx⟩ : ∃ x, l.a i₀ = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, l.b i₀ = y := ⟨_, rfl⟩
  obtain ⟨z, hz2⟩ : ∃ z, l.c i₀ = z := ⟨_, rfl⟩
  rw [hx, hy, hz2] at hdim hfix
  cases x <;> cases y <;> cases z
  · exact (hnz (by unfold Lbl.ZeroAt; exact ⟨hx, hy, hz2⟩)).elim
  · exact Or.inl ⟨i₀, hz, hy, Or.inr ⟨hx, hz2⟩⟩
  · exact Or.inr (Or.inl ⟨i₀, hz, hx, hy, hz2⟩)
  · have h9 : l.rk1 = 9 := by
      unfold Lbl.rk1
      rw [hdim, hfix] <;> decide
    right; right
    rw [h9]
    omega
  · exact Or.inl ⟨i₀, hz, hy, Or.inl ⟨hx, hz2⟩⟩
  · have h6 : l.rk1 = 6 := by
      unfold Lbl.rk1
      rw [hdim, hfix] <;> decide
    right; right
    rw [h6]
    omega
  · have h9 : l.rk1 = 9 := by
      unfold Lbl.rk1
      rw [hdim, hfix] <;> decide
    right; right
    rw [h9]
    omega
  · have h32 : l.rk1 = 32 := by
      unfold Lbl.rk1
      rw [hdim, hfix] <;> decide
    right; right
    rw [h32]
    omega

theorem Lbl.comb_lemma75 {n : ℕ} [NeZero n] (l : Lbl n) (hl : ¬ l.IsZero) {d : ℕ} (hd : 0 < d)
    (hinv : l.RotInv d) : l.SingleN ∨ l.SingleO ∨ 6 * n ≤ d * l.rk1 := by
  classical
  obtain ⟨P, hPmem⟩ : ∃ P : Finset (Fin n), ∀ i, i ∈ P ↔ ¬ l.ZeroAt i :=
    ⟨Finset.univ.filter (fun i => ¬ l.ZeroAt i), fun i => by simp⟩
  obtain ⟨i₁, hi₁⟩ : ∃ i, ¬ l.ZeroAt i := by
    by_contra h
    push Not at h
    exact hl h
  have hk : 0 < P.card := Finset.card_pos.2 ⟨i₁, (hPmem i₁).2 hi₁⟩
  obtain ⟨y, hy0, hyk, hydvd⟩ := exists_orbit_card P i₁
    (fun t => (hPmem _).2 (Lbl.orbit_nz l hinv i₁ hi₁ t))
  have hyle : n ≤ y * d := Nat.le_of_dvd (Nat.mul_pos hy0 hd) hydvd
  rcases (show P.card = 1 ∨ P.card = 2 ∨ 3 ≤ P.card by omega) with h1 | h2 | h3
  · obtain ⟨i₀, hP1⟩ := Finset.card_eq_one.1 h1
    have hmem : ∀ i, i ∈ P ↔ i = i₀ := fun i => by rw [hP1, Finset.mem_singleton]
    have hz : ∀ i, i ≠ i₀ → l.ZeroAt i := fun i hne => by
      by_contra h
      exact hne ((hmem i).1 ((hPmem i).2 h))
    have hnz : ¬ l.ZeroAt i₀ := (hPmem i₀).1 ((hmem i₀).2 rfl)
    have hy1 : y = 1 := by omega
    rw [hy1, one_mul] at hydvd
    exact case_one l hd i₀ hz hnz hydvd
  · by_cases hnd : n ∣ d
    · have hD : 4 ^ P.card ≤ l.dim :=
        dim_ge_pow l P hPmem 4 (fun i hi => locM_ge_four _ _ _ ((hPmem i).1 hi))
      have hF : l.fix1 ≤ 2 ^ P.card :=
        fix1_le_pow l P hPmem 2 (fun i _ => locF1_le_two _ _ _)
      rw [h2] at hD hF
      have hrk : 6 ≤ l.rk1 := by
        unfold Lbl.rk1
        norm_num at hD hF
        omega
      have hnd' : n ≤ d := Nat.le_of_dvd hd hnd
      right; right
      have := Nat.mul_le_mul hnd' hrk
      linarith
    · have hy2 : y = 2 := by
        rcases (show y = 1 ∨ y = 2 by omega) with e | e
        · rw [e, one_mul] at hydvd
          exact absurd hydvd hnd
        · exact e
      rw [hy2] at hydvd
      have hac : ∀ i : Fin n, l.a i = l.c i := fun i =>
        Lbl.a_eq_c_of_two_mul l hinv hydvd hnd i
      have hD : 6 ^ P.card ≤ l.dim :=
        dim_ge_pow l P hPmem 6 (fun i hi => locM_ge_six _ _ _ (hac i) ((hPmem i).1 hi))
      have hF : l.fix1 ≤ 2 ^ P.card :=
        fix1_le_pow l P hPmem 2 (fun i _ => locF1_le_two _ _ _)
      rw [h2] at hD hF
      have hrk : 16 ≤ l.rk1 := by
        unfold Lbl.rk1
        norm_num at hD hF
        omega
      have hn2 : n ≤ 2 * d := Nat.le_of_dvd (by omega) hydvd
      right; right
      have := Nat.mul_le_mul_left d hrk
      linarith
  · right; right
    have hD : 4 ^ P.card ≤ l.dim :=
      dim_ge_pow l P hPmem 4 (fun i hi => locM_ge_four _ _ _ ((hPmem i).1 hi))
    have hF : l.fix1 ≤ 2 ^ P.card :=
      fix1_le_pow l P hPmem 2 (fun i _ => locF1_le_two _ _ _)
    have hpow := four_pow_ge P.card h3
    have hrk : 6 * P.card ≤ l.rk1 := by
      unfold Lbl.rk1
      generalize 4 ^ P.card = A at hD hpow
      generalize 2 ^ P.card = B at hF hpow
      omega
    have h4 := Nat.mul_le_mul_left d hrk
    have h5 := Nat.mul_le_mul_right d hyk
    linarith

end CFSG.HardMathSupport.U4FF
