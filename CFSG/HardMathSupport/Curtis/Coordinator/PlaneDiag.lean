module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneAut
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

variable {K : Type*} [Field K]

@[expose] def diagElt (d : Fin 3 → K) (h : d 0 * d 1 * d 2 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal d, by rw [det_diagonal, Fin.prod_univ_three]; exact h⟩

@[simp] theorem coe_diagElt (d : Fin 3 → K) (h : d 0 * d 1 * d 2 = 1) :
    (diagElt d h : Matrix (Fin 3) (Fin 3) K) = diagonal d := rfl

@[expose] def elemElt (i j : Fin 3) (hij : i ≠ j) : SpecialLinearGroup (Fin 3) K :=
  ⟨transvection i j 1, by rw [det_transvection_of_ne i j hij]⟩

@[simp] theorem coe_elemElt (i j : Fin 3) (hij : i ≠ j) :
    ((elemElt (K := K) i j hij : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      transvection i j 1 := rfl

theorem elemElt_comm_diagElt (i j : Fin 3) (hij : i ≠ j) (d : Fin 3 → K)
    (h : d 0 * d 1 * d 2 = 1) (hd : d i = d j) :
    elemElt i j hij * diagElt d h = diagElt d h * elemElt i j hij := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, coe_elemElt, coe_diagElt]
  ext x y
  rw [transvection, Matrix.add_mul, Matrix.mul_add]
  simp [Matrix.add_apply, Matrix.mul_apply, diagonal_apply]
  rw [Matrix.single_apply]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    simp [hd]
  · simp

theorem false_aux (c : K) (h1 : c = 1) (h2 : (1 + 1) * c = 1) : False :=
  one_ne_zero (by rw [h1] at h2; linear_combination h2)

theorem transv_ne (i j : Fin 3) (hij : i ≠ j) (c : K) :
    transvection j i (1 : K) * transvection i j 1 ≠
      (transvection i j 1 * transvection j i 1) * scalar (Fin 3) c := by
  intro h
  have h1 := congrFun (congrFun h i) j
  have h2 := congrFun (congrFun h i) i
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [transvection, Matrix.mul_apply, Matrix.single_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.add_mul,
      Matrix.mul_add] at h1 h2 <;>
    exact false_aux c h1.symm h2.symm

theorem proj_elem_not_comm (i j : Fin 3) (hij : i ≠ j) :
    proj 3 K (elemElt i j hij) * proj 3 K (elemElt j i hij.symm) ≠
      proj 3 K (elemElt j i hij.symm) * proj 3 K (elemElt i j hij) := by
  intro hq
  rw [← map_mul, ← map_mul, proj_eq_proj_iff] at hq
  obtain ⟨X, hX⟩ : ∃ X : SpecialLinearGroup (Fin 3) K,
      X = (elemElt (K := K) i j hij * elemElt j i hij.symm)⁻¹ *
        (elemElt (K := K) j i hij.symm * elemElt i j hij) := ⟨_, rfl⟩
  rw [← hX] at hq
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hq
  have hB : elemElt (K := K) j i hij.symm * elemElt i j hij =
      (elemElt (K := K) i j hij * elemElt j i hij.symm) * X := by rw [hX, mul_inv_cancel_left]
  have := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hB
  simp only [SpecialLinearGroup.coe_mul, hc, coe_elemElt] at this
  exact transv_ne i j hij (c : K) this

theorem nonabCent_proj_diagElt (i j : Fin 3) (hij : i ≠ j) (d : Fin 3 → K)
    (h : d 0 * d 1 * d 2 = 1) (hd : d i = d j) : NonabCent (proj 3 K (diagElt d h)) := by
  refine ⟨proj 3 K (elemElt i j hij), proj 3 K (elemElt j i hij.symm), ?_, ?_,
    proj_elem_not_comm i j hij⟩
  · rw [← map_mul, ← map_mul, elemElt_comm_diagElt i j hij d h hd]
  · rw [← map_mul, ← map_mul, elemElt_comm_diagElt j i hij.symm d h hd.symm]

theorem offDiag_eq_zero_of_proj_comm {p : ℕ} (hp3 : Nat.Coprime p 3) (d : Fin 3 → K)
    (h : d 0 * d 1 * d 2 = 1) (hpow : ∀ i, d i ^ p = 1) (hdist : ∀ i j, i ≠ j → d i ≠ d j)
    (g : SpecialLinearGroup (Fin 3) K)
    (hg : proj 3 K g * proj 3 K (diagElt d h) = proj 3 K (diagElt d h) * proj 3 K g) :
    ∀ x y, x ≠ y → (g : Matrix (Fin 3) (Fin 3) K) x y = 0 := by
  rw [← map_mul, ← map_mul, proj_eq_proj_iff] at hg
  obtain ⟨X, hX⟩ : ∃ X : SpecialLinearGroup (Fin 3) K,
      X = (g * diagElt d h)⁻¹ * (diagElt d h * g) := ⟨_, rfl⟩
  rw [← hX] at hg
  obtain ⟨c, hc3, hc⟩ := mem_scalars.mp hg
  have hB : diagElt d h * g = (g * diagElt d h) * X := by rw [hX, mul_inv_cancel_left]
  have hE := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hB
  simp only [SpecialLinearGroup.coe_mul, hc, coe_diagElt] at hE
  have hE' : ∀ x y, d x * (g : Matrix (Fin 3) (Fin 3) K) x y =
      (g : Matrix (Fin 3) (Fin 3) K) x y * d y * (c : K) := by
    intro x y
    have := congrFun (congrFun hE x) y
    simpa [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.scalar_apply, Matrix.mul_diagonal,
      Matrix.diagonal_apply] using this
  obtain ⟨x₀, y₀, hxy₀⟩ : ∃ x y, (g : Matrix (Fin 3) (Fin 3) K) x y ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : (g : Matrix (Fin 3) (Fin 3) K) = 0 := Matrix.ext fun x y => hall x y
    have := g.2
    rw [h0, Matrix.det_zero] at this
    exact zero_ne_one this
  have hdxy : d x₀ = d y₀ * c := by
    refine mul_right_cancel₀ hxy₀ ?_
    rw [hE' x₀ y₀]
    ring
  have hcp : (c : K) ^ p = 1 := by
    have h1 : d x₀ ^ p = d y₀ ^ p * (c : K) ^ p := by rw [hdxy, mul_pow]
    rw [hpow, hpow, one_mul] at h1
    exact h1.symm
  have hc3K : (c : K) ^ 3 = 1 := by
    have := congrArg Units.val hc3
    simpa using this
  have hc1 : (c : K) = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hcp, hc3K⟩
    rwa [hp3.gcd_eq_one, pow_one] at this
  intro x y hxy
  have := hE' x y
  rw [hc1, mul_one] at this
  have h2 : (d x - d y) * (g : Matrix (Fin 3) (Fin 3) K) x y = 0 := by linear_combination this
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (hdist x y hxy))

theorem not_nonabCent_proj_diagElt {p : ℕ} (hp3 : Nat.Coprime p 3) (d : Fin 3 → K)
    (h : d 0 * d 1 * d 2 = 1) (hpow : ∀ i, d i ^ p = 1) (hdist : ∀ i j, i ≠ j → d i ≠ d j) :
    ¬ NonabCent (proj 3 K (diagElt d h)) := by
  rintro ⟨a, b, ha, hb, hab⟩
  obtain ⟨ga, rfl⟩ := proj_surjective 3 K a
  obtain ⟨gb, rfl⟩ := proj_surjective 3 K b
  have hdiag : ∀ g : SpecialLinearGroup (Fin 3) K,
      proj 3 K g * proj 3 K (diagElt d h) = proj 3 K (diagElt d h) * proj 3 K g →
      (g : Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => (g : Matrix (Fin 3) (Fin 3) K) i i) := by
    intro g hg
    have := offDiag_eq_zero_of_proj_comm hp3 d h hpow hdist g hg
    refine Matrix.ext fun x y => ?_
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [diagonal_apply_ne _ hxy, this x y hxy]
  apply hab
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hdiag ga ha, hdiag gb hb,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  simp [mul_comm]

@[expose] def lineFun (i : Fin 3) (a : K) : Fin 3 → K := fun t => if t = i then (a * a)⁻¹ else a

theorem lineFun_prod (i : Fin 3) {a : K} (ha : a ≠ 0) :
    lineFun i a 0 * lineFun i a 1 * lineFun i a 2 = 1 := by
  fin_cases i <;> simp [lineFun] <;> field_simp

@[expose] def lineElt (i : Fin 3) (a : K) (ha : a ≠ 0) : SpecialLinearGroup (Fin 3) K :=
  diagElt (lineFun i a) (lineFun_prod i ha)

@[simp] theorem coe_lineElt (i : Fin 3) (a : K) (ha : a ≠ 0) :
    (lineElt i a ha : Matrix (Fin 3) (Fin 3) K) = diagonal (lineFun i a) := rfl

theorem lineFun_pow (i : Fin 3) (a : K) (m : ℕ) :
    lineFun i a ^ m = lineFun i (a ^ m) := by
  funext t
  simp only [lineFun, Pi.pow_apply]
  split_ifs <;> simp [inv_pow, mul_pow]

theorem lineElt_pow (i : Fin 3) {a : K} (ha : a ≠ 0) (m : ℕ) :
    lineElt i a ha ^ m = lineElt i (a ^ m) (pow_ne_zero m ha) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow]
  simp only [coe_lineElt, diagonal_pow, lineFun_pow]

theorem lineElt_eq_one (i : Fin 3) {a : K} (ha : a ≠ 0) (h : a = 1) : lineElt i a ha = 1 := by
  subst h
  apply Subtype.ext
  have : lineFun i (1 : K) = fun _ => 1 := by funext t; simp [lineFun]
  rw [coe_lineElt, this, SpecialLinearGroup.coe_one]
  exact diagonal_one

theorem lineElt_pow_eq_one (i : Fin 3) {a : K} (ha : a ≠ 0) {p : ℕ} (hp : a ^ p = 1) :
    lineElt i a ha ^ p = 1 := by
  rw [lineElt_pow]
  exact lineElt_eq_one i _ (by simpa using hp)

theorem exists_two_ne (i : Fin 3) : ∃ j j' : Fin 3, j ≠ j' ∧ j ≠ i ∧ j' ≠ i := by
  revert i; decide

theorem fin_cases_ne : ∀ i j : Fin 3, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨
    (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by decide

theorem exists_third (i j : Fin 3) (hij : i ≠ j) : ∃ k, k ≠ i ∧ k ≠ j := by
  revert i j; decide

theorem proj_lineElt_ne_one (i : Fin 3) {a : K} (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    proj 3 K (lineElt i a ha) ≠ 1 := by
  intro h
  rw [proj_eq_one_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  obtain ⟨k, hk⟩ := exists_ne i
  have h1 := congrFun (congrFun hc i) i
  have h2 := congrFun (congrFun hc k) k
  simp [lineFun, hk, Matrix.scalar_apply] at h1 h2
  apply ha3
  have h' : a⁻¹ * a⁻¹ = a := h1.trans h2.symm
  calc a ^ 3 = a * a * a := by ring
    _ = a * a * (a⁻¹ * a⁻¹) := by rw [h']
    _ = 1 := by field_simp

theorem cube_eq_one_of_proj_lineElt_eq {i j : Fin 3} (hij : i ≠ j) {s s' : K} (hs : s ≠ 0)
    (hs' : s' ≠ 0) (h : proj 3 K (lineElt i s hs) = proj 3 K (lineElt j s' hs')) : s ^ 3 = 1 := by
  rw [proj_eq_proj_iff] at h
  obtain ⟨X, hX⟩ : ∃ X : SpecialLinearGroup (Fin 3) K,
      X = (lineElt i s hs)⁻¹ * lineElt j s' hs' := ⟨_, rfl⟩
  rw [← hX] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  have hB : lineElt j s' hs' = lineElt i s hs * X := by rw [hX, mul_inv_cancel_left]
  have hE := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hB
  simp only [SpecialLinearGroup.coe_mul, hc, coe_lineElt] at hE
  obtain ⟨k, hki, hkj⟩ := exists_third i j hij
  have e1 := congrFun (congrFun hE k) k
  have e2 := congrFun (congrFun hE i) i
  simp [lineFun, hki, hkj, hij, Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    at e1 e2
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have h' : s * (c : K) = s⁻¹ * s⁻¹ * c := e1.symm.trans e2
  have h3 : s ^ 3 * (c : K) = c :=
    calc s ^ 3 * (c : K) = s * s * (s * c) := by ring
      _ = s * s * (s⁻¹ * s⁻¹ * c) := by rw [h']
      _ = c := by field_simp
  have : (c : K) * (s ^ 3 - 1) = 0 := by linear_combination h3
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0)

theorem exists_lineFun (d : Fin 3 → K) (h : d 0 * d 1 * d 2 = 1)
    (hcase : d 0 = d 1 ∨ d 0 = d 2 ∨ d 1 = d 2) :
    ∃ (k : Fin 3) (a : K), a ≠ 0 ∧ d = lineFun k a := by
  have hd0 : ∀ i, d i ≠ 0 := fun i h0 => by fin_cases i <;> simp_all
  rcases hcase with h01 | h02 | h12
  · refine ⟨2, d 0, hd0 0, ?_⟩
    have h2 : d 2 = (d 0 * d 0)⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← h, h01]
    funext t
    fin_cases t <;> simp [lineFun, h2, h01]
  · refine ⟨1, d 0, hd0 0, ?_⟩
    have h1 : d 1 = (d 0 * d 0)⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← h, h02]; ring
    funext t
    fin_cases t <;> simp [lineFun, h1, h02]
  · refine ⟨0, d 1, hd0 1, ?_⟩
    have h0 : d 0 = (d 1 * d 1)⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← h, h12]; ring
    funext t
    fin_cases t <;> simp [lineFun, h0, h12]

theorem mem_zpowers_iff_nat {G : Type*} [Group G] {x y : G} {p : ℕ} (hp : 0 < p) (hx : x ^ p = 1) :
    y ∈ Subgroup.zpowers x ↔ ∃ m : ℕ, x ^ m = y := by
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp, hx⟩
  rw [← hfin.mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]

theorem plane_diag_aut {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (Q : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hQd : ∀ g ∈ Q, ∃ d : Fin 3 → K, (∀ i, d i ^ p = 1) ∧
      (g : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hQf : ∀ d : Fin 3 → K, (∀ i, d i ^ p = 1) → d 0 * d 1 * d 2 = 1 →
      ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hEcard : Nat.card (Q.map (proj 3 K)) = p ^ 2)
    (α : MulAut (projectiveSL 3 K)) {k : ℕ} (hα : α ^ p ^ k = 1)
    (hαQ : ∀ e ∈ Q.map (proj 3 K), α e ∈ Q.map (proj 3 K)) :
    ∀ e ∈ Q.map (proj 3 K), α e = e := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have hp0 : 0 < p := hp.pos
  have hQd' : ∀ g ∈ Q, ∃ (d : Fin 3 → K) (h : d 0 * d 1 * d 2 = 1), (∀ i, d i ^ p = 1) ∧
      g = diagElt d h := by
    intro g hg
    obtain ⟨d, hd, hgd⟩ := hQd g hg
    have h : d 0 * d 1 * d 2 = 1 := by
      have := g.2
      rwa [hgd, det_diagonal, Fin.prod_univ_three] at this
    exact ⟨d, h, hd, Subtype.ext hgd⟩
  obtain ⟨r, hrp, hr1⟩ : ∃ r : K, r ^ p = 1 ∧ r ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Nat.card (Q.map (proj 3 K)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
      have key : ∀ x : ↥(Q.map (proj 3 K)), x = 1 := by
        rintro ⟨_, ⟨g, hg, rfl⟩⟩
        obtain ⟨d, h, hd, rfl⟩ := hQd' g hg
        have : diagElt d h = 1 := by
          apply Subtype.ext
          rw [coe_diagElt, SpecialLinearGroup.coe_one]
          have : d = fun _ => 1 := funext fun i => hno _ (hd i)
          rw [this, diagonal_one]
        apply Subtype.ext
        simp [this]
      exact (key a).trans (key b).symm
    have h2 : (1 : ℕ) < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hr0 : r ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp.ne_zero] at hrp
    exact zero_ne_one hrp
  have hr3 : r ^ 3 ≠ 1 := fun h3 => by
    have := pow_gcd_eq_one.mpr ⟨hrp, h3⟩
    rw [hp3.gcd_eq_one, pow_one] at this
    exact hr1 this
  have hrord : orderOf r = p := orderOf_eq_prime hrp hr1
  have hprim : IsPrimitiveRoot r p := IsPrimitiveRoot.iff_orderOf.mpr hrord
  have : NeZero p := ⟨hp.ne_zero⟩
  have hlineQ : ∀ (i : Fin 3) (a : K) (ha : a ≠ 0), a ^ p = 1 → lineElt i a ha ∈ Q := by
    intro i a ha hap
    obtain ⟨g, hg, hgd⟩ := hQf (lineFun i a) (fun t => by
      simp only [lineFun]; split_ifs <;> simp [inv_pow, mul_pow, hap]) (lineFun_prod i ha)
    have : g = lineElt i a ha := Subtype.ext hgd
    exact this ▸ hg
  have hlpow : ∀ (i : Fin 3), (proj 3 K (lineElt i r hr0)) ^ p = 1 := fun i => by
    rw [← map_pow, lineElt_pow_eq_one i hr0 hrp, map_one]
  have hlne : ∀ i : Fin 3, proj 3 K (lineElt i r hr0) ≠ 1 := fun i =>
    proj_lineElt_ne_one i hr0 hr3
  have hnat : ∀ (i : Fin 3) (y : projectiveSL 3 K),
      y ∈ Subgroup.zpowers (proj 3 K (lineElt i r hr0)) ↔
        ∃ m : ℕ, y = proj 3 K (lineElt i (r ^ m) (pow_ne_zero m hr0)) := by
    intro i y
    rw [mem_zpowers_iff_nat hp0 (hlpow i)]
    refine exists_congr fun m => ?_
    rw [← map_pow, lineElt_pow]
    exact eq_comm
  refine aut_eq_of_three_lines hp hp5 α hα (Q.map (proj 3 K))
    (fun i => Subgroup.zpowers (proj 3 K (lineElt i r hr0))) ?_ ?_ ?_ ?_ ?_ hαQ hEcard
  · intro i
    rw [Nat.card_zpowers, orderOf_eq_prime (hlpow i) (hlne i)]
  · intro i
    rw [Subgroup.zpowers_le]
    exact ⟨_, hlineQ i r hr0 hrp, rfl⟩
  · intro i j hij g hgi hgj
    obtain ⟨m, hm⟩ := (hnat i g).mp hgi
    obtain ⟨n, hn⟩ := (hnat j g).mp hgj
    have h3 := cube_eq_one_of_proj_lineElt_eq hij (pow_ne_zero m hr0) (pow_ne_zero n hr0)
      (hm.symm.trans hn)
    have h1 : (r ^ m) = 1 := by
      have hp' : (r ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hrp, one_pow]
      have := pow_gcd_eq_one.mpr ⟨hp', h3⟩
      rwa [hp3.gcd_eq_one, pow_one] at this
    rw [hm, lineElt_eq_one i _ h1, map_one]
  · intro i g hg hg1
    obtain ⟨m, rfl⟩ := (hnat i g).mp hg
    obtain ⟨j, j', hjj', hji, hji'⟩ := exists_two_ne i
    exact nonabCent_proj_diagElt j j' hjj' _ _ (by simp [lineFun, hji, hji'])
  · intro g hg hg1 hnon
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨d, h, hd, rfl⟩ := hQd' q hq
    have hcase : d 0 = d 1 ∨ d 0 = d 2 ∨ d 1 = d 2 := by
      by_contra hno
      push Not at hno
      obtain ⟨h01, h02, h12⟩ := hno
      refine not_nonabCent_proj_diagElt hp3 d h hd (fun i j hij => ?_) hnon
      rcases fin_cases_ne i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h01
      · exact h02
      · exact h01.symm
      · exact h12
      · exact h02.symm
      · exact h12.symm
    obtain ⟨kk, a, ha0, hda⟩ := exists_lineFun d h hcase
    obtain ⟨t, ht⟩ := exists_ne kk
    have hap : a ^ p = 1 := by
      have := hd t
      rw [hda] at this
      simpa [lineFun, ht] using this
    obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one hap
    subst hm
    subst hda
    exact ⟨kk, (hnat kk _).mpr ⟨m, rfl⟩⟩

end CFSG.HardMathSupport.Curtis.Coordinator.Plane
