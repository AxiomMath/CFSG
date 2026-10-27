module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL36HomA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLinAlg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Stmt

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal FzL59BLin

variable {G : Type} [Group G] {t s lam rho u : G} {b : Fin 3 → Fin 2 → G}

theorem fzl59b_q8Hom_commute {p q p' q' : G} (hp : IsQ8Pair p q) (hp' : IsQ8Pair p' q')
    (hpp : Commute p p') (hpq : Commute p q') (hqp : Commute q p') (hqq : Commute q q') :
    ∀ x y : Q, Commute (q8Hom hp x) (q8Hom hp' y) := by
  intro x y
  cases x with
  | a i =>
    cases y with
    | a j => exact (hpp.pow_left i.val).pow_right j.val
    | xa j =>
      exact ((hpq.pow_left i.val)).mul_right ((hpp.pow_left i.val).pow_right j.val)
  | xa i =>
    cases y with
    | a j => exact ((hqp.pow_right j.val)).mul_left ((hpp.pow_right j.val).pow_left i.val)
    | xa j =>
      exact (hqq.mul_right (hqp.pow_right j.val)).mul_left
        ((hpq.pow_left i.val).mul_right ((hpp.pow_left i.val).pow_right j.val))

theorem fzl59b_comm (hg : Fz59Grid t s lam rho b) {i j : Fin 3} (hij : i ≠ j) :
    ∀ x y : Q, Commute (q8Hom (hg.quat i) x) (q8Hom (hg.quat j) y) :=
  fzl59b_q8Hom_commute (hg.quat i) (hg.quat j) (hg.comm i j hij 0 0) (hg.comm i j hij 0 1)
    (hg.comm i j hij 1 0) (hg.comm i j hij 1 1)

@[expose] def fzl59bFn (hg : Fz59Grid t s lam rho b) : N →* G :=
  (q8Hom (hg.quat 0)).noncommCoprod
    ((q8Hom (hg.quat 1)).noncommCoprod (q8Hom (hg.quat 2)) (fzl59b_comm hg (by decide)))
    (fun x yz => (fzl59b_comm hg (by decide) x yz.1).mul_right
      (fzl59b_comm hg (by decide) x yz.2))

theorem fzl59bFn_apply (hg : Fz59Grid t s lam rho b) (a c d : Q) :
    fzl59bFn hg (a, c, d) =
      q8Hom (hg.quat 0) a * (q8Hom (hg.quat 1) c * q8Hom (hg.quat 2) d) := rfl

@[expose] def single3Hom : Fin 3 → Q →* N
  | 0 => MonoidHom.inl Q (Q × Q)
  | 1 => (MonoidHom.inr Q (Q × Q)).comp (MonoidHom.inl Q Q)
  | 2 => (MonoidHom.inr Q (Q × Q)).comp (MonoidHom.inr Q Q)

@[expose] def gq (k : Fin 2) : Q := if k = 0 then QuaternionGroup.a 1 else QuaternionGroup.xa 0

@[expose] def gen3 (i : Fin 3) (k : Fin 2) : N := single3Hom i (gq k)

theorem fzl59bFn_single (hg : Fz59Grid t s lam rho b) (i : Fin 3) (q : Q) :
    fzl59bFn hg (single3Hom i q) = q8Hom (hg.quat i) q := by
  match i with
  | 0 =>
    show fzl59bFn hg (q, 1, 1) = _
    rw [fzl59bFn_apply, map_one, map_one, mul_one, mul_one]
  | 1 =>
    show fzl59bFn hg (1, q, 1) = _
    rw [fzl59bFn_apply, map_one, map_one, one_mul, mul_one]
  | 2 =>
    show fzl59bFn hg (1, 1, q) = _
    rw [fzl59bFn_apply, map_one, map_one, one_mul, one_mul]

theorem fzl59bFn_gen (hg : Fz59Grid t s lam rho b) (i : Fin 3) (k : Fin 2) :
    fzl59bFn hg (gen3 i k) = b i k := by
  rw [gen3, fzl59bFn_single]
  fin_cases k <;> simp [gq]

theorem fzl59b_hom_ext_Q {H : Type*} [Group H] {f g : Q →* H}
    (h1 : f (QuaternionGroup.a 1) = g (QuaternionGroup.a 1))
    (h2 : f (QuaternionGroup.xa 0) = g (QuaternionGroup.xa 0)) : f = g := by
  refine MonoidHom.ext fun q => ?_
  rcases q with j | j
  · have : (QuaternionGroup.a j : Q) = (QuaternionGroup.a 1) ^ j.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [this, map_pow, map_pow, h1]
  · have : (QuaternionGroup.xa j : Q) = QuaternionGroup.xa 0 * (QuaternionGroup.a 1) ^ j.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a, zero_add]
    rw [this, map_mul, map_mul, map_pow, map_pow, h1, h2]

theorem fzl59b_hom_ext_N {H : Type*} [Group H] {f g : N →* H}
    (h : ∀ i k, f (gen3 i k) = g (gen3 i k)) : f = g := by
  have hQ : ∀ i, f.comp (single3Hom i) = g.comp (single3Hom i) := fun i =>
    fzl59b_hom_ext_Q (by simpa [gen3, gq] using h i 0) (by simpa [gen3, gq] using h i 1)
  refine MonoidHom.ext fun n => ?_
  obtain ⟨n0, n1, n2⟩ := n
  have hn : ((n0, n1, n2) : N) = single3Hom 0 n0 * single3Hom 1 n1 * single3Hom 2 n2 := by
    ext <;> simp [single3Hom]
  rw [hn, map_mul, map_mul, map_mul, map_mul]
  have h0 := DFunLike.congr_fun (hQ 0) n0
  have h1 := DFunLike.congr_fun (hQ 1) n1
  have h2 := DFunLike.congr_fun (hQ 2) n2
  simp only [MonoidHom.comp_apply] at h0 h1 h2
  rw [h0, h1, h2]

@[expose] def swapRow (i : Fin 3) : Fin 3 := if i = 0 then 1 else if i = 1 then 0 else 2

private theorem fzl59b_conj_conj {g a c : G} (h : g * a * g⁻¹ = c) (hg : g ^ 2 = 1) :
    g * c * g⁻¹ = a := by
  have hg' : g * g = 1 := by rw [← pow_two]; exact hg
  rw [← h]
  calc g * (g * a * g⁻¹) * g⁻¹ = (g * g) * a * (g⁻¹ * g⁻¹) := by group
    _ = a := by rw [hg', ← mul_inv_rev, hg', inv_one]; group

theorem fzl59b_hy (hg : Fz59Grid t s lam rho b) (n : N) :
    lam * fzl59bFn hg n * lam⁻¹ = fzl59bFn hg (xiN n) := by
  have h0 : ∀ (i : Fin 3) (k : Fin 2), lam * b i k * lam⁻¹ = b (swapRow i) k := by
    intro i k
    fin_cases i
    · exact hg.lam_01 k
    · exact fzl59b_conj_conj (hg.lam_01 k) hg.lam_sq
    · exact hg.lam_2 k
  have hx : ∀ (i : Fin 3) (k : Fin 2), xiN (gen3 i k) = gen3 (swapRow i) k := by decide
  have key : (MulAut.conj lam).toMonoidHom.comp (fzl59bFn hg) = (fzl59bFn hg).comp xiN := by
    refine fzl59b_hom_ext_N fun i k => ?_
    simp only [MonoidHom.comp_apply, fzl59bFn_gen, hx]
    exact h0 i k
  have := DFunLike.congr_fun key n
  simpa using this

theorem fzl59b_q8Hom_xa_two {p q : G} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.xa 2) = q * p ^ 2 := by
  change q * zmod4Pow p 2 = q * p ^ 2
  unfold zmod4Pow
  congr 2

theorem fzl59b_q8Hom_xa_three {p q : G} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.xa 3) = q * p ^ 3 := by
  change q * zmod4Pow p 3 = q * p ^ 3
  unfold zmod4Pow
  congr 2

theorem fzl59b_pq {p q : G} (h : IsQ8Pair p q) : p * q = q * p ^ 3 := by
  calc p * q = p⁻¹ * (p ^ 2 * q) := by group
    _ = p⁻¹ * (q * p ^ 2) := by rw [h.mul_comm_sq]
    _ = p⁻¹ * q * p ^ 2 := by group
    _ = q * p * p ^ 2 := by rw [h.q_mul_p]
    _ = q * p ^ 3 := by group

theorem fzl59b_hu_good (hg : Fz59Grid t s lam rho b) (hu : Fz59UGood t s lam rho u b) (n : N) :
    u * fzl59bFn hg n * u⁻¹ = fzl59bFn hg (psiN true n) := by
  have hp0 : ∀ i : Fin 3, psiN true (gen3 i 0) =
      single3Hom i (QuaternionGroup.xa 3) * single3Hom (i - 1) (QuaternionGroup.a 2) := by
    decide +kernel
  have hp1 : ∀ i : Fin 3, psiN true (gen3 i 1) = single3Hom i (QuaternionGroup.xa 2) := by
    decide +kernel
  have h0 : ∀ i : Fin 3, u * b i 0 * u⁻¹ = fzl59bFn hg (psiN true (gen3 i 0)) := by
    intro i
    rw [hu.b0 i, hp0 i, map_mul, fzl59bFn_single, fzl59bFn_single, fzl59b_q8Hom_xa_three,
      fzl_q8Hom_a_two, fzl59b_pq (hg.quat i)]
  have h1 : ∀ i : Fin 3, u * b i 1 * u⁻¹ = fzl59bFn hg (psiN true (gen3 i 1)) := by
    intro i
    rw [hu.b1 i, hp1 i, fzl59bFn_single, fzl59b_q8Hom_xa_two, (hg.quat i).q_inv_eq]
  have key : (MulAut.conj u).toMonoidHom.comp (fzl59bFn hg) =
      (fzl59bFn hg).comp (psiN true) := by
    refine fzl59b_hom_ext_N fun i k => ?_
    simp only [MonoidHom.comp_apply, fzl59bFn_gen]
    fin_cases k
    · exact h0 i
    · exact h1 i
  have := DFunLike.congr_fun key n
  simpa using this

theorem fzl59b_hu_bad (hg : Fz59Grid t s lam rho b) (hu : Fz59UBad t s lam rho u b) (n : N) :
    u * fzl59bFn hg n * u⁻¹ = fzl59bFn hg (psiN false n) := by
  have hp0 : ∀ i : Fin 3, psiN false (gen3 i 0) = single3Hom i (QuaternionGroup.xa 3) := by
    decide +kernel
  have hp1 : ∀ i : Fin 3, psiN false (gen3 i 1) = single3Hom i (QuaternionGroup.xa 2) := by
    decide +kernel
  have h0 : ∀ i : Fin 3, u * b i 0 * u⁻¹ = fzl59bFn hg (psiN false (gen3 i 0)) := by
    intro i
    rw [hu.b0 i, hp0 i, fzl59bFn_single, fzl59b_q8Hom_xa_three, fzl59b_pq (hg.quat i)]
  have h1 : ∀ i : Fin 3, u * b i 1 * u⁻¹ = fzl59bFn hg (psiN false (gen3 i 1)) := by
    intro i
    rw [hu.b1 i, hp1 i, fzl59bFn_single, fzl59b_q8Hom_xa_two, (hg.quat i).q_inv_eq]
  have key : (MulAut.conj u).toMonoidHom.comp (fzl59bFn hg) =
      (fzl59bFn hg).comp (psiN false) := by
    refine fzl59b_hom_ext_N fun i k => ?_
    simp only [MonoidHom.comp_apply, fzl59bFn_gen]
    fin_cases k
    · exact h0 i
    · exact h1 i
  have := DFunLike.congr_fun key n
  simpa using this

theorem fzl59bFn_zeta (hg : Fz59Grid t s lam rho b) : fzl59bFn hg zetaN = 1 := by
  have h : fzl59bFn hg zetaN = b 0 0 ^ 2 * (b 1 0 ^ 2 * b 2 0 ^ 2) := by
    show fzl59bFn hg (QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2) = _
    rw [fzl59bFn_apply, fzl_q8Hom_a_two, fzl_q8Hom_a_two, fzl_q8Hom_a_two]
  rw [h, hg.sq_eq]
  have hz0 : b 0 0 ^ 2 * b 0 0 ^ 2 = 1 := (hg.quat 0).sq_mul_sq
  have hz1 : b 1 0 ^ 2 * b 1 0 ^ 2 = 1 := (hg.quat 1).sq_mul_sq
  have hc : Commute (b 0 0 ^ 2) (b 1 0 ^ 2) :=
    ((hg.comm 0 1 (by decide) 0 0).pow_left 2).pow_right 2
  calc b 0 0 ^ 2 * (b 1 0 ^ 2 * (b 0 0 ^ 2 * b 1 0 ^ 2))
      = (b 0 0 ^ 2 * b 1 0 ^ 2) * (b 0 0 ^ 2 * b 1 0 ^ 2) := by group
    _ = (b 0 0 ^ 2 * b 1 0 ^ 2) ^ 2 := (pow_two _).symm
    _ = (b 0 0 ^ 2) ^ 2 * (b 1 0 ^ 2) ^ 2 := hc.mul_pow 2
    _ = 1 := by
      rw [pow_two (b 0 0 ^ 2), pow_two (b 1 0 ^ 2), hz0, hz1, mul_one]

theorem fzl59b_linData_good (hg : Fz59Grid t s lam rho b) (hu : Fz59UGood t s lam rho u b) :
    LinData true (fzl59bFn hg) lam u := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fzl59bFn_zeta hg⟩
  · rw [← pow_two]; exact hg.lam_sq
  · rw [← pow_two]; exact hu.sq
  · intro n
    exact (mul_inv_eq_iff_eq_mul.mp (fzl59b_hy hg n))
  · intro n
    exact (mul_inv_eq_iff_eq_mul.mp (fzl59b_hu_good hg hu n))
  · have hs : fzl59bFn hg (cN true) = s := by
      have e : cN true = gen3 0 1 * gen3 1 1 * gen3 2 1 := by decide +kernel
      rw [e, map_mul, map_mul, fzl59bFn_gen, fzl59bFn_gen, fzl59bFn_gen]
      exact hg.s_eq.symm
    rw [hs]
    calc lam * u = (lam * u * lam⁻¹ * u⁻¹) * (u * lam) := by group
      _ = s * (u * lam) := by rw [hu.lam_u]

theorem fzl59b_linData_bad (hg : Fz59Grid t s lam rho b) (hu : Fz59UBad t s lam rho u b) :
    LinData false (fzl59bFn hg) lam u := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fzl59bFn_zeta hg⟩
  · rw [← pow_two]; exact hg.lam_sq
  · rw [← pow_two]; exact hu.sq
  · intro n
    exact (mul_inv_eq_iff_eq_mul.mp (fzl59b_hy hg n))
  · intro n
    exact (mul_inv_eq_iff_eq_mul.mp (fzl59b_hu_bad hg hu n))
  · have h1 : fzl59bFn hg (cN false) = 1 := by
      show fzl59bFn hg 1 = 1
      exact map_one _
    rw [h1, one_mul]
    exact hu.lam_u

end CFSG.OddStandard.SmallF3.FritzII
