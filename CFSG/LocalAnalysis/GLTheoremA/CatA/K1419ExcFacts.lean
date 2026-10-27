module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419CoverL3U3
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

section Heis

variable {H : Type} [Group H]

theorem conj_pow_of_heis {d p z : H} (hz : p * d * p⁻¹ = z * d) (hzc : z ∈ Subgroup.center H)
    (a : ℕ) : p * d ^ a * p⁻¹ = z ^ a * d ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hc : ∀ g : H, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hzc g
    calc p * d ^ (a + 1) * p⁻¹ = (p * d ^ a * p⁻¹) * (p * d * p⁻¹) := by group
      _ = z ^ a * d ^ a * (z * d) := by rw [ih, hz]
      _ = z ^ (a + 1) * d ^ (a + 1) := by
        rw [pow_succ, pow_succ]
        calc z ^ a * d ^ a * (z * d) = z ^ a * (d ^ a * z) * d := by group
          _ = z ^ a * (z * d ^ a) * d := by rw [hc (d ^ a)]
          _ = z ^ a * z * (d ^ a * d) := by group

theorem conj_pow_of_heis' {d p z : H} (hz : p * d * p⁻¹ = z * d) (hzc : z ∈ Subgroup.center H)
    (b : ℕ) : d * p ^ b * d⁻¹ = z⁻¹ ^ b * p ^ b := by
  have hc : ∀ g : H, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hzc g
  have hpd : p * d = z * d * p := by
    calc p * d = (p * d * p⁻¹) * p := by group
      _ = z * d * p := by rw [hz]
  have h1 : d * p * d⁻¹ = z⁻¹ * p := by
    calc d * p * d⁻¹ = z⁻¹ * (z * d * p) * d⁻¹ := by group
      _ = z⁻¹ * (p * d) * d⁻¹ := by rw [hpd]
      _ = z⁻¹ * p := by group
  induction b with
  | zero => simp
  | succ b ih =>
    have hci : ∀ g : H, g * z⁻¹ = z⁻¹ * g := fun g => by
      have := hc g⁻¹
      calc g * z⁻¹ = (z * g⁻¹)⁻¹ := by group
        _ = (g⁻¹ * z)⁻¹ := by rw [this]
        _ = z⁻¹ * g := by group
    calc d * p ^ (b + 1) * d⁻¹ = (d * p ^ b * d⁻¹) * (d * p * d⁻¹) := by group
      _ = z⁻¹ ^ b * p ^ b * (z⁻¹ * p) := by rw [ih, h1]
      _ = z⁻¹ ^ (b + 1) * p ^ (b + 1) := by
        rw [pow_succ, pow_succ]
        calc z⁻¹ ^ b * p ^ b * (z⁻¹ * p) = z⁻¹ ^ b * (p ^ b * z⁻¹) * p := by group
          _ = z⁻¹ ^ b * (z⁻¹ * p ^ b) * p := by rw [hci (p ^ b)]
          _ = z⁻¹ ^ b * z⁻¹ * (p ^ b * p) := by group

theorem pow_mod_three {G : Type} [Monoid G] {x : G} (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ (n % 3) = x ^ n :=
  (pow_eq_pow_mod n hx).symm

theorem exists_elemAbelian_nine_of_heis (N : Subgroup H) [N.Normal] (hN : N ≤ Subgroup.center H)
    {d p z : H} (hd : d ^ 3 = 1) (hp : p ^ 3 = 1) (hz : p * d * p⁻¹ = z * d)
    (hzc : z ∈ Subgroup.center H) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hzN : z ∈ N) :
    ∃ E : Subgroup (H ⧸ N), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  set x : H ⧸ N := QuotientGroup.mk d with hxdef
  set y : H ⧸ N := QuotientGroup.mk p with hydef
  have hx3 : x ^ 3 = 1 := by rw [hxdef, ← QuotientGroup.mk_pow, hd, QuotientGroup.mk_one]
  have hy3 : y ^ 3 = 1 := by rw [hydef, ← QuotientGroup.mk_pow, hp, QuotientGroup.mk_one]
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hpd : p * d = z * d * p := by
    calc p * d = (p * d * p⁻¹) * p := by group
      _ = z * d * p := by rw [hz]
  have hxy : x * y = y * x := by
    rw [hxdef, hydef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hpd]
    apply QuotientGroup.eq.2
    have hc : ∀ g : H, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hzc g
    have e : (d * p)⁻¹ * (z * d * p) = z := by
      calc (d * p)⁻¹ * (z * d * p) = p⁻¹ * d⁻¹ * (z * d) * p := by group
        _ = p⁻¹ * d⁻¹ * (d * z) * p := by rw [← hc d]
        _ = p⁻¹ * (z * p) := by group
        _ = p⁻¹ * (p * z) := by rw [← hc p]
        _ = z := by group
    rw [e]
    exact hzN
  have hkey : ∀ a b : ℕ, a < 3 → b < 3 → x ^ a * y ^ b = 1 → a = 0 ∧ b = 0 := by
    intro a b ha hb h1
    have hmem : d ^ a * p ^ b ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
        QuotientGroup.mk_pow]
      exact h1
    have hcen := Subgroup.mem_center_iff.1 (hN hmem)
    have hza : z ^ a = 1 := by
      have h2 := hcen p
      have h3 : p * (d ^ a * p ^ b) * p⁻¹ = z ^ a * (d ^ a * p ^ b) := by
        calc p * (d ^ a * p ^ b) * p⁻¹ = (p * d ^ a * p⁻¹) * p ^ b := by group
          _ = z ^ a * (d ^ a * p ^ b) := by rw [conj_pow_of_heis hz hzc a]; group
      have h4 : p * (d ^ a * p ^ b) * p⁻¹ = d ^ a * p ^ b := by
        rw [h2]; group
      rw [h4] at h3
      have h5 : z ^ a * (d ^ a * p ^ b) = 1 * (d ^ a * p ^ b) := by rw [one_mul]; exact h3.symm
      exact mul_right_cancel h5
    have ha0 : a = 0 := by
      have h5 := orderOf_dvd_of_pow_eq_one hza
      rw [hzo] at h5
      omega
    subst ha0
    have hcen' : ∀ g : H, g * p ^ b = p ^ b * g := by simpa using hcen
    have hzb : z⁻¹ ^ b = 1 := by
      have h3 := conj_pow_of_heis' hz hzc b
      have h4 : d * p ^ b * d⁻¹ = p ^ b := by rw [hcen' d]; group
      rw [h4] at h3
      have h5 : z⁻¹ ^ b * p ^ b = 1 * p ^ b := by rw [one_mul]; exact h3.symm
      exact mul_right_cancel h5
    have hzb' : z ^ b = 1 := by
      have := congrArg (·⁻¹) hzb
      simpa [inv_pow] using this
    have hb0 : b = 0 := by
      have h5 := orderOf_dvd_of_pow_eq_one hzb'
      rw [hzo] at h5
      omega
    exact ⟨rfl, hb0⟩
  have hcomm : ∀ (a b : ℕ), y ^ b * x ^ a = x ^ a * y ^ b := fun a b =>
    ((Commute.pow_pow (show Commute x y from hxy) a b).eq).symm
  let E : Subgroup (H ⧸ N) :=
    { carrier := {g | ∃ a b : Fin 3, g = x ^ (a : ℕ) * y ^ (b : ℕ)}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
        refine ⟨a + c, b + e, ?_⟩
        rw [Fin.val_add, Fin.val_add, pow_mod_three hx3, pow_mod_three hy3, pow_add, pow_add]
        calc x ^ (a : ℕ) * y ^ (b : ℕ) * (x ^ (c : ℕ) * y ^ (e : ℕ))
            = x ^ (a : ℕ) * (y ^ (b : ℕ) * x ^ (c : ℕ)) * y ^ (e : ℕ) := by group
          _ = x ^ (a : ℕ) * (x ^ (c : ℕ) * y ^ (b : ℕ)) * y ^ (e : ℕ) := by rw [hcomm]
          _ = x ^ (a : ℕ) * x ^ (c : ℕ) * (y ^ (b : ℕ) * y ^ (e : ℕ)) := by group
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        refine ⟨-a, -b, ?_⟩
        have hxa : (x ^ (a : ℕ))⁻¹ = x ^ ((-a : Fin 3) : ℕ) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, ← pow_mod_three hx3]
          have : ((a : ℕ) + ((-a : Fin 3) : ℕ)) % 3 = 0 := by
            have := Fin.val_add a (-a)
            rw [add_neg_cancel, Fin.val_zero] at this
            omega
          rw [this, pow_zero]
        have hyb : (y ^ (b : ℕ))⁻¹ = y ^ ((-b : Fin 3) : ℕ) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, ← pow_mod_three hy3]
          have : ((b : ℕ) + ((-b : Fin 3) : ℕ)) % 3 = 0 := by
            have := Fin.val_add b (-b)
            rw [add_neg_cancel, Fin.val_zero] at this
            omega
          rw [this, pow_zero]
        rw [mul_inv_rev, hxa, hyb, hcomm] }
  refine ⟨E, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, b, rfl⟩ ⟨_, c, e, rfl⟩
    apply Subtype.ext
    show x ^ (a : ℕ) * y ^ (b : ℕ) * (x ^ (c : ℕ) * y ^ (e : ℕ)) =
      x ^ (c : ℕ) * y ^ (e : ℕ) * (x ^ (a : ℕ) * y ^ (b : ℕ))
    calc x ^ (a : ℕ) * y ^ (b : ℕ) * (x ^ (c : ℕ) * y ^ (e : ℕ))
        = x ^ (a : ℕ) * (y ^ (b : ℕ) * x ^ (c : ℕ)) * y ^ (e : ℕ) := by group
      _ = x ^ (a : ℕ) * (x ^ (c : ℕ) * y ^ (b : ℕ)) * y ^ (e : ℕ) := by rw [hcomm]
      _ = x ^ (c : ℕ) * (x ^ (a : ℕ) * (y ^ (b : ℕ) * y ^ (e : ℕ))) := by
          rw [← mul_assoc (x ^ (a : ℕ)), ← pow_add, ← pow_add, add_comm]; group
      _ = x ^ (c : ℕ) * (x ^ (a : ℕ) * (y ^ (e : ℕ) * y ^ (b : ℕ))) := by
          rw [← pow_add, ← pow_add, add_comm]
      _ = x ^ (c : ℕ) * ((x ^ (a : ℕ) * y ^ (e : ℕ)) * y ^ (b : ℕ)) := by group
      _ = x ^ (c : ℕ) * ((y ^ (e : ℕ) * x ^ (a : ℕ)) * y ^ (b : ℕ)) := by rw [hcomm]
      _ = x ^ (c : ℕ) * y ^ (e : ℕ) * (x ^ (a : ℕ) * y ^ (b : ℕ)) := by group
  · rintro _ ⟨a, b, rfl⟩
    have hc : Commute (x ^ (a : ℕ)) (y ^ (b : ℕ)) := (hcomm _ _).symm
    rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm (a : ℕ), mul_comm (b : ℕ), pow_mul, pow_mul,
      hx3, hy3, one_pow, one_pow, one_mul]
  · let f : Fin 3 × Fin 3 → E := fun ab => ⟨x ^ (ab.1 : ℕ) * y ^ (ab.2 : ℕ), ab.1, ab.2, rfl⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · rintro ⟨a, b⟩ ⟨c, e⟩ h
        have h1 : x ^ (a : ℕ) * y ^ (b : ℕ) = x ^ (c : ℕ) * y ^ (e : ℕ) :=
          congrArg Subtype.val h
        have h2 : x ^ ((a - c : Fin 3) : ℕ) * y ^ ((b - e : Fin 3) : ℕ) = 1 := by
          have hxs : x ^ ((a - c : Fin 3) : ℕ) = x ^ (a : ℕ) * (x ^ (c : ℕ))⁻¹ := by
            rw [eq_mul_inv_iff_mul_eq, ← pow_add, ← pow_mod_three hx3,
              ← pow_mod_three hx3 (a : ℕ)]
            congr 1
            have := Fin.val_add (a - c) c
            rw [sub_add_cancel] at this
            omega
          have hys : y ^ ((b - e : Fin 3) : ℕ) = y ^ (b : ℕ) * (y ^ (e : ℕ))⁻¹ := by
            rw [eq_mul_inv_iff_mul_eq, ← pow_add, ← pow_mod_three hy3,
              ← pow_mod_three hy3 (b : ℕ)]
            congr 1
            have := Fin.val_add (b - e) e
            rw [sub_add_cancel] at this
            omega
          rw [hxs, hys]
          calc x ^ (a : ℕ) * (x ^ (c : ℕ))⁻¹ * (y ^ (b : ℕ) * (y ^ (e : ℕ))⁻¹)
              = (x ^ (c : ℕ))⁻¹ * (x ^ (a : ℕ) * y ^ (b : ℕ)) * (y ^ (e : ℕ))⁻¹ := by
                rw [show x ^ (a : ℕ) * (x ^ (c : ℕ))⁻¹ = (x ^ (c : ℕ))⁻¹ * x ^ (a : ℕ) by
                  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add, ← zpow_add,
                    add_comm]]
                group
            _ = 1 := by rw [h1]; group
        obtain ⟨ha, hb⟩ := hkey _ _ (Fin.isLt _) (Fin.isLt _) h2
        have hac : a - c = 0 := Fin.ext ha
        have hbe : b - e = 0 := Fin.ext hb
        rw [sub_eq_zero] at hac hbe
        rw [hac, hbe]
      · rintro ⟨_, a, b, rfl⟩
        exact ⟨(a, b), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_fin]

end Heis

section Matrices

open Matrix

variable {K : Type} [Field K]

@[expose] def heisD (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2]

@[expose] def heisP : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_heisD {ω : K} (hω : ω ^ 3 = 1) : (heisD ω).det = 1 := by
  rw [heisD, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_mul]
  rw [← pow_succ']
  exact hω

theorem det_heisP : (heisP : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [heisP, Matrix.det_fin_three]
  simp

theorem heisD_pow_three {ω : K} (hω : ω ^ 3 = 1) : heisD ω ^ 3 = 1 := by
  rw [heisD, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [hω, ← pow_mul]
  · rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hω, one_pow]

theorem heisP_pow_three : (heisP : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisP, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem heisP_mul_heisD {ω : K} (hω : ω ^ 3 = 1) :
    heisP * heisD ω = (ω ^ 2) • (heisD ω * heisP) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisP, heisD, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]
  · rw [← pow_succ, hω]
  · rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_add, hω, one_mul, pow_one]

theorem heisD_unitary {ω : K} {q : ℕ} (hq0 : q ≠ 0) (hq : ω ^ (q + 1) = 1) :
    ((heisD ω).map (· ^ q))ᵀ * heisD ω = 1 := by
  rw [heisD, Matrix.diagonal_map (f := fun x : K => x ^ q) (by simp [hq0]),
    Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp
  · rw [← pow_succ, hq]
  · rw [← pow_mul, ← pow_add, show 2 * q + 2 = (q + 1) * 2 by ring, pow_mul, hq, one_pow]

theorem heisP_unitary {q : ℕ} (hq : q ≠ 0) :
    ((heisP : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * heisP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisP, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, zero_pow hq]

end Matrices

section Proj

open Matrix

variable {K : Type} [Field K]

noncomputable def glD {ω : K} (hω : ω ^ 3 = 1) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (heisD ω) (by rw [det_heisD hω]; exact one_ne_zero)

noncomputable def glP : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero heisP (by rw [det_heisP]; exact one_ne_zero)

theorem coe_glD {ω : K} (hω : ω ^ 3 = 1) : ((glD hω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    heisD ω :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem coe_glP : ((glP : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisP :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem glD_pow_three {ω : K} (hω : ω ^ 3 = 1) : glD hω ^ 3 = 1 := by
  ext1
  rw [Units.val_pow_eq_pow_val, coe_glD, heisD_pow_three hω, Units.val_one]

theorem glP_pow_three : (glP : GL (Fin 3) K) ^ 3 = 1 := by
  ext1
  rw [Units.val_pow_eq_pow_val, coe_glP, heisP_pow_three, Units.val_one]

theorem glP_mul_glD {ω : Kˣ} (hω : (ω : K) ^ 3 = 1) :
    glP * glD hω = Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * glD hω * glP := by
  ext1
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_glP, coe_glD,
    Matrix.GeneralLinearGroup.coe_scalar, heisP_mul_heisD hω, Matrix.mul_assoc,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Units.val_pow_eq_pow_val]

theorem glScalar_comm (u : Kˣ) (g : GL (Fin 3) K) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 3) u =
      Matrix.GeneralLinearGroup.scalar (Fin 3) u * g := by
  ext1
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (u : K) (fun r' => Commute.all _ _) _).eq.symm

theorem eq_one_of_glScalar_eq_one {u : Kˣ} (h : Matrix.GeneralLinearGroup.scalar (Fin 3) u = 1) :
    u = 1 := by
  have h2 := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K) 0 0)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.one_apply_eq] at h2
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h2
  exact Units.ext h2

theorem exists_elemAbelian_nine_statedProj {H : Subgroup (GL (Fin 3) K)} {ω : Kˣ}
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hω3 : (ω : K) ^ 3 = 1)
    (hD : glD hω3 ∈ H) (hP : glP ∈ H) (hZ : Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) ∈ H) :
    ∃ E : Subgroup (StatedProj H), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  set N : Subgroup ↥H := (StatedScalars (Fin 3) K).subgroupOf H with hNdef
  haveI : N.Normal := Subgroup.Normal.subgroupOf inferInstance H
  have hN : N ≤ Subgroup.center ↥H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, hu⟩ := (Subgroup.mem_subgroupOf.1 hx)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu]
    exact glScalar_comm u g
  let d : ↥H := ⟨glD hω3, hD⟩
  let p : ↥H := ⟨glP, hP⟩
  let z : ↥H := ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2), hZ⟩
  have hzN : z ∈ N := Subgroup.mem_subgroupOf.2 ⟨ω ^ 2, rfl⟩
  have hz3 : z ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2)) ^ 3 = 1
    rw [← map_pow, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω, one_pow, map_one]
  have hz1 : z ≠ 1 := by
    intro h
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) = 1 := congrArg Subtype.val h
    have h3 : ω ^ 2 = 1 := eq_one_of_glScalar_eq_one h2
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω, h3]; group
  have hd : d ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact glD_pow_three hω3
  have hp : p ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact glP_pow_three
  have hpd : p * d = z * d * p := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact glP_mul_glD hω3
  have hz : p * d * p⁻¹ = z * d := by rw [hpd]; group
  exact exists_elemAbelian_nine_of_heis N hN hd hp hz (hN hzN) hz3 hz1 hzN

end Proj

section Facts

open Matrix

theorem l3u3_cases {X : Type} [Group X] (h : L3U3 X) :
    (∃ n : ℕ, (n % 6 = 2 ∨ n % 6 = 4) ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ n ∧ Nonempty (X ≃* ↥(StatedSL 3 K) ⧸ Subgroup.center ↥(StatedSL 3 K))) ∨
    (∃ n : ℕ, (n % 6 = 1 ∨ n % 6 = 5) ∧ 1 < n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (2 ^ n) ^ 2 ∧
        Nonempty (X ≃* ↥(StatedSU 3 (2 ^ n) K) ⧸ Subgroup.center ↥(StatedSU 3 (2 ^ n) K))) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie] at hi
  | alternating _ _ => simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie] at hi
  | sporadic _ => simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie] at hi
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld with
    | A r q =>
      by_cases hr : r = 2
      · subst hr
        obtain ⟨hp2, hk⟩ : q.p = 2 ∧ (q.exponent % 6 = 2 ∨ q.exponent % 6 = 4) := hi
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        have hK : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
          rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp2]
        refine Or.inl ⟨q.exponent, hk, GaloisField q.p q.exponent, inferInstance, inferInstance,
          hK, ⟨?_⟩⟩
        exact (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
          (QuotientGroup.congr _ _
            (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.sl3Equiv _)
            (Subgroup.map_center_eq _))
      · simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie, hr] at hi
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        obtain ⟨hp2, hk⟩ : q.p = 2 ∧ (q.exponent % 6 = 1 ∨ q.exponent % 6 = 5) := hi
        have hv1 : 2 ≤ 2 ∧ (2 = 2 → 3 ≤ q.card) :=
          (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
        have hq3 : 3 ≤ q.card := hv1.2 rfl
        have hqc : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp2]
        have hn1 : 1 < q.exponent := by
          by_contra hle
          have h2 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hq2 : q.card ≠ 2 := by omega
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        haveI : Fintype (GaloisField q.p (2 * q.exponent)) := Fintype.ofFinite _
        have hcardK : Nat.card (GaloisField q.p (2 * q.exponent)) = q.card ^ 2 := by
          rw [GaloisField.card q.p (2 * q.exponent) (by omega), PrimePower.card_def, ← pow_mul,
            mul_comm]
        have hchar : CharP (GaloisField q.p (2 * q.exponent)) 2 := by
          rw [← hp2]
          infer_instance
        obtain ⟨q', hv', hp', hcard', ⟨eSU⟩⟩ :=
          CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
            (K := GaloisField q.p (2 * q.exponent)) (m := 3) (q := q.card)
            (by rw [← Nat.card_eq_fintype_card]; exact hcardK) (by norm_num)
            (fun h => hq2 (Prod.mk.inj h).2)
        have hringch : ringChar (GaloisField q.p (2 * q.exponent)) = 2 := ringChar.eq_iff.2 hchar
        have hq' : q' = q := by
          apply PrimePower.ext
          · rw [hp', hringch, hp2]
          · have h1 : q'.p ^ q'.exponent = q.p ^ q.exponent := by
              rw [← PrimePower.card_def, ← PrimePower.card_def]
              exact hcard'
            rw [hp', hringch, hp2] at h1
            exact Nat.pow_right_injective (le_refl 2) h1
        subst hq'
        have hne : Nonempty (X ≃* ↥(StatedSU 3 q'.card (GaloisField q'.p (2 * q'.exponent))) ⧸
            Subgroup.center ↥(StatedSU 3 q'.card (GaloisField q'.p (2 * q'.exponent)))) :=
          ⟨e.trans eSU.symm⟩
        rw [hqc] at hne hcardK
        exact Or.inr ⟨q'.exponent, hk, hn1, _, inferInstance, inferInstance, hcardK, hne⟩
      · simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie, hr] at hi
    | _ => simp [CFSG.LocalAnalysis.GLTheoremA.l3u3Index, onLie] at hi

theorem three_dvd_two_pow_sub_one {n : ℕ} (hn : n % 2 = 0) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  rw [pow_mul]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 m

theorem three_dvd_two_pow_add_one {n : ℕ} (hn : n % 2 = 1) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  have h2 : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  omega

theorem l3u3_order {X : Type} [Group X] (h : L3U3 X) : L3U3Order (Nat.card X) := by
  rcases l3u3_cases h with ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ | ⟨n, hn, hn1, K, _, _, hK, ⟨e⟩⟩
  · have h3 : 3 ∣ Nat.card K - 1 := by
      rw [hK]
      exact three_dvd_two_pow_sub_one (by omega)
    have hc := CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.sl_quot_card K h3
      (MulEquiv.refl ↥(StatedSL 3 K))
    refine ⟨n, Or.inl ⟨hn, ?_⟩⟩
    rw [Nat.card_congr e.toEquiv, mul_comm, hc, hK, ← pow_mul, ← pow_mul, mul_comm n 3,
      mul_comm n 2]
  · have h3 : 3 ∣ 2 ^ n + 1 := three_dvd_two_pow_add_one (by omega)
    have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(StatedSU 3 (2 ^ n) K))
    rw [CFSG.Open.StatedCenterThree.card_center_statedSU_three hK h3,
      CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK] at hL
    refine ⟨n, Or.inr ⟨hn, hn1, ?_⟩⟩
    rw [Nat.card_congr e.toEquiv, mul_comm, ← hL, ← pow_mul, ← pow_mul, mul_comm n 3,
      mul_comm n 2, mul_assoc]

theorem exists_elemAbelian_nine_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ E : Subgroup B, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ E : Subgroup A, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, hc⟩ := h
  refine ⟨E.map e.symm.toMonoidHom,
    CFSG.HardMathSupport.Dickson.Sec6.isElemAbelian_map_up34 _ e.symm.injective hE, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective]
  exact hc

theorem exists_cube_root_of_unity {K : Type} [Field K] [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ (ω : K) ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [Nat.card_units]; exact h)
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  refine ⟨ω, hω3, fun h1 => ?_, by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]⟩
  rw [h1, orderOf_one] at hω
  norm_num at hω

theorem det_glScalar {K : Type} [Field K] {c : Kˣ} (hc : c ^ 3 = 1) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hc,
    Units.val_one]

theorem l3u3_elem9 {X : Type} [Group X] (h : L3U3 X) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  rcases l3u3_cases h with ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ | ⟨n, hn, hn1, K, _, _, hK, ⟨e⟩⟩
  · have h3 : 3 ∣ Nat.card K - 1 := by
      rw [hK]
      exact three_dvd_two_pow_sub_one (by omega)
    obtain ⟨ω, hω3, hω1, hωK⟩ := exists_cube_root_of_unity h3
    refine exists_elemAbelian_nine_of_mulEquiv
      (e.trans (CFSG.LocalAnalysis.GLTheoremA.H1419.projective_of_sl3 (MulEquiv.refl _))) ?_
    refine exists_elemAbelian_nine_statedProj hω3 hω1 hωK ?_ ?_ ?_
    · exact Subgroup.subset_closure (by rw [Set.mem_setOf_eq, coe_glD, det_heisD hωK])
    · exact Subgroup.subset_closure (by rw [Set.mem_setOf_eq, coe_glP, det_heisP])
    · refine Subgroup.subset_closure (det_glScalar ?_)
      rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
  · have hq0 : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have h3 : 3 ∣ 2 ^ n + 1 := three_dvd_two_pow_add_one (by omega)
    have h3' : 3 ∣ Nat.card K - 1 := by
      rw [hK]
      exact h3.trans (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.succ_dvd_sq_sub_one
        (Nat.one_le_two_pow))
    obtain ⟨ω, hω3, hω1, hωK⟩ := exists_cube_root_of_unity h3'
    have hωq : (ω : K) ^ (2 ^ n + 1) = 1 := by
      obtain ⟨m, hm⟩ := h3
      rw [hm, pow_mul, hωK, one_pow]
    refine exists_elemAbelian_nine_of_mulEquiv
      (e.trans (CFSG.LocalAnalysis.GLTheoremA.H1419.projective_of_su hK hq0 h3
        (MulEquiv.refl _))) ?_
    refine exists_elemAbelian_nine_statedProj hω3 hω1 hωK ?_ ?_ ?_
    · apply Subgroup.subset_closure
      refine ⟨by rw [coe_glD, det_heisD hωK], ?_⟩
      rw [coe_glD]
      exact heisD_unitary hq0 hωq
    · apply Subgroup.subset_closure
      refine ⟨by rw [coe_glP, det_heisP], ?_⟩
      rw [coe_glP]
      exact heisP_unitary hq0
    · refine CFSG.Open.StatedCenterThree.scalar_mem hq0 h3 ?_
      rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]

theorem l3u3Facts_holds : L3U3Facts :=
  ⟨fun _ _ _ h => l3u3_order h, fun _ _ _ h => l3u3_elem9 h⟩

end Facts

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
