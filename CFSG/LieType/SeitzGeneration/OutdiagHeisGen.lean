module

public import CFSG.LieType.SeitzGeneration.OuterLinearWide
public import CFSG.LieType.SeitzGeneration.HeisLinearNormal
public import CFSG.LieType.SeitzGeneration.HeisLinearGen

public section

namespace CFSG.LieType.SeitzGeneration

open Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Companion

variable {F : Type*} [Field F]

@[expose] def companionMat (p : ℕ) (c : F) : Matrix (Fin p) (Fin p) F :=
  (Equiv.Perm.permMatrix (σ := (finRotate p).symm) (R := F)) *
    Matrix.diagonal (fun j : Fin p => if (j : ℕ) = p - 1 then c else 1)

theorem companionMat_mulVec_single (p : ℕ) (c : F) (k : Fin p) :
    (companionMat p c).mulVec (Pi.single k 1) =
      (if (k : ℕ) = p - 1 then c else 1) • Pi.single (finRotate p k) 1 := by
  have hd : (Matrix.diagonal (fun j : Fin p => if (j : ℕ) = p - 1 then c else 1)).mulVec
      (Pi.single k 1) = (if (k : ℕ) = p - 1 then c else 1) • Pi.single k 1 := by
    ext i
    by_cases h : i = k
    · subst h
      simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, Pi.single_apply, h]
  rw [companionMat, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_smul, Matrix.permMatrix_mulVec]
  ext i
  simp only [Pi.smul_apply, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq,
    smul_eq_mul]

theorem det_companionMat {p : ℕ} (hp : Odd p) (c : F) : (companionMat p c).det = c := by
  have hp0 : 0 < p := hp.pos
  have hev : Even (p - 1) := by
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, by omega⟩
  rw [companionMat, Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal,
    Equiv.Perm.sign_symm, sign_finRotate, hev.neg_one_pow, Units.val_one, Int.cast_one, one_mul,
    Fintype.prod_eq_single (⟨p - 1, by omega⟩ : Fin p)]
  · simp
  · intro j hj
    have : (j : ℕ) ≠ p - 1 := fun h => hj (Fin.ext h)
    simp [this]

end Companion

@[expose] def SingerTorusGen (F : Type) [Field F] (p : ℕ) : Prop :=
  ∀ c : Fˣ, (¬ ∃ μ : Fˣ, μ ^ p = c) → ∀ K : Subgroup (SpecialLinearGroup (Fin p) F),
    (∀ g : SpecialLinearGroup (Fin p) F,
      (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) = Matrix.diagonal t) → g ∈ K) →
    (∀ g : SpecialLinearGroup (Fin p) F,
      (g : Matrix (Fin p) (Fin p) F) * companionMat p (c : F) =
        companionMat p (c : F) * (g : Matrix (Fin p) (Fin p) F) → g ∈ K) →
    K = ⊤

section Normal

variable {F : Type*} [Field F]

theorem val_finRotate_mod' {p : ℕ} (hp : 0 < p) (k : Fin p) :
    ((finRotate p k : Fin p) : ℕ) = ((k : ℕ) + 1) % p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

theorem heisenberg_normal_form_matrix {p : ℕ} (hp : p.Prime) {ω c : F}
    (hω : IsPrimitiveRoot ω p) (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p)
    {X Y : Matrix (Fin p) (Fin p) F} (hX : IsUnit X) (hXp : X ^ p = c • 1)
    (hYp : Y ^ p = 1) (hrel : Y * X = ω • (X * Y)) :
    ∃ (P : GL (Fin p) F) (ξ : F), ξ ^ p = 1 ∧
      ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * Y * (P : Matrix (Fin p) (Fin p) F) =
        ξ • heisDiagMat ω ∧
      ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * X * (P : Matrix (Fin p) (Fin p) F) =
        companionMat p c := by
  classical
  have hp0 : 0 < p := hp.pos
  have hYX : ∀ k : ℕ, Y * X ^ k = ω ^ k • (X ^ k * Y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ X k, pow_succ ω k, ← Matrix.mul_assoc, ih, Matrix.smul_mul,
        Matrix.mul_assoc (X ^ k) Y X, hrel, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc (X ^ k) X Y]
  obtain ⟨ξ, v, hξp, hv0, hYv⟩ := exists_eigenvector_of_pow_eq_one hp0 hζ hp0 hYp
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hξp
    exact zero_ne_one hξp
  have hYu : ∀ k : Fin p, Y.mulVec ((X ^ (k : ℕ)).mulVec v) =
      (ξ * ω ^ (k : ℕ)) • (X ^ (k : ℕ)).mulVec v := by
    intro k
    rw [Matrix.mulVec_mulVec, hYX, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hYv,
      Matrix.mulVec_smul, smul_smul, mul_comm ξ]
  have hinj : Function.Injective (fun k : Fin p => ξ * ω ^ (k : ℕ)) := by
    intro k l h
    have h' : ω ^ (k : ℕ) = ω ^ (l : ℕ) := mul_left_cancel₀ hξ0 h
    exact Fin.ext (hω.pow_inj k.2 l.2 h')
  have hu0 : ∀ k : Fin p, (X ^ (k : ℕ)).mulVec v ≠ 0 := by
    intro k hk
    apply hv0
    apply Matrix.mulVec_injective_iff_isUnit.2 (hX.pow (k : ℕ))
    rw [hk, Matrix.mulVec_zero]
  have hli : LinearIndependent F (fun k : Fin p => (X ^ (k : ℕ)).mulVec v) :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' Y)
      (fun k : Fin p => ξ * ω ^ (k : ℕ)) hinj (fun k : Fin p => (X ^ (k : ℕ)).mulVec v)
      (fun k => ⟨by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hYu k, hu0 k⟩)
  let b : Module.Basis (Fin p) F (Fin p → F) :=
    basisOfLinearIndependentOfCardEqFinrank' (fun k : Fin p => (X ^ (k : ℕ)).mulVec v) hli
      (by simp)
  have hb : ∀ k : Fin p, b k = (X ^ (k : ℕ)).mulVec v := fun k => by simp [b]
  have hXb : ∀ k : Fin p, X.mulVec (b k) =
      (if (k : ℕ) = p - 1 then c else 1) • b (finRotate p k) := by
    intro k
    rw [hb k, Matrix.mulVec_mulVec, ← pow_succ']
    split_ifs with hk
    · have h1 : ((finRotate p k : Fin p) : ℕ) = 0 := by
        rw [val_finRotate_mod' hp0, hk, show p - 1 + 1 = p by omega, Nat.mod_self]
      rw [hb (finRotate p k), h1, pow_zero, Matrix.one_mulVec, show (k : ℕ) + 1 = p by omega,
        hXp, Matrix.smul_mulVec, Matrix.one_mulVec]
    · have h1 : ((finRotate p k : Fin p) : ℕ) = (k : ℕ) + 1 := by
        rw [val_finRotate_mod' hp0, Nat.mod_eq_of_lt (by omega)]
      rw [hb (finRotate p k), h1, one_smul]
  refine ⟨basisUnit b, ξ, hξp, ?_, ?_⟩
  · refine units_inv_mul_mul_eq_of_mul_eq _ (mul_basisUnit_eq_of_mulVec b fun k => ?_)
    rw [smul_heisDiagMat_mulVec_single, basisUnit_mulVec_single, hb k]
    exact hYu k
  · refine units_inv_mul_mul_eq_of_mul_eq _ (mul_basisUnit_eq_of_mulVec b fun k => ?_)
    rw [companionMat_mulVec_single, Matrix.mulVec_smul, basisUnit_mulVec_single, one_smul]
    exact hXb k

theorem exists_heisenberg_basis_gl_p {p : ℕ} (hp : p.Prime) {ω c : F}
    (hω : IsPrimitiveRoot ω p) (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p)
    {x y : GL (Fin p) F} (hxp : (x : Matrix (Fin p) (Fin p) F) ^ p = c • 1)
    (hyp : (y : Matrix (Fin p) (Fin p) F) ^ p = 1)
    (hrel : (y : Matrix (Fin p) (Fin p) F) * (x : Matrix (Fin p) (Fin p) F) =
      ω • ((x : Matrix (Fin p) (Fin p) F) * (y : Matrix (Fin p) (Fin p) F))) :
    ∃ (P : GL (Fin p) F) (ξ : F), ξ ^ p = 1 ∧
      ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (y : Matrix (Fin p) (Fin p) F) *
        (P : Matrix (Fin p) (Fin p) F) = ξ • heisDiagMat ω ∧
      ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (x : Matrix (Fin p) (Fin p) F) *
        (P : Matrix (Fin p) (Fin p) F) = companionMat p c :=
  heisenberg_normal_form_matrix hp hω hζ x.isUnit hxp hyp hrel

end Normal

section Powers

variable {G : Type*} [Group G]

theorem sgo_pow_left_comm {z x y : G} (hz : ∀ g : G, z * g = g * z)
    (hyx : y * x = z * (x * y)) (n : ℕ) : y ^ n * x = z ^ n * (x * y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : ∀ g : G, z ^ n * g = g * z ^ n := fun g => (Commute.pow_left (hz g) n).eq
    have h1 : y * (x * y ^ n) = z * (x * y ^ (n + 1)) := by
      rw [← mul_assoc, hyx, mul_assoc z (x * y), mul_assoc x y, ← pow_succ' y n]
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (z ^ n * (x * y ^ n)) := by rw [ih]
      _ = z ^ n * (y * (x * y ^ n)) := by rw [← mul_assoc, ← hzn y, mul_assoc]
      _ = z ^ n * (z * (x * y ^ (n + 1))) := by rw [h1]
      _ = z ^ (n + 1) * (x * y ^ (n + 1)) := by rw [← mul_assoc, ← pow_succ]

theorem sgo_comm_pow_right {z x y : G} (hz : ∀ g : G, z * g = g * z)
    (hyx : y * x = z * (x * y)) (n : ℕ) : y * x ^ n = z ^ n * (x ^ n * y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc y * x ^ (n + 1) = (y * x ^ n) * x := by rw [pow_succ, mul_assoc]
      _ = z ^ n * (x ^ n * (y * x)) := by rw [ih, mul_assoc, mul_assoc]
      _ = z ^ n * (x ^ n * (z * (x * y))) := by rw [hyx]
      _ = z ^ n * (z * (x ^ n * (x * y))) := by
          rw [← mul_assoc (x ^ n) z, ← hz (x ^ n), mul_assoc]
      _ = (z ^ n * z) * (x ^ n * (x * y)) := by rw [mul_assoc]
      _ = z ^ (n + 1) * (x ^ (n + 1) * y) := by
          rw [← pow_succ z n, pow_succ x n, mul_assoc (x ^ n) x y]

theorem sgo_mul_pow {z x y : G} (hz : ∀ g : G, z * g = g * z)
    (hyx : y * x = z * (x * y)) (n : ℕ) :
    (x * y) ^ n = z ^ (n.choose 2) * (x ^ n * y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : ∀ g : G, z ^ n * g = g * z ^ n := fun g => (Commute.pow_left (hz g) n).eq
    have hxz : ∀ m : G, x ^ n * (z ^ n * m) = z ^ n * (x ^ n * m) := fun m => by
      rw [← mul_assoc, ← hzn (x ^ n), mul_assoc]
    have hM : x ^ n * (x * y ^ n) * y = x ^ (n + 1) * y ^ (n + 1) := by
      rw [← mul_assoc (x ^ n) x (y ^ n), ← pow_succ x n, mul_assoc, ← pow_succ y n]
    have hc : (n + 1).choose 2 = n.choose 2 + n := by
      have := Nat.choose_succ_succ' n 1
      simpa [Nat.choose_one_right, add_comm] using this
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = z ^ (n.choose 2) * (x ^ n * (y ^ n * x)) * y := by
          rw [ih]; simp only [mul_assoc]
      _ = z ^ (n.choose 2) * (x ^ n * (z ^ n * (x * y ^ n))) * y := by
          rw [sgo_pow_left_comm hz hyx n]
      _ = z ^ (n.choose 2) * (z ^ n * (x ^ n * (x * y ^ n))) * y := by rw [hxz]
      _ = z ^ (n.choose 2) * z ^ n * (x ^ n * (x * y ^ n) * y) := by simp only [mul_assoc]
      _ = z ^ (n.choose 2) * z ^ n * (x ^ (n + 1) * y ^ (n + 1)) := by rw [hM]
      _ = z ^ (n.choose 2 + n) * (x ^ (n + 1) * y ^ (n + 1)) := by rw [pow_add z]
      _ = z ^ ((n + 1).choose 2) * (x ^ (n + 1) * y ^ (n + 1)) := by rw [hc]

end Powers

section Class

theorem sgo_exists_pow_isPow {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    {u : Fˣ} (hu : IsPrimitiveRoot u p) (a b : Fˣ) :
    ∃ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) ∧ ∃ l : Fˣ, l ^ p = a ^ i * b ^ j := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpN : p ∣ Nat.card Fˣ := by
    have h1 := orderOf_dvd_natCard u
    rwa [← hu.eq_orderOf] at h1
  obtain ⟨m, hm⟩ := hpN
  have hpos : 0 < Nat.card Fˣ := Nat.card_pos
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have K1 : ∀ x : Fˣ, x ^ m = 1 → ∃ l : Fˣ, l ^ p = x := by
    intro x hx
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
    have h1 : g ^ (k * (m : ℤ)) = 1 := by
      rw [_root_.zpow_mul, zpow_natCast]
      exact hx
    have h2 : ((orderOf g : ℕ) : ℤ) ∣ k * (m : ℤ) := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hord, hm] at h2
    push_cast at h2
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm0.ne'
    obtain ⟨s, hs⟩ := (mul_dvd_mul_iff_right hm').1 h2
    refine ⟨g ^ s, ?_⟩
    rw [hs, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
  have hap : (a ^ m) ^ p = 1 := by
    rw [← pow_mul, mul_comm, ← hm, pow_card_eq_one']
  have hbp : (b ^ m) ^ p = 1 := by
    rw [← pow_mul, mul_comm, ← hm, pow_card_eq_one']
  have hu' : IsPrimitiveRoot (u : F) p := IsPrimitiveRoot.coe_units_iff.2 hu
  have hap' : ((a ^ m : Fˣ) : F) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hap, Units.val_one]
  have hbp' : ((b ^ m : Fˣ) : F) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hbp, Units.val_one]
  obtain ⟨s, hs, hsa'⟩ := hu'.eq_pow_of_pow_eq_one hap'
  obtain ⟨t, ht, htb'⟩ := hu'.eq_pow_of_pow_eq_one hbp'
  have hsa : u ^ s = a ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hsa')
  have htb : u ^ t = b ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact htb')
  by_cases hs0 : s = 0
  · refine ⟨1, 0, ?_, ?_⟩
    · rintro ⟨h1, -⟩
      exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
    · have ha1 : a ^ m = 1 := by rw [← hsa, hs0, pow_zero]
      obtain ⟨l, hl⟩ := K1 a ha1
      exact ⟨l, by rw [hl, pow_one, pow_zero, mul_one]⟩
  · refine ⟨t, p - s, ?_, ?_⟩
    · rintro ⟨-, h2⟩
      have hlt : p - s < p := by omega
      have hpos' : 0 < p - s := by omega
      exact absurd (Nat.le_of_dvd hpos' h2) (by omega)
    · have hsum : s * t + t * (p - s) = p * t := by
        have hps : s + (p - s) = p := Nat.add_sub_cancel' hs.le
        calc s * t + t * (p - s) = t * (s + (p - s)) := by ring
          _ = t * p := by rw [hps]
          _ = p * t := mul_comm _ _
      have e1 : (a ^ t) ^ m = (u ^ s) ^ t := by
        rw [hsa, ← pow_mul, ← pow_mul, mul_comm]
      have e2 : (b ^ (p - s)) ^ m = (u ^ t) ^ (p - s) := by
        rw [htb, ← pow_mul, ← pow_mul, mul_comm]
      have hx : (a ^ t * b ^ (p - s)) ^ m = 1 := by
        rw [mul_pow, e1, e2, ← pow_mul, ← pow_mul, ← pow_add, hsum, pow_mul, hu.pow_eq_one,
          one_pow]
      obtain ⟨l, hl⟩ := K1 _ hx
      exact ⟨l, hl⟩

end Class

section Reduction

variable {F : Type} [Field F]

theorem sgo_det_conj {p : ℕ} (P : GL (Fin p) F) (M : Matrix (Fin p) (Fin p) F) :
    (((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * M *
      (P : Matrix (Fin p) (Fin p) F)).det = M.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Units.inv_mul,
    Matrix.det_one, one_mul]

theorem sgo_mul_eq_of_inv {p : ℕ} {P : GL (Fin p) F} {M N : Matrix (Fin p) (Fin p) F}
    (h : ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * M *
      (P : Matrix (Fin p) (Fin p) F) = N) :
    M * (P : Matrix (Fin p) (Fin p) F) = (P : Matrix (Fin p) (Fin p) F) * N := by
  rw [← h]
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem sgo_conjAut_range {p : ℕ} {g : GL (Fin p) F} {μ : Fˣ}
    (hμ : (g : Matrix (Fin p) (Fin p) F).det = (μ : F) ^ p) :
    conjAut p F g ∈ (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range := by
  obtain ⟨g', hg'⟩ : ∃ g' : GL (Fin p) F,
      g' = GeneralLinearGroup.scalar (Fin p) μ⁻¹ * g := ⟨_, rfl⟩
  have hdet : (g' : Matrix (Fin p) (Fin p) F).det = 1 := by
    rw [hg', Units.val_mul, coe_scalarGL, smul_mul, one_mul, Matrix.det_smul, Fintype.card_fin,
      hμ, ← mul_pow, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero μ), one_pow]
  obtain ⟨X₁, hgX⟩ : ∃ X₁ : SpecialLinearGroup (Fin p) F,
      SpecialLinearGroup.toGL X₁ = g' :=
    ⟨⟨(g' : Matrix (Fin p) (Fin p) F), hdet⟩, Units.ext rfl⟩
  have h1 : conjAut p F g = conjAut p F g' := by
    rw [hg', map_mul, conjAut_scalar, one_mul]
  rw [h1, ← hgX]
  have h2 : conjAut p F (SpecialLinearGroup.toGL X₁) = MulAut.conj (proj p F X₁) :=
    conjAut_toGL X₁
  rw [h2]
  exact MonoidHom.mem_range.2 ⟨proj p F X₁, rfl⟩

end Reduction

section Main

variable {F : Type} [Field F]

theorem sgo_planeGen_pair [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hG : SingerTorusGen F p) {E : Subgroup (MulAut (projectiveSL p F))} (hE : OutdiagPlane p E)
    {x y : GL (Fin p) F} {w c : Fˣ} (hw : IsPrimitiveRoot (w : F) p)
    (hxp : x ^ p = GeneralLinearGroup.scalar (Fin p) c) (hyp : y ^ p = 1)
    (hyx : y * x = GeneralLinearGroup.scalar (Fin p) w * (x * y))
    (hxE : conjAut p F x ∈ E) (hyE : conjAut p F y ∈ E) : PlaneGen E := by
  classical
  have hn : 0 < p := hp.pos
  have hn3 : 3 ≤ p := by omega
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hw1 : (w : F) ≠ 1 := hw.ne_one hp.one_lt
  have hxp' : (x : Matrix (Fin p) (Fin p) F) ^ p = (c : F) • 1 := by
    have h : ((x ^ p : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        ((GeneralLinearGroup.scalar (Fin p) c : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      rw [hxp]
    rw [Units.val_pow_eq_pow_val, coe_scalarGL] at h
    exact h
  have hyp' : (y : Matrix (Fin p) (Fin p) F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hyp, Units.val_one]
  have hrel' : (y : Matrix (Fin p) (Fin p) F) * (x : Matrix (Fin p) (Fin p) F) =
      (w : F) • ((x : Matrix (Fin p) (Fin p) F) * (y : Matrix (Fin p) (Fin p) F)) := by
    have h : ((y * x : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        ((GeneralLinearGroup.scalar (Fin p) w * (x * y) : GL (Fin p) F) :
          Matrix (Fin p) (Fin p) F) := by
      rw [hyx]
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scalarGL, smul_mul, one_mul] at h
    exact h
  obtain ⟨P, ξ, hξ, hY, hX⟩ :=
    exists_heisenberg_basis_gl_p hp hw ⟨(w : F), hw⟩ hxp' hyp' hrel'
  have hxdet : (x : Matrix (Fin p) (Fin p) F).det = (c : F) := by
    rw [← sgo_det_conj P (x : Matrix (Fin p) (Fin p) F), hX, det_companionMat hodd]
  have hydet : (y : Matrix (Fin p) (Fin p) F).det = 1 := by
    rw [← sgo_det_conj P (y : Matrix (Fin p) (Fin p) F), hY, Matrix.det_smul, Fintype.card_fin,
      det_heisDiagMat hw.pow_eq_one hodd, mul_one, hξ]
  have hcomm : x * y ≠ y * x := by
    intro h
    have h1 : GeneralLinearGroup.scalar (Fin p) w * (x * y) = 1 * (x * y) := by
      rw [one_mul, ← hyx, h]
    have h2 : GeneralLinearGroup.scalar (Fin p) w = 1 := mul_right_cancel h1
    have h3 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F) ⟨0, hn⟩ ⟨0, hn⟩) h2
    simp [coe_scalarGL] at h3
    exact hw1 (by simpa using h3)
  have hx1 : conjAut p F x ≠ 1 := by
    intro h
    obtain ⟨d, hd⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn3 x).1 h
    apply hcomm
    rw [← hd]
    exact (mul_scalarGL_comm d y).symm
  have hy1 : conjAut p F y ≠ 1 := by
    intro h
    obtain ⟨d, hd⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn3 y).1 h
    apply hcomm
    rw [← hd]
    exact mul_scalarGL_comm d x
  have hne : conjAut p F y ∉ Subgroup.zpowers (conjAut p F x) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : conjAut p F (y * (x ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    obtain ⟨s, hs⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn3 _).1 h1
    have hy : y = GeneralLinearGroup.scalar (Fin p) s * x ^ k := by
      calc y = y * (x ^ k)⁻¹ * x ^ k := (inv_mul_cancel_right _ _).symm
        _ = GeneralLinearGroup.scalar (Fin p) s * x ^ k := by rw [hs]
    apply hcomm
    rw [hy, ← mul_assoc, mul_scalarGL_comm, mul_assoc, (Commute.refl x).zpow_right k |>.eq,
      ← mul_assoc]
  have hsup := zpowers_sup_zpowers_eq_of_card_sq hp hE.1.2 hE.2.1 hxE hx1 hyE hne
  have hnot : ¬ ∃ μ : Fˣ, μ ^ p = c := by
    rintro ⟨μ, hμ⟩
    have hμF : (μ : F) ^ p = (c : F) := by rw [← Units.val_pow_eq_pow_val, hμ]
    have hxr := sgo_conjAut_range (μ := μ) (g := x) (by rw [hxdet, hμF])
    have hyr := sgo_conjAut_range (μ := 1) (g := y) (by rw [hydet, Units.val_one, one_pow])
    apply hE.2.2.2
    rw [← hsup]
    exact sup_le (Subgroup.zpowers_le.2 hxr) (Subgroup.zpowers_le.2 hyr)
  have hfixY : ∀ k : SpecialLinearGroup (Fin p) F,
      (∃ t : Fin p → F, (k : Matrix (Fin p) (Fin p) F) = Matrix.diagonal t) →
        conjUnit P k ∈ FixSL (y : Matrix (Fin p) (Fin p) F) := by
    rintro k ⟨t, ht⟩
    refine mem_FixSL_conj (sgo_mul_eq_of_inv hY) ?_
    refine ⟨1, ?_⟩
    rw [one_smul, ht]
    simp only [Matrix.smul_mul, Matrix.mul_smul, heisDiagMat, heisGen_diag_comm]
  have hfixX : ∀ k : SpecialLinearGroup (Fin p) F,
      (k : Matrix (Fin p) (Fin p) F) * companionMat p (c : F) =
        companionMat p (c : F) * (k : Matrix (Fin p) (Fin p) F) →
          conjUnit P k ∈ FixSL (x : Matrix (Fin p) (Fin p) F) := by
    intro k hk
    refine mem_FixSL_conj (sgo_mul_eq_of_inv hX) ?_
    exact ⟨1, by rw [one_smul, hk]⟩
  let S : Set (SpecialLinearGroup (Fin p) F) := {k | ∃ A : GL (Fin p) F,
    conjAut p F A ∈ E ∧ conjAut p F A ≠ 1 ∧ k ∈ FixSL (A : Matrix (Fin p) (Fin p) F)}
  have hK : (Subgroup.closure S).comap (conjUnit P) = ⊤ := by
    apply hG c hnot
    · intro g hg
      rw [Subgroup.mem_comap]
      exact Subgroup.subset_closure ⟨y, hyE, hy1, hfixY g hg⟩
    · intro g hg
      rw [Subgroup.mem_comap]
      exact Subgroup.subset_closure ⟨x, hxE, hx1, hfixX g hg⟩
  have hclos : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have h1 : conjUnit P⁻¹ k ∈ (Subgroup.closure S).comap (conjUnit P) := by
      rw [hK]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_comap, heisGen_conjUnit_conjUnit_inv] at h1
    exact h1
  exact planeGen_of_closure_fixSL hn hclos

end Main

theorem outdiagHeisenbergPlanes_of_singer
    (hG : ∀ (F : Type) [Field F] [Finite F] (p : ℕ), p.Prime → 5 ≤ p → p ∣ Nat.card F - 1 →
      SingerTorusGen F p) : OutdiagHeisenbergPlanes := by
  intro F _ _ p hp5 hp _ E hE _ hpair
  obtain ⟨A, B, hAE, hBE, hAB⟩ := hpair
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn3 : 3 ≤ p := by omega
  obtain ⟨u, hu⟩ := exists_scalarGL_comm hn3 hE.1 hAE hBE
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hAB
    rw [hu, map_one, one_mul]
  have hup : u ^ p = 1 := by
    have hdet := congrArg GeneralLinearGroup.det hu
    rw [map_mul, map_mul, map_mul, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units,
      mul_comm (GeneralLinearGroup.det B)] at hdet
    exact mul_right_cancel (b := GeneralLinearGroup.det A * GeneralLinearGroup.det B)
      (by rw [one_mul, ← hdet])
  have hprim : IsPrimitiveRoot u p := by
    rw [← orderOf_eq_prime hup hu1]
    exact IsPrimitiveRoot.orderOf u
  have hdiv : p ∣ Nat.card F - 1 := by
    rw [← Nat.card_units]
    have h1 := orderOf_dvd_natCard u
    rwa [← hprim.eq_orderOf] at h1
  obtain ⟨a, ha⟩ := exists_scalarGL_pow hn3 hE.1 hAE
  obtain ⟨b, hb⟩ := exists_scalarGL_pow hn3 hE.1 hBE
  obtain ⟨i, j, hij, l, hl⟩ := sgo_exists_pow_isPow hp hprim a b
  have hz : ∀ g : GL (Fin p) F, GeneralLinearGroup.scalar (Fin p) u * g =
      g * GeneralLinearGroup.scalar (Fin p) u := fun g => (mul_scalarGL_comm u g).symm
  have hzn : ∀ (n : ℕ) (g : GL (Fin p) F), (GeneralLinearGroup.scalar (Fin p) u) ^ n * g =
      g * (GeneralLinearGroup.scalar (Fin p) u) ^ n :=
    fun n g => (Commute.pow_left (hz g) n).eq
  have hsc : ∀ g : GL (Fin p) F, GeneralLinearGroup.scalar (Fin p) l⁻¹ * g =
      g * GeneralLinearGroup.scalar (Fin p) l⁻¹ := fun g => (mul_scalarGL_comm l⁻¹ g).symm
  have hzp : (GeneralLinearGroup.scalar (Fin p) u) ^ p = 1 := by
    rw [← map_pow, hup, map_one]
  have hy0p : (A ^ i * B ^ j) ^ p = GeneralLinearGroup.scalar (Fin p) (a ^ i * b ^ j) := by
    have hBj : B ^ j * A = (GeneralLinearGroup.scalar (Fin p) u) ^ j * (A * B ^ j) :=
      sgo_pow_left_comm hz hu j
    have hBji : B ^ j * A ^ i =
        ((GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i * (A ^ i * B ^ j) :=
      sgo_comm_pow_right (hzn j) hBj i
    have hcen : ∀ g : GL (Fin p) F, ((GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i * g =
        g * ((GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i := fun g =>
      (Commute.pow_left (Commute.pow_left (hz g) j) i).eq
    rw [sgo_mul_pow hcen hBji p]
    have hw : ((GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i =
        (GeneralLinearGroup.scalar (Fin p) u) ^ (j * i) := (pow_mul _ _ _).symm
    have hwp : (((GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i) ^ p = 1 := by
      rw [hw, ← pow_mul, mul_comm (j * i) p, pow_mul, hzp, one_pow]
    obtain ⟨k, hk⟩ := hp.dvd_choose_self (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 < p)
    have hzk : (((GeneralLinearGroup.scalar (Fin p) u) ^ j) ^ i) ^ (p.choose 2) = 1 := by
      rw [hk, pow_mul, hwp, one_pow]
    rw [hzk, one_mul]
    have e1 : (A ^ i) ^ p = (GeneralLinearGroup.scalar (Fin p) a) ^ i := by
      rw [← pow_mul, mul_comm i p, pow_mul, ha]
    have e2 : (B ^ j) ^ p = (GeneralLinearGroup.scalar (Fin p) b) ^ j := by
      rw [← pow_mul, mul_comm j p, pow_mul, hb]
    rw [e1, e2, ← map_pow, ← map_pow, ← map_mul]
  have hy : (GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j)) ^ p = 1 := by
    have hc : Commute (GeneralLinearGroup.scalar (Fin p) l⁻¹) (A ^ i * B ^ j) :=
      (mul_scalarGL_comm l⁻¹ (A ^ i * B ^ j)).symm
    rw [hc.mul_pow, hy0p, ← map_pow, ← map_mul, inv_pow, ← hl, inv_mul_cancel, map_one]
  have hyE : conjAut p F (GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j)) ∈ E := by
    rw [map_mul, map_mul, map_pow, map_pow, conjAut_scalar, one_mul]
    exact E.mul_mem (E.pow_mem hAE i) (E.pow_mem hBE j)
  by_cases hj : p ∣ j
  ·
    have hi : ¬ p ∣ i := fun hi => hij ⟨hi, hj⟩
    have hcop : Nat.Coprime i p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hi).symm
    have hprimw : IsPrimitiveRoot (((u ^ i)⁻¹ : Fˣ) : F) p :=
      IsPrimitiveRoot.coe_units_iff.2 ((hprim.pow_of_coprime i hcop).inv)
    have hBi : B * A ^ i = (GeneralLinearGroup.scalar (Fin p) u) ^ i * (A ^ i * B) :=
      sgo_comm_pow_right hz hu i
    have hBy0 : B * (A ^ i * B ^ j) =
        (GeneralLinearGroup.scalar (Fin p) u) ^ i * ((A ^ i * B ^ j) * B) := by
      calc B * (A ^ i * B ^ j) = (B * A ^ i) * B ^ j := (mul_assoc _ _ _).symm
        _ = ((GeneralLinearGroup.scalar (Fin p) u) ^ i * (A ^ i * B)) * B ^ j := by rw [hBi]
        _ = (GeneralLinearGroup.scalar (Fin p) u) ^ i * ((A ^ i * B) * B ^ j) := by
            rw [mul_assoc]
        _ = (GeneralLinearGroup.scalar (Fin p) u) ^ i * ((A ^ i * B ^ j) * B) := by
            rw [mul_assoc (A ^ i) B (B ^ j), (Commute.self_pow B j).eq]
            simp only [mul_assoc]
    have hrelBy : B * (GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j)) =
        (GeneralLinearGroup.scalar (Fin p) u) ^ i *
          ((GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j)) * B) := by
      calc B * (GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j))
          = GeneralLinearGroup.scalar (Fin p) l⁻¹ * (B * (A ^ i * B ^ j)) := by
            rw [← mul_assoc, ← hsc B, mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin p) l⁻¹ * ((GeneralLinearGroup.scalar (Fin p) u) ^ i *
              ((A ^ i * B ^ j) * B)) := by rw [hBy0]
        _ = (GeneralLinearGroup.scalar (Fin p) u) ^ i * (GeneralLinearGroup.scalar (Fin p) l⁻¹ *
              ((A ^ i * B ^ j) * B)) := by
            rw [← mul_assoc, hsc ((GeneralLinearGroup.scalar (Fin p) u) ^ i), mul_assoc]
        _ = (GeneralLinearGroup.scalar (Fin p) u) ^ i *
              ((GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j)) * B) := by
            simp only [mul_assoc]
    have hyx : (GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j)) * B =
        GeneralLinearGroup.scalar (Fin p) ((u ^ i)⁻¹) *
          (B * (GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j))) := by
      rw [hrelBy, ← map_pow, ← mul_assoc (GeneralLinearGroup.scalar (Fin p) ((u ^ i)⁻¹))
        (GeneralLinearGroup.scalar (Fin p) (u ^ i)), ← map_mul, inv_mul_cancel, map_one, one_mul]
    exact sgo_planeGen_pair hp hp5 (hG F p hp hp5 hdiv) hE hprimw hb hy hyx hBE hyE
  ·
    have hcop : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hj).symm
    have hprimw : IsPrimitiveRoot (((u ^ j : Fˣ)) : F) p :=
      IsPrimitiveRoot.coe_units_iff.2 (hprim.pow_of_coprime j hcop)
    have hBj : B ^ j * A = (GeneralLinearGroup.scalar (Fin p) u) ^ j * (A * B ^ j) :=
      sgo_pow_left_comm hz hu j
    have hy0A : (A ^ i * B ^ j) * A =
        (GeneralLinearGroup.scalar (Fin p) u) ^ j * (A * (A ^ i * B ^ j)) := by
      calc (A ^ i * B ^ j) * A = A ^ i * (B ^ j * A) := mul_assoc _ _ _
        _ = A ^ i * ((GeneralLinearGroup.scalar (Fin p) u) ^ j * (A * B ^ j)) := by rw [hBj]
        _ = (GeneralLinearGroup.scalar (Fin p) u) ^ j * (A ^ i * (A * B ^ j)) := by
            rw [← mul_assoc, (hzn j (A ^ i)).symm, mul_assoc]
        _ = (GeneralLinearGroup.scalar (Fin p) u) ^ j * (A * (A ^ i * B ^ j)) := by
            rw [← mul_assoc (A ^ i) A (B ^ j), ← (Commute.self_pow A i).eq, mul_assoc A]
    have hyx : (GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j)) * A =
        GeneralLinearGroup.scalar (Fin p) (u ^ j) *
          (A * (GeneralLinearGroup.scalar (Fin p) l⁻¹ * (A ^ i * B ^ j))) := by
      rw [mul_assoc, hy0A, map_pow]
      rw [← mul_assoc (GeneralLinearGroup.scalar (Fin p) l⁻¹)
          ((GeneralLinearGroup.scalar (Fin p) u) ^ j),
        hsc ((GeneralLinearGroup.scalar (Fin p) u) ^ j),
        mul_assoc ((GeneralLinearGroup.scalar (Fin p) u) ^ j),
        ← mul_assoc (GeneralLinearGroup.scalar (Fin p) l⁻¹) A, hsc A, mul_assoc A]
    exact sgo_planeGen_pair hp hp5 (hG F p hp hp5 hdiv) hE hprimw ha hy hyx hAE hyE

end CFSG.LieType.SeitzGeneration

end
