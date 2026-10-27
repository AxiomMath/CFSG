module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryNorm

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]

theorem eq_smul_one_of_commute_diag {M : Matrix (Fin 3) (Fin 3) K} {a b c : K}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : M * (!![a, 0, 0; 0, b, 0; 0, 0, c] : Matrix (Fin 3) (Fin 3) K) =
      !![a, 0, 0; 0, b, 0; 0, 0, c] * M)
    (h2 : M * (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] * M) :
    M = M 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have aux : ∀ {X x y : K}, x ≠ y → X * y = x * X → X = 0 := fun {X x y} hxy h => by
    have h' : X * (y - x) = 0 := by rw [mul_sub, h, mul_comm, sub_self]
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr hxy.symm)
  have e : ∀ i j, (M * (!![a, 0, 0; 0, b, 0; 0, 0, c] : Matrix (Fin 3) (Fin 3) K)) i j =
      ((!![a, 0, 0; 0, b, 0; 0, 0, c] : Matrix (Fin 3) (Fin 3) K) * M) i j :=
    fun i j => by rw [h1]
  have cc : ∀ i j, (M * (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K)) i j =
      ((!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) * M) i j := fun i j => by
    rw [h2]
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have c02 := cc 0 2
  have c10 := cc 1 0
  simp [mul_apply, Fin.sum_univ_three] at e01 e02 e10 e12 e20 e21 c02 c10
  have m01 : M 0 1 = 0 := aux hab e01
  have m02 : M 0 2 = 0 := aux hac e02
  have m10 : M 1 0 = 0 := aux hab.symm e10
  have m12 : M 1 2 = 0 := aux hbc e12
  have m20 : M 2 0 = 0 := aux hac.symm e20
  have m21 : M 2 1 = 0 := aux hbc.symm e21
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m12, m20, m21, c02, c10]


section Unitary

variable {p f : ℕ}

@[expose] def diagInv (t : Kˣ) : GL (Fin 3) K :=
  ⟨!![(t : K), 0, 0; 0, ((t⁻¹ : Kˣ) : K), 0; 0, 0, 1],
    !![((t⁻¹ : Kˣ) : K), 0, 0; 0, (t : K), 0; 0, 0, 1],
    by
      have h : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
      have h' : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by simp
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h, h'],
    by
      have h : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
      have h' : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by simp
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h, h']⟩

theorem coe_diagInv (t : Kˣ) :
    ((diagInv t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![(t : K), 0, 0; 0, ((t⁻¹ : Kˣ) : K), 0; 0, 0, 1] := rfl

theorem diagInv_mem_unitarySU (h : UnitaryFieldData p f K) {t : Kˣ} (ht : (t : K) * h.bar t = 1) :
    diagInv t ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h]
  have h1 : ((t⁻¹ : Kˣ) : K) = (t : K)⁻¹ := by simp
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  refine ⟨?_, ?_⟩
  · rw [coe_diagInv, det_fin_three]
    simp [h1, ht0]
  · have hb : (h.bar (t : K))⁻¹ * (t : K)⁻¹ = 1 := by
      have : (h.bar (t : K))⁻¹ * (t : K)⁻¹ = ((t : K) * h.bar t)⁻¹ := by
        rw [mul_inv, mul_comm]
      rw [this, ht, inv_one]
    have hb' : h.bar (t : K) * (t : K) = 1 := by rw [mul_comm]; exact ht
    rw [coe_diagInv]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, transpose_apply, h1, hb, hb']


theorem exists_norm_one_sq_ne (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    ∃ t : Kˣ, (t : K) * h.bar t = 1 ∧ t ^ 2 ≠ 1 := by
  have hfin := h.finite
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
    rw [Nat.card_units, h.card, pow_mul']
  have hord : orderOf ζ = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, hcard]
  set q := p ^ f with hqdef
  have hq1 : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [hk]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  refine ⟨ζ ^ (q - 1), ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val, h.bar_apply, ← pow_mul, ← pow_add]
    have e : (q - 1) + (q - 1) * p ^ f = (q - 1) * (q + 1) := by rw [← hqdef]; ring
    rw [e, hq1]
    have h1 := pow_orderOf_eq_one ζ
    rw [hord] at h1
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa using h2
  · intro h2
    have h3 : orderOf ζ ∣ (q - 1) * 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact h2
    rw [hord, ← hq1] at h3
    have h4 := Nat.le_of_dvd (by omega) h3
    have h5 := Nat.le_of_mul_le_mul_left h4 (by omega)
    omega


theorem eq_smul_one_of_commute_su (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {M : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ x ∈ unitarySU p f K 3,
      M * (x : Matrix (Fin 3) (Fin 3) K) = (x : Matrix (Fin 3) (Fin 3) K) * M) :
    M = M 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨t, ht, ht2⟩ := exists_norm_one_sq_ne h hq
  have h1 := hM _ (diagInv_mem_unitarySU h ht)
  have h2 := hM _ (cycThree_mem_slPi (π := false) (K := K) (p := p) (f := f) (fun _ => h))
  rw [coe_diagInv] at h1
  rw [coe_cycThree] at h2
  have ht1 : (t : K) ≠ 1 := fun h' => ht2 (by
    have : t = 1 := Units.ext h'
    rw [this, one_pow])
  have htt : (t : K) ≠ ((t⁻¹ : Kˣ) : K) := by
    intro h'
    apply ht2
    have : t = t⁻¹ := Units.ext h'
    calc t ^ 2 = t * t := sq t
      _ = t * t⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel t
  have hti1 : ((t⁻¹ : Kˣ) : K) ≠ 1 := fun h' => ht1 (by
    have : t⁻¹ = 1 := Units.ext h'
    have h3 : t = 1 := by simpa using this
    rw [h3]; rfl)
  exact eq_smul_one_of_commute_diag htt ht1 hti1 h1 h2

omit [Field K] in
theorem comm_of_aux {R : Type*} [Ring R] {G Gi X Xi TG TGi TX : R} (hGiG : Gi * G = 1)
    (hXXi : X * Xi = 1) (hT1 : TG * TGi = 1) (hTX : TX = Xi)
    (h : TGi * TX * TG * (G * X * Gi) = 1) : (TG * G) * X = X * (TG * G) := by
  have h0 := congrArg (TG * ·) h
  simp only [mul_one, hTX] at h0
  have h1 : Xi * (TG * G) * X * Gi = TG := by
    calc Xi * (TG * G) * X * Gi = (TG * TGi) * Xi * TG * (G * X * Gi) := by
          rw [hT1, one_mul]; simp only [mul_assoc]
      _ = TG * (TGi * Xi * TG * (G * X * Gi)) := by simp only [mul_assoc]
      _ = TG := h0
  have h2 : Xi * (TG * G) * X = TG * G := by
    calc Xi * (TG * G) * X = Xi * (TG * G) * X * (Gi * G) := by rw [hGiG, mul_one]
      _ = (Xi * (TG * G) * X * Gi) * G := by simp only [mul_assoc]
      _ = TG * G := by rw [h1]
  calc (TG * G) * X = (X * Xi) * (TG * G) * X := by rw [hXXi, one_mul]
    _ = X * (Xi * (TG * G) * X) := by simp only [mul_assoc]
    _ = X * (TG * G) := by rw [h2]


@[expose] noncomputable def tbar (h : UnitaryFieldData p f K) (A : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K :=
  (A.map h.bar)ᵀ

theorem tbar_mul (h : UnitaryFieldData p f K) (A B : Matrix (Fin 3) (Fin 3) K) :
    tbar h (A * B) = tbar h B * tbar h A := by
  simp [tbar, Matrix.map_mul, Matrix.transpose_mul]

theorem tbar_one (h : UnitaryFieldData p f K) : tbar h (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  simp [tbar]

theorem tbar_tbar (h : UnitaryFieldData p f K) (A : Matrix (Fin 3) (Fin 3) K) :
    tbar h (tbar h A) = A := by
  ext i j
  simp [tbar, UnitaryFieldData.bar_bar]

theorem tbar_smul (h : UnitaryFieldData p f K) (c : K) (A : Matrix (Fin 3) (Fin 3) K) :
    tbar h (c • A) = h.bar c • tbar h A := by
  ext i j
  simp [tbar]

theorem commute_tbar_mul_of_normalizes (h : UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ Subgroup.normalizer (unitarySU p f K 3 : Set (GL (Fin 3) K)))
    {x : GL (Fin 3) K} (hx : x ∈ unitarySU p f K 3) :
    (tbar h (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) *
        (x : Matrix (Fin 3) (Fin 3) K) =
      (x : Matrix (Fin 3) (Fin 3) K) *
        (tbar h (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) := by
  have hx' : g * x * g⁻¹ ∈ unitarySU p f K 3 := (Subgroup.mem_normalizer_iff.1 hg x).1 hx
  have e1 := ((mem_unitarySU_iff h).1 hx').2
  have e2 := ((mem_unitarySU_iff h).1 hx).2
  have hGiG : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)
      = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXXi : (x : Matrix (Fin 3) (Fin 3) K) * ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hT1 : tbar h (g : Matrix (Fin 3) (Fin 3) K) *
      tbar h ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← tbar_mul, hGiG, tbar_one]
  have hTX : tbar h (x : Matrix (Fin 3) (Fin 3) K) =
      ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    calc tbar h (x : Matrix (Fin 3) (Fin 3) K) =
        tbar h (x : Matrix (Fin 3) (Fin 3) K) * ((x : Matrix (Fin 3) (Fin 3) K) *
          ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by rw [hXXi, mul_one]
      _ = (tbar h (x : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)) *
          ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [show tbar h (x : Matrix (Fin 3) (Fin 3) K) *
          (x : Matrix (Fin 3) (Fin 3) K) = 1 from e2, Matrix.one_mul]
  refine comm_of_aux hGiG hXXi hT1 hTX ?_
  have e1' : tbar h (((g * x * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
      ((g * x * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := e1
  simp only [Units.val_mul, tbar_mul, Matrix.mul_assoc] at e1' ⊢
  exact e1'


theorem tbar_mul_tbar_inv (h : UnitaryFieldData p f K) (g : GL (Fin 3) K) :
    tbar h (g : Matrix (Fin 3) (Fin 3) K) *
      tbar h ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← tbar_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, tbar_one]

theorem exists_isom_of_normalizes (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) {g : GL (Fin 3) K}
    (hg : g ∈ Subgroup.normalizer (unitarySU p f K 3 : Set (GL (Fin 3) K))) :
    ∃ (c : Kˣ) (u : GL (Fin 3) K), u ∈ unitaryIsom3 h ∧
      g = GeneralLinearGroup.scalar (Fin 3) c * u := by
  have hfin := h.finite
  have hmx := eq_smul_one_of_commute_su h hq
    (M := tbar h (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K))
    (fun x hx => commute_tbar_mul_of_normalizes h hg hx)
  set d : K := (tbar h (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) 0 0
    with hd
  have hTu : IsUnit (tbar h (g : Matrix (Fin 3) (Fin 3) K)) :=
    ⟨⟨_, tbar h ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), tbar_mul_tbar_inv h g,
      by simpa using tbar_mul_tbar_inv h g⁻¹⟩, rfl⟩
  have hmu : IsUnit (tbar h (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) :=
    hTu.mul g.isUnit
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hmx
    rw [hmx] at hmu
    exact not_isUnit_zero hmu
  have hherm : tbar h (tbar h (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) =
      tbar h (g : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [tbar_mul, tbar_tbar]
  have hbar : h.bar d = d := by
    have h3 : tbar h (d • (1 : Matrix (Fin 3) (Fin 3) K)) = d • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hmx]; exact hherm
    rw [tbar_smul, tbar_one] at h3
    have := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 0 0) h3
    simpa using this
  obtain ⟨τ, hτ, hτo, -⟩ := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.exists_bar_ringEquiv h
  obtain ⟨l, hl0, hl⟩ := CFSG.GH74.GLS.IVK.H90.exists_prod_pow_eq τ d⁻¹
    (by rw [hτ, map_inv₀, hbar]) (inv_ne_zero hd0)
  rw [hτo, Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one,
    RingAut.one_apply, hτ] at hl
  have hcl : h.bar l * l * d = 1 := by
    rw [mul_comm (h.bar l) l, hl]
    exact inv_mul_cancel₀ hd0
  refine ⟨(Units.mk0 l hl0)⁻¹, GeneralLinearGroup.scalar (Fin 3) (Units.mk0 l hl0) * g, ?_, ?_⟩
  · have hu : ((GeneralLinearGroup.scalar (Fin 3) (Units.mk0 l hl0) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = l • (g : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      simp [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul]
    rw [mem_unitaryIsom3]
    change tbar h _ * _ = 1
    rw [hu, tbar_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hmx, smul_smul, hcl, one_smul]
  · rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

end Unitary

section Models

theorem psiO_mk_conj {F : Type} [Field F] (A : GL (Fin 3) F) (M₀ M' : ↥(CFSG.Open.StatedSL 3 F))
    (hM' : (M' : GL (Fin 3) F) = A * M₀ * A⁻¹) :
    psiO F (QuotientGroup.mk M') = conjAut 3 F A (psiO F (QuotientGroup.mk M₀)) := by
  obtain ⟨s, rfl⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective M₀
  have h1 : (QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s) :
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F)) = mkO F s := rfl
  rw [h1, psiO_mkO, conjAut_proj]
  have h3 : M' = specialLinearGroupEquivStatedSL 3 F
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A s) := by
    apply Subtype.ext
    apply Units.ext
    simp only [hM', Units.val_mul, specialLinearGroupEquivStatedSL_coe, coe_slConjugation]
  rw [h3]
  exact psiO_mkO F _


theorem congr_psiO_mem_linearAutGroup {F : Type} [Field F]
    {φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F))}
    (hφ : Lemma54Ns.IsConjByGL (CFSG.Open.StatedSL 3 F) φ) :
    MulAut.congr (psiO F) φ ∈ linearAutGroup 3 F := by
  obtain ⟨g, hg, hφ⟩ := hφ
  have : MulAut.congr (psiO F) φ = conjAut 3 F g := by
    ext x
    obtain ⟨z, rfl⟩ := (psiO F).surjective x
    obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective z
    have hM' : g * (M : GL (Fin 3) F) * g⁻¹ ∈ CFSG.Open.StatedSL 3 F :=
      (Subgroup.mem_normalizer_iff.1 hg M).1 M.2
    change psiO F (φ ((psiO F).symm (psiO F (QuotientGroup.mk M)))) = _
    rw [MulEquiv.symm_apply_apply, hφ M ⟨_, hM'⟩ rfl]
    exact psiO_mk_conj g M ⟨_, hM'⟩ rfl
  rw [this]
  exact conjAut_mem_linearAutGroup g


section UnitaryModels

variable {p f : ℕ}

theorem congr_psuO_mem_psuConj_range (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) K))}
    (hφ : Lemma54Ns.IsConjByGL (CFSG.Open.StatedSU 3 (p ^ f) K) φ) :
    MulAut.congr (psuO h).symm φ ∈ (psuConj h).range := by
  obtain ⟨g, hg, hφ⟩ := hφ
  obtain ⟨c, u, hu, rfl⟩ := exists_isom_of_normalizes h hq hg
  refine ⟨⟨u, hu⟩, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := unitaryProj_surjective h 3 x
  have hA' : (GeneralLinearGroup.scalar (Fin 3) c * u) * (y : GL (Fin 3) K) *
      (GeneralLinearGroup.scalar (Fin 3) c * u)⁻¹ ∈ unitarySU p f K 3 :=
    (Subgroup.mem_normalizer_iff.1 hg y).1 y.2
  have h2 : φ (psuO h (unitaryProj h 3 y)) = QuotientGroup.mk (⟨_, hA'⟩ :
      ↥(CFSG.Open.StatedSU 3 (p ^ f) K)) := by
    rw [psuO_proj]
    exact hφ y ⟨_, hA'⟩ rfl
  simp only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply]
  rw [h2]
  have h4 : (psuO h).symm (QuotientGroup.mk (⟨_, hA'⟩ : ↥(CFSG.Open.StatedSU 3 (p ^ f) K))) =
      unitaryProj h 3 ⟨_, hA'⟩ := by
    rw [MulEquiv.symm_apply_eq, psuO_proj]
  rw [h4]
  change psuConj h ⟨u, hu⟩ (QuotientGroup.mk y) = QuotientGroup.mk _
  rw [psuConj_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suConj]
  have hc : ∀ w : GL (Fin 3) K, GeneralLinearGroup.scalar (Fin 3) c * w =
      w * GeneralLinearGroup.scalar (Fin 3) c := fun w => (commute_scalar c w).eq.symm
  have key : ∀ w : GL (Fin 3) K, GeneralLinearGroup.scalar (Fin 3) c * w *
      (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ = w := fun w => by rw [hc w]; group
  show u * (y : GL (Fin 3) K) * u⁻¹ = (GeneralLinearGroup.scalar (Fin 3) c * u) *
    (y : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) c * u)⁻¹
  rw [show (GeneralLinearGroup.scalar (Fin 3) c * u) * (y : GL (Fin 3) K) *
      (GeneralLinearGroup.scalar (Fin 3) c * u)⁻¹ = GeneralLinearGroup.scalar (Fin 3) c *
        (u * (y : GL (Fin 3) K) * u⁻¹) * (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ by group, key]

end UnitaryModels

end Models

section Data

theorem inndiagPSL3_data {Y : Type*} [Group Y] {α : MulAut Y} (hα : Lemma54Ns.IsInnDiagPSL3 α) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 F),
      MulAut.congr e (centerDescend Y α) ∈ (stdPinnedPSL 3 F).inndiag := by
  obtain ⟨F, _, _, θ, φ, hφ, hα⟩ := hα
  refine ⟨F, inferInstance, inferInstance, θ.trans (psiO F), ?_⟩
  have : MulAut.congr (θ.trans (psiO F)) (centerDescend Y α) = MulAut.congr (psiO F) φ := by
    ext x
    obtain ⟨z, rfl⟩ := (θ.trans (psiO F)).surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    rw [descend_apply_mk (θ.trans (psiO F)) α y]
    simp only [MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.symm_apply_apply]
    rw [hα y]
  rw [this, stdPinnedPSL_inndiag]
  exact congr_psiO_mem_linearAutGroup hφ

theorem inndiagPSU3_data {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) {α : MulAut Y}
    (hα : Lemma54Ns.IsInnDiagPSU3 α) :
    ∃ (p f : ℕ) (F : Type) (_ : Field F) (hF : UnitaryFieldData p f F)
      (e : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3),
      MulAut.congr e (centerDescend Y α) ∈ (stdPinnedPSU3 hF).inndiag := by
  obtain ⟨F, _, _, q, θ, φ, hcard, hφ, hα⟩ := hα
  obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
  refine ⟨p, f, F, inferInstance, hF, θ.trans (psuO hF).symm, ?_⟩
  have hq := two_lt_pow_of_quasisimple hY hF (θ.trans (psuO hF).symm)
  have : MulAut.congr (θ.trans (psuO hF).symm) (centerDescend Y α) = MulAut.congr (psuO hF).symm φ := by
    ext x
    obtain ⟨z, rfl⟩ := (θ.trans (psuO hF).symm).surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    rw [descend_apply_mk (θ.trans (psuO hF).symm) α y]
    simp only [MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.symm_symm]
    rw [hα y]
    simp only [MulEquiv.apply_symm_apply]
  rw [this]
  exact congr_psuO_mem_psuConj_range hF hq hφ

theorem input7_fieldInnDiag_holds : Lemma54Ns.Input7_FieldInnDiag := by
  intro K _ _ hK α hα hin
  rcases hin with hL | hU
  · obtain ⟨F, _, _, e, hmem⟩ := inndiagPSL3_data hL
    exact eq_one_of_inndiag_model hK (goodPinned_psl F) e hmem hα
  · obtain ⟨p, f, F, _, hF, e, hmem⟩ := inndiagPSU3_data hK hU
    have hq := two_lt_pow_of_quasisimple hK hF e
    exact eq_one_of_inndiag_model hK (goodPinned_psu hF hq) e hmem hα

end Data

end CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
