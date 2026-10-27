module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneTorus
public import CFSG.LinearAlgebra.ProjectivePrimePlane

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup

variable {K : Type*} [Field K] {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem scalar_mem_center' (u : Kˣ) :
    GeneralLinearGroup.scalar (Fin p) u ∈ Subgroup.center (GL (Fin p) K) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, rfl⟩

omit [NeZero p] in
theorem mul_scalar_comm (u : Kˣ) (g : GL (Fin p) K) :
    g * GeneralLinearGroup.scalar (Fin p) u = GeneralLinearGroup.scalar (Fin p) u * g :=
  Subgroup.mem_center_iff.1 (scalar_mem_center' u) g

theorem scalar_injective' :
    Function.Injective (GeneralLinearGroup.scalar (Fin p) : Kˣ →* GL (Fin p) K) := by
  intro u v h
  have h1 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K) 0 0) h
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h1
  exact Units.ext h1

variable (P : GL (Fin p) K)

omit [NeZero p] in
theorem exists_scalar_of_commute_torus {M : GL (Fin p) K} {x : Fin p → Kˣ}
    (h : torusHom P x * mk M = mk M * torusHom P x) :
    ∃ c : Kˣ, (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL x =
      GeneralLinearGroup.scalar (Fin p) c *
        (TauCeti.diagGL x * (P⁻¹ * (M : GL (Fin p) K) * P)) := by
  rw [torusHom_apply] at h
  obtain ⟨u, hu⟩ := CFSG.LinearAlgebra.ProjectivePrimePlane.exists_mul_eq_smul_of_commute h
  have hMA := CFSG.LinearAlgebra.ProjectivePrimePlane.mul_eq_scalar_mul_of_val hu
  refine ⟨u, ?_⟩
  calc (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL x =
      P⁻¹ * (M * (P * TauCeti.diagGL x * P⁻¹)) * P := by group
    _ = P⁻¹ * GeneralLinearGroup.scalar (Fin p) u *
        ((P * TauCeti.diagGL x * P⁻¹) * M) * P := by rw [hMA]; group
    _ = GeneralLinearGroup.scalar (Fin p) u * P⁻¹ *
        ((P * TauCeti.diagGL x * P⁻¹) * M) * P := by rw [mul_scalar_comm]
    _ = _ := by group

omit [NeZero p] in
theorem eq_mul_of_entry_ne_zero {N : GL (Fin p) K} {x : Fin p → Kˣ} {c : Kˣ}
    (h : N * TauCeti.diagGL x = GeneralLinearGroup.scalar (Fin p) c * (TauCeti.diagGL x * N))
    {i j : Fin p} (hij : (N : Matrix (Fin p) (Fin p) K) i j ≠ 0) :
    (x j : K) = c * x i := by
  have h1 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K) i j) h
  simp only [Units.val_mul, TauCeti.diagGL_coe, mul_diagonal, GeneralLinearGroup.coe_scalar,
    scalar_apply, diagonal_mul] at h1
  have h2 : ((x j : K) - c * x i) * (N : Matrix (Fin p) (Fin p) K) i j = 0 := by
    linear_combination h1
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hij)

omit [NeZero p] in
theorem exists_entry_ne_zero (N : GL (Fin p) K) (i : Fin p) :
    ∃ j, (N : Matrix (Fin p) (Fin p) K) i j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 := det_eq_zero_of_row_eq_zero i h
  have h1 := (Matrix.isUnit_iff_isUnit_det _).1 N.isUnit
  rw [h0] at h1
  exact not_isUnit_zero h1

@[expose] def rootVec (ζ : Kˣ) : Fin p → Kˣ := fun i => ζ ^ (i : ℕ)

abbrev frameElt (ζ : Kˣ) : ProjGenLinGroup (Fin p) K :=
  torusHom P (rootVec ζ)

abbrev framePre (ζ : Kˣ) : Subgroup (GL (Fin p) K) :=
  (Subgroup.centralizer {frameElt P ζ}).comap mk

variable (ζ : Kˣ)

omit [NeZero p] in
theorem framePre_rel [NeZero p] (M : framePre P ζ) :
    ∃ c : Kˣ, (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c *
        (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (M : GL (Fin p) K) * P)) :=
  exists_scalar_of_commute_torus P (Subgroup.mem_centralizer_iff.1 M.2 _ rfl)

@[expose] noncomputable def frameScalarFun (M : framePre P ζ) : Kˣ :=
  (framePre_rel P ζ M).choose

theorem frameScalarFun_spec (M : framePre P ζ) :
    (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL (rootVec ζ) = GeneralLinearGroup.scalar (Fin p)
      (frameScalarFun P ζ M) * (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (M : GL (Fin p) K) * P)) :=
  (framePre_rel P ζ M).choose_spec

omit [NeZero p] in
theorem frame_scalar_unique [NeZero p] {N : GL (Fin p) K} {c c' : Kˣ}
    (h : N * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c * (TauCeti.diagGL (rootVec ζ) * N))
    (h' : N * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c' * (TauCeti.diagGL (rootVec ζ) * N)) : c = c' :=
  scalar_injective' (mul_right_cancel (h.symm.trans h'))

theorem frameScalarFun_eq (M : framePre P ζ) {c : Kˣ}
    (h : (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c *
        (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (M : GL (Fin p) K) * P))) :
    frameScalarFun P ζ M = c :=
  frame_scalar_unique ζ (frameScalarFun_spec P ζ M) h

@[expose] noncomputable def frameScalarHat : framePre P ζ →* Kˣ where
  toFun := frameScalarFun P ζ
  map_one' := frameScalarFun_eq P ζ 1 (by
    rw [OneMemClass.coe_one, mul_one, inv_mul_cancel, map_one, one_mul, one_mul, mul_one])
  map_mul' M₁ M₂ := by
    refine frameScalarFun_eq P ζ (M₁ * M₂) ?_
    have h1 := frameScalarFun_spec P ζ M₁
    have h2 := frameScalarFun_spec P ζ M₂
    have hN : P⁻¹ * ((M₁ * M₂ : framePre P ζ) : GL (Fin p) K) * P =
        (P⁻¹ * (M₁ : GL (Fin p) K) * P) * (P⁻¹ * (M₂ : GL (Fin p) K) * P) := by
      rw [Subgroup.coe_mul]
      group
    set D := TauCeti.diagGL (rootVec ζ)
    set N₁ := P⁻¹ * (M₁ : GL (Fin p) K) * P
    set N₂ := P⁻¹ * (M₂ : GL (Fin p) K) * P
    set S₁ := GeneralLinearGroup.scalar (Fin p) (frameScalarFun P ζ M₁)
    set S₂ := GeneralLinearGroup.scalar (Fin p) (frameScalarFun P ζ M₂)
    have hc : ∀ g : GL (Fin p) K, g * S₂ = S₂ * g := fun g => mul_scalar_comm _ g
    rw [hN, map_mul]
    calc N₁ * N₂ * D = N₁ * (N₂ * D) := by group
      _ = N₁ * (S₂ * (D * N₂)) := by rw [h2]
      _ = N₁ * S₂ * (D * N₂) := by group
      _ = S₂ * N₁ * (D * N₂) := by rw [hc N₁]
      _ = S₂ * (N₁ * D) * N₂ := by group
      _ = S₂ * (S₁ * (D * N₁)) * N₂ := by rw [h1]
      _ = S₂ * S₁ * (D * (N₁ * N₂)) := by group
      _ = S₁ * S₂ * (D * (N₁ * N₂)) := by rw [hc S₁]

theorem frameScalarHat_spec (M : framePre P ζ) :
    (P⁻¹ * (M : GL (Fin p) K) * P) * TauCeti.diagGL (rootVec ζ) = GeneralLinearGroup.scalar (Fin p)
      (frameScalarHat P ζ M) * (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (M : GL (Fin p) K) * P)) :=
  frameScalarFun_spec P ζ M

theorem ker_mk_le_ker_frameScalarHat :
    (mk.subgroupComap (Subgroup.centralizer {frameElt P ζ})).ker ≤
      (frameScalarHat P ζ).ker := by
  intro M hM
  rw [MonoidHom.mem_ker] at hM ⊢
  have hM' : mk (M : GL (Fin p) K) = 1 := congrArg Subtype.val hM
  rw [mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hM'
  obtain ⟨u, hu⟩ := hM'
  refine frameScalarFun_eq P ζ M ?_
  have hPs : P⁻¹ * GeneralLinearGroup.scalar (Fin p) u * P =
      GeneralLinearGroup.scalar (Fin p) u := by
    rw [mul_assoc, ← mul_scalar_comm u P, inv_mul_cancel_left]
  rw [← hu, hPs, map_one, one_mul]
  exact (mul_scalar_comm u _).symm

@[expose] noncomputable def frameScalar :
    Subgroup.centralizer {frameElt P ζ} →* Kˣ :=
  (mk.subgroupComap (Subgroup.centralizer {frameElt P ζ})).liftOfSurjective
    (mk.subgroupComap_surjective _ mk_surjective)
    ⟨frameScalarHat P ζ, ker_mk_le_ker_frameScalarHat P ζ⟩

theorem frameScalar_mk (M : framePre P ζ) :
    frameScalar P ζ (mk.subgroupComap _ M) = frameScalarHat P ζ M :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ M

omit [NeZero p] in
theorem exists_framePre (y : Subgroup.centralizer {frameElt P ζ}) :
    ∃ M : framePre P ζ, mk.subgroupComap _ M = y :=
  mk.subgroupComap_surjective _ mk_surjective y

variable {P ζ}

omit [NeZero p] in
theorem rootVec_injective (hζ : IsPrimitiveRoot (ζ : K) p) {i j : Fin p}
    (h : (rootVec ζ j : K) = rootVec ζ i) : j = i := by
  simp only [rootVec, Units.val_pow_eq_pow_val] at h
  exact Fin.ext (hζ.pow_inj j.2 i.2 h)

theorem mem_torus_of_frameScalar (hζ : IsPrimitiveRoot (ζ : K) p)
    (y : Subgroup.centralizer {frameElt P ζ}) (hy : frameScalar P ζ y = 1) :
    ∃ x : Fin p → Kˣ, torusHom P x = y := by
  obtain ⟨M, rfl⟩ := exists_framePre P ζ y
  rw [frameScalar_mk] at hy
  have hrel := frameScalarHat_spec P ζ M
  rw [hy, map_one, one_mul] at hrel
  have hdiag : ((P⁻¹ * M * P : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).IsDiag := by
    intro i j hij
    by_contra hne
    have h := eq_mul_of_entry_ne_zero (x := rootVec ζ) (c := 1)
      (by rw [map_one, one_mul]; exact hrel) hne
    rw [Units.val_one, one_mul] at h
    exact hij (rootVec_injective hζ h).symm
  obtain ⟨t, ht⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.1
    (TauCeti.mem_diagonalTorus_iff.2 hdiag)
  refine ⟨t, ?_⟩
  change torusHom P t = mk (M : GL (Fin p) K)
  rw [torusHom_apply, ht]
  congr 1
  group

theorem card_omegaTorus_inf_centralizer_le (hp : p.Prime) (hζ : IsPrimitiveRoot (ζ : K) p)
    (y : Subgroup.centralizer {frameElt P ζ}) (hy : frameScalar P ζ y ≠ 1) :
    Finite (omegaTorus P ⊓ Subgroup.centralizer {(y : ProjGenLinGroup (Fin p) K)} :
      Subgroup (ProjGenLinGroup (Fin p) K)) ∧
      Nat.card (omegaTorus P ⊓ Subgroup.centralizer {(y : ProjGenLinGroup (Fin p) K)} :
        Subgroup (ProjGenLinGroup (Fin p) K)) ≤ p := by
  classical
  obtain ⟨M, rfl⟩ := exists_framePre P ζ y
  rw [frameScalar_mk] at hy
  set u := frameScalarHat P ζ M with hu
  have hrel := frameScalarHat_spec P ζ M
  set N := P⁻¹ * (M : GL (Fin p) K) * P with hN
  choose σ hσ using exists_entry_ne_zero N
  have hσζ : ∀ i, (rootVec ζ (σ i) : K) = u * rootVec ζ i := fun i =>
    eq_mul_of_entry_ne_zero hrel (hσ i)
  have hiter : ∀ (m : ℕ) (i : Fin p), (rootVec ζ (σ^[m] i) : K) = (u : K) ^ m * rootVec ζ i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [Function.iterate_succ_apply', hσζ, ih, pow_succ]
      ring
  have hζp : (ζ : K) ^ p = 1 := hζ.pow_eq_one
  have hup : (u : K) ^ p = 1 := by
    have h := hσζ 0
    simp only [rootVec, Units.val_pow_eq_pow_val, Fin.val_zero, pow_zero, Units.val_one,
      mul_one] at h
    rw [← h, ← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hu1 : (u : K) ≠ 1 := fun h => hy (Units.ext h)
  have := Fact.mk hp
  have huprim : IsPrimitiveRoot (u : K) p := by
    rw [← orderOf_eq_prime hup hu1]
    exact IsPrimitiveRoot.orderOf _
  have hcycle : ∀ i, σ^[p] i = i := fun i =>
    rootVec_injective hζ (by rw [hiter, hup, one_mul])
  have hcover : ∀ j : Fin p, ∃ m : ℕ, σ^[m] 0 = j := by
    intro j
    obtain ⟨m, -, hm⟩ := huprim.eq_pow_of_pow_eq_one (ξ := (rootVec ζ j : K)) (by
      simp only [rootVec, Units.val_pow_eq_pow_val]
      rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow])
    refine ⟨m, rootVec_injective hζ ?_⟩
    rw [hiter, ← hm]
    simp [rootVec]
  have hrelz : ∀ z ∈ (omegaTorus P ⊓ Subgroup.centralizer {mk (M : GL (Fin p) K)} :
      Subgroup (ProjGenLinGroup (Fin p) K)), ∃ (x : Fin p → Kˣ) (c : Kˣ), torusHom P x = z ∧
        N * TauCeti.diagGL x = GeneralLinearGroup.scalar (Fin p) c * (TauCeti.diagGL x * N) := by
    rintro z ⟨hzU, hzC⟩
    obtain ⟨x, -, rfl⟩ := mem_omegaTorus.1 hzU
    have hcomm := Subgroup.mem_centralizer_iff.1 hzC _ rfl
    obtain ⟨c, hc⟩ := exists_scalar_of_commute_torus P hcomm.symm
    exact ⟨x, c, rfl, hc⟩
  choose! xz cz hxz hcz using hrelz
  have hcz_mem : ∀ z ∈ (omegaTorus P ⊓ Subgroup.centralizer {mk (M : GL (Fin p) K)} :
      Subgroup (ProjGenLinGroup (Fin p) K)), cz z ∈ rootsOfUnity p K := by
    intro z hz
    have hstep : ∀ i, ((xz z (σ i)) : K) = cz z * xz z i := fun i =>
      eq_mul_of_entry_ne_zero (hcz z hz) (hσ i)
    have hit : ∀ (m : ℕ) (i : Fin p), ((xz z (σ^[m] i)) : K) = (cz z : K) ^ m * xz z i := by
      intro m
      induction m with
      | zero => intro i; simp
      | succ m ih =>
        intro i
        rw [Function.iterate_succ_apply', hstep, ih, pow_succ]
        ring
    have h0 := hit p 0
    rw [hcycle] at h0
    have hne : ((xz z 0) : K) ≠ 0 := (xz z 0).ne_zero
    rw [mem_rootsOfUnity]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h1 : ((cz z : K) ^ p - 1) * xz z 0 = 0 := by linear_combination -h0
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hne)
  let Φ : (omegaTorus P ⊓ Subgroup.centralizer {mk (M : GL (Fin p) K)} :
      Subgroup (ProjGenLinGroup (Fin p) K)) → rootsOfUnity p K := fun z => ⟨cz z, hcz_mem z z.2⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ hΦz
    have hc : cz z₁ = cz z₂ := congrArg Subtype.val hΦz
    set r : Fin p → Kˣ := xz z₁ * (xz z₂)⁻¹ with hr
    have hstep : ∀ i, r (σ i) = r i := by
      intro i
      have h1 := eq_mul_of_entry_ne_zero (hcz z₁ hz₁) (hσ i)
      have h2 := eq_mul_of_entry_ne_zero (hcz z₂ hz₂) (hσ i)
      rw [hc] at h1
      apply Units.ext
      simp only [hr, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, h1, h2]
      have hne : ((cz z₂ : Kˣ) : K) ≠ 0 := (cz z₂).ne_zero
      field_simp
    have hconst : ∀ j, r j = r 0 := by
      intro j
      obtain ⟨m, rfl⟩ := hcover j
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', hstep, ih]
    have hrt : torusHom P r = 1 := (torusHom_eq_one_iff P r).2 fun i j => by
      rw [hconst i, hconst j]
    apply Subtype.ext
    change z₁ = z₂
    rw [← hxz z₁ hz₁, ← hxz z₂ hz₂]
    have h := congrArg (· * torusHom P (xz z₂)) hrt
    simp only [hr, map_mul, map_inv, inv_mul_cancel_right, one_mul] at h
    exact h
  have : Finite (rootsOfUnity p K) := by
    have : Fintype (rootsOfUnity p K) := Fintype.ofFinite _
    infer_instance
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card _ ≤ Nat.card (rootsOfUnity p K) := Nat.card_le_card_of_injective Φ hΦ
    _ = p := hζ.card_rootsOfUnity

omit [NeZero p] in
theorem le_omegaTorus_of_elementary [NeZero p] (hp : p.Prime) (hζ : IsPrimitiveRoot (ζ : K) p)
    {E : Subgroup (ProjGenLinGroup (Fin p) K)} (hEd : E ≤ Subgroup.centralizer {frameElt P ζ})
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEcard : p ^ 2 < Nat.card E) : E ≤ omegaTorus P := by
  classical
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hker : ∀ y : Subgroup.centralizer {frameElt P ζ}, (y : ProjGenLinGroup (Fin p) K) ∈ E →
      frameScalar P ζ y = 1 → (y : ProjGenLinGroup (Fin p) K) ∈ omegaTorus P := by
    intro y hyE hy
    obtain ⟨x, hx⟩ := mem_torus_of_frameScalar hζ y hy
    rw [← hx]
    exact mem_omegaTorus_of_pow P (by rw [hx]; exact hEp _ hyE)
  by_contra hnot
  obtain ⟨y₀, hy₀E, hy₀U⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  set y₀' : Subgroup.centralizer {frameElt P ζ} := ⟨y₀, hEd hy₀E⟩
  have hlam : frameScalar P ζ y₀' ≠ 1 := fun h => hy₀U (hker y₀' hy₀E h)
  obtain ⟨hfin, hcard⟩ := card_omegaTorus_inf_centralizer_le hp hζ y₀' hlam
  let lamE : E →* Kˣ := (frameScalar P ζ).comp (Subgroup.inclusion hEd)
  have hmemU : ∀ e : lamE.ker, ((e : E) : ProjGenLinGroup (Fin p) K) ∈
      (omegaTorus P ⊓ Subgroup.centralizer {(y₀' : ProjGenLinGroup (Fin p) K)} :
        Subgroup (ProjGenLinGroup (Fin p) K)) := by
    intro e
    refine ⟨hker (Subgroup.inclusion hEd (e : E)) (e : E).2 (MonoidHom.mem_ker.1 e.2), ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    rw [Set.mem_singleton_iff.1 hg]
    exact hEab _ hy₀E _ (e : E).2
  have hkercard : Nat.card lamE.ker ≤ p := by
    refine le_trans (Nat.card_le_card_of_injective (fun e : lamE.ker => ⟨_, hmemU e⟩) ?_) hcard
    intro e₁ e₂ h
    have h' := Subtype.ext_iff.1 h
    exact Subtype.ext (Subtype.ext h')
  have hrangecard : Nat.card lamE.range ≤ p := by
    have hle : lamE.range ≤ rootsOfUnity p K := by
      rintro _ ⟨e, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow]
      have : e ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hEp _ e.2)
      rw [this, map_one]
    have : Finite (rootsOfUnity p K) := by
      have : Fintype (rootsOfUnity p K) := Fintype.ofFinite _
      infer_instance
    calc Nat.card lamE.range ≤ Nat.card (rootsOfUnity p K) := Subgroup.card_le_of_le hle
      _ = p := hζ.card_rootsOfUnity
  have hEeq := Subgroup.card_eq_card_quotient_mul_card_subgroup lamE.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange lamE).toEquiv] at hEeq
  have : Nat.card E ≤ p ^ 2 := by
    rw [hEeq, sq]
    exact Nat.mul_le_mul hrangecard hkercard
  omega

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
