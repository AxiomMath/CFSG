module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LinearAlgebra.ProjectivePrimePlane

open Matrix Matrix.ProjGenLinGroup

variable {p : ℕ} {F : Type*} [Field F]

section Commutation

variable {A B : Matrix (Fin p) (Fin p) F} {ζ : F}

theorem mul_pow_comm (h : A * B = ζ • (B * A)) (j : ℕ) : A * B ^ j = ζ ^ j • (B ^ j * A) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h, mul_smul_comm, smul_smul,
      ← mul_assoc, pow_succ, mul_comm (ζ ^ j)]

theorem pow_mul_pow_comm (h : A * B = ζ • (B * A)) (i j : ℕ) :
    A ^ i * B ^ j = ζ ^ (i * j) • (B ^ j * A ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, mul_assoc, mul_pow_comm h, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc,
      smul_smul, mul_assoc, ← pow_succ, ← pow_add, Nat.succ_mul, add_comm (i * j)]

end Commutation

section Trace

variable {M C : Matrix (Fin p) (Fin p) F} {c : F}

theorem trace_eq_zero_of_mul_eq_smul (hC : IsUnit C.det) (hc : c ≠ 1)
    (h : C * M = c • (M * C)) : M.trace = 0 := by
  have hconj : C * M * C⁻¹ = c • M := by
    rw [h, smul_mul_assoc, mul_assoc, mul_nonsing_inv _ hC, mul_one]
  have htr : (C * M * C⁻¹).trace = M.trace := by
    rw [trace_mul_comm, ← mul_assoc, nonsing_inv_mul _ hC, one_mul]
  rw [hconj, trace_smul, smul_eq_mul] at htr
  have : (c - 1) * M.trace = 0 := by linear_combination htr
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

theorem trace_eq_zero_of_mul_eq_smul' (hC : IsUnit C.det) (hc : c ≠ 1)
    (h : M * C = c • (C * M)) : M.trace = 0 := by
  have hconj : C⁻¹ * M * C = c • M := by
    rw [mul_assoc, h, mul_smul_comm, ← mul_assoc, nonsing_inv_mul _ hC, one_mul]
  have htr : (C⁻¹ * M * C).trace = M.trace := by
    rw [mul_assoc, trace_mul_comm, mul_assoc, mul_nonsing_inv _ hC, mul_one]
  rw [hconj, trace_smul, smul_eq_mul] at htr
  have : (c - 1) * M.trace = 0 := by linear_combination htr
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

variable {A B : Matrix (Fin p) (Fin p) F} {ζ : F}

theorem trace_pow_mul_pow_eq_zero (h : A * B = ζ • (B * A)) (hζ : IsPrimitiveRoot ζ p)
    (hA : IsUnit A.det) (hB : IsUnit B.det) {u v : ℕ} (huv : ¬ (p ∣ u ∧ p ∣ v)) :
    (A ^ u * B ^ v).trace = 0 := by
  by_cases hv : p ∣ v
  · have hu : ¬ p ∣ u := fun hu => huv ⟨hu, hv⟩
    refine trace_eq_zero_of_mul_eq_smul' (C := B) hB (c := ζ ^ u)
      (fun h1 => hu ((hζ.pow_eq_one_iff_dvd u).1 h1)) ?_
    have := pow_mul_pow_comm h u 1
    rw [pow_one, mul_one] at this
    rw [mul_assoc, ← pow_succ, pow_succ', ← mul_assoc, this, smul_mul_assoc, mul_assoc]
  · refine trace_eq_zero_of_mul_eq_smul (C := A) hA (c := ζ ^ v)
      (fun h1 => hv ((hζ.pow_eq_one_iff_dvd v).1 h1)) ?_
    rw [← mul_assoc, ← pow_succ', pow_succ, mul_assoc, mul_pow_comm h, mul_smul_comm,
      ← mul_assoc]

end Trace

section Basis

variable {A B : Matrix (Fin p) (Fin p) F} {ζ α β : F}

theorem eq_of_dvd_sub_add {i k : ℕ} (hi : i < p) (hk : k < p) (h : p ∣ p - k + i) : i = k := by
  obtain ⟨c, hc⟩ := h
  rcases c with _ | _ | c
  · omega
  · omega
  · have : p * (c + 1 + 1) ≥ 2 * p := by nlinarith
    omega

@[expose] def heisenbergFamily (A B : Matrix (Fin p) (Fin p) F) (ij : Fin p × Fin p) :
    Matrix (Fin p) (Fin p) F :=
  A ^ (ij.1 : ℕ) * B ^ (ij.2 : ℕ)

theorem trace_heisenberg_mul (h : A * B = ζ • (B * A)) (hζ : IsPrimitiveRoot ζ p)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (hAp : A ^ p = α • 1) (hBp : B ^ p = β • 1)
    (i j k l : Fin p) :
    (heisenbergFamily A B (i, j) * (B ^ (p - (l : ℕ)) * A ^ (p - (k : ℕ)))).trace =
      if i = k ∧ j = l then α * β * p else 0 := by
  have hrw : heisenbergFamily A B (i, j) * (B ^ (p - (l : ℕ)) * A ^ (p - (k : ℕ))) =
      (A ^ (i : ℕ) * B ^ ((j : ℕ) + (p - l))) * A ^ (p - (k : ℕ)) := by
    simp only [heisenbergFamily, pow_add, mul_assoc]
  rw [hrw, trace_mul_comm, ← mul_assoc, ← pow_add]
  split_ifs with hik
  · obtain ⟨rfl, rfl⟩ := hik
    have h1 : p - (i : ℕ) + i = p := by omega
    have h2 : (j : ℕ) + (p - j) = p := by omega
    rw [h1, h2, hAp, hBp, smul_mul_smul_comm, mul_one, trace_smul, trace_one, smul_eq_mul,
      Fintype.card_fin]
  · refine trace_pow_mul_pow_eq_zero h hζ hA hB fun ⟨hu, hv⟩ => hik ⟨?_, ?_⟩
    · exact Fin.ext (eq_of_dvd_sub_add i.isLt k.isLt hu)
    · have hv' : p ∣ p - (l : ℕ) + j := by rwa [add_comm]
      exact Fin.ext (eq_of_dvd_sub_add j.isLt l.isLt hv')

theorem linearIndependent_heisenbergFamily [NeZero p] (h : A * B = ζ • (B * A))
    (hζ : IsPrimitiveRoot ζ p) (hA : IsUnit A.det) (hB : IsUnit B.det) (hα : α ≠ 0)
    (hβ : β ≠ 0) (hAp : A ^ p = α • 1) (hBp : B ^ p = β • 1) :
    LinearIndependent F (heisenbergFamily A B) := by
  have hp0 : (p : F) ≠ 0 := (hζ.neZero').out
  rw [Fintype.linearIndependent_iff]
  intro g hg ⟨k, l⟩
  have key := congrArg (fun X => (X * (B ^ (p - (l : ℕ)) * A ^ (p - (k : ℕ)))).trace) hg
  simp only [Finset.sum_mul, trace_sum, smul_mul_assoc, trace_smul, smul_eq_mul, zero_mul,
    trace_zero] at key
  rw [Finset.sum_eq_single (k, l)] at key
  · rw [trace_heisenberg_mul h hζ hA hB hAp hBp, ite_eq_left ⟨rfl, rfl⟩] at key
    exact (mul_eq_zero.1 key).resolve_right (mul_ne_zero (mul_ne_zero hα hβ) hp0)
  · rintro ⟨i, j⟩ - hne
    rw [trace_heisenberg_mul h hζ hA hB hAp hBp, ite_eq_right fun hij => hne (by rw [hij.1, hij.2]),
      mul_zero]
  · simp

theorem span_heisenbergFamily [NeZero p] (h : A * B = ζ • (B * A))
    (hζ : IsPrimitiveRoot ζ p) (hA : IsUnit A.det) (hB : IsUnit B.det) (hα : α ≠ 0)
    (hβ : β ≠ 0) (hAp : A ^ p = α • 1) (hBp : B ^ p = β • 1) :
    Submodule.span F (Set.range (heisenbergFamily A B)) = ⊤ :=
  (linearIndependent_heisenbergFamily h hζ hA hB hα hβ hAp hBp).span_eq_top_of_card_eq_finrank'
    (by rw [Module.finrank_matrix, Fintype.card_prod, Fintype.card_fin, Module.finrank_self,
      mul_one])

theorem commute_iff_eq_smul_one [NeZero p] (h : A * B = ζ • (B * A))
    (hζ : IsPrimitiveRoot ζ p) (hA : IsUnit A.det) (hB : IsUnit B.det) (hα : α ≠ 0)
    (hβ : β ≠ 0) (hAp : A ^ p = α • 1) (hBp : B ^ p = β • 1) (X : Matrix (Fin p) (Fin p) F) :
    (Commute X A ∧ Commute X B) ↔ ∃ c : F, X = c • 1 := by
  have hp0 : (p : F) ≠ 0 := (hζ.neZero').out
  constructor
  · rintro ⟨hXA, hXB⟩
    refine ⟨X.trace / p, ?_⟩
    set Y := X - (X.trace / p) • (1 : Matrix (Fin p) (Fin p) F) with hY
    have hYA : Y * A = A * Y := by
      rw [hY, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hXA.eq]
    have hYB : Y * B = B * Y := by
      rw [hY, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hXB.eq]
    have htrY : Y.trace = 0 := by
      rw [hY, trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul,
        div_mul_cancel₀ _ hp0, sub_self]
    have hbasis : ∀ ij : Fin p × Fin p, (heisenbergFamily A B ij * Y).trace = 0 := by
      rintro ⟨i, j⟩
      simp only [heisenbergFamily]
      by_cases hj : (j : ℕ) = 0
      · rw [hj, pow_zero, mul_one]
        by_cases hi : (i : ℕ) = 0
        · rw [hi, pow_zero, one_mul, htrY]
        · refine trace_eq_zero_of_mul_eq_smul' (C := B) hB (c := ζ ^ (i : ℕ))
            (fun h1 => hi ?_) ?_
          · obtain ⟨m, hm⟩ := (hζ.pow_eq_one_iff_dvd _).1 h1
            have := i.isLt
            rcases m with _ | m
            · simpa using hm
            · nlinarith
          · have := pow_mul_pow_comm h (i : ℕ) 1
            rw [pow_one, mul_one] at this
            rw [mul_assoc, hYB, ← mul_assoc, this, smul_mul_assoc, mul_assoc]
      · refine trace_eq_zero_of_mul_eq_smul (C := A) hA (c := ζ ^ (j : ℕ))
          (fun h1 => hj ?_) ?_
        · obtain ⟨m, hm⟩ := (hζ.pow_eq_one_iff_dvd _).1 h1
          have := j.isLt
          rcases m with _ | m
          · simpa using hm
          · nlinarith
        · rw [← mul_assoc, ← mul_assoc, ← pow_succ', pow_succ, mul_assoc (A ^ (i : ℕ)) A,
            mul_pow_comm h, mul_smul_comm, smul_mul_assoc, mul_assoc, mul_assoc, ← hYA,
            ← mul_assoc, ← mul_assoc]
    have hall : ∀ Z : Matrix (Fin p) (Fin p) F, (Z * Y).trace = 0 := by
      intro Z
      have hZ : Z ∈ Submodule.span F (Set.range (heisenbergFamily A B)) := by
        rw [span_heisenbergFamily h hζ hA hB hα hβ hAp hBp]
        trivial
      induction hZ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨ij, rfl⟩ := hx
        exact hbasis ij
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, trace_add, hx, hy, add_zero]
      | smul c x _ hx => rw [smul_mul_assoc, trace_smul, hx, smul_zero]
    have hY0 : Y = 0 := Matrix.ext_iff_trace_mul_left.2 fun Z => by rw [hall Z, mul_zero,
      trace_zero]
    rw [hY, sub_eq_zero] at hY0
    exact hY0
  · rintro ⟨c, rfl⟩
    exact ⟨((Commute.one_left A).smul_left c), ((Commute.one_left B).smul_left c)⟩

end Basis

section Projective

open Matrix.ProjGenLinGroup

theorem inv_mul_mul_comm_of_mul_eq {G : Type*} [Group G] {s a x y : G}
    (hx : x * a = s * (a * x)) (hy : y * a = s * (a * y)) : y⁻¹ * x * a = a * (y⁻¹ * x) := by
  have h1 : x * a * x⁻¹ = y * a * y⁻¹ := by rw [hx, hy]; group
  calc y⁻¹ * x * a = y⁻¹ * (x * a * x⁻¹) * x := by group
    _ = y⁻¹ * (y * a * y⁻¹) * x := by rw [h1]
    _ = a * (y⁻¹ * x) := by group

theorem mul_eq_scalar_mul_of_val {X A : GL (Fin p) F} {u : Fˣ}
    (h : (X : Matrix (Fin p) (Fin p) F) * A = (u : F) • ((A : Matrix (Fin p) (Fin p) F) * X)) :
    X * A = GeneralLinearGroup.scalar (Fin p) u * (A * X) := by
  ext : 1
  rw [Units.val_mul, h, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
    ← smul_one_eq_diagonal, smul_mul_assoc, one_mul]

theorem exists_mul_eq_smul_of_commute {X A : GL (Fin p) F} (h : mk A * mk X = mk X * mk A) :
    ∃ u : Fˣ,
      (X : Matrix (Fin p) (Fin p) F) * A = (u : F) • ((A : Matrix (Fin p) (Fin p) F) * X) := by
  rw [← map_mul, ← map_mul, mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  have := congrArg Units.val hu
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
    ← smul_one_eq_diagonal, mul_smul_comm, mul_one] at this
  exact this.symm

theorem exists_pow_eq_smul_one {A : GL (Fin p) F} (h : mk A ^ p = 1) :
    ∃ α : Fˣ, (A : Matrix (Fin p) (Fin p) F) ^ p = (α : F) • 1 := by
  rw [← map_pow, mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨α, hα⟩ := h
  refine ⟨α, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← hα, GeneralLinearGroup.coe_scalar, scalar_apply,
    smul_one_eq_diagonal]

theorem pow_eq_one_of_mul_eq_smul {A B : Matrix (Fin p) (Fin p) F} {ζ α : F}
    (h : A * B = ζ • (B * A)) (hAp : A ^ p = α • 1) (hα : α ≠ 0) (hB : B ≠ 0) : ζ ^ p = 1 := by
  have key := pow_mul_pow_comm h p 1
  rw [pow_one, mul_one, hAp, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul] at key
  have h2 : (ζ ^ p * α - α) • B = 0 := by rw [sub_smul, ← key, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · have h4 : (ζ ^ p - 1) * α = 0 := by linear_combination h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_right hα)
  · exact absurd h3 hB

theorem val_ne_zero [NeZero p] (A : GL (Fin p) F) : (A : Matrix (Fin p) (Fin p) F) ≠ 0 := by
  intro h0
  have : Nonempty (Fin p) := ⟨⟨0, Nat.pos_of_neZero p⟩⟩
  have h1 := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
  rw [h0, det_zero] at h1
  exact not_isUnit_zero h1

theorem comap_mk_commute {A B : GL (Fin p) F} (hAB : A * B = B * A)
    {D : Subgroup (ProjGenLinGroup (Fin p) F)} (hD : Subgroup.closure {mk A, mk B} = D) :
    ∀ x ∈ D.comap mk, ∀ y ∈ D.comap mk, x * y = y * x := by
  have hcomm : IsMulCommutative (Subgroup.closure ({A, B} : Set (GL (Fin p) F))) :=
    Subgroup.isMulCommutative_closure (Set.pairwise_pair.2 fun _ => ⟨hAB, hAB.symm⟩)
  have hcen : ∀ (u : Fˣ) (g : GL (Fin p) F),
      g * GeneralLinearGroup.scalar (Fin p) u = GeneralLinearGroup.scalar (Fin p) u * g :=
    fun u g => (Subgroup.mem_center_iff.1 (by
      rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩) g)
  intro x hx y hy
  rw [Subgroup.mem_comap, ← hD, ← Set.image_pair, ← MonoidHom.map_closure] at hx hy
  obtain ⟨x', hx', hxx⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hy
  obtain ⟨u, rfl⟩ := mk_eq_mk_iff.1 hxx
  obtain ⟨v, rfl⟩ := mk_eq_mk_iff.1 hyy
  have hc : x' * y' = y' * x' := by
    have := hcomm.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩
    exact congrArg Subtype.val this
  set su := GeneralLinearGroup.scalar (Fin p) u
  set sv := GeneralLinearGroup.scalar (Fin p) v
  calc x' * su * (y' * sv) = x' * (su * y') * sv := by simp only [mul_assoc]
    _ = x' * (y' * su) * sv := by rw [← hcen u y']
    _ = x' * y' * (su * sv) := by simp only [mul_assoc]
    _ = y' * x' * (sv * su) := by rw [hc, ← map_mul, ← map_mul, mul_comm u v]
    _ = y' * (x' * sv) * su := by simp only [mul_assoc]
    _ = y' * (sv * x') * su := by rw [hcen v x']
    _ = y' * sv * (x' * su) := by simp only [mul_assoc]

theorem exists_closure_pair_eq {G : Type*} [Group G] (hp : p.Prime) {D : Subgroup G}
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2) :
    ∃ d ∈ D, ∃ e ∈ D, Subgroup.closure {d, e} = D := by
  have := Fact.mk hp
  have hp1 := hp.one_lt
  have hfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall D).2 hcon, Subgroup.card_bot] at hcard
    nlinarith
  have hzd : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hDp d hdD) hd1]
  have hzle : Subgroup.zpowers d ≤ D := (Subgroup.zpowers_le).2 hdD
  have hfinz : Finite (Subgroup.zpowers d) :=
    Finite.of_injective (Subgroup.inclusion hzle) (Subgroup.inclusion_injective hzle)
  obtain ⟨e, heD, he⟩ : ∃ e ∈ D, e ∉ Subgroup.zpowers d := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (fun x hx => hcon x hx : D ≤ Subgroup.zpowers d)
    rw [hcard, hzd] at h1
    nlinarith
  refine ⟨d, hdD, e, heD, ?_⟩
  have hHD : Subgroup.closure ({d, e} : Set G) ≤ D :=
    (Subgroup.closure_le D).2 (by simp [Set.insert_subset_iff, hdD, heD])
  have hfinH : Finite (Subgroup.closure ({d, e} : Set G)) :=
    Finite.of_injective (Subgroup.inclusion hHD) (Subgroup.inclusion_injective hHD)
  obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hp).1 (hcard ▸ Subgroup.card_dvd_of_le hHD)
  have hzH : Subgroup.zpowers d ≤ Subgroup.closure ({d, e} : Set G) :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have heH : e ∈ Subgroup.closure ({d, e} : Set G) := Subgroup.subset_closure (by simp)
  have hk2 : k = 2 := by
    by_contra hk2
    have hle : Nat.card (Subgroup.closure ({d, e} : Set G)) ≤ Nat.card (Subgroup.zpowers d) := by
      rw [hkH, hzd]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    exact he ((Subgroup.eq_of_le_of_card_ge hzH hle) ▸ heH)
  exact Subgroup.eq_of_le_of_card_ge hHD (by rw [hcard, hkH, hk2])

theorem exists_primitive_root_of_basis (hp : p.Prime) {D : Subgroup (ProjGenLinGroup (Fin p) F)}
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDp : ∀ x ∈ D, x ^ p = 1)
    (hna : ¬ ∀ x ∈ D.comap mk, ∀ y ∈ D.comap mk, x * y = y * x)
    {A B : GL (Fin p) F} (hgen : Subgroup.closure {mk A, mk B} = D) :
    ∃ ζ : F, IsPrimitiveRoot ζ p ∧
      (A : Matrix (Fin p) (Fin p) F) * B = ζ • ((B : Matrix (Fin p) (Fin p) F) * A) ∧
      (∃ α : Fˣ, (A : Matrix (Fin p) (Fin p) F) ^ p = (α : F) • 1) ∧
      ∃ β : Fˣ, (B : Matrix (Fin p) (Fin p) F) ^ p = (β : F) • 1 := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hAD : mk A ∈ D := hgen ▸ Subgroup.subset_closure (by simp)
  have hBD : mk B ∈ D := hgen ▸ Subgroup.subset_closure (by simp)
  obtain ⟨u, hu⟩ := exists_mul_eq_smul_of_commute (X := A) (A := B) (hDab _ hBD _ hAD)
  obtain ⟨α, hα⟩ := exists_pow_eq_smul_one (hDp _ hAD)
  obtain ⟨β, hβ⟩ := exists_pow_eq_smul_one (hDp _ hBD)
  have hup : (u : F) ^ p = 1 := pow_eq_one_of_mul_eq_smul hu hα α.ne_zero (val_ne_zero B)
  have hu1 : (u : F) ≠ 1 := by
    intro h1
    rw [h1, one_smul] at hu
    exact hna (comap_mk_commute (Units.ext hu) hgen)
  have hprim : IsPrimitiveRoot (u : F) p := by
    rw [← orderOf_eq_prime hup hu1]
    exact IsPrimitiveRoot.orderOf _
  exact ⟨u, hprim, hu, ⟨α, hα⟩, ⟨β, hβ⟩⟩

theorem exists_eq_pow_mul_pow [NeZero p] {A B : GL (Fin p) F} {ζ α β : F}
    (h : (A : Matrix (Fin p) (Fin p) F) * B = ζ • ((B : Matrix (Fin p) (Fin p) F) * A))
    (hζ : IsPrimitiveRoot ζ p) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hAp : (A : Matrix (Fin p) (Fin p) F) ^ p = α • 1)
    (hBp : (B : Matrix (Fin p) (Fin p) F) ^ p = β • 1)
    {X : GL (Fin p) F} (hXA : mk A * mk X = mk X * mk A) (hXB : mk B * mk X = mk X * mk B) :
    ∃ i j : ℕ, mk X = mk A ^ i * mk B ^ j := by
  have hdet : ∀ {C : GL (Fin p) F} {w : Fˣ}, (X : Matrix (Fin p) (Fin p) F) * C =
      (w : F) • ((C : Matrix (Fin p) (Fin p) F) * X) → (w : F) ^ p = 1 := by
    intro C w hw
    have hd := congrArg Matrix.det hw
    rw [det_mul, det_smul, det_mul, Fintype.card_fin] at hd
    have hX := (Matrix.isUnit_iff_isUnit_det _).1 X.isUnit
    have hC := (Matrix.isUnit_iff_isUnit_det _).1 C.isUnit
    have h0 : (C : Matrix (Fin p) (Fin p) F).det * (X : Matrix (Fin p) (Fin p) F).det ≠ 0 :=
      mul_ne_zero hC.ne_zero hX.ne_zero
    have h1 : ((w : F) ^ p - 1) * ((C : Matrix (Fin p) (Fin p) F).det *
        (X : Matrix (Fin p) (Fin p) F).det) = 0 := by linear_combination -hd
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right h0)
  obtain ⟨u, hu⟩ := exists_mul_eq_smul_of_commute hXA
  obtain ⟨v, hv⟩ := exists_mul_eq_smul_of_commute hXB
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (u : F)⁻¹) (by rw [inv_pow, hdet hu, inv_one])
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (hdet hv)
  have hYm : ((A ^ i * B ^ j : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (A : Matrix (Fin p) (Fin p) F) ^ i * (B : Matrix (Fin p) (Fin p) F) ^ j := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  have hYA : ((A ^ i * B ^ j : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * A =
      (u : F) • ((A : Matrix (Fin p) (Fin p) F) * (A ^ i * B ^ j : GL (Fin p) F)) := by
    have h1 : (A : Matrix (Fin p) (Fin p) F) * (B : Matrix (Fin p) (Fin p) F) ^ j =
        (u : F)⁻¹ • ((B : Matrix (Fin p) (Fin p) F) ^ j * A) := by rw [mul_pow_comm h j, hj]
    have h2 : (B : Matrix (Fin p) (Fin p) F) ^ j * A =
        (u : F) • ((A : Matrix (Fin p) (Fin p) F) * (B : Matrix (Fin p) (Fin p) F) ^ j) := by
      rw [h1, smul_smul, mul_inv_cancel₀ u.ne_zero, one_smul]
    have h3 : (A : Matrix (Fin p) (Fin p) F) ^ i * ((A : Matrix (Fin p) (Fin p) F) *
        (B : Matrix (Fin p) (Fin p) F) ^ j) = (A : Matrix (Fin p) (Fin p) F) *
        ((A : Matrix (Fin p) (Fin p) F) ^ i * (B : Matrix (Fin p) (Fin p) F) ^ j) := by
      rw [← mul_assoc, ← (Commute.self_pow (A : Matrix (Fin p) (Fin p) F) i).eq, mul_assoc]
    rw [hYm, mul_assoc, h2, mul_smul_comm, h3]
  have hYB : ((A ^ i * B ^ j : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * B =
      (v : F) • ((B : Matrix (Fin p) (Fin p) F) * (A ^ i * B ^ j : GL (Fin p) F)) := by
    have h1 := pow_mul_pow_comm h i 1
    rw [pow_one, mul_one, hi] at h1
    rw [hYm, mul_assoc, ← (Commute.self_pow (B : Matrix (Fin p) (Fin p) F) j).eq, ← mul_assoc, h1,
      smul_mul_assoc, mul_assoc]
  have hZA := inv_mul_mul_comm_of_mul_eq (mul_eq_scalar_mul_of_val hu)
    (mul_eq_scalar_mul_of_val hYA)
  have hZB := inv_mul_mul_comm_of_mul_eq (mul_eq_scalar_mul_of_val hv)
    (mul_eq_scalar_mul_of_val hYB)
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
  have hB := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  obtain ⟨c, hc⟩ := (commute_iff_eq_smul_one h hζ hA hB hα hβ hAp hBp
    (((A ^ i * B ^ j)⁻¹ * X : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)).1
    ⟨congrArg Units.val hZA, congrArg Units.val hZB⟩
  have hZc : (A ^ i * B ^ j)⁻¹ * X ∈ Subgroup.center (GL (Fin p) F) :=
    Subgroup.mem_center_iff.2 fun g => Units.ext (by
      change (g : Matrix (Fin p) (Fin p) F) * (((A ^ i * B ^ j)⁻¹ * X : GL (Fin p) F) :
          Matrix (Fin p) (Fin p) F) = (((A ^ i * B ^ j)⁻¹ * X : GL (Fin p) F) :
          Matrix (Fin p) (Fin p) F) * g
      rw [hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one])
  have hmk := mk_eq_one.2 hZc
  rw [map_mul, map_inv, inv_mul_eq_one] at hmk
  exact ⟨i, j, by rw [← hmk, map_mul, map_pow, map_pow]⟩

theorem nonabelian_projective_prime_plane_self_centralizing (hp : p.Prime)
    (D : Subgroup (ProjGenLinGroup (Fin p) F))
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDp : ∀ x ∈ D, x ^ p = 1)
    (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ x ∈ D.comap mk, ∀ y ∈ D.comap mk, x * y = y * x) :
    ringChar F ≠ p ∧ Subgroup.centralizer (D : Set (ProjGenLinGroup (Fin p) F)) = D ∧
      (∀ d ∈ D, ∀ e ∈ D, Subgroup.closure {d, e} = D → ∀ A B : GL (Fin p) F,
        mk A = d → mk B = e → ∃ ζ : F, IsPrimitiveRoot ζ p ∧
          (A : Matrix (Fin p) (Fin p) F) * B = ζ • ((B : Matrix (Fin p) (Fin p) F) * A) ∧
          LinearIndependent F (fun ij : Fin p × Fin p => (A : Matrix (Fin p) (Fin p) F) ^
            (ij.1 : ℕ) * (B : Matrix (Fin p) (Fin p) F) ^ (ij.2 : ℕ)) ∧
          Submodule.span F (Set.range fun ij : Fin p × Fin p => (A : Matrix (Fin p) (Fin p) F) ^
            (ij.1 : ℕ) * (B : Matrix (Fin p) (Fin p) F) ^ (ij.2 : ℕ)) = ⊤ ∧
          ∀ X : Matrix (Fin p) (Fin p) F, (Commute X A ∧ Commute X B) ↔ ∃ c : F, X = c • 1) ∧
      ∀ J : Subgroup (ProjGenLinGroup (Fin p) F), D ≤ J →
        J ⊓ Subgroup.centralizer (D : Set (ProjGenLinGroup (Fin p) F)) = D := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hbasis : ∀ d ∈ D, ∀ e ∈ D, Subgroup.closure {d, e} = D → ∀ A B : GL (Fin p) F,
      mk A = d → mk B = e → ∃ ζ : F, IsPrimitiveRoot ζ p ∧
        (A : Matrix (Fin p) (Fin p) F) * B = ζ • ((B : Matrix (Fin p) (Fin p) F) * A) ∧
        LinearIndependent F (fun ij : Fin p × Fin p => (A : Matrix (Fin p) (Fin p) F) ^
          (ij.1 : ℕ) * (B : Matrix (Fin p) (Fin p) F) ^ (ij.2 : ℕ)) ∧
        Submodule.span F (Set.range fun ij : Fin p × Fin p => (A : Matrix (Fin p) (Fin p) F) ^
          (ij.1 : ℕ) * (B : Matrix (Fin p) (Fin p) F) ^ (ij.2 : ℕ)) = ⊤ ∧
        ∀ X : Matrix (Fin p) (Fin p) F, (Commute X A ∧ Commute X B) ↔ ∃ c : F, X = c • 1 := by
    rintro d - e - hde A B rfl rfl
    obtain ⟨ζ, hζ, h, ⟨α, hα⟩, ⟨β, hβ⟩⟩ := exists_primitive_root_of_basis hp hDab hDp hna hde
    have hA := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    have hB := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
    exact ⟨ζ, hζ, h, linearIndependent_heisenbergFamily h hζ hA hB α.ne_zero β.ne_zero hα hβ,
      span_heisenbergFamily h hζ hA hB α.ne_zero β.ne_zero hα hβ,
      commute_iff_eq_smul_one h hζ hA hB α.ne_zero β.ne_zero hα hβ⟩
  obtain ⟨d, hd, e, he, hde⟩ := exists_closure_pair_eq hp hDp hcard
  obtain ⟨A, rfl⟩ := mk_surjective d
  obtain ⟨B, rfl⟩ := mk_surjective e
  obtain ⟨ζ, hζ, h, ⟨α, hα⟩, ⟨β, hβ⟩⟩ := exists_primitive_root_of_basis hp hDab hDp hna hde
  have hcent : Subgroup.centralizer (D : Set (ProjGenLinGroup (Fin p) F)) = D := by
    apply le_antisymm
    · intro x hx
      obtain ⟨X, rfl⟩ := mk_surjective x
      obtain ⟨i, j, hij⟩ := exists_eq_pow_mul_pow h hζ α.ne_zero β.ne_zero hα hβ
        (Subgroup.mem_centralizer_iff.1 hx (mk A) hd) (Subgroup.mem_centralizer_iff.1 hx (mk B) he)
      rw [hij]
      exact D.mul_mem (D.pow_mem hd i) (D.pow_mem he j)
    · intro x hx
      exact Subgroup.mem_centralizer_iff.2 fun y hy => hDab y hy x hx
  refine ⟨fun hc => ?_, hcent, hbasis, fun J hJ => by rw [hcent, inf_eq_right.2 hJ]⟩
  have hp0 : (p : F) ≠ 0 := (hζ.neZero').out
  rw [← hc] at hp0
  exact hp0 ringChar.Nat.cast_ringChar

end Projective

end CFSG.LinearAlgebra.ProjectivePrimePlane
