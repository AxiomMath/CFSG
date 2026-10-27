module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClArith
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Artinian.Instances
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.CatFC.DS81.ClCore

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def adj (θ : K →+* K) (M : Matrix ι ι K) (A : Matrix ι ι K) :
    Matrix ι ι K :=
  M⁻¹ * (A.map θ)ᵀ * M

variable (θ : K →+* K) (M : Matrix ι ι K)

theorem adj_add (A B : Matrix ι ι K) : adj θ M (A + B) = adj θ M A + adj θ M B := by
  simp [adj, Matrix.map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem adj_mul (hM : IsUnit M.det) (A B : Matrix ι ι K) :
    adj θ M (A * B) = adj θ M B * adj θ M A := by
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]
  calc M⁻¹ * ((B.map θ)ᵀ * (A.map θ)ᵀ) * M
      = M⁻¹ * (B.map θ)ᵀ * (M * M⁻¹) * (A.map θ)ᵀ * M := by rw [h1]; simp [Matrix.mul_assoc]
    _ = M⁻¹ * (B.map θ)ᵀ * M * (M⁻¹ * (A.map θ)ᵀ * M) := by simp [Matrix.mul_assoc]

theorem adj_one (hM : IsUnit M.det) : adj θ M 1 = 1 := by
  simp [adj, Matrix.map_one, Matrix.nonsing_inv_mul M hM]

theorem adj_algebraMap (hM : IsUnit M.det) (c : K) :
    adj θ M (algebraMap K (Matrix ι ι K) c) = algebraMap K (Matrix ι ι K) (θ c) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  simp [adj, Matrix.map_smul', Matrix.nonsing_inv_mul M hM]

theorem adj_adj (hM : IsUnit M.det) (hθ : ∀ c, θ (θ c) = c) (hMθ : (M.map θ)ᵀ = M)
    (A : Matrix ι ι K) : adj θ M (adj θ M A) = A := by
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hN : (M⁻¹).map θ = (M.map θ)⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [← Matrix.map_mul, h1, Matrix.map_one _ θ.map_zero θ.map_one]
  have hT : ((M⁻¹).map θ)ᵀ = M⁻¹ := by
    rw [hN, Matrix.transpose_nonsing_inv, hMθ]
  have hA : ((A.map θ)ᵀ.map θ)ᵀ = A := by
    rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_map]
    conv_rhs => rw [← Matrix.map_id A]
    congr 1
    funext c
    exact hθ c
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, hMθ, hT, hA]
  calc M⁻¹ * (M * (A * M⁻¹)) * M = (M⁻¹ * M) * A * (M⁻¹ * M) := by simp [Matrix.mul_assoc]
    _ = A := by rw [h2, Matrix.one_mul, Matrix.mul_one]

theorem adj_mul_self_of_form (hM : IsUnit M.det) {A : Matrix ι ι K}
    (hA : (A.map θ)ᵀ * M * A = M) : adj θ M A * A = 1 := by
  simp only [adj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (A.map θ)ᵀ, hA, Matrix.nonsing_inv_mul M hM]

theorem form_of_adj_mul_self (hM : IsUnit M.det) {A : Matrix ι ι K}
    (hA : adj θ M A * A = 1) : (A.map θ)ᵀ * M * A = M := by
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  calc (A.map θ)ᵀ * M * A = M * (M⁻¹ * (A.map θ)ᵀ * M * A) := by
        simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    _ = M := by rw [show M⁻¹ * (A.map θ)ᵀ * M = adj θ M A from rfl, hA, Matrix.mul_one]

theorem adj_mem_adjoin (hM : IsUnit M.det) {g : Matrix ι ι K}
    (hg : adj θ M g ∈ Algebra.adjoin K {g}) {x : Matrix ι ι K}
    (hx : x ∈ Algebra.adjoin K {g}) : adj θ M x ∈ Algebra.adjoin K {g} := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hg
  | algebraMap c =>
    rw [adj_algebraMap θ M hM]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [adj_add]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [adj_mul θ M hM]; exact mul_mem hy hx

theorem adj_eq_pow (hM : IsUnit M.det) {g : Matrix ι ι K} (hg : adj θ M g * g = 1) {N : ℕ}
    (hN : 0 < N) (hgN : g ^ N = 1) : adj θ M g = g ^ (N - 1) := by
  calc adj θ M g = adj θ M g * g ^ N := by rw [hgN, Matrix.mul_one]
    _ = adj θ M g * (g * g ^ (N - 1)) := by
        rw [← pow_succ', Nat.sub_add_cancel hN]
    _ = g ^ (N - 1) := by rw [← Matrix.mul_assoc, hg, Matrix.one_mul]

section Restrict

variable {g : Matrix ι ι K}

@[expose] noncomputable def adjR (hM : IsUnit M.det) (hg : adj θ M g ∈ Algebra.adjoin K {g}) :
    ↥(Algebra.adjoin K {g}) →+* ↥(Algebra.adjoin K {g}) where
  toFun x := ⟨adj θ M x, adj_mem_adjoin θ M hM hg x.2⟩
  map_one' := by ext1; exact adj_one θ M hM
  map_mul' x y := by
    ext1
    change adj θ M (x * y : Matrix ι ι K) = adj θ M x * adj θ M y
    rw [adj_mul θ M hM]
    have hc : ((⟨adj θ M y, adj_mem_adjoin θ M hM hg y.2⟩ : ↥(Algebra.adjoin K {g})) *
        ⟨adj θ M x, adj_mem_adjoin θ M hM hg x.2⟩) =
        ⟨adj θ M x, adj_mem_adjoin θ M hM hg x.2⟩ * ⟨adj θ M y, adj_mem_adjoin θ M hM hg y.2⟩ :=
      mul_comm _ _
    exact congrArg Subtype.val hc
  map_zero' := by ext1; simp [adj]
  map_add' x y := by ext1; exact adj_add θ M x y

theorem adjR_apply (hM : IsUnit M.det) (hg : adj θ M g ∈ Algebra.adjoin K {g})
    (x : ↥(Algebra.adjoin K {g})) : ((adjR θ M hM hg x : ↥(Algebra.adjoin K {g})) :
      Matrix ι ι K) = adj θ M x := rfl

theorem adjR_adjR (hM : IsUnit M.det) (hθ : ∀ c, θ (θ c) = c) (hMθ : (M.map θ)ᵀ = M)
    (hg : adj θ M g ∈ Algebra.adjoin K {g}) (x : ↥(Algebra.adjoin K {g})) :
    adjR θ M hM hg (adjR θ M hM hg x) = x := by
  ext1
  exact adj_adj θ M hM hθ hMθ x

end Restrict

section Structure

variable [Finite K] {g : Matrix ι ι K}

theorem isReduced_adjoin {N : ℕ} (hN : (N : K) ≠ 0) (hgN : g ^ N = 1) :
    IsReduced ↥(Algebra.adjoin K {g}) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hx
  obtain ⟨p, hp⟩ : ∃ p : Polynomial K, Polynomial.aeval g p = x := by
    have hx2 : (x : Matrix ι ι K) ∈ (Polynomial.aeval (R := K) g).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact x.2
    obtain ⟨p, hp⟩ := hx2
    exact ⟨p, hp⟩
  have hint : IsIntegral K g := Algebra.IsIntegral.isIntegral g
  have hmu : minpoly K g ∣ Polynomial.X ^ N - Polynomial.C 1 := by
    apply minpoly.dvd
    simp [hgN]
  have hsq : Squarefree (minpoly K g) :=
    ((Polynomial.separable_X_pow_sub_C 1 hN one_ne_zero).squarefree).squarefree_of_dvd hmu
  have hpk : minpoly K g ∣ p ^ k := by
    apply minpoly.dvd
    rw [map_pow, hp]
    have := congrArg Subtype.val hk
    simpa using this
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have h10 : (1 : ↥(Algebra.adjoin K {g})) = 0 := by simpa using hk
    calc x = x * 1 := (mul_one x).symm
      _ = 0 := by rw [h10, mul_zero]
  have hdvd : minpoly K g ∣ p := (Squarefree.dvd_pow_iff_dvd hsq hk0.ne').mp hpk
  apply Subtype.ext
  rw [← hp, ZeroMemClass.coe_zero]
  obtain ⟨c, rfl⟩ := hdvd
  rw [map_mul, minpoly.aeval, zero_mul]

end Structure

section Main

variable [Finite K]

theorem equivPi_apply_eq_mk {R : Type*} [CommRing R] [IsArtinianRing R] [IsReduced R] (x : R)
    (I : MaximalSpectrum R) : IsArtinianRing.equivPi R x I = Ideal.Quotient.mk I.asIdeal x := by
  have h := (IsArtinianRing.equivPi R).commutes x
  rw [Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h]
  rfl

theorem exists_eightynine_of_involution {R : Type} [CommRing R] [Finite R] [IsReduced R]
    [CharP R 2] (φ : R →+* R) (hφφ : ∀ x, φ (φ x) = x) (G : R) {b : ℕ}
    (hGN : G ^ (23 ^ b) = 1) (hG1 : G ≠ 1) (hφG : φ G = G ^ (23 ^ b - 1)) :
    ∃ z : R, φ z * z = 1 ∧ z ^ 89 = 1 ∧ z ≠ 1 ∧
      ∀ J : MaximalSpectrum R, Ideal.Quotient.mk J.asIdeal G = 1 →
        Ideal.Quotient.mk J.asIdeal z = 1 := by
  classical
  set N := 23 ^ b with hNdef
  have hN0 : 0 < N := by positivity
  let e := IsArtinianRing.equivPi R
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum R, Ideal.Quotient.mk I.asIdeal G ≠ 1 := by
    by_contra h
    push_neg at h
    apply hG1
    apply e.injective
    funext I
    rw [equivPi_apply_eq_mk, equivPi_apply_eq_mk, h I, map_one]
  let φe : R ≃+* R := RingEquiv.ofRingHom φ φ (RingHom.ext hφφ) (RingHom.ext hφφ)
  have hφe : ∀ x, φe x = φ x := fun _ => rfl
  let I' : MaximalSpectrum R :=
    ⟨I.asIdeal.map φe, Ideal.map_isMaximal_of_equiv φe (p := I.asIdeal)⟩
  haveI hImax : I.asIdeal.IsMaximal := I.isMaximal
  letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  haveI : Finite (R ⧸ I.asIdeal) :=
    Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
  haveI : CharP (R ⧸ I.asIdeal) 2 := CharP.quotient' 2 I.asIdeal (fun x hx => by
    rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · push_cast
      rw [← two_mul, CharTwo.two_eq_zero, zero_mul]
    · exfalso
      have h1 : ((2 * k + 1 : ℕ) : R) = 1 := by
        push_cast; rw [CharTwo.two_eq_zero, zero_mul, zero_add]
      rw [h1] at hx
      exact hImax.ne_top ((Ideal.eq_top_iff_one _).mpr hx))
  set ζ : R ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal G with hζ
  have hζN : ζ ^ N = 1 := by rw [hζ, ← map_pow, hGN, map_one]
  have hζ0 : ζ ≠ 0 := by
    intro h0; rw [h0, zero_pow hN0.ne'] at hζN; exact zero_ne_one hζN
  have hII' : I' ≠ I := by
    intro hEq
    have hmap : I.asIdeal = I.asIdeal.map (φe : R →+* R) := by
      have := congrArg MaximalSpectrum.asIdeal hEq
      exact this.symm
    let ψ : (R ⧸ I.asIdeal) ≃+* (R ⧸ I.asIdeal) :=
      Ideal.quotientEquiv I.asIdeal I.asIdeal φe hmap
    have hψ : ψ ζ = ζ ^ (N - 1) := by
      rw [hζ, ← map_pow, ← hφG]
      rfl
    letI : Algebra (ZMod 2) (R ⧸ I.asIdeal) := ZMod.algebra _ 2
    let ψa : (R ⧸ I.asIdeal) ≃ₐ[ZMod 2] (R ⧸ I.asIdeal) :=
      AlgEquiv.ofRingEquiv (f := ψ) (fun x => by
        have := RingHom.ext_zmod ((ψ : (R ⧸ I.asIdeal) →+* (R ⧸ I.asIdeal)).comp
          (algebraMap (ZMod 2) (R ⧸ I.asIdeal))) (algebraMap (ZMod 2) (R ⧸ I.asIdeal))
        exact congrArg (fun f => f x) this)
    obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (k := ZMod 2) (p := 2)
      (l := R ⧸ I.asIdeal) ψa
    have h1 : ζ ^ (2 ^ i) = ζ ^ (N - 1) := by
      have := hi ζ
      rw [Nat.card_zmod] at this
      rw [← this]
      exact hψ
    have hinv : ζ ^ (N - 1) = ζ⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hN0, hζN])
    exact CFSG.ComponentClassification.CatFC.DS81.ClArith.pow_two_pow_ne_inv hζN hI i
      (h1.trans hinv)
  set ζu : (R ⧸ I.asIdeal)ˣ := Units.mk0 ζ hζ0 with hζu
  have h23 : 23 ∣ orderOf ζu := by
    have hd : orderOf ζu ∣ 23 ^ b :=
      orderOf_dvd_of_pow_eq_one (Units.ext (by simpa [hζu] using hζN))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 23)).mp hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hI (by simpa [hζu] using congrArg Units.val hk)
    rw [hk]; exact dvd_pow_self 23 hk0
  have hcard : 89 ∣ Nat.card (R ⧸ I.asIdeal)ˣ :=
    CFSG.ComponentClassification.CatFC.DS81.ClArith.eightynine_dvd_card_units h23
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := (R ⧸ I.asIdeal)ˣ) 89 hcard
  have hw89 : w ^ 89 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : (w : R ⧸ I.asIdeal) ≠ 1 := by
    intro h
    have : w = 1 := Units.ext h
    rw [this, orderOf_one] at hw
    norm_num at hw
  let r : R := e.symm (Pi.mulSingle I (w : R ⧸ I.asIdeal))
  have her : e r = Pi.mulSingle I (w : R ⧸ I.asIdeal) := e.apply_symm_apply _
  have hrJ : ∀ J : MaximalSpectrum R, Ideal.Quotient.mk J.asIdeal r =
      Pi.mulSingle (M := fun J : MaximalSpectrum R => R ⧸ J.asIdeal) I
        (w : R ⧸ I.asIdeal) J := by
    intro J; rw [← equivPi_apply_eq_mk, her]
  have hr89 : r ^ 89 = 1 := by
    apply e.injective
    rw [map_pow, her, map_one, ← Pi.mulSingle_pow, ← Units.val_pow_eq_pow_val, hw89,
      Units.val_one, Pi.mulSingle_one]
  have hs : ∀ x, φe.symm x = φ x := by
    intro x
    apply φe.injective
    rw [RingEquiv.apply_symm_apply, hφe, hφφ]
  have hφr : Ideal.Quotient.mk I.asIdeal (φ r) = 1 := by
    have h1 : Ideal.Quotient.mk I'.asIdeal r = 1 := by
      rw [hrJ, Pi.mulSingle_eq_of_ne hII']
    have h2 : r - 1 ∈ I'.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
    have h3 : φ (r - 1) ∈ I.asIdeal := by
      have h4 : r - 1 ∈ I.asIdeal.map (φe : R →+* R) := h2
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at h4
      have h5 := hs (r - 1)
      rwa [h5] at h4
    rw [map_sub, map_one] at h3
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk I.asIdeal), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact h3
  refine ⟨r * φ r ^ 88, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_pow, hφφ]
    calc φ r * r ^ 88 * (r * φ r ^ 88) = (φ r) ^ 89 * r ^ 89 := by ring
      _ = 1 := by rw [← map_pow, hr89, map_one, one_mul]
  · rw [mul_pow, ← pow_mul, hr89, one_mul, mul_comm 88 89, pow_mul, ← map_pow, hr89, map_one,
      one_pow]
  · intro h
    have := congrArg (Ideal.Quotient.mk I.asIdeal) h
    rw [map_mul, map_pow, hφr, one_pow, mul_one, map_one, hrJ, Pi.mulSingle_eq_same] at this
    exact hw1 this
  ·
    intro J hJ
    have hJI : J ≠ I := by rintro rfl; exact hI hJ
    let J' : MaximalSpectrum R :=
      ⟨J.asIdeal.map φe, Ideal.map_isMaximal_of_equiv φe (p := J.asIdeal)⟩
    have hJ'I : J' ≠ I := by
      intro hEq
      apply hI
      have h1 : G - 1 ∈ J.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hJ, map_one, sub_self]
      have h2 : φ (G - 1) ∈ I.asIdeal := by
        have h3 : φe (G - 1) ∈ J.asIdeal.map (φe : R →+* R) := Ideal.mem_map_of_mem _ h1
        have h4 : J'.asIdeal = I.asIdeal := congrArg MaximalSpectrum.asIdeal hEq
        rw [← hφe]
        exact h4 ▸ h3
      rw [map_sub, map_one, hφG] at h2
      have h5 : ζ ^ (N - 1) = 1 := by
        rw [← sub_eq_zero, hζ, ← map_pow, ← map_one (Ideal.Quotient.mk I.asIdeal), ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem]
        exact h2
      have hinv : ζ ^ (N - 1) = ζ⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hN0, hζN])
      rw [hinv, inv_eq_one] at h5
      exact h5
    have hrJ1 : Ideal.Quotient.mk J.asIdeal r = 1 := by
      rw [hrJ, Pi.mulSingle_eq_of_ne hJI]
    have hφrJ : Ideal.Quotient.mk J.asIdeal (φ r) = 1 := by
      have h1 : Ideal.Quotient.mk J'.asIdeal r = 1 := by
        rw [hrJ, Pi.mulSingle_eq_of_ne hJ'I]
      have h2 : r - 1 ∈ J'.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : φ (r - 1) ∈ J.asIdeal := by
        have h4 : r - 1 ∈ J.asIdeal.map (φe : R →+* R) := h2
        rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at h4
        rwa [hs (r - 1)] at h4
      rw [map_sub, map_one] at h3
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J.asIdeal), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact h3
    rw [map_mul, map_pow, hrJ1, hφrJ, one_pow, one_mul]

theorem exists_eightynine_of_pow {R : Type} [CommRing R] [Finite R] [IsReduced R]
    [CharP R 2] (G : R) {b : ℕ} (hGN : G ^ (23 ^ b) = 1) (hG1 : G ≠ 1) :
    ∃ z : R, z ^ 89 = 1 ∧ z ≠ 1 := by
  classical
  set N := 23 ^ b with hNdef
  have hN0 : 0 < N := by positivity
  let e := IsArtinianRing.equivPi R
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum R, Ideal.Quotient.mk I.asIdeal G ≠ 1 := by
    by_contra h
    push_neg at h
    apply hG1
    apply e.injective
    funext I
    rw [equivPi_apply_eq_mk, equivPi_apply_eq_mk, h I, map_one]
  haveI hImax : I.asIdeal.IsMaximal := I.isMaximal
  letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  haveI : Finite (R ⧸ I.asIdeal) :=
    Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
  haveI : CharP (R ⧸ I.asIdeal) 2 := CharP.quotient' 2 I.asIdeal (fun x hx => by
    rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · push_cast
      rw [← two_mul, CharTwo.two_eq_zero, zero_mul]
    · exfalso
      have h1 : ((2 * k + 1 : ℕ) : R) = 1 := by
        push_cast; rw [CharTwo.two_eq_zero, zero_mul, zero_add]
      rw [h1] at hx
      exact hImax.ne_top ((Ideal.eq_top_iff_one _).mpr hx))
  set ζ : R ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal G with hζ
  have hζN : ζ ^ N = 1 := by rw [hζ, ← map_pow, hGN, map_one]
  have hζ0 : ζ ≠ 0 := by
    intro h0; rw [h0, zero_pow hN0.ne'] at hζN; exact zero_ne_one hζN
  set ζu : (R ⧸ I.asIdeal)ˣ := Units.mk0 ζ hζ0 with hζu
  have h23 : 23 ∣ orderOf ζu := by
    have hd : orderOf ζu ∣ 23 ^ b :=
      orderOf_dvd_of_pow_eq_one (Units.ext (by simpa [hζu] using hζN))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 23)).mp hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hI (by simpa [hζu] using congrArg Units.val hk)
    rw [hk]; exact dvd_pow_self 23 hk0
  have hcard : 89 ∣ Nat.card (R ⧸ I.asIdeal)ˣ :=
    CFSG.ComponentClassification.CatFC.DS81.ClArith.eightynine_dvd_card_units h23
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := (R ⧸ I.asIdeal)ˣ) 89 hcard
  have hw89 : w ^ 89 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : (w : R ⧸ I.asIdeal) ≠ 1 := by
    intro h
    have : w = 1 := Units.ext h
    rw [this, orderOf_one] at hw
    norm_num at hw
  let r : R := e.symm (Pi.mulSingle I (w : R ⧸ I.asIdeal))
  have her : e r = Pi.mulSingle I (w : R ⧸ I.asIdeal) := e.apply_symm_apply _
  refine ⟨r, ?_, ?_⟩
  · apply e.injective
    rw [map_pow, her, map_one, ← Pi.mulSingle_pow, ← Units.val_pow_eq_pow_val, hw89,
      Units.val_one, Pi.mulSingle_one]
  · intro h
    have := congrArg (fun x => e x I) h
    simp only [her, Pi.mulSingle_eq_same, map_one, Pi.one_apply] at this
    exact hw1 this

theorem exists_split_sub_one {R : Type} [CommRing R] [Finite R] [IsReduced R] (G : R) :
    ∃ s t : R, s * (G - 1) + t = 1 ∧ t * (G - 1) = 0 ∧
      ∀ x : R, (∀ J : MaximalSpectrum R, Ideal.Quotient.mk J.asIdeal G = 1 →
        Ideal.Quotient.mk J.asIdeal x = 1) → (x - 1) * t = 0 := by
  classical
  let e := IsArtinianRing.equivPi R
  let tt : ∀ J : MaximalSpectrum R, R ⧸ J.asIdeal := fun J =>
    if Ideal.Quotient.mk J.asIdeal G = 1 then 1 else 0
  let ss : ∀ J : MaximalSpectrum R, R ⧸ J.asIdeal := fun J =>
    if Ideal.Quotient.mk J.asIdeal G = 1 then 0
    else Ring.inverse (Ideal.Quotient.mk J.asIdeal G - 1)
  have hcomp : ∀ (x : R) (J : MaximalSpectrum R), e x J = Ideal.Quotient.mk J.asIdeal x :=
    fun x J => equivPi_apply_eq_mk x J
  refine ⟨e.symm ss, e.symm tt, ?_, ?_, ?_⟩
  · apply e.injective
    funext J
    rw [map_add, map_mul, map_one, Pi.add_apply, Pi.mul_apply, Pi.one_apply, e.apply_symm_apply,
      e.apply_symm_apply, hcomp, map_sub, map_one]
    simp only [ss, tt]
    split_ifs with h
    · rw [h, sub_self, mul_zero, zero_add]
    · haveI := J.isMaximal
      letI : Field (R ⧸ J.asIdeal) := Ideal.Quotient.field J.asIdeal
      have hu : IsUnit (Ideal.Quotient.mk J.asIdeal G - 1) :=
        isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h)
      rw [Ring.inverse_mul_cancel _ hu, add_zero]
  · apply e.injective
    funext J
    rw [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply, e.apply_symm_apply, hcomp, map_sub, map_one]
    simp only [tt]
    split_ifs with h
    · rw [h, sub_self, mul_zero]
    · rw [zero_mul]
  · intro x hx
    apply e.injective
    funext J
    rw [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply, e.apply_symm_apply, hcomp, map_sub, map_one]
    simp only [tt]
    split_ifs with h
    · rw [hx J h, sub_self, zero_mul]
    · rw [mul_zero]

theorem exists_form_order_eightynine [CharP K 2] (θ : K →+* K)
    (hθ : ∀ c, θ (θ c) = c) (M : Matrix ι ι K) (hM : IsUnit M.det) (hMθ : (M.map θ)ᵀ = M)
    (g : Matrix ι ι K) (hg : (g.map θ)ᵀ * M * g = M) {b : ℕ} (hgb : g ^ (23 ^ b) = 1)
    (hg1 : g ≠ 1) :
    ∃ z ∈ Algebra.adjoin K {g}, (z.map θ)ᵀ * M * z = M ∧ z ^ 89 = 1 ∧ z ≠ 1 := by
  classical
  have hN0 : 0 < 23 ^ b := by positivity
  have hNK : ((23 ^ b : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    exact fun h => by
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)
      norm_num at this
  have hga : adj θ M g * g = 1 := adj_mul_self_of_form θ M hM hg
  have hgR : adj θ M g ∈ Algebra.adjoin K {g} := by
    rw [adj_eq_pow θ M hM hga hN0 hgb]
    exact pow_mem (Algebra.self_mem_adjoin_singleton K g) _
  haveI : IsReduced ↥(Algebra.adjoin K {g}) := isReduced_adjoin hNK hgb
  let G : ↥(Algebra.adjoin K {g}) := ⟨g, Algebra.self_mem_adjoin_singleton K g⟩
  have hG1 : G ≠ 1 := fun h => hg1 (congrArg Subtype.val h)
  haveI : Nontrivial ↥(Algebra.adjoin K {g}) := ⟨⟨G, 1, hG1⟩⟩
  haveI : CharP ↥(Algebra.adjoin K {g}) 2 :=
    charP_of_injective_algebraMap (algebraMap K ↥(Algebra.adjoin K {g})).injective 2
  have hGN : G ^ (23 ^ b) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hgb
  have hφG : adjR θ M hM hgR G = G ^ (23 ^ b - 1) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact adj_eq_pow θ M hM hga hN0 hgb
  obtain ⟨z, hz1, hz2, hz3, -⟩ := exists_eightynine_of_involution (adjR θ M hM hgR)
    (adjR_adjR θ M hM hθ hMθ hgR) G hGN hG1 hφG
  refine ⟨z, z.2, ?_, ?_, ?_⟩
  · apply form_of_adj_mul_self θ M hM
    have := congrArg Subtype.val hz1
    rwa [MulMemClass.coe_mul, adjR_apply, OneMemClass.coe_one] at this
  · have := congrArg Subtype.val hz2
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  · intro h
    exact hz3 (Subtype.ext (by rw [h, OneMemClass.coe_one]))

theorem eq_one_of_pow_eightynine {c : K} (hK : ¬ 89 ∣ Nat.card K - 1) (hc : c ^ 89 = 1) :
    c = 1 := by
  classical
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  set u : Kˣ := Units.mk0 c hc0
  have hu : u ^ 89 = 1 := Units.ext (by simpa [u] using hc)
  have hd : orderOf u ∣ 89 := orderOf_dvd_of_pow_eq_one hu
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 89)).mp hd with h | h
  · have := orderOf_eq_one_iff.mp h
    simpa [u] using congrArg Units.val this
  · exfalso
    apply hK
    have := Fintype.ofFinite K
    rw [← h, show Nat.card K - 1 = Nat.card Kˣ by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]]
    exact orderOf_dvd_natCard u

theorem exists_det_one_order_eightynine [CharP K 2] (hK : ¬ 89 ∣ Nat.card K - 1)
    (g : Matrix ι ι K) {b : ℕ} (hgb : g ^ (23 ^ b) = 1) (hg1 : g ≠ 1) :
    ∃ z ∈ Algebra.adjoin K {g}, z.det = 1 ∧ z ^ 89 = 1 ∧ ∀ c : K, z ≠ Matrix.scalar ι c := by
  classical
  have hNK : ((23 ^ b : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    exact fun h => by
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)
      norm_num at this
  haveI : IsReduced ↥(Algebra.adjoin K {g}) := isReduced_adjoin hNK hgb
  let G : ↥(Algebra.adjoin K {g}) := ⟨g, Algebra.self_mem_adjoin_singleton K g⟩
  have hG1 : G ≠ 1 := fun h => hg1 (congrArg Subtype.val h)
  haveI : Nontrivial ↥(Algebra.adjoin K {g}) := ⟨⟨G, 1, hG1⟩⟩
  haveI : CharP ↥(Algebra.adjoin K {g}) 2 :=
    charP_of_injective_algebraMap (algebraMap K ↥(Algebra.adjoin K {g})).injective 2
  have hGN : G ^ (23 ^ b) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hgb
  obtain ⟨z, hz1, hz2⟩ := exists_eightynine_of_pow G hGN hG1
  have hz89 : (z : Matrix ι ι K) ^ 89 = 1 := by
    have := congrArg Subtype.val hz1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  refine ⟨z, z.2, ?_, hz89, ?_⟩
  · apply eq_one_of_pow_eightynine hK
    rw [← Matrix.det_pow, hz89, Matrix.det_one]
  · intro c hc
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hg1 (Subsingleton.elim _ _)
    have hc89 : c ^ 89 = 1 := by
      have h1 : Matrix.scalar ι (c ^ 89) = Matrix.scalar ι 1 := by
        rw [map_pow, ← hc, hz89, map_one]
      exact (Matrix.scalar_inj).mp h1
    have hc1 : c = 1 := eq_one_of_pow_eightynine hK hc89
    apply hz2
    apply Subtype.ext
    rw [hc, hc1, map_one, OneMemClass.coe_one]

end Main

section Quadratic

theorem dotProduct_mulVec_conj (A M : Matrix ι ι K) (x y : ι → K) :
    (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ y)) = x ⬝ᵥ ((Aᵀ * M * A) *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem eq_of_dotProduct_mulVec {A B : Matrix ι ι K}
    (h : ∀ x y : ι → K, x ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ (B *ᵥ y)) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

end Quadratic


section QuadraticMain

variable [Finite K]

theorem exists_quadForm_order_eightynine [CharP K 2] (Q : (ι → K) → K) (M : Matrix ι ι K)
    (hM : IsUnit M.det) (hMT : Mᵀ = M)
    (hpolar : ∀ u v, Q (u + v) = Q u + Q v + u ⬝ᵥ (M *ᵥ v))
    (g : Matrix ι ι K) (hgQ : ∀ v, Q (g *ᵥ v) = Q v) {b : ℕ} (hgb : g ^ (23 ^ b) = 1)
    (hg1 : g ≠ 1) :
    ∃ z ∈ Algebra.adjoin K {g}, (∀ v, Q (z *ᵥ v) = Q v) ∧ z ^ 89 = 1 ∧ z ≠ 1 := by
  classical
  have hgM : (g.map (RingHom.id K))ᵀ * M * g = M := by
    rw [show g.map (RingHom.id K) = g from Matrix.map_id' g]
    apply eq_of_dotProduct_mulVec
    intro x y
    rw [← dotProduct_mulVec_conj]
    have h1 := hpolar (g *ᵥ x) (g *ᵥ y)
    have h2 := hpolar x y
    rw [← Matrix.mulVec_add, hgQ, hgQ, hgQ] at h1
    exact add_left_cancel (h1.symm.trans h2)
  have hMθ : (M.map (RingHom.id K))ᵀ = M := by
    rw [show M.map (RingHom.id K) = M from Matrix.map_id' M, hMT]
  have hθ : ∀ c : K, (RingHom.id K) ((RingHom.id K) c) = c := fun _ => rfl
  set θ := RingHom.id K
  have hN0 : 0 < 23 ^ b := by positivity
  have hNK : ((23 ^ b : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    exact fun h => by
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)
      norm_num at this
  have hga : adj θ M g * g = 1 := adj_mul_self_of_form θ M hM hgM
  have hgR : adj θ M g ∈ Algebra.adjoin K {g} := by
    rw [adj_eq_pow θ M hM hga hN0 hgb]
    exact pow_mem (Algebra.self_mem_adjoin_singleton K g) _
  haveI : IsReduced ↥(Algebra.adjoin K {g}) := isReduced_adjoin hNK hgb
  let G : ↥(Algebra.adjoin K {g}) := ⟨g, Algebra.self_mem_adjoin_singleton K g⟩
  have hG1 : G ≠ 1 := fun h => hg1 (congrArg Subtype.val h)
  haveI : Nontrivial ↥(Algebra.adjoin K {g}) := ⟨⟨G, 1, hG1⟩⟩
  haveI : CharP ↥(Algebra.adjoin K {g}) 2 :=
    charP_of_injective_algebraMap (algebraMap K ↥(Algebra.adjoin K {g})).injective 2
  have hGN : G ^ (23 ^ b) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hgb
  have hφG : adjR θ M hM hgR G = G ^ (23 ^ b - 1) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact adj_eq_pow θ M hM hga hN0 hgb
  obtain ⟨z, hz1, hz2, hz3, hz4⟩ := exists_eightynine_of_involution (adjR θ M hM hgR)
    (adjR_adjR θ M hM hθ hMθ hgR) G hGN hG1 hφG
  obtain ⟨s, t, hst, -, htz⟩ := exists_split_sub_one G
  have hzt := htz z hz4
  set zM : Matrix ι ι K := (z : Matrix ι ι K) with hzM
  set sM : Matrix ι ι K := (s : Matrix ι ι K) with hsM
  set tM : Matrix ι ι K := (t : Matrix ι ι K) with htM
  have hzt' : zM * tM = tM := by
    have := congrArg Subtype.val hzt
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
      ZeroMemClass.coe_zero] at this
    rw [sub_mul, one_mul, sub_eq_zero] at this
    exact this
  have hst' : sM * (g - 1) + tM = 1 := by
    have := congrArg Subtype.val hst
    simpa only [AddMemClass.coe_add, MulMemClass.coe_mul, AddSubgroupClass.coe_sub,
      OneMemClass.coe_one] using this
  have hsg : sM * (g - 1) = (g - 1) * sM := by
    have := congrArg Subtype.val (mul_comm s (G - 1))
    simpa only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one] using this
  have hzg : zM * (g - 1) = (g - 1) * zM := by
    have := congrArg Subtype.val (mul_comm z (G - 1))
    simpa only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one] using this
  have hzg' : zM * g = g * zM := by
    have := congrArg Subtype.val (mul_comm z G)
    simpa only [MulMemClass.coe_mul] using this
  have hzform : zMᵀ * M * zM = M := by
    have h1 : adj θ M zM * zM = 1 := by
      have := congrArg Subtype.val hz1
      rwa [MulMemClass.coe_mul, adjR_apply, OneMemClass.coe_one] at this
    have := form_of_adj_mul_self θ M hM h1
    rwa [show zM.map θ = zM from Matrix.map_id' zM] at this
  have hzB : ∀ x y : ι → K, (zM *ᵥ x) ⬝ᵥ (M *ᵥ (zM *ᵥ y)) = x ⬝ᵥ (M *ᵥ y) := by
    intro x y; rw [dotProduct_mulVec_conj, hzform]
  have hneg : ∀ w : ι → K, -w = w := fun w => funext fun i => CharTwo.neg_eq (w i)
  have hQsub : ∀ w : ι → K, Q ((g - 1) *ᵥ w) = (g *ᵥ w) ⬝ᵥ (M *ᵥ w) := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_add_neg, hneg, hpolar, hgQ,
      CharTwo.add_self_eq_zero, zero_add]
  refine ⟨zM, z.2, ?_, ?_, ?_⟩
  · intro v
    set u := sM *ᵥ v with hu
    set w := tM *ᵥ v with hw
    have hv : v = (g - 1) *ᵥ u + w := by
      have := congrArg (fun A => A *ᵥ v) hst'
      simp only [Matrix.add_mulVec, Matrix.one_mulVec] at this
      rw [← this, hsg, ← Matrix.mulVec_mulVec]
    have hzw : zM *ᵥ w = w := by rw [hw, Matrix.mulVec_mulVec, hzt']
    have hzv : zM *ᵥ v = (g - 1) *ᵥ (zM *ᵥ u) + w := by
      conv_lhs => rw [hv]
      rw [Matrix.mulVec_add, hzw, Matrix.mulVec_mulVec, hzg, ← Matrix.mulVec_mulVec]
    have hA : Q ((g - 1) *ᵥ (zM *ᵥ u)) = Q ((g - 1) *ᵥ u) := by
      rw [hQsub, hQsub, Matrix.mulVec_mulVec, ← hzg', ← Matrix.mulVec_mulVec, hzB]
    have hB : ((g - 1) *ᵥ (zM *ᵥ u)) ⬝ᵥ (M *ᵥ w) = ((g - 1) *ᵥ u) ⬝ᵥ (M *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, ← hzg, ← Matrix.mulVec_mulVec]
      conv_lhs => rw [← hzw]
      rw [hzB]
    rw [hzv, hpolar, hA, hB, ← hpolar, ← hv]
  · have := congrArg Subtype.val hz2
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  · intro h
    exact hz3 (Subtype.ext (by rw [← hzM, h, OneMemClass.coe_one]))

end QuadraticMain

end CFSG.ComponentClassification.CatFC.DS81.ClCore
