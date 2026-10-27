module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqBase
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqHeisFrame
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqHeisNum
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqHeisZ
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnField
import CFSG.GH74.GLS.Stage2.OddAut.LinNAut
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical
open scoped commutatorElement

section Elements

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uq_norm_pow {s : Kˣ} (hs : h.bar (s : K) * s = 1) (k : ℕ) :
    h.norm (((s ^ k : Kˣ) : K)) = 1 := by
  rw [UnitaryFieldData.norm, Units.val_pow_eq_pow_val, map_pow, ← mul_pow, mul_comm, hs, one_pow]

include h in
theorem uq_exists_gen : ∃ s : Kˣ, orderOf s = p ^ f + 1 := by
  have : Finite K := h.finite
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, pow_mul']
  have hq : 1 < p ^ f := by
    have : Fact p.Prime := ⟨h.prime⟩
    have := h.charP
    exact CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      CFSG.ClassicalGroups.Unitary.card_units_of_card hK]
  refine ⟨g ^ (p ^ f - 1), ?_⟩
  have hdvd : p ^ f - 1 ∣ orderOf g := by
    rw [hord, CFSG.ClassicalGroups.Unitary.sq_sub_one_eq _ hq.le]
    exact Dvd.intro_left _ rfl
  rw [orderOf_pow_of_dvd (by omega) hdvd, hord, CFSG.ClassicalGroups.Unitary.sq_sub_one_eq _ hq.le,
    Nat.mul_div_cancel _ (by omega)]

theorem uq_psi_fix_scalar (F x : UqU h n) (g : ↥(gramSU h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K))) {ζ : Kˣ} (hζN : h.bar (ζ : K) * ζ = 1) (hζn : ζ ^ n = 1)
    (e : (x : GL (Fin n) K) * ((F : GL (Fin n) K) * g * (F : GL (Fin n) K)⁻¹) *
      (x : GL (Fin n) K)⁻¹ = GeneralLinearGroup.scalar (Fin n) ζ *
        ((F : GL (Fin n) K) * g * (F : GL (Fin n) K)⁻¹)) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x (uqPsi h n F g) =
      uqPsi h n F g := by
  show primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x
    ((primeFormConjSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) F g : _) : UqT h n) = _
  rw [primeFormConjHom_mk]
  change _ = ((primeFormConjSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) F g : _) :
    UqT h n)
  rw [QuotientGroup.eq]
  have hζ'N : h.bar ((ζ⁻¹ : Kˣ) : K) * ((ζ⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hζN, inv_one]
  refine ⟨ζ⁻¹, ?_, by rw [inv_pow, hζn, inv_one], ?_⟩
  · rw [UnitaryFieldData.norm, mul_comm]; exact hζ'N
  · show (((x : GL (Fin n) K) * ((F : GL (Fin n) K) * g * (F : GL (Fin n) K)⁻¹) *
        (x : GL (Fin n) K)⁻¹))⁻¹ * ((F : GL (Fin n) K) * g * (F : GL (Fin n) K)⁻¹) = _
    rw [e, _root_.mul_inv_rev, ← map_inv,
      ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ _).inv_left).eq]
    group

theorem uq_conj_fix_scalar_aux {F x g : GL (Fin n) K} {d : Fin n → K} {ζ : Kˣ}
    (hd0 : ∀ k, d k ≠ 0)
    (hxF : (x : Matrix (Fin n) (Fin n) K) * (F : Matrix (Fin n) (Fin n) K) =
      (F : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d)
    (hcomm : Matrix.diagonal d * (g : Matrix (Fin n) (Fin n) K) =
      (ζ : K) • ((g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d)) :
    x * (F * g * F⁻¹) * x⁻¹ = GeneralLinearGroup.scalar (Fin n) ζ * (F * g * F⁻¹) := by
  set Dg : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d)
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k) with hDg
  have hxF' : x * F = F * Dg := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hxF)
  have hcomm' : Dg * g = GeneralLinearGroup.scalar (Fin n) ζ * (g * Dg) := Units.ext (by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scalar_smul_n, Matrix.smul_mul,
      Matrix.one_mul]
    exact hcomm)
  have h1 : Dg * g * Dg⁻¹ = GeneralLinearGroup.scalar (Fin n) ζ * g := by rw [hcomm']; group
  have hc : F * GeneralLinearGroup.scalar (Fin n) ζ = GeneralLinearGroup.scalar (Fin n) ζ * F :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ F).eq
  calc x * (F * g * F⁻¹) * x⁻¹ = (x * F) * g * (x * F)⁻¹ := by group
    _ = F * (Dg * g * Dg⁻¹) * F⁻¹ := by rw [hxF']; group
    _ = F * (GeneralLinearGroup.scalar (Fin n) ζ * g) * F⁻¹ := by rw [h1]
    _ = (F * GeneralLinearGroup.scalar (Fin n) ζ) * g * F⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin n) ζ * (F * g * F⁻¹) := by rw [hc]; group

theorem uq_diag_eq_of_scalar {E x : GL (Fin n) K} {d : Fin n → K} {w : K}
    (hxE : (x : Matrix (Fin n) (Fin n) K) * (E : Matrix (Fin n) (Fin n) K) =
      (E : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d)
    (hx : (x : Matrix (Fin n) (Fin n) K) = w • (1 : Matrix (Fin n) (Fin n) K)) (i : Fin n) :
    d i = w := by
  have h1 : Matrix.diagonal d = w • (1 : Matrix (Fin n) (Fin n) K) := by
    calc Matrix.diagonal d = ((E⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (E : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      _ = ((E⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : Matrix (Fin n) (Fin n) K) * (E : Matrix (Fin n) (Fin n) K)) := by
          rw [Matrix.mul_assoc, ← hxE]
      _ = w • (1 : Matrix (Fin n) (Fin n) K) := by
          rw [hx, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Units.val_mul,
            inv_mul_cancel, Units.val_one]
  have := congrFun (congrFun h1 i) i
  simpa using this

end Elements

section Five

variable {K : Type} [Field K]

@[expose] noncomputable def uq5Cyc : GL (Fin 5) K := unitaryPermGL (finRotate 5)

theorem uq5Cyc_apply (a b : Fin 5) :
    ((uq5Cyc : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) a b = if a + 1 = b then 1 else 0 := by
  rw [uq5Cyc, coe_unitaryPermGL, permMatrix_apply']
  have : finRotate 5 a = a + 1 := finRotate_apply a
  rw [this]

theorem uq5_diag_mul_cyc (d c : Fin 5 → K) (hdc : ∀ a : Fin 5, d a = c a * d (a + 1)) :
    Matrix.diagonal d * ((uq5Cyc : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal c * (((uq5Cyc : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        Matrix.diagonal d) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, uq5Cyc_apply]
  by_cases hab : a + 1 = b
  · subst hab
    simp only [ite_true, mul_one]
    rw [hdc a]
    ring
  · simp [hab]

@[expose] noncomputable def uq5Tor (s : Kˣ) : GL (Fin 5) K :=
  unitaryDiagGL ![s, (s ^ 4)⁻¹, s, s, s]

@[expose] noncomputable def uq5Com (s : Kˣ) : GL (Fin 5) K :=
  unitaryDiagGL ![s ^ 5, (s ^ 5)⁻¹, 1, 1, 1]

theorem coe_uq5Tor (s : Kˣ) : ((uq5Tor s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
    Matrix.diagonal ![(s : K), ((s : K) ^ 4)⁻¹, (s : K), (s : K), (s : K)] := by
  rw [uq5Tor, coe_unitaryDiagGL]
  congr 1
  funext i
  fin_cases i <;> simp

theorem coe_uq5Com (s : Kˣ) : ((uq5Com s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
    Matrix.diagonal ![(s : K) ^ 5, ((s : K) ^ 5)⁻¹, 1, 1, 1] := by
  rw [uq5Com, coe_unitaryDiagGL]
  congr 1
  funext i
  fin_cases i <;> simp

theorem uq5Tor_comm_cyc (s : Kˣ) :
    (uq5Tor s : GL (Fin 5) K) * uq5Cyc = uq5Com s * (uq5Cyc * uq5Tor s) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_uq5Tor, coe_uq5Com]
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  refine uq5_diag_mul_cyc (K := K) ![(s : K), ((s : K) ^ 4)⁻¹, (s : K), (s : K), (s : K)]
    ![(s : K) ^ 5, ((s : K) ^ 5)⁻¹, 1, 1, 1] fun a => ?_
  fin_cases a <;> simp <;> field_simp

end Five

section Members

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uq5Tor_mem {s : Kˣ} (hs : h.bar (s : K) * s = 1) :
    uq5Tor s ∈ gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  have hn : h.norm (s : K) = 1 := by rw [UnitaryFieldData.norm, mul_comm]; exact hs
  have hn' : h.norm (((s ^ 4)⁻¹ : Kˣ) : K) = 1 := by
    have := uq_norm_pow h hs 4
    rw [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv,
      ← UnitaryFieldData.norm, this, inv_one]
  refine unitaryDiagGL_mem_gramSU h (d := ![s, (s ^ 4)⁻¹, s, s, s]) (fun i => ?_) ?_
  · fin_cases i
    · exact hn
    · exact hn'
    · exact hn
    · exact hn
    · exact hn
  · simp [Fin.prod_univ_five]
    field_simp

theorem uq5Com_mem {s : Kˣ} (hs : h.bar (s : K) * s = 1) :
    uq5Com s ∈ gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  have hn1 : h.norm (((1 : Kˣ)) : K) = 1 := by
    rw [UnitaryFieldData.norm, Units.val_one, map_one, mul_one]
  have hn' : h.norm (((s ^ 5)⁻¹ : Kˣ) : K) = 1 := by
    have := uq_norm_pow h hs 5
    rw [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv,
      ← UnitaryFieldData.norm, this, inv_one]
  refine unitaryDiagGL_mem_gramSU h (d := ![s ^ 5, (s ^ 5)⁻¹, 1, 1, 1]) (fun i => ?_) ?_
  · fin_cases i
    · exact uq_norm_pow h hs 5
    · exact hn'
    · exact hn1
    · exact hn1
    · exact hn1
  · simp [Fin.prod_univ_five]

theorem uq5Cyc_mem [Finite K] [Fact p.Prime] [CharP K p] :
    (uq5Cyc : GL (Fin 5) K) ∈ gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  refine unitaryPermGL_mem_gramSU h ?_
  rw [sign_finRotate]
  decide

end Members


section Main

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem false_of_uq5_heis (hp2 : p ≠ 2) (h5 : 5 ∣ p ^ f + 1)
    {V Z : Subgroup (MulAut (UqT h 5))} (h2 : N2Cfg (UqT h 5) 5 V Z)
    (h3 : N3Deriv (UqT h 5) V Z) (a b : UqU h 5) (u : Kˣ) (hu : u ≠ 1)
    (ha : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) a ∈ V)
    (hb : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) b ∈ V)
    (hab : (a : GL (Fin 5) K) * b =
      GeneralLinearGroup.scalar (Fin 5) u * ((b : GL (Fin 5) K) * a)) : False := by
  classical
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  set c := primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hc
  obtain ⟨hr, hodd, hVe, hVc, hZab, hZodd, hZcop, hZbot, hcomm⟩ := id h2
  have hVe' : ∀ v ∈ V, v ^ 5 = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  obtain ⟨E, x, y, ξ, m0, hx, hy, hξ5, hξ1, hξN, hm0, hm0N, hxE, hxy⟩ :=
    uq5_heis_frame h h5 hVe' a b u hu ha hb hab
  have hZD := uq5_heis_inter_D h hZcop hcomm hVe' hξ5 hξ1 hm0 hx hy hxE hxy
  have hq2 : ¬(5 = 3 ∧ p ^ f = 2) := by omega
  have hn3 : 3 ≤ 5 := by norm_num
  have hZfin : Finite ↥Z := Nat.finite_of_card_ne_zero hZodd.pos.ne'
  have hZnt : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZbot
  have hZ1 : 1 < Nat.card ↥Z := Finite.one_lt_card_iff_nontrivial.2 hZnt
  have htp : (Nat.card ↥Z).minFac.Prime := Nat.minFac_prime (by omega)
  set t := (Nat.card ↥Z).minFac with htdef
  have htd : t ∣ Nat.card ↥Z := Nat.minFac_dvd _
  have : Fact t.Prime := ⟨htp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) t htd
  have ht2 : t ≠ 2 := by
    rintro h2'
    have := Odd.of_dvd_nat hZodd htd
    rw [h2'] at this
    exact absurd this (by decide)
  have ht5 : t ≠ 5 := by
    intro h5'
    have := Nat.Coprime.coprime_dvd_left htd hZcop
    rw [h5'] at this
    exact absurd this (by decide)
  have hz1 : (z : MulAut (UqT h 5)) ≠ 1 := by
    intro h1
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    exact htp.one_lt.ne hz
  have hzt : (z : MulAut (UqT h 5)) ^ t = 1 := by
    have : z ^ t = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    simpa using congrArg Subtype.val this
  have hreal :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_prime_form_full_semilinear_realization
    h (isPrimeFormGram_one (n := 5)) hn3 hq2
  obtain ⟨τ, ⟨X, hzX⟩, -⟩ := hreal.2.2.2.2.1 (z : MulAut (UqT h 5))
  have hτψ : primeFormFieldFactor h (isPrimeFormGram_one (n := 5)) hn3 hq2
      (z : MulAut (UqT h 5)) = τ := by rw [hzX]; exact hreal.2.2.2.2.2.1 X τ
  have hτ1 : τ ≠ 1 := by
    intro h1
    have hzD : (z : MulAut (UqT h 5)) ∈
        primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
      rw [hzX, h1, map_one, mul_one]
      exact ⟨X, rfl⟩
    exact hz1 (hZD _ z.2 hzD)
  have hτt : τ ^ t = 1 := by
    rw [← hτψ, ← map_pow, hzt, map_one]
  have hτord : orderOf τ = t := orderOf_eq_prime hτt hτ1
  obtain ⟨s, hs⟩ := uq_exists_gen h
  have hsN : h.bar (s : K) * s = 1 := by
    rw [h.bar_apply, ← pow_succ]
    have : s ^ (p ^ f + 1) = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
    simpa using congrArg Units.val this
  have hP : (uq5Cyc : GL (Fin 5) K) ∈ gramSU h ((1 : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) := uq5Cyc_mem h
  set Tor' : ↥(gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :=
    ⟨uq5Tor s, uq5Tor_mem h hsN⟩ with hTor'
  set Cyc' : ↥(gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) := ⟨uq5Cyc, hP⟩
    with hCyc'
  set Com' : ↥(gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :=
    ⟨uq5Com s, uq5Com_mem h hsN⟩ with hCom'
  have hcom : ⁅Tor', Cyc'⁆ = Com' := by
    apply Subtype.ext
    have h1 := map_commutatorElement (gramSU h ((1 : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)).subtype Tor' Cyc'
    refine h1.trans ?_
    show ⁅uq5Tor s, (uq5Cyc : GL (Fin 5) K)⁆ = uq5Com s
    rw [commutatorElement_def, uq5Tor_comm_cyc]
    group
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ5
  set ξu : Kˣ := Units.mk0 ξ hξ0 with hξu
  have hξuN : h.bar (ξu : K) * ξu = 1 := hξN
  have hξu5 : ξu ^ 5 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, hξu, Units.val_mk0]; exact hξ5)
  have hd0 : ∀ k : Fin 5, ξ ^ (k : ℕ) * m0 ≠ 0 := fun k =>
    mul_ne_zero (pow_ne_zero _ hξ0) hm0
  have hTfix : c x (uqPsi h 5 E Tor') = uqPsi h 5 E Tor' := by
    refine uq_psi_fix_scalar h E x Tor' (ζ := 1) (by simp) (by simp) ?_
    refine uq_conj_fix_scalar_aux hd0 hxE ?_
    show Matrix.diagonal (fun i : Fin 5 => ξ ^ (i : ℕ) * m0) *
      ((uq5Tor s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = _
    rw [coe_uq5Tor, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Units.val_one,
      one_smul]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)
  have hCfix : c x (uqPsi h 5 E Cyc') = uqPsi h 5 E Cyc' := by
    have hζN : h.bar ((ξu⁻¹ : Kˣ) : K) * ((ξu⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hξuN, inv_one]
    refine uq_psi_fix_scalar h E x Cyc' (ζ := ξu⁻¹) hζN (by rw [inv_pow, hξu5, inv_one]) ?_
    refine uq_conj_fix_scalar_aux hd0 hxE ?_
    have h0 := uq5_diag_mul_cyc (K := K) (fun i : Fin 5 => ξ ^ (i : ℕ) * m0) (fun _ => ξ⁻¹) (by
      intro a
      fin_cases a
      · simp; field_simp
      · simp; field_simp
      · simp; field_simp
      · simp; field_simp
      · simp; field_simp; left; exact hξ5)
    show Matrix.diagonal (fun i : Fin 5 => ξ ^ (i : ℕ) * m0) *
      ((uq5Cyc : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = ((ξu⁻¹ : Kˣ) : K) • _
    rw [h0, Units.val_inv_eq_inv_val, hξu, Units.val_mk0, ← Matrix.smul_eq_diagonal_mul]
  have hcmem : uqPsi h 5 E Com' ∈ ⁅fixSub (c x), fixSub (c x)⁆ := by
    rw [← hcom, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (mem_fixSub.2 hTfix) (mem_fixSub.2 hCfix)
  have hcx1 : c x ≠ 1 := by
    intro h1
    obtain ⟨w, hw⟩ := (uq_conj_eq_one_iff h hn3 x).1 h1
    have hxs : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        (w : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by rw [hw, coe_scalar_smul_n]
    have h01 : ξ ^ ((0 : Fin 5) : ℕ) * m0 = ξ ^ ((1 : Fin 5) : ℕ) * m0 :=
      (uq_diag_eq_of_scalar hxE hxs 0).trans (uq_diag_eq_of_scalar hxE hxs 1).symm
    apply hξ1
    have : m0 = ξ * m0 := by simpa using h01
    exact (mul_right_cancel₀ hm0 (by rw [one_mul]; exact this.symm))
  have hTs := isSimpleGroup_primeFormP_one h hn3 hq2
  have hTn := not_commute_primeFormP_one h hn3 hq2
  have hcen : Subgroup.center (UqT h 5) = ⊥ := by
    refine un_center_eq_bot_of_simple hTs ?_
    by_contra hcon
    push Not at hcon
    exact hTn fun a b => hcon a b
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hnorm := h3 (c x) hx hcx1 (uqPsi h 5 E Com') hcmem
  have hzc : (z : MulAut (UqT h 5)) (uqPsi h 5 E Com') = uqPsi h 5 E Com' := by
    set cc := uqPsi h 5 E Com' with hcc
    have hzZ : (z : MulAut (UqT h 5)) ∈ Z := z.2
    have h1 := (Subgroup.mem_normalizer_iff.mp hnorm _).mp hzZ
    have h4 : MulAut.conj cc * (z : MulAut (UqT h 5)) * (MulAut.conj cc)⁻¹ *
        (z : MulAut (UqT h 5))⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hzZ)
    have h5' : MulAut.conj cc * (z : MulAut (UqT h 5)) * (MulAut.conj cc)⁻¹ *
        (z : MulAut (UqT h 5))⁻¹ = MulAut.conj (cc * (z : MulAut (UqT h 5)) cc⁻¹) := by
      have : (z : MulAut (UqT h 5)) * (MulAut.conj cc)⁻¹ * (z : MulAut (UqT h 5))⁻¹ =
          MulAut.conj ((z : MulAut (UqT h 5)) cc⁻¹) := by
        have := mulAut_conj_conj (z : MulAut (UqT h 5)) cc⁻¹
        simpa [map_inv] using this
      calc MulAut.conj cc * (z : MulAut (UqT h 5)) * (MulAut.conj cc)⁻¹ *
            (z : MulAut (UqT h 5))⁻¹
          = MulAut.conj cc * ((z : MulAut (UqT h 5)) * (MulAut.conj cc)⁻¹ *
              (z : MulAut (UqT h 5))⁻¹) := by group
        _ = MulAut.conj (cc * (z : MulAut (UqT h 5)) cc⁻¹) := by rw [this, map_mul]
    rw [h5'] at h4
    have h6 := hZD _ h4 (uq_conj_mem_D h _)
    have h7 : cc * (z : MulAut (UqT h 5)) cc⁻¹ = 1 := hinj (by rw [h6, map_one])
    have h8 : (z : MulAut (UqT h 5)) cc⁻¹ = cc⁻¹ := by
      have := congrArg (fun t => cc⁻¹ * t) h7
      simpa using this
    have := congrArg (fun t => t⁻¹) h8
    simpa using this
  have hzc' : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) X
      (primeFormFieldHom h (isPrimeFormGram_one (n := 5)) τ (uqPsi h 5 E Com')) =
        uqPsi h 5 E Com' := by
    have h1 := hzc
    rw [hzX, MulAut.mul_apply] at h1
    exact h1
  have e1 : primeFormFieldHom h (isPrimeFormGram_one (n := 5)) τ (uqPsi h 5 E Com') =
      ((primeFormFieldSU h (isPrimeFormGram_one (n := 5)) τ
        (primeFormConjSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) E Com') : _) :
          UqT h 5) :=
    primeFormFieldAut_mk h (isPrimeFormGram_one (n := 5)) τ _
  rw [e1, primeFormConjHom_mk] at hzc'
  change _ = ((primeFormConjSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) E Com' : _) :
    UqT h 5) at hzc'
  rw [QuotientGroup.eq] at hzc'
  obtain ⟨ζ, hζN, hζ5, hζ⟩ := hzc'
  have hζ' : ((X : GL (Fin 5) K) * glAut τ ((E : GL (Fin 5) K) * uq5Com s *
      (E : GL (Fin 5) K)⁻¹) * (X : GL (Fin 5) K)⁻¹)⁻¹ *
      ((E : GL (Fin 5) K) * uq5Com s * (E : GL (Fin 5) K)⁻¹) =
        GeneralLinearGroup.scalar (Fin 5) ζ := hζ
  set Xp : GL (Fin 5) K := (E : GL (Fin 5) K)⁻¹ * X * glAut τ (E : GL (Fin 5) K) with hXp
  have hW : (X : GL (Fin 5) K) * glAut τ ((E : GL (Fin 5) K) * uq5Com s *
      (E : GL (Fin 5) K)⁻¹) * (X : GL (Fin 5) K)⁻¹ = ((E : GL (Fin 5) K) * uq5Com s *
        (E : GL (Fin 5) K)⁻¹) * GeneralLinearGroup.scalar (Fin 5) ζ⁻¹ := by
    rw [map_inv, ← hζ']
    group
  have hX' : Xp * glAut τ (uq5Com s : GL (Fin 5) K) * Xp⁻¹ =
      uq5Com s * GeneralLinearGroup.scalar (Fin 5) ζ⁻¹ := by
    have h1 : (X : GL (Fin 5) K) * (glAut τ (E : GL (Fin 5) K) *
        glAut τ (uq5Com s : GL (Fin 5) K) * (glAut τ (E : GL (Fin 5) K))⁻¹) *
          (X : GL (Fin 5) K)⁻¹ = ((E : GL (Fin 5) K) * uq5Com s * (E : GL (Fin 5) K)⁻¹) *
            GeneralLinearGroup.scalar (Fin 5) ζ⁻¹ := by
      rw [← hW, map_mul, map_mul, map_inv]
    have h2 : (E : GL (Fin 5) K)⁻¹ * GeneralLinearGroup.scalar (Fin 5) ζ⁻¹ =
        GeneralLinearGroup.scalar (Fin 5) ζ⁻¹ * (E : GL (Fin 5) K)⁻¹ :=
      ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ (E : GL (Fin 5) K)).inv_left).eq
    calc Xp * glAut τ (uq5Com s : GL (Fin 5) K) * Xp⁻¹
        = (E : GL (Fin 5) K)⁻¹ * ((X : GL (Fin 5) K) * (glAut τ (E : GL (Fin 5) K) *
            glAut τ (uq5Com s : GL (Fin 5) K) * (glAut τ (E : GL (Fin 5) K))⁻¹) *
              (X : GL (Fin 5) K)⁻¹) * (E : GL (Fin 5) K) := by rw [hXp]; group
      _ = (E : GL (Fin 5) K)⁻¹ * (((E : GL (Fin 5) K) * uq5Com s * (E : GL (Fin 5) K)⁻¹) *
            GeneralLinearGroup.scalar (Fin 5) ζ⁻¹) * (E : GL (Fin 5) K) := by rw [h1]
      _ = uq5Com s * ((E : GL (Fin 5) K)⁻¹ * GeneralLinearGroup.scalar (Fin 5) ζ⁻¹ *
            (E : GL (Fin 5) K)) := by group
      _ = uq5Com s * GeneralLinearGroup.scalar (Fin 5) ζ⁻¹ := by rw [h2]; group
  have hτcS : ((glAut τ (uq5Com s : GL (Fin 5) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal ![τ (s : K) ^ 5, (τ (s : K) ^ 5)⁻¹, 1, 1, 1] := by
    rw [coe_glAut, coe_uq5Com, Matrix.diagonal_map (map_zero τ)]
    congr 1
    funext i
    fin_cases i <;> simp [map_pow, map_inv₀]
  have hmat : ((Xp : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      Matrix.diagonal ![τ (s : K) ^ 5, (τ (s : K) ^ 5)⁻¹, 1, 1, 1] *
      ((Xp⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((ζ⁻¹ : Kˣ) : K) • Matrix.diagonal ![(s : K) ^ 5, ((s : K) ^ 5)⁻¹, 1, 1, 1] := by
    have h1 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K)) hX'
    simp only [Units.val_mul, hτcS, coe_uq5Com, coe_scalar_smul_n, Matrix.mul_smul,
      Matrix.mul_one] at h1
    exact h1
  exact uq5_heis_torus_contra h hp2 h5 htp ht2 ht5 τ hτord s hs Xp ((ζ⁻¹ : Kˣ) : K) hmat

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
