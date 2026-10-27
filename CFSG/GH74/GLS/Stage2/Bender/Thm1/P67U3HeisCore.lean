module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3HeisZ
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3HeisNum
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Geo
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Toral
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnField
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3HeisFrame

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical
open scoped commutatorElement

section Core

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_conj_mem_D (y : U3T h) :
    (MulAut.conj y : MulAut (U3T h)) ∈
      primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have hs : (s : GL (Fin 3) K) ∈ U3U h := ((mem_gramSU_iff_unitary h).1 s.2).1
  refine ⟨⟨s, hs⟩, ?_⟩
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk]
  simp only [MulAut.conj_apply]
  rfl

theorem u3_psi_fix_scalar (F x : U3U h) (g : ↥(gramSU h ((1 : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K))) {ζ : Kˣ} (hζN : h.bar (ζ : K) * ζ = 1) (hζ3 : ζ ^ 3 = 1)
    (e : (x : GL (Fin 3) K) * ((F : GL (Fin 3) K) * g * (F : GL (Fin 3) K)⁻¹) *
      (x : GL (Fin 3) K)⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ *
        ((F : GL (Fin 3) K) * g * (F : GL (Fin 3) K)⁻¹)) :
    primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x (u3Psi h F g) =
      u3Psi h F g := by
  show primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x
    ((primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) F g : _) : U3T h) = _
  rw [primeFormConjHom_mk]
  change _ = ((primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) F g : _) :
    U3T h)
  rw [QuotientGroup.eq]
  have hζ'N : h.bar ((ζ⁻¹ : Kˣ) : K) * ((ζ⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hζN, inv_one]
  refine ⟨ζ⁻¹, ?_, by rw [inv_pow, hζ3, inv_one], ?_⟩
  · rw [UnitaryFieldData.norm, mul_comm]; exact hζ'N
  · show (((x : GL (Fin 3) K) * ((F : GL (Fin 3) K) * g * (F : GL (Fin 3) K)⁻¹) *
        (x : GL (Fin 3) K)⁻¹))⁻¹ * ((F : GL (Fin 3) K) * g * (F : GL (Fin 3) K)⁻¹) = _
    rw [e, _root_.mul_inv_rev, ← map_inv,
      ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ _).inv_left).eq]
    group

theorem u3_diag_mul_cyc (d c : Fin 3 → K) (h1 : d 1 = c 1 * d 0) (h2 : d 2 = c 2 * d 1)
    (h0 : d 0 = c 0 * d 2) :
    Matrix.diagonal d * (u3CycMat : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal c * ((u3CycMat : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [u3CycMat] <;> first | exact h1 | exact h2 | exact h0

@[expose] noncomputable def u3Tor (s : Kˣ) : GL (Fin 3) K := unitaryDiagGL ![s ^ 2, s⁻¹, s⁻¹]

@[expose] noncomputable def u3Com (s : Kˣ) : GL (Fin 3) K := unitaryDiagGL ![s ^ 3, (s ^ 3)⁻¹, 1]

theorem coe_u3Tor (s : Kˣ) : ((u3Tor s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.diagonal ![(s : K) ^ 2, (s : K)⁻¹, (s : K)⁻¹] := by
  rw [u3Tor, coe_unitaryDiagGL]
  congr 1
  funext i
  fin_cases i <;> simp

theorem coe_u3Com (s : Kˣ) : ((u3Com s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.diagonal ![(s : K) ^ 3, ((s : K) ^ 3)⁻¹, 1] := by
  rw [u3Com, coe_unitaryDiagGL]
  congr 1
  funext i
  fin_cases i <;> simp

theorem u3_norm_pow {s : Kˣ} (hs : h.bar (s : K) * s = 1) (k : ℕ) :
    h.norm (((s ^ k : Kˣ) : K)) = 1 := by
  rw [UnitaryFieldData.norm, Units.val_pow_eq_pow_val, map_pow, ← mul_pow, mul_comm, hs, one_pow]

theorem u3Tor_mem {s : Kˣ} (hs : h.bar (s : K) * s = 1) :
    u3Tor s ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hn : h.norm (s : K) = 1 := by rw [UnitaryFieldData.norm, mul_comm]; exact hs
  have hn' : h.norm ((s⁻¹ : Kˣ) : K) = 1 := by
    have := u3_norm_pow h hs 1
    rw [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, mul_comm, hs,
      inv_one]
  refine unitaryDiagGL_mem_gramSU h (d := ![s ^ 2, s⁻¹, s⁻¹]) (fun i => ?_) ?_
  · fin_cases i
    · exact u3_norm_pow h hs 2
    · exact hn'
    · exact hn'
  · simp [Fin.prod_univ_three]
    field_simp

theorem u3Com_mem {s : Kˣ} (hs : h.bar (s : K) * s = 1) :
    u3Com s ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hn1 : h.norm (((1 : Kˣ)) : K) = 1 := by
    rw [UnitaryFieldData.norm, Units.val_one, map_one, mul_one]
  have hn' : h.norm (((s ^ 3)⁻¹ : Kˣ) : K) = 1 := by
    have := u3_norm_pow h hs 3
    rw [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv,
      ← UnitaryFieldData.norm,
      this, inv_one]
  refine unitaryDiagGL_mem_gramSU h (d := ![s ^ 3, (s ^ 3)⁻¹, 1]) (fun i => ?_) ?_
  · fin_cases i
    · exact u3_norm_pow h hs 3
    · exact hn'
    · exact hn1
  · simp [Fin.prod_univ_three]

theorem u3Tor_comm_cyc (s : Kˣ) :
    (u3Tor s : GL (Fin 3) K) * u3CycGL = u3Com s * (u3CycGL * u3Tor s) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_u3CycGL, coe_u3Tor, coe_u3Com]
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have := u3_diag_mul_cyc (K := K) ![(s : K) ^ 2, (s : K)⁻¹, (s : K)⁻¹]
    ![(s : K) ^ 3, ((s : K) ^ 3)⁻¹, 1] (by simp; field_simp) (by simp) (by simp; field_simp)
  exact this

include h in
theorem u3_exists_gen : ∃ s : Kˣ, orderOf s = p ^ f + 1 := by
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

theorem u3_conj_fix_scalar_aux {F x g : GL (Fin 3) K} {d : Fin 3 → K} {ζ : Kˣ}
    (hd0 : ∀ k, d k ≠ 0)
    (hxF : (x : Matrix (Fin 3) (Fin 3) K) * (F : Matrix (Fin 3) (Fin 3) K) =
      (F : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d)
    (hcomm : Matrix.diagonal d * (g : Matrix (Fin 3) (Fin 3) K) =
      (ζ : K) • ((g : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d)) :
    x * (F * g * F⁻¹) * x⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * (F * g * F⁻¹) := by
  set Dg : GL (Fin 3) K := GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d)
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k) with hDg
  have hxF' : x * F = F * Dg := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hxF)
  have hcomm' : Dg * g = GeneralLinearGroup.scalar (Fin 3) ζ * (g * Dg) := Units.ext (by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scalar_smul, Matrix.smul_mul,
      Matrix.one_mul]
    exact hcomm)
  have h1 : Dg * g * Dg⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * g := by rw [hcomm']; group
  have hc : F * GeneralLinearGroup.scalar (Fin 3) ζ = GeneralLinearGroup.scalar (Fin 3) ζ * F :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ F).eq
  calc x * (F * g * F⁻¹) * x⁻¹ = (x * F) * g * (x * F)⁻¹ := by group
    _ = F * (Dg * g * Dg⁻¹) * F⁻¹ := by rw [hxF']; group
    _ = F * (GeneralLinearGroup.scalar (Fin 3) ζ * g) * F⁻¹ := by rw [h1]
    _ = (F * GeneralLinearGroup.scalar (Fin 3) ζ) * g * F⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin 3) ζ * (F * g * F⁻¹) := by rw [hc]; group

theorem false_of_u3_heis (hp5 : 5 ≤ p) {V Z : Subgroup (MulAut (U3T h))}
    (h2 : N2Cfg (U3T h) 3 V Z) (h3 : N3Deriv (U3T h) V Z) (a b : U3U h) (u : Kˣ) (hu : u ≠ 1)
    (ha : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a ∈ V)
    (hb : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) b ∈ V)
    (hab : (a : GL (Fin 3) K) * b =
      GeneralLinearGroup.scalar (Fin 3) u * ((b : GL (Fin 3) K) * a)) : False := by
  classical
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  set c := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hc
  obtain ⟨hr, hodd, hVe, hVc, hZab, hZodd, hZcop, hZbot, hcomm⟩ := id h2
  have hVe' : ∀ v ∈ V, v ^ 3 = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  obtain ⟨E, x, y, ξ, m0, hx, hy, hξ3, hξ1, hξN, hm0, hm0N, hxE, hxy⟩ :=
    u3_heis_frame h hVe' a b u hu ha hb hab
  have hZD := u3_heis_inter_D h hZcop hcomm hVe' hξ3 hξ1 hm0 hx hy hxE hxy
  have hu3 : u ^ 3 = 1 := comm_scalar_cube hab
  have h3q : 3 ∣ p ^ f + 1 := u3_three_dvd h a.2 b.2 hu hu3 hab
  have hq2 : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h4⟩
    have : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    rw [h4] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
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
  have ht3 : t ≠ 3 := by
    intro h3'
    have := Nat.Coprime.coprime_dvd_left htd hZcop
    rw [h3'] at this
    exact absurd this (by decide)
  have hz1 : (z : MulAut (U3T h)) ≠ 1 := by
    intro h1
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    exact htp.one_lt.ne hz
  have hzt : (z : MulAut (U3T h)) ^ t = 1 := by
    have : z ^ t = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    simpa using congrArg Subtype.val this
  have hreal :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_prime_form_full_semilinear_realization
    h (isPrimeFormGram_one (n := 3)) (le_refl 3) hq2
  obtain ⟨τ, ⟨X, hzX⟩, -⟩ := hreal.2.2.2.2.1 (z : MulAut (U3T h))
  have hτψ : primeFormFieldFactor h (isPrimeFormGram_one (n := 3)) (le_refl 3) hq2
      (z : MulAut (U3T h)) = τ := by rw [hzX]; exact hreal.2.2.2.2.2.1 X τ
  have hτ1 : τ ≠ 1 := by
    intro h1
    have hzD : (z : MulAut (U3T h)) ∈
        primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hzX, h1, map_one, mul_one]
      exact ⟨X, rfl⟩
    exact hz1 (hZD _ z.2 hzD)
  have hτt : τ ^ t = 1 := by
    rw [← hτψ, ← map_pow, hzt, map_one]
  have hτord : orderOf τ = t := orderOf_eq_prime hτt hτ1
  obtain ⟨s, hs⟩ := u3_exists_gen h
  have hsN : h.bar (s : K) * s = 1 := by
    rw [h.bar_apply, ← pow_succ]
    have : s ^ (p ^ f + 1) = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
    simpa using congrArg Units.val this
  have hP : (u3CycGL : GL (Fin 3) K) ∈ gramSU h ((1 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) := by
    rw [← u3_SUid_eq h]
    exact u3CycGL_mem _
  set Tor' : ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    ⟨u3Tor s, u3Tor_mem h hsN⟩ with hTor'
  set Cyc' : ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := ⟨u3CycGL, hP⟩
    with hCyc'
  set Com' : ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    ⟨u3Com s, u3Com_mem h hsN⟩ with hCom'
  have hcom : ⁅Tor', Cyc'⁆ = Com' := by
    apply Subtype.ext
    have h1 := map_commutatorElement (gramSU h ((1 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)).subtype Tor' Cyc'
    refine h1.trans ?_
    show ⁅u3Tor s, (u3CycGL : GL (Fin 3) K)⁆ = u3Com s
    rw [commutatorElement_def, u3Tor_comm_cyc]
    group
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  set ξu : Kˣ := Units.mk0 ξ hξ0 with hξu
  have hξuN : h.bar (ξu : K) * ξu = 1 := hξN
  have hξu3 : ξu ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, hξu, Units.val_mk0]; exact hξ3)
  have hd0 : ∀ k : Fin 3, ξ ^ (k : ℕ) * m0 ≠ 0 := fun k =>
    mul_ne_zero (pow_ne_zero _ hξ0) hm0
  have hTfix : c x (u3Psi h E Tor') = u3Psi h E Tor' := by
    refine u3_psi_fix_scalar h E x Tor' (ζ := 1) (by simp) (by simp) ?_
    rw [map_one, one_mul]
    refine u3_conj_fix_aux hd0 hxE ?_
    show Matrix.diagonal (fun i : Fin 3 => ξ ^ (i : ℕ) * m0) *
      ((u3Tor s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [coe_u3Tor, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)
  have hCfix : c x (u3Psi h E Cyc') = u3Psi h E Cyc' := by
    refine u3_psi_fix_scalar h E x Cyc' (ζ := ξu) hξuN hξu3 ?_
    refine u3_conj_fix_scalar_aux hd0 hxE ?_
    have h0 := u3_diag_mul_cyc (K := K) (fun i : Fin 3 => ξ ^ (i : ℕ) * m0) (fun _ => ξ)
      (by simp) (by simp; ring) (by simp; linear_combination (-m0) * hξ3)
    show Matrix.diagonal (fun i : Fin 3 => ξ ^ (i : ℕ) * m0) *
      ((u3CycGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ξ • _
    rw [coe_u3CycGL, h0, ← Matrix.smul_eq_diagonal_mul]
  have hcmem : u3Psi h E Com' ∈ ⁅fixSub (c x), fixSub (c x)⁆ := by
    rw [← hcom, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (mem_fixSub.2 hTfix) (mem_fixSub.2 hCfix)
  have hcx1 : c x ≠ 1 := by
    intro h1
    obtain ⟨w, hw⟩ := (u3_conj_eq_one_iff h x).1 h1
    have hxs : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (w : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by rw [hw, coe_scalar_smul]
    have hall := (u3f_scalar_iff (E : GL (Fin 3) K).isUnit hxE (w : K)).1 hxs
    have h01 : ξ ^ ((0 : Fin 3) : ℕ) * m0 = ξ ^ ((1 : Fin 3) : ℕ) * m0 :=
      (hall 0).trans (hall 1).symm
    apply hξ1
    have : m0 = ξ * m0 := by simpa using h01
    exact (mul_right_cancel₀ hm0 (by rw [one_mul]; exact this.symm))
  have hTs := isSimpleGroup_primeFormP_one h (le_refl 3) hq2
  have hTn := not_commute_primeFormP_one h (le_refl 3) hq2
  have hcen : Subgroup.center (U3T h) = ⊥ := by
    refine un_center_eq_bot_of_simple hTs ?_
    by_contra hcon
    push Not at hcon
    exact hTn fun a b => hcon a b
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hnorm := h3 (c x) hx hcx1 (u3Psi h E Com') hcmem
  have hzc : (z : MulAut (U3T h)) (u3Psi h E Com') = u3Psi h E Com' := by
    set cc := u3Psi h E Com' with hcc
    have hzZ : (z : MulAut (U3T h)) ∈ Z := z.2
    have h1 := (Subgroup.mem_normalizer_iff.mp hnorm _).mp hzZ
    have h4 : MulAut.conj cc * (z : MulAut (U3T h)) * (MulAut.conj cc)⁻¹ *
        (z : MulAut (U3T h))⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hzZ)
    have h5 : MulAut.conj cc * (z : MulAut (U3T h)) * (MulAut.conj cc)⁻¹ *
        (z : MulAut (U3T h))⁻¹ = MulAut.conj (cc * (z : MulAut (U3T h)) cc⁻¹) := by
      have : (z : MulAut (U3T h)) * (MulAut.conj cc)⁻¹ * (z : MulAut (U3T h))⁻¹ =
          MulAut.conj ((z : MulAut (U3T h)) cc⁻¹) := by
        have := mulAut_conj_conj (z : MulAut (U3T h)) cc⁻¹
        simpa [map_inv] using this
      calc MulAut.conj cc * (z : MulAut (U3T h)) * (MulAut.conj cc)⁻¹ *
            (z : MulAut (U3T h))⁻¹
          = MulAut.conj cc * ((z : MulAut (U3T h)) * (MulAut.conj cc)⁻¹ *
              (z : MulAut (U3T h))⁻¹) := by group
        _ = MulAut.conj (cc * (z : MulAut (U3T h)) cc⁻¹) := by rw [this, map_mul]
    rw [h5] at h4
    have h6 := hZD _ h4 (u3_conj_mem_D h _)
    have h7 : cc * (z : MulAut (U3T h)) cc⁻¹ = 1 := hinj (by rw [h6, map_one])
    have h8 : (z : MulAut (U3T h)) cc⁻¹ = cc⁻¹ := by
      have := congrArg (fun t => cc⁻¹ * t) h7
      simpa using this
    have := congrArg (fun t => t⁻¹) h8
    simpa using this
  have hzc' : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) X
      (primeFormFieldHom h (isPrimeFormGram_one (n := 3)) τ (u3Psi h E Com')) =
        u3Psi h E Com' := by
    have h1 := hzc
    rw [hzX, MulAut.mul_apply] at h1
    exact h1
  have e1 : primeFormFieldHom h (isPrimeFormGram_one (n := 3)) τ (u3Psi h E Com') =
      ((primeFormFieldSU h (isPrimeFormGram_one (n := 3)) τ
        (primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) E Com') : _) :
          U3T h) :=
    primeFormFieldAut_mk h (isPrimeFormGram_one (n := 3)) τ _
  rw [e1, primeFormConjHom_mk] at hzc'
  change _ = ((primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) E Com' : _) :
    U3T h) at hzc'
  rw [QuotientGroup.eq] at hzc'
  obtain ⟨ζ, hζN, hζ3, hζ⟩ := hzc'
  have hζ' : ((X : GL (Fin 3) K) * glAut τ ((E : GL (Fin 3) K) * u3Com s * (E : GL (Fin 3) K)⁻¹) *
      (X : GL (Fin 3) K)⁻¹)⁻¹ * ((E : GL (Fin 3) K) * u3Com s * (E : GL (Fin 3) K)⁻¹) =
        GeneralLinearGroup.scalar (Fin 3) ζ := hζ
  set Xp : GL (Fin 3) K := (E : GL (Fin 3) K)⁻¹ * X * glAut τ (E : GL (Fin 3) K) with hXp
  have hW : (X : GL (Fin 3) K) * glAut τ ((E : GL (Fin 3) K) * u3Com s * (E : GL (Fin 3) K)⁻¹) *
      (X : GL (Fin 3) K)⁻¹ = ((E : GL (Fin 3) K) * u3Com s * (E : GL (Fin 3) K)⁻¹) *
        GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by
    rw [map_inv, ← hζ']
    group
  have hX' : Xp * glAut τ (u3Com s : GL (Fin 3) K) * Xp⁻¹ =
      u3Com s * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by
    have h1 : (X : GL (Fin 3) K) * (glAut τ (E : GL (Fin 3) K) * glAut τ (u3Com s : GL (Fin 3) K) *
        (glAut τ (E : GL (Fin 3) K))⁻¹) * (X : GL (Fin 3) K)⁻¹ =
          ((E : GL (Fin 3) K) * u3Com s * (E : GL (Fin 3) K)⁻¹) *
            GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by
      rw [← hW, map_mul, map_mul, map_inv]
    have h2 : (E : GL (Fin 3) K)⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * (E : GL (Fin 3) K)⁻¹ :=
      ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ (E : GL (Fin 3) K)).inv_left).eq
    calc Xp * glAut τ (u3Com s : GL (Fin 3) K) * Xp⁻¹
        = (E : GL (Fin 3) K)⁻¹ * ((X : GL (Fin 3) K) * (glAut τ (E : GL (Fin 3) K) *
            glAut τ (u3Com s : GL (Fin 3) K) * (glAut τ (E : GL (Fin 3) K))⁻¹) *
              (X : GL (Fin 3) K)⁻¹) * (E : GL (Fin 3) K) := by rw [hXp]; group
      _ = (E : GL (Fin 3) K)⁻¹ * (((E : GL (Fin 3) K) * u3Com s * (E : GL (Fin 3) K)⁻¹) *
            GeneralLinearGroup.scalar (Fin 3) ζ⁻¹) * (E : GL (Fin 3) K) := by rw [h1]
      _ = u3Com s * ((E : GL (Fin 3) K)⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ *
            (E : GL (Fin 3) K)) := by group
      _ = u3Com s * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by rw [h2]; group
  have hτcS : ((glAut τ (u3Com s : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![τ (s : K) ^ 3, (τ (s : K) ^ 3)⁻¹, 1] := by
    rw [coe_glAut, coe_u3Com, Matrix.diagonal_map (map_zero τ)]
    congr 1
    funext i
    fin_cases i <;> simp [map_pow, map_inv₀]
  have hmat : ((Xp : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal ![τ (s : K) ^ 3, (τ (s : K) ^ 3)⁻¹, 1] *
      ((Xp⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((ζ⁻¹ : Kˣ) : K) • Matrix.diagonal ![(s : K) ^ 3, ((s : K) ^ 3)⁻¹, 1] := by
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hX'
    simp only [Units.val_mul, hτcS, coe_u3Com, coe_scalar_smul, Matrix.mul_smul,
      Matrix.mul_one] at h1
    exact h1
  exact u3_heis_torus_contra h hp5 h3q htp ht2 ht3 τ hτord s hs Xp ((ζ⁻¹ : Kˣ) : K) hmat

end Core

end CFSG.GH74.GLS.Stage2.Bender.Thm1
