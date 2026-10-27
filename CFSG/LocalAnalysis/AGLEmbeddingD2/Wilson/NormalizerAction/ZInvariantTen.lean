module

public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.CentralizerExtraspecial

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.LinearAlgebra Module Polynomial

theorem ten_dvd_finrank_of_pow_eleven {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M] (T : Module.End (ZMod 2) M) (hT : T ^ 11 = 1)
    (hfix : ∀ m, T m = m → m = 0) : 10 ∣ finrank (ZMod 2) M := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  by_cases hM : Subsingleton M
  · rw [Module.finrank_zero_of_subsingleton]
    exact dvd_zero _
  rw [not_subsingleton_iff_nontrivial] at hM
  let Tu : (Module.End (ZMod 2) M)ˣ := Units.ofPowEqOne T 11 hT (by norm_num)
  let ρ : Representation (ZMod 2) (Module.End (ZMod 2) M)ˣ M := Units.coeHom _
  have hρ : ρ Tu = T := rfl
  have hTp : ρ Tu ^ 11 = 1 := hT
  have hΦ := irreducible_cyclotomic_two (p := 11) (by norm_num) orderOf_two_zmod_eleven'
  have hfixed : centralFixed ρ Tu = ⊥ := by
    refine eq_bot_iff.2 fun m hm => ?_
    rw [Submodule.mem_bot]
    refine hfix m ?_
    simpa [centralFixed, hρ, sub_eq_zero] using hm
  have hcompl := isCompl_centralFixed_centralImage (p := 11) (by norm_num) hTp
  rw [hfixed] at hcompl
  have htop : centralImage ρ Tu = ⊤ := by
    simpa using hcompl.sup_eq_top
  have hΦT : aeval T (cyclotomic 11 (ZMod 2)) = 0 := by
    refine LinearMap.ext fun m => ?_
    have hm : m ∈ centralImage ρ Tu := by rw [htop]; trivial
    rw [centralImage_eq_ker_cyclotomic (p := 11) (by norm_num) hTp, LinearMap.mem_ker] at hm
    exact hm
  have hfield := isField_adjoin_singleton_of_aeval_eq_zero hΦ T hΦT
  have hfr := finrank_adjoin_singleton_of_aeval_eq_zero hΦ (cyclotomic.monic 11 (ZMod 2)) T hΦT
  rw [natDegree_cyclotomic_two] at hfr
  let _ : Field (Algebra.adjoin (ZMod 2) {T}) := hfield.toField
  have hfin : FiniteDimensional (Algebra.adjoin (ZMod 2) {T}) M :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) _ M
  have := Module.finrank_mul_finrank (ZMod 2) (Algebra.adjoin (ZMod 2) {T}) M
  rw [hfr] at this
  exact ⟨_, this.symm⟩

theorem ten_dvd_finrank_of_invariant_of_no_fixed {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (z : V ≃ₗ[ZMod 2] V) (hz : z ^ 11 = 1)
    (S : Submodule (ZMod 2) V) (hS : ∀ s ∈ S, z s ∈ S) (hfix : ∀ s ∈ S, z s = s → s = 0) :
    10 ∣ finrank (ZMod 2) S := by
  let T : Module.End (ZMod 2) S := (z : V →ₗ[ZMod 2] V).restrict hS
  have hpow : ∀ n : ℕ, ∀ s : S, ((T ^ n) s : V) = (z ^ n) (s : V) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
      rfl
  refine ten_dvd_finrank_of_pow_eleven T ?_ fun m hm => ?_
  · refine LinearMap.ext fun s => Subtype.ext ?_
    rw [hpow, hz]
    rfl
  · have := hfix m m.2 (by simpa [T] using congrArg Subtype.val hm)
    exact Subtype.ext this

theorem aeval_apply_of_apply_eq_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (c : Module.End (ZMod 2) V) {s : V} (hs : c s = s) (f : (ZMod 2)[X]) :
    aeval c f s = f.eval 1 • s := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg, eval_add, add_smul]
  | monomial n a =>
    have hpow : (c ^ n) s = s := by
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hs, ih]
    rw [aeval_monomial, Module.End.mul_apply, hpow, eval_monomial, one_pow, mul_one]
    rfl

theorem ten_dvd_finrank_ker_aeval_of_fixed_trivial {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (z : V ≃ₗ[ZMod 2] V) (hz : z ^ 11 = 1)
    (c : V ≃ₗ[ZMod 2] V) (hcz : c * z = z * c) (hCU : ∀ u, z u = u → c u = u)
    (f : (ZMod 2)[X]) (hf : f.eval 1 ≠ 0) :
    10 ∣ finrank (ZMod 2) (LinearMap.ker (aeval (c : V →ₗ[ZMod 2] V) f)) := by
  set C : Module.End (ZMod 2) V := (c : V →ₗ[ZMod 2] V) with hC
  set Z : Module.End (ZMod 2) V := (z : V →ₗ[ZMod 2] V) with hZ
  have hcomm : Commute Z C := by
    refine LinearMap.ext fun v => ?_
    exact (congrArg (fun g : V ≃ₗ[ZMod 2] V => g v) hcz).symm
  refine ten_dvd_finrank_of_invariant_of_no_fixed z hz (LinearMap.ker (aeval C f)) ?_ ?_
  · intro s hs
    rw [LinearMap.mem_ker] at hs ⊢
    rw [show (z : V →ₗ[ZMod 2] V) = Z from rfl] at *
    have h := (commute_aeval_of_commute hcomm f).eq
    have := congrArg (fun A : Module.End (ZMod 2) V => A s) h
    simp only [Module.End.mul_apply, hs, map_zero] at this
    exact this.symm
  · intro s hs hzs
    rw [LinearMap.mem_ker] at hs
    rw [aeval_apply_of_apply_eq_self C (hCU s hzs) f] at hs
    exact (smul_eq_zero.1 hs).resolve_left hf

theorem ten_dvd_finrank_ker_aeval_of_commute {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (z : V ≃ₗ[ZMod 2] V) (hz : z ^ 11 = 1)
    (hU : finrank (ZMod 2) (LinearMap.ker ((z : V →ₗ[ZMod 2] V) - 1)) = 2)
    (c : V ≃ₗ[ZMod 2] V) (hcz : c * z = z * c) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hcr : c ^ r = 1) (f : (ZMod 2)[X]) (hf : f.eval 1 ≠ 0) :
    10 ∣ finrank (ZMod 2) (LinearMap.ker (aeval (c : V →ₗ[ZMod 2] V) f)) := by
  set C : Module.End (ZMod 2) V := (c : V →ₗ[ZMod 2] V) with hC
  set Z : Module.End (ZMod 2) V := (z : V →ₗ[ZMod 2] V) with hZ
  have hcomm : Commute Z C := by
    refine LinearMap.ext fun v => ?_
    exact (congrArg (fun g : V ≃ₗ[ZMod 2] V => g v) hcz).symm
  have hCr : C ^ r = 1 := by
    have hpow : ∀ n : ℕ, ∀ v, (C ^ n) v = (c ^ n) v := by
      intro n
      induction n with
      | zero => intro v; rfl
      | succ n ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
        rfl
    refine LinearMap.ext fun v => ?_
    rw [hpow, hcr]
    rfl
  set U := LinearMap.ker (Z - 1) with hUdef
  have hmemU : ∀ u, u ∈ U ↔ Z u = u := by
    intro u
    simp [hUdef, sub_eq_zero]
  have hcU : ∀ u ∈ U, C u ∈ U := by
    intro u hu
    rw [hmemU] at hu ⊢
    rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, hu]
  have hCU : ∀ u ∈ U, C u = u := by
    let cU : Module.End (ZMod 2) U := C.restrict hcU
    have hcUr : cU ^ r = 1 := by
      refine LinearMap.ext fun u => Subtype.ext ?_
      rw [Module.End.pow_restrict r hcU, LinearMap.coe_restrict_apply, hCr]
      rfl
    let g : LinearMap.GeneralLinearGroup (ZMod 2) U := Units.ofPowEqOne cU r hcUr hr.ne_zero
    have hgr : g ^ r = 1 := Units.ext hcUr
    have hrodd : Odd r := hr.odd_of_ne_two (by omega)
    have hg3 : g ^ 3 = 1 :=
      pow_three_eq_one_of_dvd_odd hU hrodd (orderOf_dvd_of_pow_eq_one hgr)
    have hcop : Nat.Coprime 3 r := (Nat.coprime_primes (by norm_num) hr).2 (by omega)
    have hg1 : g = 1 := by
      have : orderOf g ∣ Nat.gcd 3 r :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg3) (orderOf_dvd_of_pow_eq_one hgr)
      rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
      exact this
    intro u hu
    have h1 : cU = 1 := congrArg Units.val hg1
    have := congrArg (fun A : Module.End (ZMod 2) U => (A ⟨u, hu⟩ : V)) h1
    simpa [cU] using this
  exact ten_dvd_finrank_ker_aeval_of_fixed_trivial z hz c hcz
    (fun u hu => hCU u ((hmemU u).2 hu)) f hf

theorem not_commute_of_not_ten_dvd_finrank_ker_aeval {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (z : V ≃ₗ[ZMod 2] V) (hz : z ^ 11 = 1)
    (hU : finrank (ZMod 2) (LinearMap.ker ((z : V →ₗ[ZMod 2] V) - 1)) = 2)
    (c : V ≃ₗ[ZMod 2] V) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hcr : c ^ r = 1)
    (f : (ZMod 2)[X]) (hf : f.eval 1 ≠ 0)
    (h10 : ¬ 10 ∣ finrank (ZMod 2) (LinearMap.ker (aeval (c : V →ₗ[ZMod 2] V) f))) :
    c * z ≠ z * c :=
  fun hcz => h10 (ten_dvd_finrank_ker_aeval_of_commute z hz hU c hcz hr hr5 hcr f hf)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
