module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Representations.TypePFittingInducedWitness
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
import CFSG.FeitThompson.Foundations.NontrivialKernelParameterTriple
import CFSG.FeitThompson.Foundations.NormOneIndexBoundTwoQ
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import Mathlib.Algebra.Order.Star.Real

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05
open ChiefFactorFaithfulImage

attribute [local instance] CFSG.FeitThompson.subgroupFintype

variable {G : Type*} [Group G]

noncomputable def conjLinear (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {H M : Subgroup G} (hHM : M ≤ normalizer (H : Set G)) (e : ↥H ≃* Multiplicative V) :
    ↥M →* (V ≃ₗ[ZMod p] V) :=
  (mulAutMultiplicativeMulEquivLinearEquiv p V).toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (conjOnNormalized H hHM))

theorem conjLinear_apply (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {H M : Subgroup G} (hHM : M ≤ normalizer (H : Set G)) (e : ↥H ≃* Multiplicative V)
    (x : ↥M) (h : ↥H) :
    conjLinear p hHM e x (Multiplicative.toAdd (e h))
      = Multiplicative.toAdd (e (conjOnNormalized H hHM x h)) := by
  simp [conjLinear, MulAut.congr_apply]

theorem isConjModule_conjLinear (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {H M : Subgroup G} (hHM : M ≤ normalizer (H : Set G)) (e : ↥H ≃* Multiplicative V) :
    IsConjModule p H M V e (conjLinear p hHM e) := by
  refine ⟨fun x h hc => ?_⟩
  rw [conjLinear_apply]
  change _ = e (conjOnNormalized H hHM x h)
  congr 1
  exact Subtype.ext (conjOnNormalized_apply_coe hHM x h).symm

theorem natCard_dvd_natCard_centralizerIn_sub_one [Finite G] {M U W₁ : Subgroup G}
    (hnormC : M ≤ normalizer ((centralizerIn U (hallCoreOf M) : Subgroup G) : Set G))
    (hW₁M : W₁ ≤ M) (hfree : IsFixedPointFreeOn U W₁) :
    Nat.card ↥W₁ ∣ Nat.card ↥(centralizerIn U (hallCoreOf M)) - 1 := by
  have hnorm : W₁ ≤ normalizer ((centralizerIn U (hallCoreOf M) : Subgroup G) : Set G) :=
    hW₁M.trans hnormC
  refine card_dvd_card_sub_one_of_fixedPointFree
    (φ := conjOnNormalized (centralizerIn U (hallCoreOf M)) hnorm) ?_
  intro w hw x hx
  have hwx : (w : G) * (x : G) * (w : G)⁻¹ = (x : G) := by
    have h := congrArg (Subtype.val (p := fun y => y ∈ centralizerIn U (hallCoreOf M))) hx
    rwa [conjOnNormalized_apply_coe] at h
  have hcomm : Commute (x : G) (w : G) := (mul_inv_eq_iff_eq_mul.1 hwx).symm
  have hbot := hfree (w : G) w.2 (fun h => hw (Subtype.ext h))
  have hmem : (x : G) ∈ centralizerIn U (zpowers (w : G)) := by
    refine Subgroup.mem_inf.2 ⟨centralizerIn_le _ _ x.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (hcomm.zpow_right n).symm
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

noncomputable def fittingEquiv [Finite G] (M : Subgroup G) :
    ↥(fittingRaw ↥M) ≃* ↥(fittingOf M) :=
  (fittingRaw ↥M).equivMapOfInjective M.subtype M.subtype_injective

@[simp]
theorem coe_fittingEquiv [Finite G] (M : Subgroup G) (x : ↥(fittingRaw ↥M)) :
    ((fittingEquiv M x : ↥(fittingOf M)) : G) = ((x : ↥M) : G) := (rfl)

theorem fittingOf_le_hallCoreOf_of_coprime [Finite G] {M : Subgroup G}
    (h : Nat.Coprime (Nat.card ↥(fittingOf M)) ((fittingOf M).relIndex M)) :
    fittingOf M ≤ hallCoreOf M := by
  have hcard : Nat.card ↥(fittingRaw ↥M) = Nat.card ↥(fittingOf M) :=
    Nat.card_congr (fittingEquiv M).toEquiv
  have hidx : (fittingRaw ↥M).index = (fittingOf M).relIndex M := by
    rw [Subgroup.relIndex, subgroupOf_fittingOf]
  exact Subgroup.map_mono (le_hallCore_of_normal_of_isNilpotent_of_coprime
    (isGreatest_fittingRaw ↥M).1.1 (isGreatest_fittingRaw ↥M).1.2 (by rw [hcard, hidx]; exact h))

theorem indClassFun_congr_subgroup {L : Type*} [Group L] [Fintype L] {K K' : Subgroup L}
    (h : K = K') (f : ↥K → ℂ) (g : ↥K' → ℂ)
    (hfg : ∀ x : ↥K, f x = g ⟨(x : L), h ▸ x.2⟩) :
    indClassFun K f = indClassFun K' g := by
  subst h
  congr 1
  funext x
  exact (hfg x).trans (by congr 1)

theorem indBetween_fittingOf_eq [Finite G] [Fintype G] (M : Subgroup G)
    (ψ : ↥(fittingOf M) → ℂ) :
    indBetween (fittingOf M) M ψ
      = indClassFun (fittingRaw ↥M) (fun z => ψ (fittingEquiv M z)) := by
  rw [indBetween_eq_indClassFun_extendZero]
  refine indClassFun_congr_subgroup (subgroupOf_fittingOf M) _ _ ?_
  intro x
  have hx : ((x : ↥M) : G) ∈ fittingOf M := x.2
  rw [show extendZero ψ ((x : ↥M) : G) = ψ ⟨((x : ↥M) : G), hx⟩ from extendZero_coe ψ ⟨_, hx⟩]
  rfl

theorem eq_three_five_seven_of_ratio {p q u c N : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hop : Odd p) (hoq : Odd q) (hpq : p ≠ q) (hc1 : 1 < c)
    (hcp : Nat.Coprime p c) (hcq : 2 * q ∣ c - 1)
    (hN : N = (p ^ q - 1) / (p - 1)) (huN : u ≤ N)
    (hratio : (1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
        + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)) * (p : ℚ) ^ (q - 1) / (q : ℚ) < (u : ℚ) / (c : ℚ)) :
    q = 3 ∧ p = 5 ∧ c = 7 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hPR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hQR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hmR : kernelRatioCoeff p q * (p : ℝ) ^ (q - 1) / (q : ℝ) < (u : ℝ) / (c : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 hratio
    push_cast at h
    rw [kernelRatioCoeff_eq]
    convert h using 2
  have hNR : ((N : ℝ)) = ((p : ℝ) ^ q - 1) / ((p : ℝ) - 1) := by
    have h := sub_one_mul_cast_pow_sub_one_div_sub_one hp2 q
    rw [hN, eq_div_iff (by linarith), mul_comm]
    exact h
  have huNR : (u : ℝ) ≤ (N : ℝ) := by exact_mod_cast huN
  have hcR : (0 : ℝ) < (c : ℝ) := by
    have h : (1 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
    linarith
  have hqR : (0 : ℝ) < (q : ℝ) := by linarith
  have hpowR : (0 : ℝ) < (p : ℝ) ^ (q - 1) := by positivity
  have hfinal : kernelRatioCoeff p q
      < (q : ℝ) * (((p : ℝ) ^ q - 1) / ((p : ℝ) - 1)) / ((c : ℝ) * (p : ℝ) ^ (q - 1)) := by
    rw [← hNR, lt_div_iff₀ (by positivity)]
    rw [div_lt_div_iff₀ hqR hcR] at hmR
    nlinarith [hmR, huNR, hcR, hpowR, hqR]
  have hcz : (1 : ℤ) < (c : ℤ) := by exact_mod_cast hc1
  have hgcd : Int.gcd (c : ℤ) (p : ℤ) = 1 := by simpa [Nat.Coprime] using hcp.symm
  have hcqz : 2 * (q : ℤ) ∣ (c : ℤ) - 1 := by
    obtain ⟨k, hk⟩ := hcq
    refine ⟨(k : ℤ), ?_⟩
    have hcc : (c : ℤ) - 1 = ((c - 1 : ℕ) : ℤ) := by omega
    rw [hcc, hk]; push_cast; ring
  obtain ⟨h3, h5, h7⟩ := eq_three_five_seven_of_kernelRatioCoeff_lt hp hq
    (by rintro rfl; simp [Nat.odd_iff] at hop) (by rintro rfl; simp [Nat.odd_iff] at hoq)
    hpq hcz hgcd hcqz hfinal
  exact ⟨h3, h5, by exact_mod_cast h7⟩

theorem eq_one_of_odd_of_injective_pi_zmod {n a u : ℕ} (ha1 : 1 < a) (ha4 : a ∣ 4)
    (hu : Odd u) {D : Type*} [Group D] (hDu : Nat.card D = u)
    {φ : D →* (Fin n → Multiplicative (ZMod a))} (hφ : Function.Injective φ) : u = 1 := by
  have hNe : NeZero a := ⟨by omega⟩
  have hdvd : u ∣ Nat.card (Fin n → Multiplicative (ZMod a)) := by
    rw [← hDu]; exact Subgroup.card_dvd_of_injective φ hφ
  rw [show Nat.card (Fin n → Multiplicative (ZMod a)) = a ^ n by
    simp [Nat.card_eq_fintype_card]] at hdvd
  have h2 : a ∣ 2 ^ 2 := by simpa using ha4
  have hdvd2 : u ∣ 2 ^ (2 * n) := hdvd.trans (by
    calc a ^ n ∣ (2 ^ 2) ^ n := pow_dvd_pow_of_dvd h2 n
      _ = 2 ^ (2 * n) := by rw [← pow_mul])
  exact Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr hu).pow_right _) hdvd2

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

theorem FNI_type_p_inner_action_faithful
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FNI_type_p_inner_action_faithful.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hc
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨-, hpp, hqp, hop, hoq, hpq, -, -, hsemi₁, hsemi₂, hcop, hfree,
    hVex, hcardH, -, -, -, -, hCltU, hnormC, hFdir, -, -, -⟩ :=
    h₂ G hG M U W₁ W₂ hM hc (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  set C : Subgroup G := centralizerIn U (hallCoreOf M) with hCdef
  set p : ℕ := Nat.card ↥W₂ with hpdef
  set q : ℕ := Nat.card ↥W₁ with hqdef
  set c : ℕ := Nat.card ↥C with hcdef
  set uu : ℕ := C.relIndex U with huudef
  have hCbot : C = ⊥ := by
    by_contra hCne
    have hc1 : 1 < c := (Subgroup.one_lt_card_iff_ne_bot C).2 hCne
    have huu2 : 2 ≤ uu := by
      have h1 : uu ≠ 1 := fun h =>
        hCltU.ne (le_antisymm hCltU.le (Subgroup.relIndex_eq_one.1 h))
      have h0 : uu ≠ 0 := by
        rw [huudef, Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      omega
    have hqc : q ∣ c - 1 :=
      natCard_dvd_natCard_centralizerIn_sub_one hnormC hc.le_M_W₁ hfree
    have hcodd : Odd c := Odd.of_dvd_nat hG.odd_natCard C.card_subgroup_dvd_card
    have h2qc : 2 * q ∣ c - 1 := by
      have h2 : 2 ∣ c - 1 := by
        obtain ⟨k, hk⟩ := hcodd
        omega
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.coprime_two_left.mpr hoq) h2 hqc
    have hpc : Nat.Coprime p c := by
      have hpH : p ∣ Nat.card ↥(hallCoreOf M) := by
        rw [hcardH]; exact dvd_pow_self _ hqp.pos.ne'
      have hcU : c ∣ Nat.card ↥U := Subgroup.card_dvd_of_le (centralizerIn_le _ _)
      exact Nat.Coprime.coprime_dvd_right (hcU.trans (Dvd.intro _ rfl))
        (Nat.Coprime.coprime_dvd_left hpH hcop)
    obtain ⟨V, _, _, -, ⟨e⟩⟩ := hVex
    have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
      le_normalizer_map_subtype_hallCore M
    obtain ⟨-, -, hDcard, hDodd, -, -, -, -, -, hxor, huuN⟩ :=
      FNI_type_p_core_linear_alternative.{u, u} h₂ G hG M U W₁ W₂ hM hc p q uu
        ((p ^ q - 1) / (p - 1)) rfl rfl rfl rfl V e
        (conjLinear p hHM e) (isConjModule_conjLinear _ hHM e) _ _ rfl rfl
    have hA : CFSG.FeitThompson.Prep03.IsAmbient G :=
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    obtain ⟨ψ, hψIrr, hψ1, β, -, -, lam, -, hlam, hlamIrr, -, -, hker⟩ :=
      FNI_type_p_fitting_induced_witness.{u} h₂ G hG M U W₁ W₂ hM hc q uu rfl rfl hCne
    have hratio := h₁ G hA M U W₁ W₂ ⟨hA, hM, hc⟩ p q uu c rfl rfl rfl rfl
      (1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
        + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)) rfl
      ⟨fun z => ψ (fittingEquiv M z),
        FrobeniusInduction.mem_Irr_comp_mulEquiv hψIrr (fittingEquiv M), by simpa using hψ1,
        by rw [← indBetween_fittingOf_eq, ← hlam]; exact hlamIrr,
        by rw [← indBetween_fittingOf_eq, ← hlam]; exact hker⟩
    obtain ⟨hq3, hp5, hc7⟩ :=
      eq_three_five_seven_of_ratio hpp hqp hop hoq hpq hc1 hpc h2qc rfl huuN hratio
    have huuN31 : uu ∣ 31 := by
      rcases hxor with ⟨⟨-, L, -, -, -, -, -, ⟨a, ha1, ha4, φ, hφ⟩, -⟩, -⟩ |
        ⟨⟨-, E, -, -, -, ρ, -, -, -, -, -, hdvd⟩, -⟩
      · exfalso
        have ha4' : a ∣ 4 := by rw [hp5] at ha4; simpa using ha4
        have := eq_one_of_odd_of_injective_pi_zmod ha1 ha4' hDodd hDcard hφ
        omega
      · have hN : (p ^ q - 1) / (p - 1) = 31 := by rw [hp5, hq3]; norm_num
        rwa [hN] at hdvd
    have hFcard : Nat.card ↥(fittingOf M) = 875 := by
      rw [hFdir.card_eq_mul, ← hcdef, hcardH, hp5, hq3, hc7]; norm_num
    have hidx : (fittingOf M).relIndex M = q * uu :=
      relIndex_fittingOf_eq hsemi₁ hsemi₂ hFdir
    have hidxdvd : (fittingOf M).relIndex M ∣ 93 := by
      rw [hidx, hq3]
      exact mul_dvd_mul_left 3 huuN31 |>.trans (by norm_num)
    have hFH : fittingOf M ≤ hallCoreOf M := by
      refine fittingOf_le_hallCoreOf_of_coprime ?_
      rw [hFcard]
      exact Nat.Coprime.coprime_dvd_right hidxdvd (by norm_num)
    have hCH : C ≤ hallCoreOf M := hFdir.right_le.trans hFH
    have h7 : (7 : ℕ) ∣ 125 := by
      have h := Subgroup.card_dvd_of_le hCH
      rwa [← hcdef, hc7, hcardH, hp5, hq3, show (5 : ℕ) ^ 3 = 125 from by norm_num] at h
    norm_num at h7
  exact ⟨hCbot, by rw [← hFdir.sup_eq, hCbot, sup_bot_eq]⟩

end

end CFSG.FeitThompson.Proofs
