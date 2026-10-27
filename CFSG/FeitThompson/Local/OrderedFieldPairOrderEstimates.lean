module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.TypePFieldInnerComplementOrder
import CFSG.FeitThompson.Local.TypePReducibleInnerActionOrder
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Local.PairedFullSupportForcesFieldAction
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Local.TypePFixedCoreNormalizer
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.OddOrder.GeometricSumCongruences
import CFSG.FeitThompson.OddOrder.NormQuotientDegreeComparison

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace OrderedFieldPairEstimates

open Subgroup Finset

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05
open CFSG.FeitThompson.PairedFullSupportFieldAction

universe u

variable {G : Type u} [Group G]

theorem hallCoreIn_eq_hallCoreOf (M : Subgroup G) :
    CFSG.FeitThompson.hallCoreIn M = hallCoreOf M := by
  rw [CFSG.FeitThompson.hallCoreIn_eq, hallCoreOf_eq]

theorem dvd_geomSum_sub_one (r : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    r ∣ (∑ i ∈ Finset.range n, r ^ i) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', pow_zero, Nat.add_sub_cancel]
  exact Finset.dvd_sum fun i _ => dvd_pow_self r (Nat.succ_ne_zero i)

theorem two_mul_lt_of_dvd_sub_one {r n : ℕ} (hr : Odd r) (hn : Odd n) (h1 : 1 < n)
    (hdvd : r ∣ n - 1) : 2 * r < n := by
  obtain ⟨k, hk⟩ := hdvd
  have hev : Even (n - 1) := Nat.Odd.sub_odd hn odd_one
  rw [hk] at hev
  have hk2 : 2 ≤ k := by
    rcases Nat.even_mul.1 hev with h | h
    · exact absurd h (Nat.not_even_iff_odd.2 hr)
    · have hk0 : k ≠ 0 := by
        intro h0
        rw [h0, Nat.mul_zero] at hk
        omega
      rcases h with ⟨j, hj⟩
      omega
  have h2r : 2 * r ≤ n - 1 := by
    calc 2 * r = r * 2 := by ring
      _ ≤ r * k := Nat.mul_le_mul_left r hk2
      _ = n - 1 := hk.symm
  omega

theorem cast_geomSumDiv {K : Type*} [Field K] [CharZero K] {r : ℕ} (hr : 2 ≤ r) (n : ℕ) :
    (((r ^ n - 1) / (r - 1) : ℕ) : K) = ((r : K) ^ n - 1) / ((r : K) - 1) := by
  have hne : (r : K) - 1 ≠ 0 := by
    have h : (r : K) ≠ 1 := by exact_mod_cast (show r ≠ 1 by omega)
    exact sub_ne_zero_of_ne h
  rw [← sum_range_pow_eq_div hr]
  push_cast
  rw [← geom_sum_mul (r : K) n, mul_div_assoc, div_self hne, mul_one]

theorem natCard_dvd_natCard_sub_one_of_free [Finite G] {A B : Subgroup G}
    (hnorm : B ≤ normalizer (A : Set G)) (hfree : IsFixedPointFreeOn A B) :
    Nat.card ↥B ∣ Nat.card ↥A - 1 := by
  refine card_dvd_card_sub_one_of_fixedPointFree (φ := conjOnNormalized A hnorm) ?_
  intro w hw x hx
  have hwx : (w : G) * (x : G) * (w : G)⁻¹ = (x : G) := by
    have h := congrArg (Subtype.val (p := fun y : G => y ∈ A)) hx
    rwa [conjOnNormalized_apply_coe] at h
  have hcomm : Commute (x : G) (w : G) := (mul_inv_eq_iff_eq_mul.1 hwx).symm
  have hbot := hfree (w : G) w.2 (fun h => hw (Subtype.ext h))
  have hmem : (x : G) ∈ centralizerIn A (zpowers (w : G)) := by
    refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (hcomm.zpow_right n).symm
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem isIrreducibleLinear_map_of_minimal {M U H : Subgroup G} {p : ℕ} {Vm : Type u}
    [AddCommGroup Vm] [Module (ZMod p) Vm] {e : ↥H ≃* Multiplicative Vm}
    {ρ : ↥M →* (Vm ≃ₗ[ZMod p] Vm)} (hρ : IsConjModule p H M Vm e ρ)
    (hHM : M ≤ normalizer (H : Set G)) (hUM : U ≤ M)
    (hmin : ∀ K : Subgroup G, K ≤ H → U ≤ normalizer (K : Set G) → K = ⊥ ∨ K = H) :
    IsIrreducibleLinear ((U.subgroupOf M).map ρ) := by
  intro W hW
  have hKH : _root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W ≤ H :=
    _root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule_le e W
  have hconj : ∀ x ∈ U, ∀ z ∈ _root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W,
      x * z * x⁻¹ ∈ _root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W := by
    intro x hx z hz
    obtain ⟨hzH, hzW⟩ := _root_.CFSG.FeitThompson.Proofs.mem_subgroupOfSubmodule.1 hz
    refine _root_.CFSG.FeitThompson.Proofs.mem_subgroupOfSubmodule.2
      ⟨_root_.CFSG.FeitThompson.Proofs.conj_mem_of_le_normalizer hHM (hUM hx) hzH, ?_⟩
    rw [← _root_.CFSG.FeitThompson.Proofs.toAdd_e_conj hρ hHM ⟨x, hUM hx⟩ ⟨z, hzH⟩]
    exact hW _ (Subgroup.mem_map.2 ⟨⟨x, hUM hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩) _ hzW
  have hnorm : U ≤ normalizer ((_root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W :
      Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.mem_set_normalizer_iff.2 fun z => ⟨fun hz => hconj x hx z hz, fun hz => ?_⟩
    have h2 := hconj x⁻¹ (U.inv_mem hx) _ hz
    rwa [show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z by group] at h2
  rcases hmin _ hKH hnorm with h | h
  · exact Or.inl (_root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule_eq_bot_iff.1 h)
  · exact Or.inr (_root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule_eq_top_iff.1 h)

theorem eq_bot_or_eq_hallCoreOf_of_le_normalizer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    [Finite G] (hG : IsMinimalSimpleOdd G) {T V W₁ W₂ : Subgroup G} (hT : IsCoatom T)
    (hcT : IsWitnessedPConfiguration T V W₂ W₁) (hqp : Nat.card ↥W₁ < Nat.card ↥W₂)
    {K : Subgroup G} (hK : K ≤ hallCoreOf T) (hnorm : V ≤ normalizer (K : Set G)) :
    K = ⊥ ∨ K = hallCoreOf T := by
  set q := Nat.card ↥W₁ with hqdef
  set p := Nat.card ↥W₂ with hpdef
  obtain ⟨-, hqq, -, hoq, -, -, -, -, -, -, -, -, hmod, -⟩ :=
    h₂ G hG T V W₂ W₁ hT hcT q p rfl rfl
  have hq3 : 3 ≤ q := hqq.odd_iff.mp hoq
  obtain ⟨Vt, hVadd, hVmod, -, ⟨e⟩⟩ := hmod
  by_contra hcon
  push Not at hcon
  have hTnorm : T ≤ normalizer ((hallCoreOf T : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore T
  have hρ := isConjModule_conjLinear q hTnorm e
  have hinv : ∀ x ∈ V, ∀ z ∈ K, x * z * x⁻¹ ∈ K := fun x hx z hz =>
    (Subgroup.mem_set_normalizer_iff.1 (hnorm hx) z).1 hz
  obtain ⟨hp3, -⟩ := _root_.CFSG.FeitThompson.Proofs.FNI_type_p_reducible_inner_action_order.{u, u}
    h₁ h₂ G hG T V W₂ W₁ hT hcT q p rfl rfl Vt e (conjLinear q hTnorm e) hρ
    ⟨submoduleOfSubgroup q e K, fun h => hcon.1 ((submoduleOfSubgroup_eq_bot_iff hK).1 h),
      fun h => hcon.2 (le_antisymm hK (submoduleOfSubgroup_eq_top_iff.1 h)),
      isInvariantSubmodule_submoduleOfSubgroup hρ hTnorm hinv⟩
  omega

theorem natCard_reciprocal
    (h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    [Finite G] (hG : IsMinimalSimpleOdd G) {T V W₁ W₂ : Subgroup G} (hT : IsCoatom T)
    (hcT : IsWitnessedPConfiguration T V W₂ W₁) (hqp : Nat.card ↥W₁ < Nat.card ↥W₂) :
    Nat.card ↥V = (Nat.card ↥W₁ ^ Nat.card ↥W₂ - 1) / (Nat.card ↥W₁ - 1) := by
  set q := Nat.card ↥W₁ with hqdef
  set p := Nat.card ↥W₂ with hpdef
  obtain ⟨-, hqq, hpp, hoq, -, -, -, -, -, -, -, -, hmod, -⟩ :=
    h₂ G hG T V W₂ W₁ hT hcT q p rfl rfl
  have hq3 : 3 ≤ q := hqq.odd_iff.mp hoq
  obtain ⟨Vt, hVadd, hVmod, -, ⟨e⟩⟩ := hmod
  have hTnorm : T ≤ normalizer ((hallCoreOf T : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore T
  have hρ := isConjModule_conjLinear q hTnorm e
  have hirr : IsIrreducibleLinear ((V.subgroupOf T).map (conjLinear q hTnorm e)) :=
    isIrreducibleLinear_map_of_minimal hρ hTnorm hcT.le_M_E
      (fun K hK hnorm => eq_bot_or_eq_hallCoreOf_of_le_normalizer h₁ h₂ hG hT hcT hqp hK hnorm)
  obtain ⟨-, -, hfull⟩ := _root_.CFSG.FeitThompson.Proofs.FNI_type_p_field_inner_complement_order.{u, u}
    h₁ h₂ G hG T V W₂ W₁ hT hcT q p ((q ^ p - 1) / (q - 1)) rfl rfl rfl Vt e
    (conjLinear q hTnorm e) hρ hirr
  exact hfull (fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))

theorem natCard_le_norm
    (h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    [Finite G] (hG : IsMinimalSimpleOdd G) {S U W₁ W₂ : Subgroup G} (hS : IsCoatom S)
    (hcS : IsWitnessedPConfiguration S U W₁ W₂)
    (hmin : ∀ K : Subgroup G, K ≤ hallCoreOf S → U ≤ normalizer (K : Set G) →
      K = ⊥ ∨ K = hallCoreOf S) :
    Nat.card ↥U ≤ (Nat.card ↥W₂ ^ Nat.card ↥W₁ - 1) / (Nat.card ↥W₂ - 1) := by
  set p := Nat.card ↥W₂ with hpdef
  set q := Nat.card ↥W₁ with hqdef
  set N := (p ^ q - 1) / (p - 1) with hNdef
  obtain ⟨-, hpp, hqq, hop, hoq, -, -, -, -, -, -, -, hmod, -⟩ :=
    h₂ G hG S U W₁ W₂ hS hcS p q rfl rfl
  obtain ⟨Vm, hVadd, hVmod, -, ⟨e⟩⟩ := hmod
  have hSnorm : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore S
  have hρ := isConjModule_conjLinear p hSnorm e
  have hirr : IsIrreducibleLinear ((U.subgroupOf S).map (conjLinear p hSnorm e)) :=
    isIrreducibleLinear_map_of_minimal hρ hSnorm hcS.le_M_E hmin
  obtain ⟨-, hred, hfull⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FNI_type_p_field_inner_complement_order.{u, u}
      h₁ h₂ G hG S U W₁ W₂ hS hcS p q N rfl rfl rfl Vm e (conjLinear p hSnorm e) hρ hirr
  by_cases hd : q ∣ p - 1
  · obtain ⟨-, hu⟩ := hred hd
    rw [hu]
    exact Nat.div_le_self _ _
  · exact le_of_eq (hfull hd)

theorem nonempty_mulEquiv_hallCoreOf
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    [Finite G] (hG : IsMinimalSimpleOdd G) {T V W₁ W₂ : Subgroup G} (hT : IsCoatom T)
    (hcT : IsWitnessedPConfiguration T V W₂ W₁) :
    Nonempty (↥(hallCoreOf T) ≃*
      (Fin (Nat.card ↥W₂) → Multiplicative (ZMod (Nat.card ↥W₁)))) := by
  set q := Nat.card ↥W₁ with hqdef
  set p := Nat.card ↥W₂ with hpdef
  obtain ⟨-, hqq, -, -, -, -, -, -, -, -, -, -, hmod, hcard, -⟩ :=
    h₂ G hG T V W₂ W₁ hT hcT q p rfl rfl
  obtain ⟨Vt, hVadd, hVmod, -, ⟨e⟩⟩ := hmod
  exact nonempty_mulEquiv_pi_of_isElementaryAbelian hqq
    (isElementaryAbelian_of_mulEquiv_multiplicative e) hcard

end OrderedFieldPairEstimates

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05
open CFSG.FeitThompson.OrderedFieldPairEstimates

public section

universe u

theorem FBG_ordered_field_pair_order_estimates
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FBG_ordered_field_pair_order_estimates.{u} := by
  intro G _ _ hG S T U V W₁ W₂ p q hsetup
  have hG5 : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hp : Nat.card ↥W₂ = p := hsetup.natCard_W₂
  have hq : Nat.card ↥W₁ = q := hsetup.natCard_W₁
  have hpp : p.Prime := hsetup.prime_p
  have hqq : q.Prime := hsetup.prime_q
  have hop : Odd p := hsetup.odd_p
  have hoq : Odd q := hsetup.odd_q
  have hlt : q < p := hsetup.lt
  have hqp : Nat.card ↥W₁ < Nat.card ↥W₂ := by rw [hp, hq]; exact hlt
  obtain ⟨-, -, -, -, -, -, hUne, -, -, hsdU, -, hfreeU, -⟩ :=
    h₂ G hG5 S U W₁ W₂ hsetup.isCoatom_S hsetup.pconfig_S (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  obtain ⟨-, -, -, -, -, -, hVne, -, -, hsdV, -, hfreeV, -⟩ :=
    h₂ G hG5 T V W₂ W₁ hsetup.isCoatom_T hsetup.pconfig_T (Nat.card ↥W₁) (Nat.card ↥W₂) rfl rfl
  have hminS : ∀ K : Subgroup G, K ≤ hallCoreOf S → U ≤ normalizer (K : Set G) →
      K = ⊥ ∨ K = hallCoreOf S := by
    intro K hK hnorm
    have h := hsetup.irreducible.2 K (by rwa [hallCoreIn_eq_hallCoreOf]) hnorm
    rwa [hallCoreIn_eq_hallCoreOf] at h
  have hvnat : Nat.card ↥V = (q ^ p - 1) / (q - 1) := by
    have h := natCard_reciprocal h₁ h₂ hG5 hsetup.isCoatom_T hsetup.pconfig_T hqp
    rwa [hp, hq] at h
  have hunat : Nat.card ↥U ≤ (p ^ q - 1) / (p - 1) := by
    have h := natCard_le_norm h₁ h₂ hG5 hsetup.isCoatom_S hsetup.pconfig_S hminS
    rwa [hp, hq] at h
  have hqU : q ∣ Nat.card ↥U - 1 := by
    have h := natCard_dvd_natCard_sub_one_of_free hsdU.right_le_normalizer hfreeU
    rwa [hq] at h
  have hpV : p ∣ Nat.card ↥V - 1 := by
    have h := natCard_dvd_natCard_sub_one_of_free hsdV.right_le_normalizer hfreeV
    rwa [hp] at h
  have hUodd : Odd (Nat.card ↥U) := Odd.of_dvd_nat hG.odd_natCard U.card_subgroup_dvd_card
  have hVodd : Odd (Nat.card ↥V) := Odd.of_dvd_nat hG.odd_natCard V.card_subgroup_dvd_card
  have hU1 : 1 < Nat.card ↥U := (Subgroup.one_lt_card_iff_ne_bot U).2 hUne
  have hV1 : 1 < Nat.card ↥V := (Subgroup.one_lt_card_iff_ne_bot V).2 hVne
  have hqV : q ∣ Nat.card ↥V - 1 := by
    rw [hvnat, ← sum_range_pow_eq_div hqq.two_le]
    exact dvd_geomSum_sub_one q hpp.pos
  have hpqV : p * q ∣ Nat.card ↥V - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hpp hqq).2 (by omega)) hpV hqV
  refine ⟨⟨⟨p, hpp.pos, ?_⟩, ?_⟩, hU1, ?_, ?_, ?_, ?_, hpqV, ?_, ?_⟩
  ·
    have h := nonempty_mulEquiv_hallCoreOf h₂ hG5 hsetup.isCoatom_T hsetup.pconfig_T
    rw [hallCoreIn_eq_hallCoreOf, hp, hq] at *
    exact h
  ·
    intro K hK hnorm
    rw [hallCoreIn_eq_hallCoreOf] at hK ⊢
    exact eq_bot_or_eq_hallCoreOf_of_le_normalizer h₁ h₂ hG5 hsetup.isCoatom_T
      hsetup.pconfig_T hqp hK hnorm
  ·
    calc (Nat.card ↥U : ℚ) ≤ (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) := by exact_mod_cast hunat
      _ = ((p : ℚ) ^ q - 1) / ((p : ℚ) - 1) := cast_geomSumDiv hpp.two_le q
  ·
    rw [hvnat]
    exact cast_geomSumDiv hqq.two_le p
  · exact two_mul_lt_of_dvd_sub_one hoq hUodd hU1 hqU
  · exact two_mul_lt_of_dvd_sub_one hop hVodd hV1 hpV
  ·
    have hvQ : (Nat.card ↥V : ℚ) = ((q : ℚ) ^ p - 1) / ((q : ℚ) - 1) := by
      rw [hvnat]; exact cast_geomSumDiv hqq.two_le p
    have huQ : (Nat.card ↥U : ℚ) ≤ ((p : ℚ) ^ q - 1) / ((p : ℚ) - 1) := by
      calc (Nat.card ↥U : ℚ) ≤ (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) := by exact_mod_cast hunat
        _ = ((p : ℚ) ^ q - 1) / ((p : ℚ) - 1) := cast_geomSumDiv hpp.two_le q
    have huR : ((Nat.card ↥U : ℕ) : ℝ) ≤ ((p : ℝ) ^ q - 1) / ((p : ℝ) - 1) := by
      have h := (Rat.cast_le (K := ℝ)).2 huQ
      push_cast at h
      exact h
    have hvR : ((Nat.card ↥V : ℕ) : ℝ) = ((q : ℝ) ^ p - 1) / ((q : ℝ) - 1) := by
      have h := congrArg (fun x : ℚ => (x : ℝ)) hvQ
      push_cast at h
      exact h
    have hR := sub_one_div_lt_sub_one_div_of_odd_prime_lt' hpp hqq hop hoq hlt
      (u := ((Nat.card ↥U : ℕ) : ℝ)) (v := ((Nat.card ↥V : ℕ) : ℝ))
      (by exact_mod_cast hU1.le) huR hvR
    have hcast : ((((Nat.card ↥U : ℚ) - 1) / (q : ℚ) : ℚ) : ℝ) <
        ((((Nat.card ↥V : ℚ) - 1) / (p : ℚ) : ℚ) : ℝ) := by
      push_cast
      exact hR
    exact_mod_cast hcast
  ·
    have h0 : 0 < Nat.card ↥V - 1 := by omega
    have := Nat.le_of_dvd h0 hpqV
    omega

end

end CFSG.FeitThompson.Proofs
