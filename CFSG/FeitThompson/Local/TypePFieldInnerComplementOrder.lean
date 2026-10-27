module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Representations.TypePNoFittingInducedWitness
import CFSG.FeitThompson.Foundations.NormOneIndexBoundTwoQ
import CFSG.FeitThompson.Foundations.GeomSumDivisorsCongruentOne
import CFSG.FeitThompson.OddOrder.MobiusNormIteration
import CFSG.FeitThompson.OddOrder.ScalarFreePlaneGroupOrderDividesPPlusOne

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

theorem odd_geomSum {p q : ℕ} (hop : Odd p) (hoq : Odd q) :
    Odd (∑ i ∈ Finset.range q, p ^ i) := by
  rw [Nat.odd_iff, Finset.sum_nat_mod]
  have h : ∀ i ∈ Finset.range q, p ^ i % 2 = 1 := fun i _ => Nat.odd_iff.1 hop.pow
  rw [Finset.sum_congr rfl h]
  simp [Nat.odd_iff.1 hoq]

theorem eq_of_dvd_of_odd_of_le {q b : ℕ} (hq : q.Prime) (hoq : Odd q) (hob : Odd b)
    (hqb : q ∣ b) (hb : b ≤ 2 * q) : b = q := by
  rw [Nat.odd_iff] at hob hoq
  obtain ⟨k, hk⟩ := hqb
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have h3 : q * 3 ≤ q * k := Nat.mul_le_mul_left q (by omega)
    omega
  interval_cases k <;> omega

theorem eq_one_of_modEq_one_of_odd_of_le {q b : ℕ} (hoq : Odd q) (hob : Odd b) (hb0 : 0 < b)
    (hbq : b ≡ 1 [MOD q]) (hb : b ≤ 2 * q) : b = 1 := by
  rw [Nat.odd_iff] at hob hoq
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hb0).1 hbq.symm
  have ht1 : t ≤ 1 := by
    by_contra hcon
    have h2 : q * 2 ≤ q * t := Nat.mul_le_mul_left q (by omega)
    omega
  interval_cases t <;> omega

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u v

theorem index_le_two_mul_of_hyps
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (G : Type u) [Group G] [Finite G] [Fintype G]
    (hA : CFSG.FeitThompson.Prep03.IsAmbient G)
    (M U W₁ W₂ : Subgroup G) (hM : IsCoatom M) (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (p q N b : ℕ) (hp : p = Nat.card ↥W₂) (hq : q = Nat.card ↥W₁)
    (hN : N = (p ^ q - 1) / (p - 1)) (hpp : p.Prime) (hqp : q.Prime)
    (hop : Odd p) (hoq : Odd q) (hpq : p ≠ q)
    (hCbot : centralizerIn U (hallCoreOf M) = ⊥)
    (hb0 : 0 < b) (hu0 : 0 < Nat.card ↥U) (hbu : b * Nat.card ↥U = N) :
    b ≤ 2 * q := by
  set u : ℕ := Nat.card ↥U with hudef
  have hueq : (centralizerIn U (hallCoreOf M)).relIndex U = u := by
    rw [hCbot, Subgroup.relIndex_bot_left]
  by_cases hw : ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ CFSG.FeitThompson.Prep03.hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1
  ·
    have hc1 : Nat.card ↥(CFSG.FeitThompson.Prep03.cent U
        (CFSG.FeitThompson.Prep03.hallCoreIn M : Set G)) = 1 := by
      rw [show CFSG.FeitThompson.Prep03.cent U (CFSG.FeitThompson.Prep03.hallCoreIn M : Set G)
          = centralizerIn U (hallCoreOf M) from rfl, hCbot]
      simp
    have hratio := h₁ G hA M U W₁ W₂ ⟨hA, hM, hc⟩ p q u 1 hp hq hueq.symm hc1.symm
      (1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
        + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)) rfl hw
    have hlt : kernelRatioCoeff p q * (p : ℝ) ^ (q - 1) / (q : ℝ) < (u : ℝ) := by
      have h := (Rat.cast_lt (K := ℝ)).2 hratio
      push_cast at h
      rw [div_one] at h
      rw [kernelRatioCoeff_eq]
      exact h
    exact index_le_two_mul_of_kernelRatioCoeff_lt hpp hqp
      (by rintro rfl; simp [Nat.odd_iff] at hop) (by rintro rfl; simp [Nat.odd_iff] at hoq)
      hpq hu0 hb0 (by rw [hbu, hN]) hlt
  ·
    obtain ⟨-, -, -, -, -, -, -, -, hmul, -⟩ :=
      FCH_type_p_no_fitting_induced_witness.{u} h₂ G hA M U W₁ W₂ ⟨hA, hM, hc⟩ p q u hp hq
        hueq.symm hw
    have hNu : N = u := by
      rw [hN, ← hmul, Nat.mul_div_cancel]
      have := hpp.two_le
      omega
    have hb1 : b = 1 := by
      rw [hNu] at hbu
      exact Nat.eq_of_mul_eq_mul_right hu0 (by rw [hbu, one_mul])
    have hq2 := hqp.two_le
    omega

theorem FNI_type_p_field_inner_complement_order
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FNI_type_p_field_inner_complement_order.{u, v} := by
  intro G _ _ hG M U W₁ W₂ hM hc p q N hp hq hN V _ _ e ρ hρ hirr
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨-, hpp, hqp, hop, hoq, hpq, -, hUab, -, -, -, -, -, hcardH, -, -, -, -, -, -, -, -, -,
    -⟩ := h₂ G hG M U W₁ W₂ hM hc p q hp hq
  obtain ⟨hCbot, -⟩ := FNI_type_p_inner_action_faithful.{u} h₁ h₂ G hG M U W₁ W₂ hM hc
  have hA : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hueq : (centralizerIn U (hallCoreOf M)).relIndex U = Nat.card ↥U := by
    rw [hCbot, Subgroup.relIndex_bot_left]
  obtain ⟨-, -, -, -, hDcop, -, -, -, -, hxor, -⟩ :=
    FNI_type_p_core_linear_alternative.{u, v} h₂ G hG M U W₁ W₂ hM hc p q
      ((centralizerIn U (hallCoreOf M)).relIndex U) N hp hq rfl hN V e ρ hρ _ _ rfl rfl
  have hudvd : Nat.card ↥U ∣ N := by
    rcases hxor with ⟨hred, -⟩ | ⟨hfield, -⟩
    · exact absurd hirr hred.1
    · obtain ⟨-, E, _, _, -, φ, -, -, -, -, hd⟩ := hfield
      exact hueq ▸ hd.2
  have hucop : (Nat.card ↥U).Coprime q := hueq ▸ hDcop
  have hUM : U ≤ M := hc.le_M_E
  have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  have hfinV : Finite V :=
    Finite.of_equiv ↥(hallCoreOf M) (e.toEquiv.trans (Multiplicative.toAdd (α := V)))
  have hfp : Fact p.Prime := ⟨hpp⟩
  have hdimV : finrank (ZMod p) V = q := by
    have hcV : Nat.card V = p ^ q := by
      rw [← hcardH]
      exact (Nat.card_congr (e.toEquiv.trans (Multiplicative.toAdd (α := V)))).symm
    have h := FiniteField.pow_finrank_eq_natCard p V
    rw [hcV] at h
    exact Nat.pow_right_injective hpp.two_le h
  have hfd : FiniteDimensional (ZMod p) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdimV]; exact hqp.pos)
  have hntV : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hdimV]; exact hqp.pos)
  have hirr' : (linearGroupRep ((U.subgroupOf M).map ρ)).IsIrreducible :=
    isIrreducibleLinear_iff.1 hirr
  have hDab : IsMulCommutative ↥((U.subgroupOf M).map ρ) := isMulCommutative_map hUab
  have hDcyc : IsCyclic ↥((U.subgroupOf M).map ρ) := isCyclic_of_abelian_irreducible
  have hcyc : IsCyclic ↥U := by
    refine isCyclic_of_injective
      ((ρ.comp (Subgroup.inclusion hUM)).codRestrict ((U.subgroupOf M).map ρ)
        (fun x => Subgroup.mem_map.2 ⟨Subgroup.inclusion hUM x,
          Subgroup.mem_subgroupOf.2 x.2, rfl⟩)) ?_
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : ρ (Subgroup.inclusion hUM x) = 1 := by
      simpa using congrArg (Subtype.val (p := fun z => z ∈ (U.subgroupOf M).map ρ)) hx
    have hmem : (x : G) ∈ centralizerIn U (hallCoreOf M) :=
      Subgroup.mem_inf.2 ⟨x.2, (rho_eq_one_iff hρ hHM _).1 hx1⟩
    rw [hCbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hNgeom : N = ∑ i ∈ Finset.range q, p ^ i := eq_geomSum_of_eq_div hpp hN
  have hNodd : Odd N := hNgeom ▸ odd_geomSum hop hoq
  have hu0 : 0 < Nat.card ↥U := Nat.card_pos
  have hN0 : 0 < N := hNodd.pos
  set b : ℕ := N / Nat.card ↥U with hbdef
  have hbu : b * Nat.card ↥U = N := Nat.div_mul_cancel hudvd
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, zero_mul] at hbu; omega
    · exact h
  have hbodd : Odd b := hNodd.of_dvd_nat ⟨Nat.card ↥U, hbu.symm⟩
  have hble : b ≤ 2 * q := index_le_two_mul_of_hyps h₁ h₂ G hA M U W₁ W₂ hM hc p q N b hp hq hN
    hpp hqp hop hoq hpq hCbot hb0 hu0 hbu
  refine ⟨hcyc, fun hqd => ?_, fun hqd => ?_⟩
  ·
    have hpmod : p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' hpp.one_le).2 hqd).symm
    obtain ⟨-, -, -, hdvd0, -⟩ := sum_range_pow_congruences hpp hqp
    have hqN : q ∣ N := by
      have h := hdvd0 hpmod
      rw [← hNgeom] at h
      exact (Nat.modEq_zero_iff_dvd).1 h
    have hqb : q ∣ b := Nat.Coprime.dvd_of_dvd_mul_right hucop.symm (hbu ▸ hqN)
    have hbq : b = q := eq_of_dvd_of_odd_of_le hqp hoq hbodd hqb hble
    refine ⟨hqN, ?_⟩
    rw [hbq] at hbu
    rw [← hbu, Nat.mul_div_cancel_left _ hqp.pos]
  ·
    have hbdvdN : b ∣ N := ⟨Nat.card ↥U, hbu.symm⟩
    have hbmod : b ≡ 1 [MOD q] :=
      modEq_one_of_dvd_pow_sub_one_div_sub_one hqp hqd hb0 (hN ▸ hbdvdN)
    have hb1 : b = 1 := eq_one_of_modEq_one_of_odd_of_le hoq hbodd hb0 hbmod hble
    rw [hb1, one_mul] at hbu
    exact hbu

end

end CFSG.FeitThompson.Proofs
