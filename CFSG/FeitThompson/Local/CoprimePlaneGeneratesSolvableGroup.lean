module

public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.CoprimePlaneActionFixedOrders
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
public import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
import CFSG.FeitThompson.Local.FixedOrderMultiplicativityNormal
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p : ℕ} {A K : Type*} [Group A] [Group K]

private theorem isInvariantSubgroup_of_forall_apply_mem {ρ : A →* MulAut K} {N : Subgroup K}
    (h : ∀ b : A, ∀ v ∈ N, ρ b v ∈ N) : IsInvariantSubgroup ρ N := by
  rw [isInvariantSubgroup_iff_forall_map_eq]
  intro b
  refine le_antisymm ?_ fun v hv => ⟨ρ b⁻¹ v, h b⁻¹ v hv, ?_⟩
  · rintro x ⟨v, hv, rfl⟩
    exact h b v hv
  · change ρ b (ρ b⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem isInvariantSubgroup_iSup {ι : Sort*} {ρ : A →* MulAut K} {N : ι → Subgroup K}
    (h : ∀ i, IsInvariantSubgroup ρ (N i)) : IsInvariantSubgroup ρ (⨆ i, N i) := by
  rw [isInvariantSubgroup_iff_forall_map_eq]
  intro b
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => (h i).map_eq b

theorem fixedPoints_comp_zpowers_subtype_eq (ρ : A →* MulAut K) (a : A) :
    FixedPoints.subgroup (ρ.comp (Subgroup.zpowers a).subtype).range K
      = autFixedSubgroup (ρ a) := by
  ext x
  rw [mem_fixedPoints_comp_subtype_iff, mem_autFixedSubgroup]
  refine ⟨fun h => h a (Subgroup.mem_zpowers a), fun h b hb => ?_⟩
  exact (Subgroup.zpowers_le (g := a)
    (H := (MulAction.stabilizer (MulAut K) x).comap ρ)).mpr h hb

theorem isInvariantSubgroup_autFixedSubgroup [IsMulCommutative A] (ρ : A →* MulAut K) (a : A) :
    IsInvariantSubgroup ρ (autFixedSubgroup (ρ a)) := by
  refine isInvariantSubgroup_of_forall_apply_mem fun c x hx => ?_
  rw [mem_autFixedSubgroup] at hx ⊢
  have hcomm : ρ a * ρ c = ρ c * ρ a := by rw [← map_mul, ← map_mul, mul_comm' a c]
  have h2 : ρ a (ρ c x) = ρ c (ρ a x) := by
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
  rw [h2, hx]

theorem natCard_fixedPoints_restrictAut_comp_subtype {ρ : A →* MulAut K} {N : Subgroup K}
    (hN : IsInvariantSubgroup ρ N) (B : Subgroup A)
    (hle : FixedPoints.subgroup (ρ.comp B.subtype).range K ≤ N) :
    Nat.card (FixedPoints.subgroup (hN.restrictAut.comp B.subtype).range N)
      = Nat.card (FixedPoints.subgroup (ρ.comp B.subtype).range K) := by
  have key : ∀ x : N, ((x : K) ∈ FixedPoints.subgroup (ρ.comp B.subtype).range K)
      ↔ x ∈ FixedPoints.subgroup (hN.restrictAut.comp B.subtype).range N := by
    intro x
    rw [mem_fixedPoints_comp_subtype_iff, mem_fixedPoints_comp_subtype_iff]
    refine ⟨fun h b hb => Subtype.ext ?_, fun h b hb => ?_⟩
    · rw [hN.coe_restrictAut_apply]; exact h b hb
    · have := congrArg Subtype.val (h b hb)
      rwa [hN.coe_restrictAut_apply] at this
  exact Nat.card_congr
    ⟨fun x => ⟨((x : N) : K), (key _).2 x.2⟩,
      fun y => ⟨⟨(y : K), hle y.2⟩, (key _).1 y.2⟩,
      fun _ => Subtype.ext (Subtype.ext rfl), fun _ => Subtype.ext rfl⟩

theorem iSup_autFixedSubgroup_eq_closure (ρ : A →* MulAut K) :
    ⨆ (a : A) (_ : a ≠ 1), autFixedSubgroup (ρ a)
      = Subgroup.closure {x : K | ∃ a : A, a ≠ 1 ∧ ρ a x = x} := by
  refine le_antisymm (iSup₂_le fun a ha x hx => Subgroup.subset_closure
    ⟨a, ha, mem_autFixedSubgroup.mp hx⟩) ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨a, ha, hx⟩
  exact le_iSup₂ (f := fun (a : A) (_ : a ≠ 1) => autFixedSubgroup (ρ a)) a ha
    (mem_autFixedSubgroup.mpr hx)

theorem iSup_autFixedSubgroup_eq_top (hp : p.Prime) (hcard : Nat.card A = p ^ 2)
    (hexp : ∀ a : A, a ^ p = 1) [Finite K] [Group.IsSolvable K] (ρ : A →* MulAut K)
    (hpK : ¬ p ∣ Nat.card K) :
    ⨆ (a : A) (_ : a ≠ 1), autFixedSubgroup (ρ a) = ⊤ := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hA : Finite A := Nat.finite_of_card_ne_zero (by simp [hcard, hp.ne_zero])
  have hcomm : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hcard
  set J : Subgroup K := ⨆ (a : A) (_ : a ≠ 1), autFixedSubgroup (ρ a) with hJdef
  have hJinv : IsInvariantSubgroup ρ J :=
    isInvariantSubgroup_iSup fun a => isInvariantSubgroup_iSup fun _ =>
      isInvariantSubgroup_autFixedSubgroup ρ a
  have hle : ∀ a : A, a ≠ 1 → autFixedSubgroup (ρ a) ≤ J := fun a ha => by
    rw [hJdef]
    exact le_iSup₂ (f := fun (a : A) (_ : a ≠ 1) => autFixedSubgroup (ρ a)) a ha
  have hCle : ∀ B ∈ subgroupsOfCard A p,
      FixedPoints.subgroup (ρ.comp B.subtype).range K ≤ J := by
    intro B hB
    have hBnt : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [mem_subgroupsOfCard.mp hB]; exact hp.one_lt)
    obtain ⟨a, haB, ha⟩ := B.exists_ne_one_of_nontrivial
    rw [eq_zpowers_of_mem_subgroupsOfCard hp hexp hB ha haB, fixedPoints_comp_zpowers_subtype_eq]
    exact hle a ha
  have hAnt : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [hcard]; exact Nat.one_lt_pow two_ne_zero hp.one_lt)
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : A)
  have htopLe : FixedPoints.subgroup ρ.range K ≤ J :=
    le_trans (fun x hx => mem_autFixedSubgroup.2 ((mem_fixedPoints_range_iff ρ).1 hx a₀))
      (hle a₀ ha₀)
  have hpJ : ¬ p ∣ Nat.card J := fun h => hpK (h.trans (Subgroup.card_subgroup_dvd_card J))
  have key1 := natCard_mul_natCard_fixedPoints_pow_eq_finprod hp hcard hexp ρ hpK
  have key2 := natCard_mul_natCard_fixedPoints_pow_eq_finprod hp hcard hexp hJinv.restrictAut hpJ
  have hprod : (∏ᶠ B ∈ subgroupsOfCard A p,
        Nat.card (FixedPoints.subgroup (hJinv.restrictAut.comp B.subtype).range J))
      = ∏ᶠ B ∈ subgroupsOfCard A p,
        Nat.card (FixedPoints.subgroup (ρ.comp B.subtype).range K) :=
    finprod_mem_congr rfl fun B hB =>
      natCard_fixedPoints_restrictAut_comp_subtype hJinv B (hCle B hB)
  have hfix : Nat.card (FixedPoints.subgroup hJinv.restrictAut.range J)
      = Nat.card (FixedPoints.subgroup ρ.range K) := by
    rw [← fixedPoints_comp_subtype_top hJinv.restrictAut, ← fixedPoints_comp_subtype_top ρ]
    exact natCard_fixedPoints_restrictAut_comp_subtype hJinv ⊤
      (by rw [fixedPoints_comp_subtype_top ρ]; exact htopLe)
  rw [hprod, hfix, ← key1] at key2
  have hXpos : 0 < Nat.card (FixedPoints.subgroup ρ.range K) := Nat.card_pos
  exact Subgroup.eq_top_of_card_eq J (Nat.eq_of_mul_eq_mul_right (pow_pos hXpos p) key2)

theorem closure_setOf_exists_ne_one_apply_eq_self_eq_top (hp : p.Prime)
    (hcard : Nat.card A = p ^ 2) (hexp : ∀ a : A, a ^ p = 1) [Finite K] [Group.IsSolvable K]
    (ρ : A →* MulAut K) (hpK : ¬ p ∣ Nat.card K) :
    Subgroup.closure {x : K | ∃ a : A, a ≠ 1 ∧ ρ a x = x} = ⊤ := by
  rw [← iSup_autFixedSubgroup_eq_closure ρ]
  exact iSup_autFixedSubgroup_eq_top hp hcard hexp ρ hpK

theorem iSup_autFixedSubgroup_eq_top_of_mulEquiv (e : A ≃* Multiplicative (ZMod p × ZMod p))
    (hp : p.Prime) [Finite K] [Group.IsSolvable K] (ρ : A →* MulAut K)
    (hpK : ¬ p ∣ Nat.card K) :
    ⨆ (a : A) (_ : a ≠ 1), autFixedSubgroup (ρ a) = ⊤ :=
  iSup_autFixedSubgroup_eq_top hp (card_eq_sq_of_mulEquiv e hp) (pow_eq_one_of_mulEquiv e hp)
    ρ hpK

end CFSG.FeitThompson
