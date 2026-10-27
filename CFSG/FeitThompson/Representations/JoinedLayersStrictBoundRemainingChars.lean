module

public import CFSG.FeitThompson.Representations.CentralFrobeniusLayerDegreeSquareSum
public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
import CFSG.FeitThompson.Representations.LinearFrobeniusLayerCoherence
public import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.CentralSubgroupBoundsDegreeSquare
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import CFSG.FeitThompson.Representations.CentralActionCasesComplementOrderBound
import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup NormalLinearInduced
open scoped ComplexOrder

section Internal

variable {L : Type*} [Group L] [Fintype L] {P E Z : Subgroup L}

noncomputable def indFamLinearFinset (P : Subgroup L) : Finset (L → ℂ) :=
  (finite_indFamLinear P).toFinset

@[simp] theorem mem_indFamLinearFinset {P : Subgroup L} {f : L → ℂ} :
    f ∈ indFamLinearFinset P ↔ f ∈ indFamLinear P := Set.Finite.mem_toFinset _

@[simp] theorem coe_indFamLinearFinset (P : Subgroup L) :
    (indFamLinearFinset P : Set (L → ℂ)) = indFamLinear P := Set.Finite.coe_toFinset _

theorem sum_sq_degree_indFamLinear (P : Subgroup L) :
    ∑ η ∈ indFamLinearFinset P, η 1 ^ 2
      = (((indFamLinearFinset P).card * P.index ^ 2 : ℕ) : ℂ) := by
  rw [Finset.sum_congr rfl fun η hη => by
    rw [apply_one_of_mem_indFamLinear P (mem_indFamLinearFinset.1 hη)],
    Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

theorem card_indFamLinearFinset_pos [Group.IsSolvable ↥P] [Nontrivial ↥P] :
    0 < (indFamLinearFinset P).card := by
  obtain ⟨η, hη⟩ := indFamLinear_nonempty (P := P)
  exact Finset.card_pos.2 ⟨η, mem_indFamLinearFinset.2 hη⟩

theorem exists_pos_apply_one_eq_index_mul {ψ : L → ℂ}
    (hψ : ψ ∈ indFam P (nonprincipalIrr ↥P)) :
    ∃ n : ℕ, 0 < n ∧ ψ 1 = (P.index : ℂ) * n := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFam P).1 hψ
  obtain ⟨n, hn0, hn1, -⟩ := Irr.exists_degree (mem_nonprincipalIrr.1 hθ).1
  exact ⟨n, hn0, by rw [indClassFun_apply_one, hn1]⟩

theorem exists_pos_apply_one_div_index_eq {ψ : L → ℂ}
    (hψ : ψ ∈ indFam P (nonprincipalIrr ↥P)) :
    ∃ n : ℕ, 0 < n ∧ ψ 1 / (P.index : ℂ) = n := by
  obtain ⟨n, hn0, hn⟩ := exists_pos_apply_one_eq_index_mul hψ
  refine ⟨n, hn0, ?_⟩
  have hidx : ((P.index : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  rw [hn, mul_comm, mul_div_assoc, div_self hidx, mul_one]

theorem exists_degree_sq_le_relIndex_of_mem_indFam_nonprincipalIrr
    (hZc : Z ≤ centralizer (P : Set L)) {ψ : L → ℂ}
    (hψ : ψ ∈ indFam P (nonprincipalIrr ↥P)) :
    ∃ n : ℕ, 0 < n ∧ ψ 1 = (P.index : ℂ) * n ∧ n ^ 2 ≤ Z.relIndex P := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFam P).1 hψ
  have hθirr : θ ∈ Irr ↥P := (mem_nonprincipalIrr.1 hθ).1
  obtain ⟨n, hn0, hn1, -⟩ := Irr.exists_degree hθirr
  have hcen : Z.subgroupOf P ≤ Subgroup.center ↥P :=
    subgroupOf_le_center_of_le_centralizer le_rfl (Subgroup.le_centralizer_iff.1 hZc)
  obtain ⟨m, hm, hmle⟩ := exists_degree_eq_and_sq_le_index_of_le_center hθirr hcen
  have hmn : m = n := by
    have : ((m : ℕ) : ℂ) = ((n : ℕ) : ℂ) := by rw [← hm, hn1]
    exact_mod_cast this
  refine ⟨n, hn0, by rw [indClassFun_apply_one, hn1], ?_⟩
  rw [Subgroup.relIndex, ← hmn]
  exact hmle

omit [Fintype L] in
theorem inf_centralizer_eq_bot_of_free
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) :
    ∀ u ∈ E, u ≠ 1 → Z ⊓ centralizer ({u} : Set L) = ⊥ := by
  intro u hu hu1
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hzZ, hzc⟩ := Subgroup.mem_inf.1 hz
  exact hfree u hu hu1 z hzZ (Subgroup.mem_centralizer_singleton_iff.1 hzc).symm

variable [P.Normal] [Z.Normal]

theorem two_mul_index_mul_apply_one_lt_sum_sq
    [Group.IsSolvable ↥P] [Nontrivial ↥P]
    (hZP : Z ≤ P) (hZc : Z ≤ centralizer (P : Set L)) (hPE : P ⊔ E = ⊤) (hinf : P ⊓ E = ⊥)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1)
    (hLodd : Odd (Nat.card L)) (hZbot : Z ≠ ⊥) {ψ : L → ℂ}
    (hψ : ψ ∈ indFam P (nonprincipalIrr ↥P)) :
    2 * (P.index : ℂ) * ψ 1
      < (∑ ξ ∈ indFamDetectFinset P (Z.subgroupOf P), ξ 1 ^ 2)
        + ∑ η ∈ indFamLinearFinset P, η 1 ^ 2 := by
  obtain ⟨n, hn0, hn1, hnr⟩ :=
    exists_degree_sq_le_relIndex_of_mem_indFam_nonprincipalIrr hZc hψ
  set e := P.index with he
  set r := Z.relIndex P with hr
  set c := (indFamLinearFinset P).card with hc
  have hZcard : 1 ≤ Nat.card ↥Z := Nat.card_pos
  have hidx : e = Nat.card ↥E := index_eq_natCard_of_sup_eq_top hPE hinf
  have h2e : 2 * e ≤ Nat.card ↥Z - 1 := by
    rw [hidx]
    exact two_mul_natCard_le_natCard_sub_one (E := E) hLodd hZbot
      (inf_centralizer_eq_bot_of_free hfree)
  have he0 : 0 < e := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hc0 : 0 < c := card_indFamLinearFinset_pos
  have hX : (∑ ξ ∈ indFamDetectFinset P (Z.subgroupOf P), ξ 1 ^ 2)
      = ((e * r * (Nat.card ↥Z - 1) : ℕ) : ℂ) := by
    rw [sum_sq_degree_indFamDetect (E := E) hZP hZc hPE hfree]
    push_cast [Nat.cast_sub hZcard]
    ring
  have hY : (∑ η ∈ indFamLinearFinset P, η 1 ^ 2) = ((c * e ^ 2 : ℕ) : ℂ) :=
    sum_sq_degree_indFamLinear P
  have hlhs : 2 * (e : ℂ) * ψ 1 = ((2 * e * e * n : ℕ) : ℂ) := by
    rw [hn1]; push_cast; ring
  have key : 2 * e * e * n < e * r * (Nat.card ↥Z - 1) + c * e ^ 2 := by
    have h1 : 2 * e * e * n ≤ e * r * (2 * e) := by
      have hn2 : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
      calc 2 * e * e * n = e * n * (2 * e) := by ring
        _ ≤ e * (n ^ 2) * (2 * e) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn2)
        _ ≤ e * r * (2 * e) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hnr)
    have h2 : e * r * (2 * e) ≤ e * r * (Nat.card ↥Z - 1) := Nat.mul_le_mul_left _ h2e
    have h3 : 0 < c * e ^ 2 := Nat.mul_pos hc0 (pow_pos he0 2)
    omega
  rw [hX, hY, hlhs, ← Nat.cast_add]
  exact_mod_cast key

end Internal

namespace IsFreeCentralSection

variable {G : Type*} [Group G] [Finite G] {p a : ℕ} {L P E Z : Subgroup G}
  (h : IsFreeCentralSection p a L P E Z)

include h

variable [Fintype ↥L] [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

theorem exists_pos_apply_one_div_natCard_eq {ψ : ↥L → ℂ}
    (hψ : ψ ∈ indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))) :
    ∃ n : ℕ, 0 < n ∧ ψ 1 / (Nat.card ↥E : ℂ) = n := by
  obtain ⟨n, hn0, hn⟩ := exists_pos_apply_one_div_index_eq hψ
  exact ⟨n, hn0, by rwa [h.index_subgroupOf_eq] at hn⟩

theorem two_mul_natCard_mul_apply_one_lt_sum_sq {ψ : ↥L → ℂ}
    (hψ : ψ ∈ indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))) :
    2 * (Nat.card ↥E : ℂ) * ψ 1
      < (∑ ξ ∈ indFamDetectFinset (P.subgroupOf L)
            ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), ξ 1 ^ 2)
        + ∑ η ∈ indFamLinearFinset (P.subgroupOf L), η 1 ^ 2 := by
  have := h.isSolvable_subgroupOf_P
  have := h.nontrivial_subgroupOf_P
  have hres := two_mul_index_mul_apply_one_lt_sum_sq (E := E.subgroupOf L)
    h.Z_subgroupOf_le_P_subgroupOf h.Z_subgroupOf_le_centralizer h.sup_subgroupOf
    h.inf_subgroupOf_eq_bot h.free_subgroupOf h.odd_natCard_L h.Z_subgroupOf_ne_bot hψ
  rwa [h.index_subgroupOf_eq] at hres

end IsFreeCentralSection

end CFSG.FeitThompson
