module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Local.PrimeChiefFactorsCoprimeQuotient
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.Foundations.AbelianSolvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

variable {L : Type*} [Group L] {H E A K N : Subgroup L} {u : L}

def conjSubgroupAut (H A : Subgroup L) [H.Normal] : ↥A →* MulAut ↥H :=
  (MulAut.conjNormal (H := H)).comp A.subtype

@[simp]
theorem coe_conjSubgroupAut_apply [H.Normal] (a : ↥A) (x : ↥H) :
    ((conjSubgroupAut H A a x : ↥H) : L) = (a : L) * (x : L) * (a : L)⁻¹ :=
  MulAut.conjNormal_apply _ _

theorem fixedPointFree_conjSubgroupAut [H.Normal] {a : ↥A}
    (ha : H ⊓ Subgroup.centralizer {(a : L)} = ⊥) :
    MonoidHom.FixedPointFree (conjSubgroupAut H A a : ↥H → ↥H) := by
  intro x hx
  have hx' : (a : L) * (x : L) * (a : L)⁻¹ = (x : L) := by
    rw [← coe_conjSubgroupAut_apply (A := A) a x, hx]
  have hmem : (x : L) ∈ H ⊓ Subgroup.centralizer ({(a : L)} : Set L) :=
    mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 (by
      calc (x : L) * (a : L) = ((a : L) * (x : L) * (a : L)⁻¹) * (a : L) := by rw [hx']
        _ = (a : L) * (x : L) := by group)⟩
  rw [ha, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem fixedPoints_conjSubgroupAut_range_eq_bot [H.Normal] (hu : u ∈ A)
    (hC : H ⊓ Subgroup.centralizer {u} = ⊥) :
    FixedPoints.subgroup (conjSubgroupAut H A).range ↥H = ⊥ :=
  Subgroup.eq_bot_iff_forall _ |>.2 fun x hx =>
    fixedPointFree_conjSubgroupAut (A := A) (a := ⟨u, hu⟩) hC x
      ((mem_fixedPoints_range_iff _).1 hx ⟨u, hu⟩)

theorem coprime_natCard_of_forall_inf_centralizer_eq_bot [Finite L] [H.Normal] [Nontrivial ↥H]
    (hC : ∀ v ∈ A, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) :
    (Nat.card ↥H).Coprime (Nat.card ↥A) :=
  coprime_card_of_fixedPointFree (φ := conjSubgroupAut H A) fun v hv =>
    fixedPointFree_conjSubgroupAut (hC (v : L) v.2 fun h => hv (Subtype.ext h))

theorem isInvariantSubgroup_subgroupOf_conjSubgroupAut [H.Normal] [N.Normal] :
    IsInvariantSubgroup (conjSubgroupAut H A) (N.subgroupOf H) := by
  rw [isInvariantSubgroup_iff_forall_map_eq]
  intro a
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, mem_subgroupOf] at hy ⊢
    rw [MonoidHom.coe_coe, coe_conjSubgroupAut_apply]
    exact ‹N.Normal›.conj_mem _ hy _
  · intro x hx
    rw [mem_subgroupOf] at hx
    refine ⟨conjSubgroupAut H A a⁻¹ x, ?_, ?_⟩
    · simp only [SetLike.mem_coe, mem_subgroupOf, coe_conjSubgroupAut_apply, InvMemClass.coe_inv]
      simpa using ‹N.Normal›.conj_mem _ hx (a : L)⁻¹
    · refine Subtype.ext ?_
      rw [MonoidHom.coe_coe, coe_conjSubgroupAut_apply, coe_conjSubgroupAut_apply,
        InvMemClass.coe_inv]
      group

theorem quotientAut_isInvariantSubgroup_subgroupOf [K.Normal] [N.Normal] (a : ↥A)
    (q : ↥K ⧸ N.subgroupOf K) :
    (isInvariantSubgroup_subgroupOf_conjSubgroupAut (H := K) (A := A) (N := N)).quotientAut a q
      = factorConj K N (a : L) q := by
  induction q using QuotientGroup.induction_on with
  | _ x => rw [IsInvariantSubgroup.quotientAut_mk, factorConj_apply_mk]; rfl

theorem zpow_apply_eq_self {M : Type*} [Group M] {φ : MulAut M} {x : M} (h : φ x = x) (k : ℤ) :
    (φ ^ k) x = x := by
  have hφ : φ ∈ MulAction.stabilizer (MulAut M) x := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact h
  have h2 := (MulAction.stabilizer (MulAut M) x).zpow_mem hφ k
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2

theorem fixedPointFree_factorConj_of_isSolvable [Finite L] [K.Normal] [N.Normal]
    [Group.IsSolvable ↥K] (hC : ∀ v ∈ E, v ≠ 1 → K ⊓ Subgroup.centralizer {v} = ⊥) (hu : u ∈ E)
    (hu1 : u ≠ 1) :
    MonoidHom.FixedPointFree (factorConj K N u : ↥K ⧸ N.subgroupOf K → ↥K ⧸ N.subgroupOf K) := by
  intro q hq
  set A : Subgroup L := Subgroup.zpowers u with hA
  have huA : u ∈ A := Subgroup.mem_zpowers u
  have hAE : A ≤ E := Subgroup.zpowers_le.2 hu
  have : IsMulCommutative ↥A := Subgroup.zpowers_isMulCommutative u
  have : Group.IsSolvable ↥A := isSolvable_of_isMulCommutative
  set ρ : ↥A →* MulAut ↥K := conjSubgroupAut K A with hρ
  have hN : IsInvariantSubgroup ρ (N.subgroupOf K) :=
    isInvariantSubgroup_subgroupOf_conjSubgroupAut
  have hcop : (Nat.card ↥A).Coprime (Nat.card ↥K) := by
    rcases subsingleton_or_nontrivial ↥K with hK | hK
    · rw [Nat.card_eq_one_iff_unique.2 ⟨hK, inferInstance⟩]
      exact Nat.coprime_one_right _
    · exact (coprime_natCard_of_forall_inf_centralizer_eq_bot (H := K) (A := A)
        fun v hv => hC v (hAE hv)).symm
  have hfixK : FixedPoints.subgroup ρ.range ↥K = ⊥ :=
    fixedPoints_conjSubgroupAut_range_eq_bot huA (hC u hu hu1)
  have hqA : ∀ a : ↥A, hN.quotientAut a q = q := by
    intro a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
    rw [quotientAut_isInvariantSubgroup_subgroupOf, ← hk, map_zpow]
    exact zpow_apply_eq_self hq k
  have hmem : q ∈ FixedPoints.subgroup hN.quotientAut.range (↥K ⧸ N.subgroupOf K) :=
    (mem_fixedPoints_range_iff _).2 hqA
  rwa [fixedPoints_quotientAut_range_of_isSolvable_subgroup hN hcop, hfixK, Subgroup.map_bot,
    Subgroup.mem_bot] at hmem

theorem fixedPointFree_factorConj [Finite L] [H.Normal] [K.Normal] [N.Normal]
    [Group.IsNilpotent ↥H] (hKH : K ≤ H)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) (hu : u ∈ E) (hu1 : u ≠ 1) :
    MonoidHom.FixedPointFree (factorConj K N u : ↥K ⧸ N.subgroupOf K → ↥K ⧸ N.subgroupOf K) := by
  have : Group.IsSolvable ↥H := IsNilpotent.to_isSolvable
  have : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKH)
  exact fixedPointFree_factorConj_of_isSolvable
    (fun v hv hv1 => le_bot_iff.1 (le_trans (inf_le_inf_right _ hKH) (hC v hv hv1).le)) hu hu1

theorem factorConj_eq_self_iff_eq_one [Finite L] [H.Normal] [K.Normal] [N.Normal]
    [Group.IsNilpotent ↥H] (hKH : K ≤ H)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) (hu : u ∈ E) (hu1 : u ≠ 1)
    (q : ↥K ⧸ N.subgroupOf K) : factorConj K N u q = q ↔ q = 1 :=
  ⟨fixedPointFree_factorConj hKH hC hu hu1 q, fun hq => by rw [hq, map_one]⟩

theorem mem_of_conj_mul_inv_mk_eq [Finite L] [H.Normal] [K.Normal] [N.Normal]
    [Group.IsNilpotent ↥H] (hKH : K ≤ H)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) (hu : u ∈ E) (hu1 : u ≠ 1)
    {x : ↥K} (hx : (QuotientGroup.mk (MulAut.conjNormal u x) : ↥K ⧸ N.subgroupOf K)
      = QuotientGroup.mk x) : (x : L) ∈ N := by
  have h : factorConj K N u (QuotientGroup.mk x) = QuotientGroup.mk x := by
    rw [factorConj_apply_mk]; exact hx
  have := (factorConj_eq_self_iff_eq_one hKH hC hu hu1 _).1 h
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at this
  exact this

theorem index_eq_natCard_of_isComplement' (h : H.IsComplement' E) : H.index = Nat.card ↥E :=
  h.symm.index_eq_card

end CFSG.FeitThompson
