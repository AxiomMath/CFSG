module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Local.FixedOrderMultiplicativityNormal
public import CFSG.FeitThompson.Representations.FrobeniusComplementPermutationCharacter
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

section Action

variable {A V : Type*} [Group A] [Group V] {ρ : A →* MulAut V} {N : Subgroup V}

theorem isSolvable_zpowers (u : A) : Group.IsSolvable ↥(Subgroup.zpowers u) := by
  refine Group.isSolvable_of_comm fun x y => ?_
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
  refine Subtype.ext ?_
  push_cast
  rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]

theorem isInvariantSubgroup_of_forall (h : ∀ b : A, ∀ v ∈ N, ρ b v ∈ N) :
    IsInvariantSubgroup ρ N := by
  rw [isInvariantSubgroup_iff_forall_map_eq]
  intro b
  refine le_antisymm ?_ fun v hv => ⟨ρ b⁻¹ v, h b⁻¹ v hv, ?_⟩
  · rintro x ⟨v, hv, rfl⟩
    exact h b v hv
  · change ρ b (ρ b⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem quotientAut_comp_subtype_apply {S : Subgroup A} [N.Normal]
    (hN : IsInvariantSubgroup ρ N) (b : ↥S) (x : V ⧸ N) :
    (hN.comp S.subtype).quotientAut b x = hN.quotientAut (b : A) x := by
  induction x using QuotientGroup.induction_on with
  | H v => rw [IsInvariantSubgroup.quotientAut_mk, IsInvariantSubgroup.quotientAut_mk]; rfl

theorem fixedPointFree_quotientAut_of_forall_fixed_mem [Finite A] [Finite V] [Group.IsSolvable V]
    [N.Normal]
    (hN : IsInvariantSubgroup ρ N) (hcop : (Nat.card A).Coprime (Nat.card V)) {u : A}
    (hle : ∀ v : V, ρ u v = v → v ∈ N) :
    MonoidHom.FixedPointFree (hN.quotientAut u : V ⧸ N → V ⧸ N) := by
  intro x hx
  set hNu := hN.comp (Subgroup.zpowers u).subtype with hNudef
  have := isSolvable_zpowers u
  have hcop' : (Nat.card ↥(Subgroup.zpowers u)).Coprime (Nat.card V) :=
    hcop.coprime_dvd_left (by rw [Nat.card_zpowers]; exact orderOf_dvd_natCard u)
  have hfix : FixedPoints.subgroup (ρ.comp (Subgroup.zpowers u).subtype).range V ≤ N := fun v hv =>
    hle v (by simpa using (mem_fixedPoints_range_iff _).1 hv ⟨u, Subgroup.mem_zpowers u⟩)
  have key : FixedPoints.subgroup hNu.quotientAut.range (V ⧸ N) = ⊥ := by
    rw [fixedPoints_quotientAut_range hNu hcop', eq_bot_iff]
    exact (Subgroup.map_mono hfix).trans_eq (QuotientGroup.map_mk'_self N)
  have hxmem : x ∈ FixedPoints.subgroup hNu.quotientAut.range (V ⧸ N) := by
    rw [mem_fixedPoints_range_iff]
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
    have hst : hN.quotientAut u ∈ MulAction.stabilizer (MulAut (V ⧸ N)) x :=
      MulAction.mem_stabilizer_iff.2 (by rw [MulAut.smul_def]; exact hx)
    have h2 := (MulAction.stabilizer (MulAut (V ⧸ N)) x).zpow_mem hst k
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← map_zpow] at h2
    rw [hNudef, quotientAut_comp_subtype_apply hN b x, show (b : A) = u ^ k from hk.symm]
    exact h2
  rw [key, Subgroup.mem_bot] at hxmem
  exact hxmem

theorem two_mul_natCard_add_one_le_index_of_forall_fixed_mem [Finite A] [Finite V]
    [Group.IsSolvable V] [N.Normal] (hN : IsInvariantSubgroup ρ N)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (hVodd : Odd (Nat.card V))
    (hAodd : Odd (Nat.card A)) (hNtop : N ≠ ⊤)
    (hfix : ∀ u : A, u ≠ 1 → ∀ v : V, ρ u v = v → v ∈ N) :
    2 * Nat.card A + 1 ≤ N.index := by
  have : Nontrivial (V ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
  have hfree : ∀ u : A, u ≠ 1 → MonoidHom.FixedPointFree (hN.quotientAut u : V ⧸ N → V ⧸ N) :=
    fun u hu => fixedPointFree_quotientAut_of_forall_fixed_mem hN hcop (hfix u hu)
  have hoddsemi : Odd (Nat.card ((V ⧸ N) ⋊[hN.quotientAut] A)) := by
    rw [SemidirectProduct.card]
    exact Odd.mul (by rw [← Subgroup.index_eq_card]; exact hVodd.of_dvd_nat N.index_dvd_card) hAodd
  have h := two_mul_card_le_card_sub_one_of_fixedPointFree hfree hoddsemi
  rw [← Subgroup.index_eq_card] at h
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  omega

end Action

section Conj

variable {L : Type*} [Group L] {E : Subgroup L}

theorem conjAutOn_apply_eq_self_iff {V : Subgroup L} [V.Normal] (u : ↥E) (v : ↥V) :
    conjAutOn V E u v = v ↔ (v : L) * (u : L) = (u : L) * (v : L) := by
  rw [← Subtype.coe_inj, conjAutOn_apply_coe]
  constructor
  · intro h
    calc (v : L) * (u : L) = ((u : L) * (v : L) * (u : L)⁻¹) * (u : L) := by rw [h]
      _ = (u : L) * (v : L) := by group
  · intro h
    rw [← h]; group

theorem isInvariantSubgroup_subgroupOf_conjAutOn (V W : Subgroup L) [V.Normal] [hW : W.Normal] :
    IsInvariantSubgroup (conjAutOn V E) (W.subgroupOf V) :=
  isInvariantSubgroup_of_forall fun u v hv => by
    rw [mem_subgroupOf] at hv ⊢
    rw [conjAutOn_apply_coe]
    exact hW.conj_mem _ hv _

variable [Finite L]

theorem two_mul_natCard_add_one_le_relIndex_of_forall_commute_mem
    {V W : Subgroup L} [V.Normal] [W.Normal]
    [Group.IsSolvable ↥V] (hLodd : Odd (Nat.card L))
    (hcop : (Nat.card ↥E).Coprime (Nat.card ↥V)) (hWV : W < V)
    (hfix : ∀ u ∈ E, u ≠ 1 → ∀ v ∈ V, v * u = u * v → v ∈ W) :
    2 * Nat.card ↥E + 1 ≤ W.relIndex V := by
  refine two_mul_natCard_add_one_le_index_of_forall_fixed_mem
    (isInvariantSubgroup_subgroupOf_conjAutOn V W) hcop
    (hLodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card V))
    (hLodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card E))
    (fun h => absurd (subgroupOf_eq_top.1 h) (not_le_of_gt hWV)) ?_
  intro u hu v hv
  rw [mem_subgroupOf]
  exact hfix (u : L) u.2 (fun h => hu (Subtype.ext h)) (v : L) v.2
    ((conjAutOn_apply_eq_self_iff u v).1 hv)

theorem two_mul_natCard_le_natCard_sub_one {V : Subgroup L} [V.Normal]
    (hLodd : Odd (Nat.card L)) (hV : V ≠ ⊥)
    (hfree : ∀ u ∈ E, u ≠ 1 → V ⊓ Subgroup.centralizer {u} = ⊥) :
    2 * Nat.card ↥E ≤ Nat.card ↥V - 1 := by
  have : Nontrivial ↥V := V.nontrivial_iff_ne_bot.2 hV
  refine two_mul_card_le_card_sub_one_of_fixedPointFree
    (φ := conjAutOn V E) (fun u hu => fixedPointFree_conjAutOn hfree u hu) ?_
  rw [SemidirectProduct.card]
  exact (hLodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card V)).mul
    (hLodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card E))

end Conj

section Threshold

variable {L : Type*} [Group L] [Finite L] {E P Z : Subgroup L} {p a : ℕ}

theorem four_mul_sq_natCard_le_relIndex_mul_sq_case_A [Z.Normal] (hLodd : Odd (Nat.card L))
    (hZbot : ⊥ < Z) (hfree : ∀ u ∈ E, u ≠ 1 → Z ⊓ Subgroup.centralizer {u} = ⊥) :
    4 * Nat.card ↥E ^ 2 ≤ Z.relIndex P * (Nat.card ↥Z - 1) ^ 2 := by
  have h := two_mul_natCard_le_natCard_sub_one (E := E) hLodd hZbot.ne' hfree
  have hrel : 1 ≤ Z.relIndex P := by
    have : Z.relIndex P ≠ 0 := by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
    omega
  calc 4 * Nat.card ↥E ^ 2 = (2 * Nat.card ↥E) ^ 2 := by ring
    _ ≤ (Nat.card ↥Z - 1) ^ 2 := Nat.pow_le_pow_left h 2
    _ ≤ Z.relIndex P * (Nat.card ↥Z - 1) ^ 2 := Nat.le_mul_of_pos_left _ hrel

theorem four_mul_sq_natCard_le_relIndex_mul_sq_case_B [P.Normal] [Z.Normal] (hp : p.Prime)
    (hPcard : Nat.card ↥P = p ^ a) (ha : 1 ≤ a) (hLodd : Odd (Nat.card L))
    (hcop : (Nat.card ↥P).Coprime (Nat.card ↥E)) (hZbot : ⊥ < Z) (hZP' : Z < ⁅P, P⁆)
    (hcent : ∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = Z) :
    4 * Nat.card ↥E ^ 2 ≤ Z.relIndex P * (Nat.card ↥Z - 1) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hPnil := (IsPGroup.of_card hPcard).isNilpotent
  have hPsolv : Group.IsSolvable ↥P := inferInstance
  have hPnontriv : Nontrivial ↥P := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hPcard]
    calc 1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  have hP'P : ⁅P, P⁆ < P := by
    have h1 : _root_.commutator ↥P < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥P
    have h2 := (Subgroup.map_lt_map_iff_of_injective (f := P.subtype) P.subtype_injective).2 h1
    rwa [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  have hP'le : ⁅P, P⁆ ≤ P := hP'P.le
  have hZle : Z ≤ ⁅P, P⁆ := hZP'.le
  have hP'solv : Group.IsSolvable ↥(⁅P, P⁆) := isSolvable_of_le hP'le
  have hcop' : (Nat.card ↥E).Coprime (Nat.card ↥P) := hcop.symm
  have hcopP' : (Nat.card ↥E).Coprime (Nat.card ↥(⁅P, P⁆)) :=
    hcop'.coprime_dvd_right (Subgroup.card_dvd_of_le hP'le)
  have hb1 : 2 * Nat.card ↥E + 1 ≤ (⁅P, P⁆).relIndex P := by
    refine two_mul_natCard_add_one_le_relIndex_of_forall_commute_mem hLodd hcop' hP'P
      fun u hu hu1 v hv hcomm => ?_
    have hmem : v ∈ P ⊓ Subgroup.centralizer {u} :=
      Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
    rw [hcent u hu hu1] at hmem
    exact hZle hmem
  have hb2 : 2 * Nat.card ↥E + 1 ≤ Z.relIndex ⁅P, P⁆ := by
    refine two_mul_natCard_add_one_le_relIndex_of_forall_commute_mem hLodd hcopP' hZP'
      fun u hu hu1 v hv hcomm => ?_
    have hmem : v ∈ P ⊓ Subgroup.centralizer {u} :=
      Subgroup.mem_inf.2 ⟨hP'le hv, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
    rwa [hcent u hu hu1] at hmem
  have hmul : Z.relIndex ⁅P, P⁆ * (⁅P, P⁆).relIndex P = Z.relIndex P :=
    Subgroup.relIndex_mul_relIndex Z ⁅P, P⁆ P hZle hP'le
  have hZcard : 2 ≤ Nat.card ↥Z := by
    have : Nontrivial ↥Z := Z.nontrivial_iff_ne_bot.2 hZbot.ne'
    have := (Finite.one_lt_card_iff_nontrivial (α := ↥Z)).2 this
    omega
  have key : 4 * Nat.card ↥E ^ 2 ≤ Z.relIndex P := by
    have h := Nat.mul_le_mul hb2 hb1
    rw [hmul] at h
    nlinarith [h]
  calc 4 * Nat.card ↥E ^ 2 ≤ Z.relIndex P := key
    _ ≤ Z.relIndex P * (Nat.card ↥Z - 1) ^ 2 :=
        Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))

theorem four_mul_sq_natCard_le_relIndex_mul_sq_natCard_sub_one [P.Normal] [Z.Normal]
    (hp : p.Prime) (_hpodd : Odd p) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hLodd : Odd (Nat.card L)) (_hcompl : P.IsComplement' E)
    (hcop : (Nat.card ↥P).Coprime (Nat.card ↥E)) [Nontrivial ↥E] (_hEcyc : IsCyclic ↥E)
    (hZbot : ⊥ < Z) (hZP' : Z < ⁅P, P⁆) (_hZcent : Z ≤ Subgroup.centralizer (P : Set L))
    (hcase : (∀ u ∈ E, u ≠ 1 → Z ⊓ Subgroup.centralizer {u} = ⊥) ∨
      (∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = Z)) :
    4 * Nat.card ↥E ^ 2 ≤ Z.relIndex P * (Nat.card ↥Z - 1) ^ 2 := by
  rcases hcase with hA | hB
  · exact four_mul_sq_natCard_le_relIndex_mul_sq_case_A hLodd hZbot hA
  · exact four_mul_sq_natCard_le_relIndex_mul_sq_case_B hp hPcard ha hLodd hcop hZbot hZP' hB

end Threshold

end CFSG.FeitThompson
