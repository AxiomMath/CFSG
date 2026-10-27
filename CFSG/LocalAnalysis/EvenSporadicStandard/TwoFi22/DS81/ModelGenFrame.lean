module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.E0
public import Certificates.Certificate25260
import all CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.EvenSporadicStandard.Wong77.Module
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

@[expose] def uPts : Finset (Fin 3510) := Finset.univ.filter fun x => x.val ∈ genUSorted

theorem genU_lt : ∀ n ∈ genU, n < 3510 := by decide

theorem genU_perm : genU.Perm genUSorted := by decide

theorem genU_length : genU.length = 22 := by decide

theorem mem_uPts {x : Fin 3510} : x ∈ uPts ↔ x.val ∈ genUSorted := by
  simp [uPts]

section

theorem ptE_genU (u : Fin 3510) (j : ℕ) (hj : j < 22) (hu : u.val = genU.getD j 0) :
    (ptE u : J) = fjPt ⟨j + 1, by omega⟩ := by
  have hA : genChecksA CFSG.Sporadic.Fi23.orb = true := Certificates.certificate25260
  unfold genChecksA at hA
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hA
  have h := hA j hj
  have hea : CFSG.Sporadic.Fi23.ea = CFSG.Sporadic.Fi23.Native.starPts
      (CFSG.Sporadic.Fi23.Native.dTable CFSG.Sporadic.Fi23.orb) := by
    rw [CFSG.Sporadic.Fi23.ea, CFSG.Sporadic.Fi23.frozen_eq, CFSG.Sporadic.Fi23.dT,
      CFSG.Sporadic.Fi23.frozen_eq]
  have hphiP : CFSG.Sporadic.Fi23.phiP = CFSG.Sporadic.Fi23.Native.starPhiPos := by
    rw [CFSG.Sporadic.Fi23.phiP, CFSG.Sporadic.Fi23.frozen_eq]
  rw [ptE_apply, hea, hphiP, hu]
  exact congrArg CFSG.Sporadic.Fi23.conjPt h

theorem mem_uPts_iff {x : Fin 3510} :
    x ∈ uPts ↔ ∃ j : Fin 23, j ≠ 0 ∧ (ptE x : J) = fjPt j := by
  constructor
  · intro hx
    have hx' : x.val ∈ genU := genU_perm.mem_iff.2 (mem_uPts.1 hx)
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.1 hx'
    have hj22 : j < 22 := by simpa [genU_length] using hj
    refine ⟨⟨j + 1, by omega⟩, fun h => ?_, ptE_genU x j hj22 ?_⟩
    · have := congrArg Fin.val h
      simp at this
    · rw [List.getD_eq_getElem _ _ hj, hjx]
  · rintro ⟨j, hj0, hjx⟩
    have hjv : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    obtain ⟨j', hj'⟩ : ∃ j' : ℕ, j.val = j' + 1 := ⟨j.val - 1, by omega⟩
    have hj22 : j' < 22 := by have := j.2; omega
    have hj22' : j' < genU.length := by rw [genU_length]; exact hj22
    have hmemU : genU.getD j' 0 ∈ genU := by
      rw [List.getD_eq_getElem _ _ hj22']
      exact List.getElem_mem _
    have hlt : genU.getD j' 0 < 3510 := genU_lt _ hmemU
    have hu := ptE_genU ⟨genU.getD j' 0, hlt⟩ j' hj22 rfl
    have hjeq : j = ⟨j' + 1, by omega⟩ := Fin.ext hj'
    have hx : x = ⟨genU.getD j' 0, hlt⟩ := by
      apply ptE.injective
      apply Subtype.ext
      rw [hjx, hjeq, hu]
    rw [hx, mem_uPts]
    exact genU_perm.mem_iff.1 hmemU

theorem fjPt_mem_range (i : Fin 23) : fjPt i ∈ fjHom.range :=
  ⟨eVec i, fjHom_eVec i⟩

theorem star_mem_range {x : J} (hx : x ∈ star) (hxr : x ∈ fjHom.range) :
    ∃ i : Fin 23, i ≠ 0 ∧ fjPt i = x := by
  have hE : IsPGroup 2 fjProj.range :=
    isPGroup_word.of_surjective fjProj.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  have hSi : ∀ i : Fin 23, piC (fjQ i) ∈ (S : Subgroup CFSG.Sporadic.Fi22.J) := fun i =>
    hES ⟨eVec i, fjProj_eVec i⟩
  obtain ⟨w, rfl⟩ := hxr
  have hxS : piC (ofStar ⟨fjHom w, hx⟩) ∈ (S : Subgroup CFSG.Sporadic.Fi22.J) :=
    hES ⟨w, rfl⟩
  exact exists_pt_of_image_mem hSi hx hxS

theorem ofAdd_mem_closure (w : Word) :
    Multiplicative.ofAdd w ∈ Subgroup.closure (Set.range eVec) := by
  have hw : w = ind (Finset.univ.filter fun i => w i = 1) := by
    funext i
    rw [ind_apply]
    by_cases h : w i = 1
    · simp [h]
    · have : w i = 0 := by
        revert h
        generalize w i = a
        revert a
        decide
      simp [this]
  rw [hw, ind_eq_sum, ofAdd_sum]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.subset_closure ⟨i, rfl⟩

theorem range_le_closure : fjHom.range ≤ Subgroup.closure (Set.range fjPt) := by
  rintro _ ⟨w, rfl⟩
  have h := ofAdd_mem_closure (Multiplicative.toAdd w)
  rw [ofAdd_toAdd] at h
  have h2 : fjHom w ∈ (Subgroup.closure (Set.range eVec)).map fjHom := ⟨w, h, rfl⟩
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, (fjHom_eVec i).symm⟩

theorem ptE_smul (c : Cd) (u : Fin 3510) :
    (ptE (c • u) : J) = (c : J) * ptE u * (c : J)⁻¹ := by
  have h : ptE (c • u) = c • ptE u := by
    rw [Equiv.smul_def ptE c u, Equiv.apply_symm_apply]
  rw [h]
  rfl

@[expose] noncomputable def Stab : Subgroup Cd := MulAction.stabilizer Cd uPts

theorem mem_stab_iff {c : Cd} : c ∈ Stab ↔ ∀ u ∈ uPts, c • u ∈ uPts := by
  unfold Stab
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h u hu
    rw [← h]
    exact Finset.smul_mem_smul_finset hu
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_smul_finset.1 hy
      exact h u hu
    · rw [Finset.card_smul_finset]

theorem conj_mem_range {c : Cd} (hc : c ∈ Stab) {x : J} (hx : x ∈ fjHom.range) :
    (c : J) * x * (c : J)⁻¹ ∈ fjHom.range := by
  have key : ∀ y ∈ Subgroup.closure (Set.range fjPt), (c : J) * y * (c : J)⁻¹ ∈ fjHom.range := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      by_cases hi : i = 0
      · subst hi
        rw [fjPt_zero, (mem_Cd.1 c.2), mul_inv_cancel_right]
        exact fjPt_zero ▸ fjPt_mem_range 0
      · obtain ⟨u, hu⟩ := ptE.surjective ⟨fjPt i, fjPt_star hi⟩
        have hpt : (ptE u : J) = fjPt i := by rw [hu]
        have hui : u ∈ uPts := mem_uPts_iff.2 ⟨i, hi, hpt⟩
        obtain ⟨j, -, hj⟩ := mem_uPts_iff.1 ((mem_stab_iff.1 hc) u hui)
        rw [← hpt, ← ptE_smul, hj]
        exact fjPt_mem_range j
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul y z _ _ hy hz =>
      have : (c : J) * (y * z) * (c : J)⁻¹ =
          ((c : J) * y * (c : J)⁻¹) * ((c : J) * z * (c : J)⁻¹) := by group
      rw [this]
      exact mul_mem hy hz
    | inv y _ hy =>
      have : (c : J) * y⁻¹ * (c : J)⁻¹ = ((c : J) * y * (c : J)⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hy
  exact key x (range_le_closure hx)

theorem conj_conj_inv {G : Type*} [Group G] (c h : G) : c⁻¹ * (c * h * c⁻¹) * c = h := by group

theorem mem_normalizer_iff_mem_stab {c : Cd} :
    c ∈ normalizer (E0 : Set Cd) ↔ c ∈ Stab := by
  constructor
  · intro hc
    rw [mem_stab_iff]
    intro u hu
    obtain ⟨j, hj0, hj⟩ := mem_uPts_iff.1 hu
    have hmem : (⟨fjPt j, mem_Cd.2 (fjPt_comm_d j)⟩ : Cd) ∈ E0 :=
      Subgroup.mem_subgroupOf.2 (fjPt_mem_range j)
    have h1 := (Subgroup.mem_normalizer_iff.1 hc _).1 hmem
    rw [E0, Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h3 : (ptE (c • u) : J) = (c : J) * fjPt j * (c : J)⁻¹ := by rw [ptE_smul, hj]
    obtain ⟨i, hi, hix⟩ := star_mem_range (ptE (c • u)).2 (h3 ▸ h1)
    exact mem_uPts_iff.2 ⟨i, hi, hix.symm⟩
  · intro hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 := conj_mem_range hc (Subgroup.mem_subgroupOf.1 hh)
      rw [E0, Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    · intro hh
      have h1 := conj_mem_range (inv_mem hc) (Subgroup.mem_subgroupOf.1 hh)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [inv_inv, conj_conj_inv] at h1
      rw [E0, Subgroup.mem_subgroupOf]
      exact h1

theorem E0_smul_eq {e : Cd} (he : e ∈ E0) {u : Fin 3510} (hu : u ∈ uPts) : e • u = u := by
  obtain ⟨j, -, hj⟩ := mem_uPts_iff.1 hu
  apply ptE.injective
  apply Subtype.ext
  rw [ptE_smul, hj]
  obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 he
  obtain ⟨v, hv⟩ := fjPt_mem_range j
  rw [← hw, ← hv, ← map_inv, ← map_mul, ← map_mul, mul_inv_cancel_comm]

theorem card_E0 : Nat.card E0 = 2 ^ 11 := by
  have h1 : Nat.card E0 = Nat.card fjHom.range := by
    have h : Nat.card (E0.map Cd.subtype) = Nat.card E0 :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [← h, E0, Subgroup.subgroupOf_map_subtype]
    congr 2
    exact inf_eq_left.2 (fun x hx => by
      obtain ⟨w, rfl⟩ := hx
      exact fjHom_mem_Cd w)
  have h2 : Nat.card (Multiplicative Word) = 2 ^ 23 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := Word)), Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 : Nat.card fjHom.ker = 2 ^ 12 := by
    rw [← natCard_golayCode]
    refine Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd x.1,
          (fjHom_eq_one_iff _).1 (by rw [ofAdd_toAdd]; exact MonoidHom.mem_ker.1 x.2)⟩
        invFun := fun w => ⟨Multiplicative.ofAdd w.1,
          MonoidHom.mem_ker.2 ((fjHom_eq_one_iff w.1).2 w.2)⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup fjHom.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange fjHom).toEquiv, h2, h3] at h4
  rw [h1]
  have h5 : Nat.card fjHom.range * 2 ^ 12 = 2 ^ 11 * 2 ^ 12 := by
    rw [← h4]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h5

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen
