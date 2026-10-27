module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks
public import CFSG.LieType.SeitzGeneration.UnitaryRankThreeBlocks

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.LocalRank (natCast_card_subgroup_ne_zero)
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)
open scoped DirectSum CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]

theorem mem_fixSub_iff' {D : Subgroup ↥A} {v : V} :
    v ∈ fixSub (actionEnd A) D ↔ ∀ d ∈ D, (d : V ≃ₗ[F] V) v = v :=
  ⟨fun h d hd => h d hd, fun h d hd => h d hd⟩

theorem natCast_card_subgroup_ne_zero' {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (D : Subgroup ↥A) : ((Fintype.card ↥D : ℕ) : F) ≠ 0 := by
  have hpow : ∀ g : ↥A, g ^ p = 1 := fun g => Subtype.ext (by
    simpa using hA.2 (g : V ≃ₗ[F] V) g.2)
  have h := natCast_card_subgroup_ne_zero (G := ↥A) hp hpow hpF D
  rwa [Nat.card_eq_fintype_card] at h

variable {p : ℕ}

def avgCoeff (D : Subgroup ↥A) : F := (((Fintype.card ↥D : ℕ) : F))⁻¹

private theorem avgCoeff_mul_card (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Subgroup ↥A) : avgCoeff A D * ((Fintype.card ↥D : ℕ) : F) = 1 :=
  inv_mul_cancel₀ (natCast_card_subgroup_ne_zero' A hp hpF hA D)

private theorem actionEnd_mul_sumOp {q : ℕ} (hA : IsElemAbelian q A) (D : Subgroup ↥A) (a : ↥A) :
    actionEnd A a * sumOp (actionEnd A) D = sumOp (actionEnd A) D * actionEnd A a := by
  haveI : IsMulCommutative ↥A := hA.1
  rw [sumOp, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← map_mul, ← map_mul, mul_comm' a (d : ↥A)]

private theorem actionEnd_sumOp_apply {q : ℕ} (hA : IsElemAbelian q A) (D : Subgroup ↥A) (a : ↥A)
    (v : V) :
    actionEnd A a (sumOp (actionEnd A) D v) = sumOp (actionEnd A) D (actionEnd A a v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, actionEnd_mul_sumOp A hA]

@[expose] def projBlock (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) : Module.End F V :=
  avgCoeff A D.1 • sumOp (actionEnd A) D.1 -
    avgCoeff A (⊤ : Subgroup ↥A) • sumOp (actionEnd A) ⊤

theorem projBlock_apply_eq (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) (v : V) :
    projBlock A hp hpF hA D v
      = avgCoeff A D.1 • sumOp (actionEnd A) D.1 v
        - avgCoeff A (⊤ : Subgroup ↥A) • sumOp (actionEnd A) ⊤ v := by
  rw [projBlock, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply]

private theorem sumOp_top_sumOp {q : ℕ} (hA : IsElemAbelian q A) (D : Subgroup ↥A) (v : V) :
    sumOp (actionEnd A) ⊤ (sumOp (actionEnd A) D v)
      = ((Fintype.card ↥D : ℕ) : F) • sumOp (actionEnd A) ⊤ v := by
  haveI : IsMulCommutative ↥A := hA.1
  have hL : sumOp (actionEnd A) ⊤ (sumOp (actionEnd A) D v)
      = ∑ a : ↥(⊤ : Subgroup ↥A), ∑ d : ↥D,
          actionEnd A (a : ↥A) (actionEnd A (d : ↥A) v) := by
    rw [sumOp, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sumOp, LinearMap.sum_apply, map_sum]
  have hR : sumOp (actionEnd A) D (sumOp (actionEnd A) ⊤ v)
      = ∑ d : ↥D, ∑ a : ↥(⊤ : Subgroup ↥A),
          actionEnd A (d : ↥A) (actionEnd A (a : ↥A) v) := by
    rw [sumOp, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [sumOp, LinearMap.sum_apply, map_sum]
  have hcomm : (∑ a : ↥(⊤ : Subgroup ↥A), ∑ d : ↥D,
        actionEnd A (a : ↥A) (actionEnd A (d : ↥A) v))
      = ∑ d : ↥D, ∑ a : ↥(⊤ : Subgroup ↥A),
          actionEnd A (d : ↥A) (actionEnd A (a : ↥A) v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
    calc actionEnd A (a : ↥A) (actionEnd A (d : ↥A) v)
        = (actionEnd A (a : ↥A) * actionEnd A (d : ↥A)) v := (Module.End.mul_apply ..).symm
      _ = actionEnd A ((a : ↥A) * (d : ↥A)) v := by rw [map_mul]
      _ = actionEnd A ((d : ↥A) * (a : ↥A)) v := by rw [mul_comm' (a : ↥A) (d : ↥A)]
      _ = (actionEnd A (d : ↥A) * actionEnd A (a : ↥A)) v := by rw [map_mul]
      _ = actionEnd A (d : ↥A) (actionEnd A (a : ↥A) v) := Module.End.mul_apply ..
  have h2 : sumOp (actionEnd A) D (sumOp (actionEnd A) ⊤ v)
      = ((Fintype.card ↥D : ℕ) : F) • sumOp (actionEnd A) ⊤ v :=
    sumOp_apply_of_fix (actionEnd A) D ((mem_fixSub_iff' A).mpr fun d _ =>
      (mem_fixSub_iff' A).mp (sumOp_mem_fixSub (actionEnd A) ⊤ v) d (Subgroup.mem_top d))
  rw [hL, hcomm, ← hR, h2]

theorem projBlock_apply_mem (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) (v : V) : projBlock A hp hpF hA D v ∈ blockSpace A D.1 := by
  refine (mem_blockSpace A).mpr ⟨fun d hd => ?_, ?_⟩
  · rw [projBlock_apply_eq]
    have h1 : (d : V ≃ₗ[F] V) (sumOp (actionEnd A) D.1 v) = sumOp (actionEnd A) D.1 v :=
      (mem_fixSub_iff' A).mp (sumOp_mem_fixSub (actionEnd A) D.1 v) d hd
    have h2 : (d : V ≃ₗ[F] V) (sumOp (actionEnd A) ⊤ v) = sumOp (actionEnd A) ⊤ v :=
      (mem_fixSub_iff' A).mp (sumOp_mem_fixSub (actionEnd A) ⊤ v) d (Subgroup.mem_top d)
    rw [map_sub, map_smul, map_smul, h1, h2]
  · rw [mem_commutatorSpaceOf, projBlock_apply_eq, map_sub, map_smul, map_smul,
      sumOp_top_sumOp A hA D.1 v, sumOp_top_sumOp A hA (⊤ : Subgroup ↥A) v]
    simp only [avgCoeff, smul_smul, inv_mul_cancel₀ (natCast_card_subgroup_ne_zero' A hp hpF hA D.1),
      inv_mul_cancel₀ (natCast_card_subgroup_ne_zero' A hp hpF hA ⊤), one_smul, sub_self]

theorem projBlock_apply_of_mem (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) {v : V} (hv : v ∈ blockSpace A D.1) :
    projBlock A hp hpF hA D v = v := by
  have hcard := natCast_card_subgroup_ne_zero' A hp hpF hA D.1
  have h1 : sumOp (actionEnd A) D.1 v = ((Fintype.card ↥D.1 : ℕ) : F) • v :=
    sumOp_apply_of_fix (actionEnd A) D.1 ((mem_fixSub_iff' A).mpr ((mem_blockSpace A).mp hv).1)
  have h2 : sumOp (actionEnd A) ⊤ v = 0 := ((mem_blockSpace A).mp hv).2
  rw [projBlock_apply_eq, h1, h2, smul_zero, sub_zero, avgCoeff, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

theorem projBlock_idem (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) (v : V) :
    projBlock A hp hpF hA D (projBlock A hp hpF hA D v) = projBlock A hp hpF hA D v :=
  projBlock_apply_of_mem A hp hpF hA D (projBlock_apply_mem A hp hpF hA D v)

theorem projBlock_apply_fixed (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) {c : V} (hc : c ∈ fixedSpaceOf A) :
    projBlock A hp hpF hA D c = 0 := by
  have h1 : sumOp (actionEnd A) D.1 c = ((Fintype.card ↥D.1 : ℕ) : F) • c :=
    sumOp_apply_of_fix (actionEnd A) D.1 ((mem_fixSub_iff' A).mpr fun d _ =>
      (mem_fixedSpaceOf A).mp hc d)
  have h2 : sumOp (actionEnd A) ⊤ c = ((Fintype.card ↥(⊤ : Subgroup ↥A) : ℕ) : F) • c :=
    sumOp_apply_of_fix (actionEnd A) ⊤ ((mem_fixSub_iff' A).mpr fun d _ =>
      (mem_fixedSpaceOf A).mp hc d)
  simp only [projBlock_apply_eq, h1, h2, avgCoeff, smul_smul,
    inv_mul_cancel₀ (natCast_card_subgroup_ne_zero' A hp hpF hA D.1),
    inv_mul_cancel₀ (natCast_card_subgroup_ne_zero' A hp hpF hA ⊤), one_smul, sub_self]

theorem projBlock_apply_of_mem_block (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    {D E : Hyperplane A p} (hDE : E ≠ D) {v : V} (hv : v ∈ blockSpace A E.1) :
    projBlock A hp hpF hA D v = 0 := by
  haveI : IsMulCommutative ↥A := hA.1
  have hcomm : ∀ a ∈ (⊤ : Subgroup ↥A), ∀ b ∈ (⊤ : Subgroup ↥A), a * b = b * a :=
    fun a _ b _ => mul_comm' a b
  have hgen : D.1 ⊔ E.1 = ⊤ := by
    refine HyperBlocks.sup_eq_of_ne_relIndex_prime hp le_top le_top ?_ ?_ ?_
    · rw [Subgroup.relIndex_top_right]; exact D.2
    · rw [Subgroup.relIndex_top_right]; exact E.2
    · intro h
      exact hDE (Subtype.ext h.symm)
  have hzero : sumOp (actionEnd A) D.1 v = 0 :=
    CFSG.LieType.SeitzGeneration.URankThree.sumOp_eq_zero_of_block (actionEnd A)
      (A := (⊤ : Subgroup ↥A)) (natCast_card_top_ne_zero A hp hpF hA) hcomm le_top le_top hgen hv
  have h2 : sumOp (actionEnd A) ⊤ v = 0 := ((mem_blockSpace A).mp hv).2
  rw [projBlock_apply_eq, hzero, h2, smul_zero, smul_zero, sub_self]

theorem projBlock_commute (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) (a : ↥A) :
    actionEnd A a * projBlock A hp hpF hA D = projBlock A hp hpF hA D * actionEnd A a := by
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, projBlock_apply_eq, projBlock_apply_eq,
    map_sub, map_smul, map_smul, actionEnd_sumOp_apply A hA, actionEnd_sumOp_apply A hA]

theorem projBlock_apply_of_commute (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) (a : ↥A) (v : V) :
    projBlock A hp hpF hA D ((a : V ≃ₗ[F] V) v) = (a : V ≃ₗ[F] V) (projBlock A hp hpF hA D v) := by
  have h := congrArg (fun f : Module.End F V => f v) (projBlock_commute A hp hpF hA D a)
  simpa only [Module.End.mul_apply, actionEnd_apply] using h.symm

theorem isCompl_blockSpace_ker (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (D : Hyperplane A p) :
    IsCompl (blockSpace A D.1) (LinearMap.ker (projBlock A hp hpF hA D)) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro v hv
    obtain ⟨hvD, hvk⟩ := Submodule.mem_inf.mp hv
    rw [LinearMap.mem_ker, projBlock_apply_of_mem A hp hpF hA D hvD] at hvk
    exact hvk
  · rw [codisjoint_iff_le_sup]
    intro v _
    have h1 : projBlock A hp hpF hA D v ∈ blockSpace A D.1 := projBlock_apply_mem A hp hpF hA D v
    have h2 : v - projBlock A hp hpF hA D v ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
      rw [LinearMap.mem_ker, LinearMap.map_sub, projBlock_idem, sub_self]
    have hv : v = projBlock A hp hpF hA D v + (v - projBlock A hp hpF hA D v) := by abel
    rw [hv]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

abbrev blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) : V ≃ₗ[F] V :=
  glue (isCompl_blockSpace_ker A hp hpF hA D)
    (restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[F] V)
      (fun u hu => blockSpace_invariant A hp hpF hA hu)
      (fun u hu => blockSpace_invariant A hp hpF hA (a := (t D)⁻¹) hu))
    1

theorem blockEnd_apply_mem (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) {u : V}
    (hu : u ∈ blockSpace A D.1) : blockEnd A hp hpF hA t ht D u = (t D : V ≃ₗ[F] V) u := by
  have h := glue_apply (isCompl_blockSpace_ker A hp hpF hA D)
    (restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[F] V)
      (fun u hu => blockSpace_invariant A hp hpF hA hu)
      (fun u hu => blockSpace_invariant A hp hpF hA (a := (t D)⁻¹) hu)) 1
    (⟨u, hu⟩ : ↥(blockSpace A D.1))
    (⟨0, Submodule.zero_mem _⟩ : ↥(LinearMap.ker (projBlock A hp hpF hA D)))
  simpa using h

theorem blockEnd_apply_of_ker (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) {r : V}
    (hr : r ∈ LinearMap.ker (projBlock A hp hpF hA D)) :
    blockEnd A hp hpF hA t ht D r = r := by
  have h := glue_apply (isCompl_blockSpace_ker A hp hpF hA D)
    (restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[F] V)
      (fun u hu => blockSpace_invariant A hp hpF hA hu)
      (fun u hu => blockSpace_invariant A hp hpF hA (a := (t D)⁻¹) hu)) 1
    (⟨0, Submodule.zero_mem _⟩ : ↥(blockSpace A D.1))
    (⟨r, hr⟩ : ↥(LinearMap.ker (projBlock A hp hpF hA D)))
  simpa using h

theorem blockEnd_apply_fixed (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) {c : V}
    (hc : c ∈ fixedSpaceOf A) : blockEnd A hp hpF hA t ht D c = c :=
  blockEnd_apply_of_ker A hp hpF hA t ht D (by
    rw [LinearMap.mem_ker]; exact projBlock_apply_fixed A hp hpF hA D hc)

theorem blockEnd_apply_of_mem_block (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D E : Hyperplane A p} (hDE : E ≠ D)
    {v : V} (hv : v ∈ blockSpace A E.1) : blockEnd A hp hpF hA t ht D v = v :=
  blockEnd_apply_of_ker A hp hpF hA t ht D (by
    rw [LinearMap.mem_ker]; exact projBlock_apply_of_mem_block A hp hpF hA hDE hv)

theorem blockEnd_pow_apply (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) (n : ℕ) {u r : V}
    (hu : u ∈ blockSpace A D.1) (hr : r ∈ LinearMap.ker (projBlock A hp hpF hA D)) :
    (blockEnd A hp hpF hA t ht D ^ n) (u + r) = ((t D : V ≃ₗ[F] V) ^ n) u + r := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu' : ((t D : V ≃ₗ[F] V) ^ n) u ∈ blockSpace A D.1 :=
      blockSpace_pow_mem A hp hpF hA (t D) hu
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add,
      blockEnd_apply_mem A hp hpF hA t ht D hu',
      blockEnd_apply_of_ker A hp hpF hA t ht D hr,
      pow_succ', LinearEquiv.mul_apply]

theorem blockEnd_pow (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) :
    blockEnd A hp hpF hA t ht D ^ p = 1 := by
  have hpow : ((t D : V ≃ₗ[F] V) ^ p) = 1 := by
    have h := map_pow A.subtype (t D) p
    rw [pow_eq_one A hA (t D), map_one] at h
    exact h.symm
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, r, hcu, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
  rw [blockEnd_pow_apply A hp hpF hA t ht D p u.2 (by rw [LinearMap.mem_ker]; exact r.2), hpow]
  simp

theorem blockEnd_commute (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) (a : ↥A) :
    (a : V ≃ₗ[F] V) * blockEnd A hp hpF hA t ht D =
      blockEnd A hp hpF hA t ht D * (a : V ≃ₗ[F] V) := by
  haveI : IsMulCommutative ↥A := hA.1
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, r, hcu, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
  have hu' : (a : V ≃ₗ[F] V) u ∈ blockSpace A D.1 := blockSpace_invariant A hp hpF hA u.2
  have hr' : (a : V ≃ₗ[F] V) (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    rw [LinearMap.mem_ker, projBlock_apply_of_commute A hp hpF hA D a (r : V),
      LinearMap.mem_ker.mp r.2, map_zero]
  simp only [LinearEquiv.mul_apply, map_add]
  rw [blockEnd_apply_mem A hp hpF hA t ht D u.2,
    blockEnd_apply_of_ker A hp hpF hA t ht D r.2,
    blockEnd_apply_mem A hp hpF hA t ht D hu',
    blockEnd_apply_of_ker A hp hpF hA t ht D hr']
  congr 1
  have h1 : (a * t D : ↥A) = t D * a := mul_comm' a (t D)
  calc (a : V ≃ₗ[F] V) ((t D : V ≃ₗ[F] V) (u : V))
      = ((a : V ≃ₗ[F] V) * (t D : V ≃ₗ[F] V)) (u : V) := (LinearEquiv.mul_apply ..).symm
    _ = (((t D : V ≃ₗ[F] V) * (a : V ≃ₗ[F] V)) (u : V)) := by
        have h2 : (a : V ≃ₗ[F] V) * (t D : V ≃ₗ[F] V) = (((a * t D : ↥A)) : V ≃ₗ[F] V) :=
          (map_mul A.subtype a (t D)).symm
        have h3 : (((a * t D : ↥A)) : V ≃ₗ[F] V) = (((t D * a : ↥A)) : V ≃ₗ[F] V) := by rw [h1]
        have h4 : (((t D * a : ↥A)) : V ≃ₗ[F] V) = (t D : V ≃ₗ[F] V) * (a : V ≃ₗ[F] V) :=
          map_mul A.subtype (t D) a
        rw [h2, h3, h4]
    _ = (t D : V ≃ₗ[F] V) ((a : V ≃ₗ[F] V) (u : V)) := LinearEquiv.mul_apply ..

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks



