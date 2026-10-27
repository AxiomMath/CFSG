module

public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section MatrixInner

variable (τ : Tag) (K L : Type) [Field K] [Field L] [Algebra K L]

@[expose] def matrixInner : Subgroup (MulAut (adjointGroup τ K)) where
  carrier := {α | ∃ y : ModGL τ L, ∀ u : adjointGroup τ K,
    baseChangeGL (algebraMap K L) (α u : ModGL τ K) =
      y * baseChangeGL (algebraMap K L) (u : ModGL τ K) * y⁻¹}
  mul_mem' := by
    rintro α β ⟨y, hy⟩ ⟨z, hz⟩
    refine ⟨y * z, fun u => ?_⟩
    rw [MulAut.mul_apply, hy, hz]
    group
  one_mem' := ⟨1, fun u => by simp⟩
  inv_mem' := by
    rintro α ⟨y, hy⟩
    refine ⟨y⁻¹, fun u => ?_⟩
    have h := hy (α⁻¹ u)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group

variable {τ K L}

theorem eq_one_of_mem_matrixInner_of_fix_subfield [Finite K] (k : Subfield K)
    (hk : entryDegreeBound τ < Nat.card k) {ι : MulAut (adjointGroup τ K)}
    (hι : ι ∈ matrixInner τ K L)
    (hfix : ∀ x : adjointGroup τ K,
      (x : ModGL τ K) ∈ (adjointGroup τ k).map (baseChangeGL k.subtype) → ι x = x) : ι = 1 := by
  classical
  obtain ⟨y, hy⟩ := hι
  have : Fintype k := Fintype.ofFinite k
  have hD : entryDegreeBound τ < Fintype.card k := by
    rw [← Nat.card_eq_fintype_card]
    exact hk
  have hinj : Function.Injective (fun c : k => algebraMap K L (c : K)) := fun c d h =>
    Subtype.ext ((algebraMap K L).injective h)
  have hcomm : ∀ (g : ModGL τ k) (hg : g ∈ adjointGroup τ k),
      y * baseChangeGL (algebraMap K L) (baseChangeGL k.subtype g) =
        baseChangeGL (algebraMap K L) (baseChangeGL k.subtype g) * y := by
    intro g hg
    have hmem : (baseChangeGL k.subtype g : ModGL τ K) ∈ adjointGroup τ K :=
      baseChangeGL_mem_adjointGroup k.subtype hg
    have h1 := hfix ⟨_, hmem⟩ ⟨g, hg, rfl⟩
    have h2 := hy ⟨_, hmem⟩
    rw [h1] at h2
    have h3 : (baseChangeGL (algebraMap K L) (baseChangeGL k.subtype g) : ModGL τ L) =
        y * baseChangeGL (algebraMap K L) (baseChangeGL k.subtype g) * y⁻¹ := h2
    calc y * baseChangeGL (algebraMap K L) (baseChangeGL k.subtype g) =
        (y * baseChangeGL (algebraMap K L) (baseChangeGL k.subtype g) * y⁻¹) * y := by group
      _ = _ := by rw [← h3]
  have hx : ∀ (i : Fin τ.rank) (c : k), (y : Module.End L (RootModule τ L)) *
      xOp τ L i (algebraMap K L (c : K)) =
        xOp τ L i (algebraMap K L (c : K)) * (y : Module.End L (RootModule τ L)) := fun i c => by
    have h1 := hcomm (xUnit τ k i c) (xUnit_mem_adjointGroup i c)
    rw [baseChangeGL_xUnit, baseChangeGL_xUnit] at h1
    exact congrArg Units.val h1
  have hy' : ∀ (i : Fin τ.rank) (c : k), (y : Module.End L (RootModule τ L)) *
      yOp τ L i (algebraMap K L (c : K)) =
        yOp τ L i (algebraMap K L (c : K)) * (y : Module.End L (RootModule τ L)) := fun i c => by
    have h1 := hcomm (yUnit τ k i c) (yUnit_mem_adjointGroup i c)
    rw [baseChangeGL_yUnit, baseChangeGL_yUnit] at h1
    exact congrArg Units.val h1
  have hgen : ∀ (i : Fin τ.rank) (t : L),
      (y : Module.End L (RootModule τ L)) * xOp τ L i t = xOp τ L i t * (y : Module.End L _) ∧
      (y : Module.End L (RootModule τ L)) * yOp τ L i t = yOp τ L i t * (y : Module.End L _) := by
    intro i t
    refine ⟨?_, ?_⟩
    · refine commute_of_polynomial_entries (F := xOp τ L i) (fun a b => ?_) _
        (fun c : k => algebraMap K L (c : K)) hinj hD (fun c => hx i c) t
      obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) τ i a b
      exact ⟨p, hp, fun c => (hpq c).1⟩
    · refine commute_of_polynomial_entries (F := yOp τ L i) (fun a b => ?_) _
        (fun c : k => algebraMap K L (c : K)) hinj hD (fun c => hy' i c) t
      obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) τ i a b
      exact ⟨q, hq, fun c => (hpq c).2⟩
  have hle : adjointGroup τ L ≤ Subgroup.centralizer {y} := by
    rw [adjointGroup, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩ <;>
      refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_) <;>
      rw [Units.val_mul, Units.val_mul, hg]
    · exact (hgen i c).1.symm
    · exact (hgen i c).2.symm
  refine MulEquiv.ext fun u => ?_
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K L)
  have h3 := Subgroup.mem_centralizer_singleton_iff.1
    (hle (baseChangeGL_mem_adjointGroup (algebraMap K L) u.2))
  rw [MulAut.one_apply, hy u]
  calc y * baseChangeGL (algebraMap K L) (u : ModGL τ K) * y⁻¹ =
      baseChangeGL (algebraMap K L) (u : ModGL τ K) * y * y⁻¹ := by rw [← h3]
    _ = _ := by group

end MatrixInner

end CFSG.LieType.SeitzGeneration.ExcWideThree
