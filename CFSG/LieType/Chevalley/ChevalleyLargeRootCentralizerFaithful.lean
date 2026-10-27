module

public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem Chevalley_large_finite_root_centralizer_faithfulness
    (τ : Tag) (K : Type) [Field K]
    [Finite K] (hK : (if τ = .G2 then 3 else 2) < Nat.card K) (L : Type) [Field L]
    (ι : K →+* L) :
    Function.Injective (baseChangeGL (τ := τ) ι) ∧
    (adjointGroup τ K).map (baseChangeGL ι) ≤ adjointGroup τ L ∧
    (∀ z ∈ adjointGroup τ L, (∀ h ∈ (adjointGroup τ K).map (baseChangeGL ι), z * h = h * z) →
      z = 1) ∧
    Function.Injective (conjNormalizerHom (adjointGroup τ L)
      ((adjointGroup τ K).map (baseChangeGL ι))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set H := (adjointGroup τ K).map (baseChangeGL ι)
  have hHle : H ≤ adjointGroup τ L := by
    rintro _ ⟨g, hg, rfl⟩
    exact baseChangeGL_mem_adjointGroup ι hg
  have hD : entryDegreeBound τ < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hgen : ∀ z ∈ adjointGroup τ L,
      (∀ (i : Fin τ.rank) (t : L), (z : Module.End L (RootModule τ L)) * xOp τ L i t =
        xOp τ L i t * z ∧ (z : Module.End L (RootModule τ L)) * yOp τ L i t =
          yOp τ L i t * z) → z = 1 := by
    intro z hzC hzg
    have hcent : ⟨z, hzC⟩ ∈ Subgroup.center (adjointGroup τ L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hle : adjointGroup τ L ≤ Subgroup.centralizer {z} := by
        rw [adjointGroup, Subgroup.closure_le]
        rintro g ⟨i, c, hg | hg⟩ <;>
          refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_) <;>
          rw [Units.val_mul, Units.val_mul, hg]
        · exact (hzg i c).1.symm
        · exact (hzg i c).2.symm
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have hcentralizer : ∀ z ∈ adjointGroup τ L, (∀ h ∈ H, z * h = h * z) → z = 1 := by
    intro z hzC hz
    have hx : ∀ (i : Fin τ.rank) (c : K), (z : Module.End L (RootModule τ L)) *
        xOp τ L i (ι c) = xOp τ L i (ι c) * z := fun i c => by
      have h1 := hz _ ⟨xUnit τ K i c, xUnit_mem_adjointGroup i c, rfl⟩
      rw [baseChangeGL_xUnit] at h1
      exact congrArg Units.val h1
    have hy : ∀ (i : Fin τ.rank) (c : K), (z : Module.End L (RootModule τ L)) *
        yOp τ L i (ι c) = yOp τ L i (ι c) * z := fun i c => by
      have h1 := hz _ ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c, rfl⟩
      rw [baseChangeGL_yUnit] at h1
      exact congrArg Units.val h1
    refine hgen z hzC fun i t => ⟨?_, ?_⟩
    · refine commute_of_polynomial_entries (F := xOp τ L i) (fun a b => ?_) _ ι ι.injective hD
        (fun c => hx i c) t
      obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) τ i a b
      exact ⟨p, hp, fun c => (hpq c).1⟩
    · refine commute_of_polynomial_entries (F := yOp τ L i) (fun a b => ?_) _ ι ι.injective hD
        (fun c => hy i c) t
      obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) τ i a b
      exact ⟨q, hq, fun c => (hpq c).2⟩
  refine ⟨baseChangeGL_injective ι, hHle, hcentralizer, ?_⟩
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  apply Subtype.ext
  refine hcentralizer g (Subgroup.mem_inf.1 g.2).1 fun h hh => ?_
  have h1 := congrArg (fun φ : MulAut H => ((φ ⟨h, hh⟩ : H) : ModGL τ L)) hg
  simp only [conjNormalizerHom_apply, MulAut.one_apply] at h1
  calc (g : ModGL τ L) * h = (g * h * (g : ModGL τ L)⁻¹) * g := by group
    _ = h * g := by rw [h1]

theorem Chevalley_large_finite_root_centralizer_faithfulness_of_four_le
    (τ : Tag) (K : Type)
    [Field K] [Finite K] (hK : 4 ≤ Nat.card K) (L : Type) [Field L] (ι : K →+* L) :
    Function.Injective (baseChangeGL (τ := τ) ι) ∧
    (adjointGroup τ K).map (baseChangeGL ι) ≤ adjointGroup τ L ∧
    (∀ z ∈ adjointGroup τ L, (∀ h ∈ (adjointGroup τ K).map (baseChangeGL ι), z * h = h * z) →
      z = 1) ∧
    Function.Injective (conjNormalizerHom (adjointGroup τ L)
      ((adjointGroup τ K).map (baseChangeGL ι))) := by
  refine Chevalley_large_finite_root_centralizer_faithfulness τ K ?_ L ι
  split_ifs <;> omega

end CFSG.LieType.Chevalley
