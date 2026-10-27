module

public import CFSG.LargeExtraspecial.DW2ModRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {f : LinearMap.BilinForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem orth_sup (A B : Submodule (ZMod 2) V) :
    f.orthogonal (A ⊔ B) = f.orthogonal A ⊓ f.orthogonal B := by
  ext v
  simp only [mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨fun a ha => h a (mem_sup_left ha), fun b hb => h b (mem_sup_right hb)⟩
  · rintro ⟨hA, hB⟩ w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hw
    rw [map_add, LinearMap.add_apply, hA a ha, hB b hb, add_zero]

theorem orth_inf (hf : f.Nondegenerate) (A B : Submodule (ZMod 2) V) :
    f.orthogonal (A ⊓ B) = f.orthogonal A ⊔ f.orthogonal B := by
  have hle : f.orthogonal A ⊔ f.orthogonal B ≤ f.orthogonal (A ⊓ B) :=
    sup_le (LinearMap.BilinForm.orthogonal_le inf_le_left)
      (LinearMap.BilinForm.orthogonal_le inf_le_right)
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (f.orthogonal A) (f.orthogonal B)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [← orth_sup, LinearMap.BilinForm.finrank_orthogonal hf,
    LinearMap.BilinForm.finrank_orthogonal hf, LinearMap.BilinForm.finrank_orthogonal hf] at h1
  rw [LinearMap.BilinForm.finrank_orthogonal hf]
  have h3 := Submodule.finrank_le A
  have h4 := Submodule.finrank_le B
  have h5 := Submodule.finrank_le (A ⊔ B)
  omega

variable {Y : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem exists_minimal {R U : Submodule (ZMod 2) V}
    (hne : ∃ W, IsInv Y W ∧ R < W ∧ W ≤ U) :
    ∃ F, IsInv Y F ∧ R < F ∧ F ≤ U ∧ ∀ W, IsInv Y W → R < W → W ≤ F → W = F := by
  obtain ⟨F, ⟨hF, hRF, hFU⟩, hmin⟩ :=
    (measure fun W : Submodule (ZMod 2) V => finrank (ZMod 2) W).wf.has_min
      {W | IsInv Y W ∧ R < W ∧ W ≤ U} hne
  refine ⟨F, hF, hRF, hFU, fun W hW hRW hWF => ?_⟩
  by_contra hne'
  exact hmin W ⟨hW, hRW, hWF.trans hFU⟩
    (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hWF hne'))

omit [FiniteDimensional (ZMod 2) V] in
theorem forall_sub_mem_of_forall {D : Set (V ≃ₗ[ZMod 2] V)} (hgen : Y = Subgroup.closure D)
    {A B : Submodule (ZMod 2) V} (hB : IsInv Y B) (h : ∀ d ∈ D, ∀ b ∈ B, d b - b ∈ A) :
    ∀ y ∈ Y, ∀ b ∈ B, y b - b ∈ A := by
  have hDY : ∀ t ∈ D, t ∈ Y := fun t ht => hgen ▸ Subgroup.subset_closure ht
  have hle : Y ≤ secCent A B := by
    rw [hgen, Subgroup.closure_le]
    exact fun t ht => mem_secCent_of_isInv hB (hDY t ht) (h t ht)
  exact fun y hy => (hle hy).2.2

theorem forall_sub_mem_of_secRank_eq_zero {D : Set (V ≃ₗ[ZMod 2] V)}
    (hgen : Y = Subgroup.closure D) {A B : Submodule (ZMod 2) V} (hB : IsInv Y B)
    (h : ∀ d ∈ D, secRank d A B = 0) : ∀ y ∈ Y, ∀ b ∈ B, y b - b ∈ A :=
  forall_sub_mem_of_forall hgen hB fun d hd => secRank_eq_zero_iff.mp (h d hd)

section Pair

variable (hr : f.IsRefl) (hY : Y ≤ TauCeti.BilinForm.isometryGroup f)
  {R F U : Submodule (ZMod 2) V}
include hr hY

omit [FiniteDimensional (ZMod 2) V] in
theorem sub_mem_inf_orth_of_forall (hU : IsInv Y U) (hRU : R ≤ f.orthogonal U)
    {y : V ≃ₗ[ZMod 2] V} (hy : y ∈ Y) (h : ∀ w ∈ F, y⁻¹ w - w ∈ R) :
    ∀ u ∈ U, y u - u ∈ U ⊓ f.orthogonal F := by
  intro u hu
  refine ⟨sub_mem (hU y hy u hu) hu, LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw =>
    hr _ _ ?_⟩
  rw [apply_sub_eq hY hy]
  exact LinearMap.BilinForm.mem_orthogonal_iff.mp (hRU (h w hw)) u hu

omit [FiniteDimensional (ZMod 2) V] in
theorem inv_sub_mem_of_forall (hF : IsInv Y F) (hFR : F ⊓ f.orthogonal U ≤ R)
    {y : V ≃ₗ[ZMod 2] V} (hy : y ∈ Y) (h : ∀ u ∈ U, y u - u ∈ f.orthogonal F) :
    ∀ w ∈ F, y⁻¹ w - w ∈ R := by
  intro w hw
  refine hFR ⟨sub_mem (hF.inv_apply_mem hy hw) hw,
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => ?_⟩
  rw [← apply_sub_eq hY hy]
  exact hr _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp (h u hu) w hw)

end Pair

end CFSG.LargeExtraspecial.DW
