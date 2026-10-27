module

public import CFSG.ClassicalInvolution.Q3.Q3ZASym

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Q3.Q3Z
open scoped MatrixGroups commutatorElement

theorem swap_mul_lb1 (x : SL(2, F3)) :
    swapElt * longBlock F3 2 1 x * swapElt⁻¹ = longBlock F3 2 0 x := by
  have h := swap_mul_lb x
  rw [swapElt_inv]
  calc swapElt * longBlock F3 2 1 x * swapElt = swapElt * (longBlock F3 2 1 x * swapElt) := by
        rw [mul_assoc]
    _ = swapElt * (swapElt * longBlock F3 2 0 x) := by rw [h]
    _ = longBlock F3 2 0 x := by rw [← mul_assoc, swapElt_mul_self, one_mul]

section Frame

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} (fr : C3Frame G Ω)

@[expose] noncomputable def frameSw : G := fr.Θ₀₁ swapElt

theorem frameSw_mul_self : frameSw fr * frameSw fr = 1 := by
  rw [frameSw, ← map_mul, swapElt_mul_self, map_one]

theorem frameSw_mem_range : frameSw fr ∈ fr.Θ₀₁.range := ⟨swapElt, rfl⟩

theorem frameSw_conj (x : StatedSp 2 F3) :
    frameSw fr * fr.Θ₀₁ x * (frameSw fr)⁻¹ = fr.Θ₀₁ (swapElt * x * swapElt⁻¹) := by
  simp only [frameSw, map_mul, map_inv]

theorem frameSw_conj_lb1 (x : SL(2, F3)) :
    frameSw fr * fr.Θ₀₁ (longBlock F3 2 1 x) * (frameSw fr)⁻¹ = fr.Θ₀₁ (longBlock F3 2 0 x) := by
  rw [frameSw_conj, swap_mul_lb1]

theorem frame_lb0_mem_K₀ (x : SL(2, F3)) : fr.Θ₀₁ (longBlock F3 2 0 x) ∈ fr.K₀ := by
  rw [← fr.blk₀₁₀]
  exact ⟨_, mem_planeGroup_lb 0 x, rfl⟩

theorem frame_lb1_mem_K₂ (x : SL(2, F3)) : fr.Θ₁₂ (longBlock F3 2 1 x) ∈ fr.K₂ := by
  rw [← fr.blk₁₂₁]
  exact ⟨_, mem_planeGroup_lb 1 x, rfl⟩

@[expose] noncomputable def SymTri.ofFrame (h₀ : fr.K₀ ∈ Ω) (h₁ : fr.K₁ ∈ Ω)
    (hhub : ∀ x : SL(2, F3), fr.Θ₁₂ (longBlock F3 2 0 x) = fr.Θ₀₁ (longBlock F3 2 1 x)) :
    SymTri G Ω where
  K₀ := fr.K₀
  K₁ := fr.K₁
  K₂ := fr.K₂
  Θ₀₁ := fr.Θ₀₁
  Θ₀₂ := (MulAut.conj (frameSw fr)).toMonoidHom.comp fr.Θ₁₂
  inj₀₁ := fr.inj₀₁
  inj₀₂ := (MulAut.conj (frameSw fr)).injective.comp fr.inj₁₂
  mem₀ := h₀
  mem₁ := h₁
  mem₂ := fr.hK₂
  blk₀₁₀ := fr.blk₀₁₀
  blk₀₁₁ := fr.blk₀₁₁
  blk₀₂₀ := by
    rw [← fr.blk₀₁₀, planeGroup_stdPlane]
    show (longBlock F3 2 0).range.map ((MulAut.conj (frameSw fr)).toMonoidHom.comp fr.Θ₁₂) =
      (longBlock F3 2 0).range.map fr.Θ₀₁
    rw [MonoidHom.map_range, MonoidHom.map_range]
    congr 1
    refine MonoidHom.ext fun x => ?_
    show frameSw fr * fr.Θ₁₂ (longBlock F3 2 0 x) * (frameSw fr)⁻¹ = fr.Θ₀₁ (longBlock F3 2 0 x)
    rw [hhub, frameSw_conj_lb1]
  blk₀₂₁ := by
    rw [← fr.blk₁₂₁, planeGroup_stdPlane]
    show (longBlock F3 2 1).range.map ((MulAut.conj (frameSw fr)).toMonoidHom.comp fr.Θ₁₂) =
      (longBlock F3 2 1).range.map fr.Θ₁₂
    rw [MonoidHom.map_range, MonoidHom.map_range]
    congr 1
    refine MonoidHom.ext fun x => ?_
    show frameSw fr * fr.Θ₁₂ (longBlock F3 2 1 x) * (frameSw fr)⁻¹ = fr.Θ₁₂ (longBlock F3 2 1 x)
    rw [fr.comm₀₁ (frameSw fr) (frameSw_mem_range fr) _ (frame_lb1_mem_K₂ fr x), mul_assoc,
      mul_inv_cancel, mul_one]
  comm₀₁ := fr.comm₀₁
  comm₀₂ := by
    rintro _ ⟨x, rfl⟩ b hb
    have hb' : frameSw fr * b * (frameSw fr)⁻¹ ∈ fr.K₀ := by
      rw [← fr.blk₀₁₁] at hb
      obtain ⟨y, hy, rfl⟩ := hb
      rw [planeGroup_stdPlane] at hy
      obtain ⟨c, rfl⟩ := hy
      rw [frameSw_conj_lb1]
      exact frame_lb0_mem_K₀ fr c
    have hc := fr.comm₁₂ (fr.Θ₁₂ x) ⟨x, rfl⟩ _ hb'
    have hss : ∀ a : G, frameSw fr * (frameSw fr * a * (frameSw fr)⁻¹) * (frameSw fr)⁻¹ = a := by
      intro a
      calc frameSw fr * (frameSw fr * a * (frameSw fr)⁻¹) * (frameSw fr)⁻¹
          = (frameSw fr * frameSw fr) * a * (frameSw fr * frameSw fr)⁻¹ := by group
        _ = a := by rw [frameSw_mul_self]; group
    have hmul : ∀ u v : G, frameSw fr * (u * v) * (frameSw fr)⁻¹ =
        (frameSw fr * u * (frameSw fr)⁻¹) * (frameSw fr * v * (frameSw fr)⁻¹) := fun u v => by
      group
    refine (MulAut.conj (frameSw fr)).injective ?_
    show frameSw fr * ((frameSw fr * fr.Θ₁₂ x * (frameSw fr)⁻¹) * b) * (frameSw fr)⁻¹ =
      frameSw fr * (b * (frameSw fr * fr.Θ₁₂ x * (frameSw fr)⁻¹)) * (frameSw fr)⁻¹
    rw [hmul (frameSw fr * fr.Θ₁₂ x * (frameSw fr)⁻¹) b,
      hmul b (frameSw fr * fr.Θ₁₂ x * (frameSw fr)⁻¹), hss]
    exact hc
  matched x := by
    show frameSw fr * fr.Θ₁₂ (longBlock F3 2 0 x) * (frameSw fr)⁻¹ = fr.Θ₀₁ (longBlock F3 2 0 x)
    rw [hhub, frameSw_conj_lb1]

end Frame

end CFSG.ClassicalInvolution.Q3.Q3ZA
