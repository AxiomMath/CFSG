module

public import CFSG.ClassicalInvolution.Q3.Q3ZFraFrame
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLevi

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

section Layers

variable {F : Type} [Field F] {n : ℕ} {i j : Fin n}

@[expose] noncomputable def layerEmbed (F : Type) [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    StatedSp 2 F →* StatedSp n F :=
  spEmbed (pairMap i j) (pairMap_injective hij)

theorem layerEmbed_injective (hij : i ≠ j) : Function.Injective (layerEmbed F hij) :=
  spEmbed_injective _

theorem map_longBlock_range_layerEmbed (hij : i ≠ j) (k : Fin 2) :
    (longBlock F 2 k).range.map (layerEmbed F hij) =
      (longBlock F n (pairMap i j k)).range := by
  have h : (layerEmbed F hij).comp (longBlock F 2 k) = longBlock F n (pairMap i j k) :=
    MonoidHom.ext fun A => spEmbed_longBlock (pairMap_injective hij) k A
  rw [← MonoidHom.range_comp, h]

theorem map_planeGroup_layerEmbed_zero (hij : i ≠ j) :
    (planeGroup (stdPlane F 2 0)).map (layerEmbed F hij) = (longBlock F n i).range := by
  rw [planeGroup_stdPlane]
  exact map_longBlock_range_layerEmbed hij 0

theorem map_planeGroup_layerEmbed_one (hij : i ≠ j) :
    (planeGroup (stdPlane F 2 1)).map (layerEmbed F hij) = (longBlock F n j).range := by
  rw [planeGroup_stdPlane]
  exact map_longBlock_range_layerEmbed hij 1

theorem layerEmbed_comm_longBlock (hij : i ≠ j) {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    ∀ a ∈ (layerEmbed F hij).range, ∀ b ∈ (longBlock F n k).range, a * b = b * a := by
  intro a ha b hb
  have hsub : coords k ⊆ (coords i ∪ coords j)ᶜ := by
    intro t ht hmem
    rcases mem_coords.1 ht with rfl | rfl
    · rcases inl_mem_union_iff.1 hmem with h | h
      · exact hki h
      · exact hkj h
    · rcases inr_mem_union_iff.1 hmem with h | h
      · exact hki h
      · exact hkj h
  have ha' : a ∈ suppGroup (coords i ∪ coords j) := by
    rw [layerEmbed, range_spEmbed (pairMap_injective hij), range_pairMap] at ha
    exact ha
  have hb' : b ∈ suppGroup (coords i ∪ coords j)ᶜ := by
    rw [range_longBlock] at hb
    exact suppGroup_mono hsub hb
  exact (commute_suppGroup_compl ha' hb').eq

theorem map_shortBlock_range_layerEmbed (hij : i ≠ j) :
    (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (layerEmbed F hij) =
      (shortBlock F hij).range := by
  rw [← MonoidHom.range_comp, layerEmbed, spEmbed_comp_shortBlock hij]

end Layers

section Std

@[expose] noncomputable def stdFrame (Ω : Set (Subgroup (StatedSp 3 (GaloisField 3 1))))
    (hΩ : (longBlock (GaloisField 3 1) 3 2).range ∈ Ω) :
    C3Frame (StatedSp 3 (GaloisField 3 1)) Ω where
  K₀ := (longBlock (GaloisField 3 1) 3 0).range
  K₁ := (longBlock (GaloisField 3 1) 3 1).range
  K₂ := (longBlock (GaloisField 3 1) 3 2).range
  Θ₀₁ := layerEmbed (GaloisField 3 1) (show (0 : Fin 3) ≠ 1 by decide)
  Θ₁₂ := layerEmbed (GaloisField 3 1) (show (1 : Fin 3) ≠ 2 by decide)
  inj₀₁ := layerEmbed_injective _
  inj₁₂ := layerEmbed_injective _
  hK₂ := hΩ
  blk₀₁₀ := map_planeGroup_layerEmbed_zero _
  blk₀₁₁ := map_planeGroup_layerEmbed_one _
  blk₁₂₀ := map_planeGroup_layerEmbed_zero _
  blk₁₂₁ := map_planeGroup_layerEmbed_one _
  comm₀₁ := layerEmbed_comm_longBlock _ (by decide) (by decide)
  comm₁₂ := layerEmbed_comm_longBlock (show (1 : Fin 3) ≠ 2 by decide) (k := 0) (by decide)
    (by decide)

theorem stdFrame_shortNodes (Ω : Set (Subgroup (StatedSp 3 (GaloisField 3 1))))
    (hΩ : (longBlock (GaloisField 3 1) 3 2).range ∈ Ω) :
    (shortBlock (GaloisField 3 1) (show (0 : Fin 3) ≠ 1 by decide)).range ∈
        shortNodes (stdFrame Ω hΩ).Θ₀₁ ∧
      (shortBlock (GaloisField 3 1) (show (1 : Fin 3) ≠ 2 by decide)).range ∈
        shortNodes (stdFrame Ω hΩ).Θ₁₂ :=
  ⟨⟨_, shortBlock_range_mem_adaptedShort, (map_shortBlock_range_layerEmbed _).symm⟩,
   ⟨_, shortBlock_range_mem_adaptedShort, (map_shortBlock_range_layerEmbed _).symm⟩⟩

theorem stdFrame_a2 (Ω : Set (Subgroup (StatedSp 3 (GaloisField 3 1))))
    (hΩ : (longBlock (GaloisField 3 1) 3 2).range ∈ Ω) :
    ∃ T₀ ∈ shortNodes (stdFrame Ω hΩ).Θ₀₁, ∃ T₁ ∈ shortNodes (stdFrame Ω hΩ).Θ₁₂,
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W T₀ T₁ :=
  ⟨_, (stdFrame_shortNodes Ω hΩ).1, _, (stdFrame_shortNodes Ω hΩ).2, _,
    linearBlockStandardPair_shortBlock (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide)⟩

theorem stdFrame_chain (Ω : Set (Subgroup (StatedSp 3 (GaloisField 3 1))))
    (hΩ : (longBlock (GaloisField 3 1) 3 2).range ∈ Ω) :
    ∃ U : Fin 3 → Subgroup (StatedSp 3 (GaloisField 3 1)), U 2 ∈ Ω ∧
      (∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a) ∧
      (∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1)) ∧
      (∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U 2) (U 1)) := by
  obtain ⟨T₀, h₀, T₁, h₁, hA⟩ := stdFrame_a2 Ω hΩ
  exact chain_of_frame (stdFrame Ω hΩ) h₀ h₁ hA

end Std

end CFSG.ClassicalInvolution.Q3.Q3Z
