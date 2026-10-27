module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedMat spEmbedGL spEmbedMat_apply_image
  spEmbedMat_apply_of_not_mem leviEmbedGL leviEmbedSL)
open CFSG.SeitzReduction.SymplecticPilot (planeEnum planeEnum_injective range_planeEnum)
open scoped MatrixGroups

section Four

variable {F : Type} [Field F]

theorem coe_leviEmbedSL (A : SL(2, F)) :
    (((leviEmbedSL F 2 A : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks (A : Matrix (Fin 2) (Fin 2) F) 0 0
        ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  change (((leviEmbedGL F 2 (Matrix.SpecialLinearGroup.toGL A) : StatedSp 2 F) :
    GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
  rw [coe_leviEmbedGL, ← map_inv]
  rfl

theorem commute_leviEmbedSL_two_flip (A B : SL(2, F)) (j : Fin 2) :
    Commute ((leviEmbedSL F 2 A : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)
      (flipGL F {j} * ((leviEmbedSL F 2 B : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
        (flipGL F {j})⁻¹) := by
  show _ * _ = _ * _
  apply Units.ext
  set y := flipGL F {j} * ((leviEmbedSL F 2 B : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
    (flipGL F {j})⁻¹ with hy
  have hyent : ∀ a c, (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) a c =
      (((leviEmbedSL F 2 B : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (flipPerm {j} a) (flipPerm {j} c) :=
    fun a c => flipGL_conj_apply _ _ a c
  clear_value y
  rw [Units.val_mul, Units.val_mul]
  ext a c
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hyent,
    coe_leviEmbedSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases j <;> rcases a with a | a <;> rcases c with c | c <;> fin_cases a <;> fin_cases c <;>
    simp [flipPerm_apply, flipPermFun, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.of_apply] <;> ring

theorem commute_omegaLeviSL_flip {k : ℕ} (hk : k = 2) {X Y : GL (Fin k ⊕ Fin k) F}
    (hX : X ∈ omegaLeviSL F k) (hY : Y ∈ omegaLeviSL F k) (j : Fin k) :
    Commute X (flipGL F {j} * Y * (flipGL F {j})⁻¹) := by
  subst hk
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hX
  obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hY
  exact commute_leviEmbedSL_two_flip A B j

end Four

section Embed

variable {F : Type} [Field F] {k m : ℕ}

@[expose] def preFlip (σ : Fin k → Fin m) (P : Finset (Fin m)) : Finset (Fin k) :=
  Finset.univ.filter fun l => σ l ∈ P

theorem mem_preFlip {σ : Fin k → Fin m} {P : Finset (Fin m)} {l : Fin k} :
    l ∈ preFlip σ P ↔ σ l ∈ P := by
  simp [preFlip]

theorem flipPerm_sumMap (σ : Fin k → Fin m) (P : Finset (Fin m)) (x : Fin k ⊕ Fin k) :
    flipPerm P (Sum.map σ σ x) = Sum.map σ σ (flipPerm (preFlip σ P) x) := by
  rcases x with l | l <;> by_cases h : σ l ∈ P <;>
    simp [flipPerm_apply, flipPermFun, mem_preFlip, h]

theorem flipPerm_mem_range_sumMap_iff (σ : Fin k → Fin m) (P : Finset (Fin m))
    (a : Fin m ⊕ Fin m) :
    flipPerm P a ∈ Set.range (Sum.map σ σ) ↔ a ∈ Set.range (Sum.map σ σ) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨flipPerm (preFlip σ P) x, ?_⟩
    rw [← flipPerm_sumMap, hx, flipPerm_apply, flipPerm_apply, flipPermFun_flipPermFun]
  · rintro ⟨x, rfl⟩
    exact ⟨flipPerm (preFlip σ P) x, (flipPerm_sumMap σ P x).symm⟩

theorem flipGL_conj_spEmbedGL {σ : Fin k → Fin m} (hσ : Function.Injective σ)
    (P : Finset (Fin m)) (X : GL (Fin k ⊕ Fin k) F) :
    flipGL F P * spEmbedGL σ hσ X * (flipGL F P)⁻¹ =
      spEmbedGL σ hσ (flipGL F (preFlip σ P) * X * (flipGL F (preFlip σ P))⁻¹) := by
  apply Units.ext
  ext a b
  rw [flipGL_conj_apply]
  change spEmbedMat σ (X : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) (flipPerm P a)
      (flipPerm P b) =
    spEmbedMat σ ((flipGL F (preFlip σ P) * X * (flipGL F (preFlip σ P))⁻¹ :
      GL (Fin k ⊕ Fin k) F) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) a b
  by_cases h : a ∈ Set.range (Sum.map σ σ) ∧ b ∈ Set.range (Sum.map σ σ)
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    rw [flipPerm_sumMap, flipPerm_sumMap, spEmbedMat_apply_image hσ, spEmbedMat_apply_image hσ,
      flipGL_conj_apply]
  · have h' : ¬(flipPerm P a ∈ Set.range (Sum.map σ σ) ∧
        flipPerm P b ∈ Set.range (Sum.map σ σ)) := by
      rwa [flipPerm_mem_range_sumMap_iff, flipPerm_mem_range_sumMap_iff]
    rw [spEmbedMat_apply_of_not_mem _ h', spEmbedMat_apply_of_not_mem _ h]
    simp only [Matrix.one_apply, (flipPerm P).injective.eq_iff]

end Embed

section Siegel

variable {F : Type} [Field F] [Finite F] {m : ℕ}

theorem preFlip_planeEnum_eq_singleton {B P : Finset (Fin m)} {b : Fin m} (hPB : B ∩ P = {b}) :
    ∃ j : Fin B.card, preFlip (planeEnum B) P = {j} := by
  have hbBP : b ∈ B ∩ P := hPB ▸ Finset.mem_singleton_self b
  have hbr : b ∈ Set.range (planeEnum B) := by
    rw [range_planeEnum]
    exact Finset.mem_coe.2 (Finset.mem_inter.1 hbBP).1
  obtain ⟨j, hj⟩ := hbr
  refine ⟨j, ?_⟩
  ext l
  rw [mem_preFlip, Finset.mem_singleton]
  constructor
  · intro hl
    have hlB : planeEnum B l ∈ B := by
      have h1 : planeEnum B l ∈ Set.range (planeEnum B) := ⟨l, rfl⟩
      rw [range_planeEnum] at h1
      exact Finset.mem_coe.1 h1
    have h2 : planeEnum B l ∈ B ∩ P := Finset.mem_inter.2 ⟨hlB, hl⟩
    rw [hPB, Finset.mem_singleton, ← hj] at h2
    exact planeEnum_injective B h2
  · rintro rfl
    rw [hj]
    exact (Finset.mem_inter.1 hbBP).2

theorem commute_siegelBlockGL_flip (hF : 4 ≤ Nat.card F) {B P : Finset (Fin m)}
    (hB : B.card = 2) {b : Fin m} (hPB : B ∩ P = {b}) {x y : GL (Fin m ⊕ Fin m) F}
    (hx : x ∈ siegelBlockGL F B)
    (hy : y ∈ (siegelBlockGL F B).map (MulAut.conj (flipGL F P)).toMonoidHom) :
    Commute x y := by
  rw [siegelBlockGL_eq_map_omegaLeviSL hF hB.ge] at hx hy
  obtain ⟨X, hX, rfl⟩ := hx
  obtain ⟨_, ⟨Y, hY, rfl⟩, rfl⟩ := hy
  obtain ⟨j, hj⟩ := preFlip_planeEnum_eq_singleton hPB
  have h := commute_omegaLeviSL_flip hB hX hY j
  change Commute (spEmbedGL (planeEnum B) (planeEnum_injective B) X)
    (flipGL F P * spEmbedGL (planeEnum B) (planeEnum_injective B) Y * (flipGL F P)⁻¹)
  rw [flipGL_conj_spEmbedGL, hj]
  exact h.map (spEmbedGL (planeEnum B) (planeEnum_injective B))

end Siegel

section Fork

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {m : ℕ}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)} {ι : K →+* F}

theorem plusNode_fork_le_centralizer (hm : 2 ≤ m) (C : PlusFieldCover e ι 0)
    (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) {i j : Fin (m + 1)} (hi : i.val + 2 = m + 1)
    (hj : j.val + 1 = m + 1) :
    plusNode e i ≤ centralizer (plusNode e j : Set G) := by
  have hsetEq : plusNodeSet (m + 1) i = plusNodeSet (m + 1) j := by
    ext x
    rw [mem_plusNodeSet, mem_plusNodeSet]
    have := x.isLt
    omega
  have hki : (0 : Fin (m + 1)) ∉ plusNodeSet (m + 1) i := by
    rw [mem_plusNodeSet]
    simp only [Fin.val_zero]
    omega
  have hkj : (0 : Fin (m + 1)) ∉ plusNodeSet (m + 1) j := hsetEq ▸ hki
  have hcard : (plusNodeSet (m + 1) i).card = 2 :=
    le_antisymm (card_plusNodeSet_le i) (two_le_card_plusNodeSet (by omega) i)
  have hcardj : 2 ≤ (plusNodeSet (m + 1) j).card := hsetEq ▸ hcard.ge
  have hU := C.map_signedLevelCore hK hF hki hcard.ge (plusNodeFlip (m + 1) i)
  have hV := C.map_signedLevelCore hK hF hkj hcardj (plusNodeFlip (m + 1) j)
  have hPi : preimagePlanes 0 (plusNodeFlip (m + 1) i) = ∅ := by
    ext x
    rw [mem_preimagePlanes, mem_plusNodeFlip]
    simp only [Fin.succAbove_zero, Fin.val_succ, Finset.notMem_empty, iff_false]
    omega
  rw [hPi, flipGL_empty, map_conj_one_eq] at hU
  set B := preimagePlanes 0 (plusNodeSet (m + 1) i) with hBdef
  have hB : B.card = 2 := by rw [hBdef, card_preimagePlanes hki, hcard]
  have hBj : preimagePlanes 0 (plusNodeSet (m + 1) j) = B := by rw [hBdef, hsetEq]
  rw [hBj] at hV
  have hPB : B ∩ preimagePlanes 0 (plusNodeFlip (m + 1) j) = {⟨m - 1, by omega⟩} := by
    ext x
    rw [Finset.mem_inter, hBdef, mem_preimagePlanes, mem_preimagePlanes, mem_plusNodeSet,
      mem_plusNodeFlip, Finset.mem_singleton]
    simp only [Fin.succAbove_zero, Fin.val_succ, Fin.ext_iff]
    have := x.isLt
    omega
  have hU' : (((plusNode e i).subgroupOf (plusNeighbourCore e 0)).map C.π).map
      (StatedOmega (StatedQuadPlus m F)).subtype = siegelBlockGL F B := hU
  have hV' : (((plusNode e j).subgroupOf (plusNeighbourCore e 0)).map C.π).map
      (StatedOmega (StatedQuadPlus m F)).subtype =
      (siegelBlockGL F B).map
        (MulAut.conj (flipGL F (preimagePlanes 0 (plusNodeFlip (m + 1) j)))).toMonoidHom := hV
  refine C.le_centralizer (plusSignedLevelCore_le_plusNeighbourCore e hki _)
    (plusSignedLevelCore_le_plusNeighbourCore e hkj _) (commutator_plusNode e j) ?_
  intro x hx y hy
  rw [hU'] at hx
  rw [hV'] at hy
  exact commute_siegelBlockGL_flip hF hB hPB hx hy

end Fork

end CFSG.SeitzReduction.OmegaPilot
