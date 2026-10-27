module

public import CFSG.ClassicalInvolution.Q3.Q3ZAdjChain
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (blockSL B12 B23 LinearBlockStandardPair pair_normalize
  pair_block_inj coe_blockSL_three_zero coe_blockSL_three_one)
open scoped MatrixGroups

section Transport

variable {K K' : Type} [Field K] [Field K']

theorem slMap_injective (e : K ≃+* K') (m : ℕ) :
    Function.Injective (Matrix.SpecialLinearGroup.map e.toRingHom : SL(m, K) →* SL(m, K')) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h'
  exact Matrix.map_injective e.injective h'

theorem slMap_surjective (e : K ≃+* K') (m : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map e.toRingHom : SL(m, K) →* SL(m, K')) := by
  intro b
  refine ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom b, ?_⟩
  apply Subtype.ext
  ext i j
  simp

theorem slMap_blockSL_zero (φ : K →+* K') (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map φ (blockSL K 3 2 0 (by omega) A) =
      blockSL K' 3 2 0 (by omega) (Matrix.SpecialLinearGroup.map φ A) := by
  apply Subtype.ext
  show φ.mapMatrix ((blockSL K 3 2 0 (by omega) A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = _
  rw [coe_blockSL_three_zero, coe_blockSL_three_zero]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem slMap_blockSL_one (φ : K →+* K') (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map φ (blockSL K 3 2 1 (by omega) A) =
      blockSL K' 3 2 1 (by omega) (Matrix.SpecialLinearGroup.map φ A) := by
  apply Subtype.ext
  show φ.mapMatrix ((blockSL K 3 2 1 (by omega) A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = _
  rw [coe_blockSL_three_one, coe_blockSL_three_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem range_comp_of_surjective {A B C : Type*} [Group A] [Group B] [Group C] (g : B →* C)
    {f : A →* B} (hf : Function.Surjective f) : (g.comp f).range = g.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf, Subgroup.map_top]

end Transport

section Pairs

variable {G : Type} [Group G] {F : Type} [Field F]

theorem exists_pairA_zmod (e : ZMod 3 ≃+* F) {W U V : Subgroup G}
    (h : LinearBlockStandardPair F W U V) :
    ∃ θ : SL(3, ZMod 3) →* G,
      Function.Injective (θ.comp (blockSL (ZMod 3) 3 2 1 (by omega))) ∧
      (blockSL (ZMod 3) 3 2 0 (by omega)).range.map θ = U ∧
      (blockSL (ZMod 3) 3 2 1 (by omega)).range.map θ = V := by
  obtain ⟨θ, -, hker, h0, h1⟩ := pair_normalize h
  obtain ⟨-, -, hinj1, -⟩ := pair_block_inj hker h0 h1
  let Φ3 : SL(3, ZMod 3) →* SL(3, F) := Matrix.SpecialLinearGroup.map e.toRingHom
  let Φ2 : SL(2, ZMod 3) →* SL(2, F) := Matrix.SpecialLinearGroup.map e.toRingHom
  have c0 : (θ.comp Φ3).comp (blockSL (ZMod 3) 3 2 0 (by omega)) =
      (θ.comp (blockSL F 3 2 0 (by omega))).comp Φ2 := by
    ext A
    exact congrArg θ (slMap_blockSL_zero e.toRingHom A)
  have c1 : (θ.comp Φ3).comp (blockSL (ZMod 3) 3 2 1 (by omega)) =
      (θ.comp (blockSL F 3 2 1 (by omega))).comp Φ2 := by
    ext A
    exact congrArg θ (slMap_blockSL_one e.toRingHom A)
  refine ⟨θ.comp Φ3, ?_, ?_, ?_⟩
  · rw [c1]
    exact hinj1.comp (slMap_injective e 2)
  · calc (blockSL (ZMod 3) 3 2 0 (by omega)).range.map (θ.comp Φ3)
        = ((θ.comp Φ3).comp (blockSL (ZMod 3) 3 2 0 (by omega))).range :=
          (MonoidHom.range_comp _ _).symm
      _ = (θ.comp (blockSL F 3 2 0 (by omega))).range := by
          rw [c0]
          exact range_comp_of_surjective _ (slMap_surjective e 2)
      _ = (B12 F).map θ := MonoidHom.range_comp _ _
      _ = U := h0
  · calc (blockSL (ZMod 3) 3 2 1 (by omega)).range.map (θ.comp Φ3)
        = ((θ.comp Φ3).comp (blockSL (ZMod 3) 3 2 1 (by omega))).range :=
          (MonoidHom.range_comp _ _).symm
      _ = (θ.comp (blockSL F 3 2 1 (by omega))).range := by
          rw [c1]
          exact range_comp_of_surjective _ (slMap_surjective e 2)
      _ = (B23 F).map θ := MonoidHom.range_comp _ _
      _ = V := h1

theorem exists_pairB_zmod (e : ZMod 3 ≃+* F) {W U V : Subgroup G}
    (h : SymplecticBlockStandardPair F W U V) :
    ∃ θ : StatedSp 2 (ZMod 3) →* G,
      Function.Injective (θ.comp (longBlock (ZMod 3) 2 1)) ∧
      Function.Injective
        (θ.comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1))) ∧
      (longBlock (ZMod 3) 2 1).range.map θ = U ∧
      (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map θ = V := by
  obtain ⟨θ, c, -, -, hinjL, hinjS, hU, hV⟩ := h
  let θ0 : StatedSp 2 F →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  let Φ2 : SL(2, ZMod 3) →* SL(2, F) := Matrix.SpecialLinearGroup.map e.toRingHom
  let Sp2 : StatedSp 2 (ZMod 3) →* StatedSp 2 F := spMap e.toRingHom
  have cL : (θ0.comp Sp2).comp (longBlock (ZMod 3) 2 1) = (θ0.comp (longBlock F 2 1)).comp Φ2 := by
    ext A
    exact congrArg θ0 (spMap_longBlock e.toRingHom 1 A)
  have cS : (θ0.comp Sp2).comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)) =
      (θ0.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))).comp Φ2 := by
    ext A
    exact congrArg θ0 (spMap_shortBlock e.toRingHom zero_ne_one A)
  refine ⟨θ0.comp Sp2, ?_, ?_, ?_, ?_⟩
  · rw [cL]
    exact hinjL.comp (slMap_injective e 2)
  · rw [cS]
    exact hinjS.comp (slMap_injective e 2)
  · calc (longBlock (ZMod 3) 2 1).range.map (θ0.comp Sp2)
        = ((θ0.comp Sp2).comp (longBlock (ZMod 3) 2 1)).range := (MonoidHom.range_comp _ _).symm
      _ = (θ0.comp (longBlock F 2 1)).range := by
          rw [cL]
          exact range_comp_of_surjective _ (slMap_surjective e 2)
      _ = ((longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
          rw [MonoidHom.range_comp, Subgroup.map_map]
      _ = U := hU
  · calc (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (θ0.comp Sp2)
        = ((θ0.comp Sp2).comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1))).range :=
          (MonoidHom.range_comp _ _).symm
      _ = (θ0.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))).range := by
          rw [cS]
          exact range_comp_of_surjective _ (slMap_surjective e 2)
      _ = ((shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
            (MulAut.conj c⁻¹).toMonoidHom).map θ := by
          rw [MonoidHom.range_comp, Subgroup.map_map]
      _ = V := hV

end Pairs

theorem natCard_galoisField_three : Nat.card (GaloisField 3 1) = 3 := by
  simpa using GaloisField.card 3 1 one_ne_zero

theorem nonempty_ringEquiv_galoisField_three : Nonempty (ZMod 3 ≃+* GaloisField 3 1) := by
  have := Fintype.ofFinite (GaloisField 3 1)
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, natCard_galoisField_three])⟩

theorem weakCT3_symplectic_chain_of {G : Type} [Group G]
    (hU : ∀ g : Fin 12 → G, RelsHold g v6Words →
      ∃ ψ : StatedSp 3 (ZMod 3) →* G, ∀ i, ψ (v6Mat i) = g i)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → G,
      RelsHold g (v6aWords k) → ∀ i, g i = 1)
    (U : Fin 3 → Subgroup G) (hcomm : ∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a)
    (hA : ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1))
    (hB : ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 2)
      (U 1)) :
    ∃ Ψ : StatedSp 3 (GaloisField 3 1) →* G,
      Ψ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField 3 1)) ∧
      (Models.SymplecticPairs.longBlock (GaloisField 3 1) 3 2).range.map Ψ = U 2 := by
  obtain ⟨e⟩ := nonempty_ringEquiv_galoisField_three
  obtain ⟨WA, hWA⟩ := hA
  obtain ⟨WB, hWB⟩ := hB
  obtain ⟨θA, hιA, hA0, hA1⟩ := exists_pairA_zmod e hWA
  obtain ⟨θB, hιL, hιS, hB2, hB1⟩ := exists_pairB_zmod e hWB
  obtain ⟨ψ, hψ, x, hx⟩ := exists_hom_of_chain U hcomm hU hC θA hιA hA0 hA1 θB hιS hιL hB2 hB1
  have hqs : IsQuasisimple (StatedSp 3 (GaloisField 3 1)) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple 3 (GaloisField 3 1) (by norm_num)
      (Or.inr (Or.inl ⟨natCard_galoisField_three, by norm_num⟩))
  refine ⟨ψ.comp (spMap e.symm.toRingHom), ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := spMap_surjective e.symm x
    exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqs ⟨y, hx⟩
  · have c : (ψ.comp (spMap e.symm.toRingHom)).comp (longBlock (GaloisField 3 1) 3 2) =
        (ψ.comp (longBlock (ZMod 3) 3 2)).comp
          (Matrix.SpecialLinearGroup.map e.symm.toRingHom) := by
      ext A
      exact congrArg ψ (spMap_longBlock e.symm.toRingHom 2 A)
    calc (longBlock (GaloisField 3 1) 3 2).range.map (ψ.comp (spMap e.symm.toRingHom))
        = ((ψ.comp (spMap e.symm.toRingHom)).comp (longBlock (GaloisField 3 1) 3 2)).range :=
          (MonoidHom.range_comp _ _).symm
      _ = (ψ.comp (longBlock (ZMod 3) 3 2)).range := by
          rw [c]
          exact range_comp_of_surjective _ (slMap_surjective e.symm 2)
      _ = (longBlock (ZMod 3) 3 2).range.map ψ := MonoidHom.range_comp _ _
      _ = U 2 := hψ

end CFSG.ClassicalInvolution.Q3.Q3Z
