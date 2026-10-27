module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaHyp
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataNorm

public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Matrix
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  matrixDerived matrixProjectiveProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus minusIndexEquiv plusIndexEquiv coordinateQuadMinus_apply)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_mk inclHom inclHom_val glIncl_val)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply coe_quadPlus)

section Chart

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

@[expose] noncomputable def minusCoord (hn : 1 ≤ r + 2) (s : Fin (r + 1) ⊕ Fin (r + 1)) :
    Fin (2 * (r + 2)) :=
  minusIndexEquiv (r + 2) hn (Sum.map id Sum.inl (s : Fin (r + 2 - 1) ⊕ Fin (r + 2 - 1)))

theorem minusCoord_injective (hn : 1 ≤ r + 2) : Function.Injective (minusCoord hn) := by
  intro s s' h
  have h1 := (minusIndexEquiv (r + 2) hn).injective h
  exact (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩) h1

theorem anisoPerpCoord_eq_minusCoord (hn : 1 ≤ r + 2) (s : Fin (r + 1) ⊕ Fin (r + 1)) :
    anisoPerpCoord hn (plusIndexEquiv (r + 1) s) = minusCoord hn s := by
  simp [anisoPerpCoord, minusCoord]

theorem extend_single_eq {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {f : ι → κ}
    (hf : Function.Injective f) (b : ι) :
    Function.extend f (Pi.single b (1 : K)) 0 = Pi.single (f b) 1 := by
  funext i
  by_cases h : ∃ a, f a = i
  · obtain ⟨a, rfl⟩ := h
    rw [hf.extend_apply]
    simp only [Pi.single_apply, hf.eq_iff]
  · rw [Function.extend_apply' _ _ _ h, Pi.single_eq_of_ne (fun h' => h ⟨b, h'.symm⟩)]
    rfl

variable [Finite K] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem minusChain_entry (hn4 : 4 ≤ r + 2) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    {k₀ : Subfield F} [CharP k₀ 2] (φ : K ≃+* k₀)
    (x : anisoPerp (K := K) (n := r + 2) (by omega) 1 1)
    (G : orthDerived (coordinateQuadMinus (r + 2) K (by omega) 1 1))
    (hG : (G : (Fin (2 * (r + 2)) → K) ≃ₗ[K] (Fin (2 * (r + 2)) → K)) ∈
      stabSub (anisoCoordLeft (by omega : 1 ≤ r + 2)) (anisoCoordRight (by omega : 1 ≤ r + 2)))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) 1 1)) =
      projHom _ G) (i j : Fin (r + 1) ⊕ Fin (r + 1)) :
    ((((statedOmegaPlusEquiv F (r + 1) (by omega)).symm
        (incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (r + 1) k₀)
          (plusCongr φ (r + 1) (anisoPerpModelEquiv (n := r + 2) hn4 hirr x))) :
        StatedOmega (StatedQuadPlus (r + 1) F)) : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) F) i j =
      ((φ ((G : (Fin (2 * (r + 2)) → K) ≃ₗ[K] (Fin (2 * (r + 2)) → K))
        (Pi.single (minusCoord (by omega) j) 1) (minusCoord (by omega) i)) : k₀) : F) := by
  set X := anisoPerpEquiv hn4 hirr x with hX
  set A := (derivedEquiv (coordinateQuadPlus (r + 1) K)).symm X with hA
  have hBmem : glCongr φ (A : GL (Fin (2 * (r + 1))) K) ∈
      matrixDerived (coordinateQuadPlus (r + 1) k₀) := by
    rw [← map_matrixDerived_glCongr φ (coordinateQuadPlus_comp_ringEquiv φ (r + 1))]
    exact ⟨_, A.2, rfl⟩
  set B : matrixDerived (coordinateQuadPlus (r + 1) k₀) := ⟨_, hBmem⟩ with hB
  have h1 : anisoPerpModelEquiv (n := r + 2) hn4 hirr x =
      matrixProjectiveProjection _ A := rfl
  have h2 : plusCongr φ (r + 1) (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ B :=
    matrixProjectiveCongr_mk φ _ A B rfl
  have h4 : ∀ C : matrixDerived (coordinateQuadPlus (r + 1) F),
      (statedOmegaPlusEquiv F (r + 1) (by omega)).symm (matrixProjectiveProjection _ C) =
        (statedDerivedPlusEquiv F (r + 1)).symm C := by
    intro C
    rw [MulEquiv.symm_apply_eq]
    simp only [statedOmegaPlusEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [h1, h2, incl_mk, h4, statedDerivedPlusEquiv_symm_entry, inclHom_val, glIncl_val,
    Matrix.map_apply]
  change ((((glCongr φ (A : GL (Fin (2 * (r + 1))) K) : GL (Fin (2 * (r + 1))) k₀) :
    Matrix _ _ k₀) (plusIndexEquiv (r + 1) i) (plusIndexEquiv (r + 1) j) : k₀) : F) = _
  rw [glCongr_coe, Matrix.map_apply, hA, derivedEquiv_symm_entry, hX,
    anisoPerpEquiv_apply hn4 hirr x G hG hxG, extend_single_eq (anisoPerpCoord_injective _),
    anisoPerpCoord_eq_minusCoord, anisoPerpCoord_eq_minusCoord]

@[expose] noncomputable def minusChainHom (hn4 : 4 ≤ r + 2) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    {k₀ : Subfield F} [CharP k₀ 2] (φ : K ≃+* k₀) :
    anisoPerp (K := K) (n := r + 2) (by omega) 1 1 →* GL (Fin (r + 1) ⊕ Fin (r + 1)) F :=
  (StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp
    ((statedOmegaPlusEquiv F (r + 1) (by omega)).symm.toMonoidHom.comp
      ((incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (r + 1) k₀)).comp
        ((plusCongr φ (r + 1)).toMonoidHom.comp (anisoPerpModelEquiv (n := r + 2) hn4 hirr).toMonoidHom)))

theorem minusChainHom_apply (hn4 : 4 ≤ r + 2) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    {k₀ : Subfield F} [CharP k₀ 2] (φ : K ≃+* k₀) (x : anisoPerp (K := K) (n := r + 2) (by omega) 1 1) :
    minusChainHom hn4 hirr φ x = (((statedOmegaPlusEquiv F (r + 1) (by omega)).symm
        (incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (r + 1) k₀)
          (plusCongr φ (r + 1) (anisoPerpModelEquiv (n := r + 2) hn4 hirr x))) :
        StatedOmega (StatedQuadPlus (r + 1) F)) : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) := rfl

theorem eq_sum_minusCoord (hn : 1 ≤ r + 2) {v : Fin (2 * (r + 2)) → K}
    (hv : v (anisoCoordLeft hn) = 0 ∧ v (anisoCoordRight hn) = 0) :
    v = ∑ j, v (minusCoord hn j) • Pi.single (minusCoord hn j) 1 := by
  funext t
  rw [Finset.sum_apply]
  by_cases ht : ∃ j, minusCoord hn j = t
  · obtain ⟨j, rfl⟩ := ht
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [Pi.single_apply, (minusCoord_injective hn).eq_iff, hj']
    · simp
  · have h0 : v t = 0 := by
      by_cases h1 : t = anisoCoordLeft hn
      · rw [h1]
        exact hv.1
      by_cases h2 : t = anisoCoordRight hn
      · rw [h2]
        exact hv.2
      obtain ⟨x, hx⟩ := exists_anisoPerpCoord_eq hn h1 h2
      exact absurd ⟨(plusIndexEquiv (r + 1)).symm x, by
        rw [← anisoPerpCoord_eq_minusCoord, Equiv.apply_symm_apply, hx]⟩ ht
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => ht ⟨j, h.symm⟩), smul_zero]

variable (E : EnnolaParam K F)

@[expose] noncomputable def minusJ (hn : 1 ≤ r + 2) (v : Fin (2 * (r + 2)) → K) : Fin (r + 1) ⊕ Fin (r + 1) → F :=
  fun s => E.ι (v (minusCoord hn s))

theorem minusJ_add (hn : 1 ≤ r + 2) (v w : Fin (2 * (r + 2)) → K) :
    minusJ E hn (v + w) = minusJ E hn v + minusJ E hn w := by
  funext s
  simp [minusJ]

theorem minusJ_smul (hn : 1 ≤ r + 2) (c : K) (v : Fin (2 * (r + 2)) → K) :
    minusJ E hn (c • v) = E.ι c • minusJ E hn v := by
  funext s
  simp [minusJ]

theorem quadPlus_minusJ (hn : 1 ≤ r + 2) {v : Fin (2 * (r + 2)) → K}
    (hv : v (anisoCoordLeft hn) = 0 ∧ v (anisoCoordRight hn) = 0) :
    quadPlus (r + 1) F (minusJ E hn v) = E.ι (coordinateQuadMinus (r + 2) K hn 1 1 v) := by
  rw [quadPlus_apply, coordinateQuadMinus_apply]
  have h1 : v (minusIndexEquiv (r + 2) hn (.inr (.inr 0))) = 0 := hv.1
  have h2 : v (minusIndexEquiv (r + 2) hn (.inr (.inr 1))) = 0 := hv.2
  rw [h1, h2]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    map_sum, map_mul]
  rfl

theorem polar_quadPlus_minusJ (hn : 1 ≤ r + 2) {v w : Fin (2 * (r + 2)) → K}
    (hv : v (anisoCoordLeft hn) = 0 ∧ v (anisoCoordRight hn) = 0)
    (hw : w (anisoCoordLeft hn) = 0 ∧ w (anisoCoordRight hn) = 0) :
    polar (quadPlus (r + 1) F) (minusJ E hn v) (minusJ E hn w) =
      E.ι (polar (coordinateQuadMinus (r + 2) K hn 1 1) v w) := by
  have hvw : (v + w) (anisoCoordLeft hn) = 0 ∧ (v + w) (anisoCoordRight hn) = 0 := by
    simp [hv.1, hv.2, hw.1, hw.2]
  rw [QuadraticMap.polar, QuadraticMap.polar, ← minusJ_add, quadPlus_minusJ E hn hvw,
    quadPlus_minusJ E hn hv, quadPlus_minusJ E hn hw, map_sub, map_sub]

theorem minusChain_mulVec (hn4 : 4 ≤ r + 2) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    {k₀ : Subfield F} [CharP k₀ 2] (φ : K ≃+* k₀) (hE : ∀ p, E.ι p = ((φ p : k₀) : F))
    (x : anisoPerp (K := K) (n := r + 2) (by omega) 1 1)
    (G : orthDerived (coordinateQuadMinus (r + 2) K (by omega) 1 1))
    (hG : (G : (Fin (2 * (r + 2)) → K) ≃ₗ[K] (Fin (2 * (r + 2)) → K)) ∈
      stabSub (anisoCoordLeft (by omega : 1 ≤ r + 2)) (anisoCoordRight (by omega : 1 ≤ r + 2)))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) 1 1)) =
      projHom _ G) {v : Fin (2 * (r + 2)) → K}
    (hv : v (anisoCoordLeft (by omega : 1 ≤ r + 2)) = 0 ∧
      v (anisoCoordRight (by omega : 1 ≤ r + 2)) = 0) :
    ((minusChainHom hn4 hirr φ x : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) F) *ᵥ
        minusJ E (by omega) v =
      minusJ E (by omega) ((G : (Fin (2 * (r + 2)) → K) ≃ₗ[K] (Fin (2 * (r + 2)) → K)) v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have hent := fun j => minusChain_entry hn4 hirr φ x G hG hxG i j
  rw [minusChainHom_apply]
  simp only [hent, ← hE, minusJ, ← map_mul, ← map_sum]
  congr 1
  conv_rhs => rw [eq_sum_minusCoord (by omega : 1 ≤ r + 2) hv]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem quadPlus_minusJ_combo (hn : 1 ≤ r + 2) {a b : Fin (2 * (r + 2)) → K}
    (ha : a (anisoCoordLeft hn) = 0 ∧ a (anisoCoordRight hn) = 0)
    (hb : b (anisoCoordLeft hn) = 0 ∧ b (anisoCoordRight hn) = 0) (α β : F) :
    quadPlus (r + 1) F (α • minusJ E hn a + β • minusJ E hn b) =
      α ^ 2 * E.ι (coordinateQuadMinus (r + 2) K hn 1 1 a) +
        β ^ 2 * E.ι (coordinateQuadMinus (r + 2) K hn 1 1 b) +
        α * β * E.ι (polar (coordinateQuadMinus (r + 2) K hn 1 1) a b) := by
  rw [QuadraticMap.map_add (quadPlus (r + 1) F), QuadraticMap.map_smul, QuadraticMap.map_smul,
    polar_smul_left, polar_smul_right, quadPlus_minusJ E hn ha, quadPlus_minusJ E hn hb,
    polar_quadPlus_minusJ E hn ha hb]
  simp only [smul_eq_mul]
  ring

theorem polar_minusJ_combo (hn : 1 ≤ r + 2) {a b c d : Fin (2 * (r + 2)) → K}
    (ha : a (anisoCoordLeft hn) = 0 ∧ a (anisoCoordRight hn) = 0)
    (hb : b (anisoCoordLeft hn) = 0 ∧ b (anisoCoordRight hn) = 0)
    (hc : c (anisoCoordLeft hn) = 0 ∧ c (anisoCoordRight hn) = 0)
    (hd : d (anisoCoordLeft hn) = 0 ∧ d (anisoCoordRight hn) = 0) (α β γ δ : F) :
    polar (quadPlus (r + 1) F) (α • minusJ E hn a + β • minusJ E hn b)
        (γ • minusJ E hn c + δ • minusJ E hn d) =
      α * γ * E.ι (polar (coordinateQuadMinus (r + 2) K hn 1 1) a c) +
        α * δ * E.ι (polar (coordinateQuadMinus (r + 2) K hn 1 1) a d) +
        β * γ * E.ι (polar (coordinateQuadMinus (r + 2) K hn 1 1) b c) +
        β * δ * E.ι (polar (coordinateQuadMinus (r + 2) K hn 1 1) b d) := by
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
    polar_quadPlus_minusJ E hn ha hc, polar_quadPlus_minusJ E hn ha hd,
    polar_quadPlus_minusJ E hn hb hc, polar_quadPlus_minusJ E hn hb hd]
  ring

end Chart

section Basis

variable {K : Type} [Field K] [CharP K 2] [Finite K] {r : ℕ}

@[expose] noncomputable def minusPairA (hn : 1 ≤ r + 2) (k : ℕ) : Fin (2 * (r + 2)) → K :=
  if 2 * (k / 2) + 1 < r + 1 then blockVec (minusHypE hn) (minusHypF hn) k else minusHypE hn k

@[expose] noncomputable def minusPairB (hn : 1 ≤ r + 2) (k : ℕ) : Fin (2 * (r + 2)) → K :=
  if 2 * (k / 2) + 1 < r + 1 then blockVec' (minusHypE hn) (minusHypF hn) k else minusHypF hn k

theorem minusHypE_vanish (hn : 1 ≤ r + 2) (l : ℕ) :
    minusHypE (K := K) hn l (anisoCoordLeft hn) = 0 ∧
      minusHypE (K := K) hn l (anisoCoordRight hn) = 0 := by
  by_cases h : l < r + 1
  · rw [minusHypE_of_lt hn h]
    exact ⟨Pi.single_eq_of_ne (fun h' => by simpa using (minusIndexEquiv _ hn).injective h') _,
      Pi.single_eq_of_ne (fun h' => by simpa using (minusIndexEquiv _ hn).injective h') _⟩
  · rw [minusHypE_of_not_lt hn h]
    exact ⟨rfl, rfl⟩

theorem minusHypF_vanish (hn : 1 ≤ r + 2) (l : ℕ) :
    minusHypF (K := K) hn l (anisoCoordLeft hn) = 0 ∧
      minusHypF (K := K) hn l (anisoCoordRight hn) = 0 := by
  by_cases h : l < r + 1
  · rw [minusHypF_of_lt hn h]
    exact ⟨Pi.single_eq_of_ne (fun h' => by simpa using (minusIndexEquiv _ hn).injective h') _,
      Pi.single_eq_of_ne (fun h' => by simpa using (minusIndexEquiv _ hn).injective h') _⟩
  · rw [minusHypF_of_not_lt hn h]
    exact ⟨rfl, rfl⟩

theorem blockVec_minus_vanish (hn : 1 ≤ r + 2) (i : ℕ) :
    (blockVec (minusHypE (K := K) hn) (minusHypF hn) i (anisoCoordLeft hn) = 0 ∧
      blockVec (minusHypE (K := K) hn) (minusHypF hn) i (anisoCoordRight hn) = 0) ∧
    (blockVec' (minusHypE (K := K) hn) (minusHypF hn) i (anisoCoordLeft hn) = 0 ∧
      blockVec' (minusHypE (K := K) hn) (minusHypF hn) i (anisoCoordRight hn) = 0) := by
  have e1 := minusHypE_vanish (K := K) hn (2 * (i / 2))
  have e2 := minusHypE_vanish (K := K) hn (2 * (i / 2) + 1)
  have f1 := minusHypF_vanish (K := K) hn (2 * (i / 2))
  have f2 := minusHypF_vanish (K := K) hn (2 * (i / 2) + 1)
  unfold blockVec blockVec'
  split_ifs <;> simp [e1.1, e1.2, e2.1, e2.2, f1.1, f1.2, f2.1, f2.2]

theorem minusPair_vanish (hn : 1 ≤ r + 2) (k : ℕ) :
    (minusPairA (K := K) hn k (anisoCoordLeft hn) = 0 ∧
      minusPairA (K := K) hn k (anisoCoordRight hn) = 0) ∧
    (minusPairB (K := K) hn k (anisoCoordLeft hn) = 0 ∧
      minusPairB (K := K) hn k (anisoCoordRight hn) = 0) := by
  unfold minusPairA minusPairB
  split_ifs
  · exact blockVec_minus_vanish hn k
  · exact ⟨minusHypE_vanish hn k, minusHypF_vanish hn k⟩

theorem eq_of_not_block {k : ℕ} (hk : k < r + 1) (h : ¬2 * (k / 2) + 1 < r + 1) : k = r := by
  omega

theorem isUnitPlane_minusPair (hn : 1 ≤ r + 2) {k : ℕ} (h : 2 * (k / 2) + 1 < r + 1) :
    IsUnitPlane (coordinateQuadMinus (r + 2) K hn 1 1) (minusPairA hn k) (minusPairB hn k) := by
  unfold minusPairA minusPairB
  simp only [h, ↓reduceIte]
  exact (isHypSystem_minus hn 1 1).isUnitPlane_blockVec h

theorem hyp_minusPair (hn : 1 ≤ r + 2) {k : ℕ} (hk : k < r + 1) (h : ¬2 * (k / 2) + 1 < r + 1) :
    coordinateQuadMinus (r + 2) K hn 1 1 (minusPairA hn k) = 0 ∧
      coordinateQuadMinus (r + 2) K hn 1 1 (minusPairB hn k) = 0 ∧
      polar (coordinateQuadMinus (r + 2) K hn 1 1) (minusPairA hn k) (minusPairB hn k) = 1 := by
  have hS := isHypSystem_minus (K := K) hn 1 1
  unfold minusPairA minusPairB
  simp only [h, ↓reduceIte]
  exact ⟨hS.map_e k, hS.map_f k, hS.ef_self k hk⟩

theorem polar_minusPair_ne (hn : 1 ≤ r + 2) {k k' : ℕ} (hk : k < r + 1) (hk' : k' < r + 1)
    (hne : k ≠ k') :
    polar (coordinateQuadMinus (r + 2) K hn 1 1) (minusPairA hn k) (minusPairA hn k') = 0 ∧
      polar (coordinateQuadMinus (r + 2) K hn 1 1) (minusPairA hn k) (minusPairB hn k') = 0 ∧
      polar (coordinateQuadMinus (r + 2) K hn 1 1) (minusPairB hn k) (minusPairA hn k') = 0 ∧
      polar (coordinateQuadMinus (r + 2) K hn 1 1) (minusPairB hn k) (minusPairB hn k') = 0 := by
  have hS := isHypSystem_minus (K := K) hn 1 1
  unfold minusPairA minusPairB
  by_cases h : 2 * (k / 2) + 1 < r + 1 <;> by_cases h' : 2 * (k' / 2) + 1 < r + 1
  · simp only [h, h', ↓reduceIte]
    obtain ⟨a1, a2, a3⟩ := hS.polar_blockVec_ne h hne
    obtain ⟨-, b2, -⟩ := hS.polar_blockVec_ne h' (Ne.symm hne)
    exact ⟨a1, a2, by rw [polar_comm]; exact b2, a3⟩
  · simp only [h, h', ↓reduceIte]
    have hk'r := eq_of_not_block hk' h'
    obtain ⟨a1, a2, a3, a4⟩ := hS.polar_blockVec_of_ne k (l := k') (by omega) (by omega)
    exact ⟨a1, a2, a3, a4⟩
  · simp only [h, h', ↓reduceIte]
    have hkr := eq_of_not_block hk h
    obtain ⟨a1, a2, a3, a4⟩ := hS.polar_blockVec_of_ne k' (l := k) (by omega) (by omega)
    exact ⟨by rw [polar_comm]; exact a1, by rw [polar_comm]; exact a3,
      by rw [polar_comm]; exact a2, by rw [polar_comm]; exact a4⟩
  · exact absurd ((eq_of_not_block hk h).trans (eq_of_not_block hk' h').symm) hne

variable {F : Type} [Field F] [Finite F] [CharP F 2] (E : EnnolaParam K F)

@[expose] def minusIdx (l : Fin (r + 1) ⊕ Fin (r + 1)) : ℕ := (Sum.elim id id l : Fin (r + 1)).val

theorem minusIdx_lt (l : Fin (r + 1) ⊕ Fin (r + 1)) : minusIdx l < r + 1 :=
  (Sum.elim id id l : Fin (r + 1)).2

@[expose] noncomputable def minusCoefA (l : Fin (r + 1) ⊕ Fin (r + 1)) : F :=
  Sum.elim (fun _ => 1) (fun k => if 2 * (k.val / 2) + 1 < r + 1 then 1 else 0) l

@[expose] noncomputable def minusCoefB (l : Fin (r + 1) ⊕ Fin (r + 1)) : F :=
  Sum.elim (fun k => if 2 * (k.val / 2) + 1 < r + 1 then E.ω else 0)
    (fun k => if 2 * (k.val / 2) + 1 < r + 1 then E.ω + 1 else 1) l

@[expose] noncomputable def minusW (hn : 1 ≤ r + 2) (l : Fin (r + 1) ⊕ Fin (r + 1)) :
    Fin (r + 1) ⊕ Fin (r + 1) → F :=
  (minusCoefA l : F) • minusJ E hn (minusPairA hn (minusIdx l)) +
    minusCoefB E l • minusJ E hn (minusPairB hn (minusIdx l))

theorem polar_minusPair_self (hn : 1 ≤ r + 2) {k : ℕ} (hk : k < r + 1) :
    polar (coordinateQuadMinus (r + 2) K hn 1 1) (minusPairA hn k) (minusPairB hn k) = 1 ∧
      polar (coordinateQuadMinus (r + 2) K hn 1 1) (minusPairB hn k) (minusPairA hn k) = 1 := by
  by_cases h : 2 * (k / 2) + 1 < r + 1
  · have hu := isUnitPlane_minusPair (K := K) hn h
    exact ⟨hu.polar_eq, hu.polar_symm⟩
  · have hh := hyp_minusPair (K := K) hn hk h
    exact ⟨hh.2.2, by rw [polar_comm]; exact hh.2.2⟩

theorem quadPlus_minusW (hn : 1 ≤ r + 2) (l : Fin (r + 1) ⊕ Fin (r + 1)) :
    quadPlus (r + 1) F (minusW E hn l) = 0 := by
  have hsq := E.sq
  have hv := minusPair_vanish (K := K) hn (minusIdx l)
  rw [minusW, quadPlus_minusJ_combo E hn hv.1 hv.2]
  by_cases h : 2 * (minusIdx l / 2) + 1 < r + 1
  · have hu := isUnitPlane_minusPair (K := K) hn h
    rw [hu.map_left, hu.map_right, hu.polar_eq, map_one]
    rcases l with k | k <;> simp only [minusIdx, Sum.elim_inl, Sum.elim_inr, id] at h <;>
      simp only [minusCoefA, minusCoefB, Sum.elim_inl, Sum.elim_inr, h, ↓reduceIte] <;> grind
  · have hh := hyp_minusPair (K := K) hn (minusIdx_lt l) h
    rw [hh.1, hh.2.1, hh.2.2, map_zero, map_one]
    rcases l with k | k <;> simp only [minusIdx, Sum.elim_inl, Sum.elim_inr, id] at h <;>
      simp only [minusCoefA, minusCoefB, Sum.elim_inl, Sum.elim_inr, h, ↓reduceIte] <;> ring

theorem polar_minusW (hn : 1 ≤ r + 2) (l l' : Fin (r + 1) ⊕ Fin (r + 1)) :
    polar (quadPlus (r + 1) F) (minusW E hn l) (minusW E hn l') =
      if l' = Sum.swap l then 1 else 0 := by
  have hsq := E.sq
  have hv := minusPair_vanish (K := K) hn (minusIdx l)
  have hv' := minusPair_vanish (K := K) hn (minusIdx l')
  rw [minusW, minusW, polar_minusJ_combo E hn hv.1 hv.2 hv'.1 hv'.2]
  by_cases hidx : minusIdx l = minusIdx l'
  · obtain ⟨b1, b2⟩ := polar_minusPair_self (K := K) hn (minusIdx_lt l)
    rw [← hidx, polar_self_charTwo, polar_self_charTwo, b1, b2]
    simp only [map_zero, map_one, mul_zero, mul_one, zero_add, add_zero]
    rcases l with k | k <;> rcases l' with k' | k' <;>
      simp only [minusIdx, Sum.elim_inl, Sum.elim_inr, id] at hidx <;>
      obtain rfl : k = k' := Fin.ext hidx <;>
      simp only [minusCoefA, minusCoefB, Sum.elim_inl, Sum.elim_inr, Sum.swap_inl, Sum.swap_inr,
        reduceCtorEq, ↓reduceIte] <;>
      split_ifs <;> grind
  · have ho := polar_minusPair_ne (K := K) hn (minusIdx_lt l) (minusIdx_lt l') hidx
    rw [ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
    simp only [map_zero, mul_zero, add_zero]
    have hne : l' ≠ Sum.swap l := by
      intro h
      apply hidx
      rw [h]
      rcases l with k | k <;> rfl
    simp only [hne, ↓reduceIte]

theorem minusPairA_of_lt (hn : 1 ≤ r + 2) {k : ℕ} (hk : k < r) :
    minusPairA (K := K) hn k = blockVec (minusHypE hn) (minusHypF hn) k := by
  simp only [minusPairA, show 2 * (k / 2) + 1 < r + 1 by omega, ↓reduceIte]

theorem minusPairB_of_lt (hn : 1 ≤ r + 2) {k : ℕ} (hk : k < r) :
    minusPairB (K := K) hn k = blockVec' (minusHypE hn) (minusHypF hn) k := by
  simp only [minusPairB, show 2 * (k / 2) + 1 < r + 1 by omega, ↓reduceIte]

end Basis

section Diag

variable {F : Type} [Field F] {r : ℕ}

theorem restrictParam_zero_mulSingle_succ (k : Fin r) (x : Fˣ) :
    restrictParam 0 (Pi.mulSingle k.succ x : Fin (r + 1) → Fˣ) = Pi.mulSingle k x := by
  funext i
  rw [restrictParam_apply, Fin.succAbove_zero, Pi.mulSingle_apply, Pi.mulSingle_apply]
  simp only [Fin.succ_inj]

theorem liftParam_id (u : Fin r → Fˣ) :
    SymplecticPilot.liftParam (RingHom.id F) u = u := by
  funext i
  ext
  simp [SymplecticPilot.liftParam]

theorem snocOneParam_mulSingle (k : Fin r) (x : Fˣ) :
    snocOneParam F r (Pi.mulSingle k x) = Pi.mulSingle k.castSucc x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snocOneParam_last, Pi.mulSingle_eq_of_ne (Fin.castSucc_ne_last k).symm]
  · rw [snocOneParam_castSucc, Pi.mulSingle_apply, Pi.mulSingle_apply]
    simp only [Fin.castSucc_inj]

theorem minusNeighbourDiag_mulSingle_succ (k : Fin r) (x : Fˣ) :
    (minusNeighbourDiag (RingHom.id F) 0 (Pi.mulSingle k.succ x) :
      Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) F) =
      diagonal (SymplecticPilot.diagSpEntry (Pi.mulSingle k.castSucc x)) := by
  rw [minusNeighbourDiag_apply, restrictParam_zero_mulSingle_succ, liftParam_id,
    snocOneParam_mulSingle, diagOmega_coe]

@[expose] def consOneHom : (Fin r → Fˣ) →* (Fin (r + 1) → Fˣ) where
  toFun u := Fin.cons 1 u
  map_one' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_mul' u v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem consOneHom_apply (u : Fin r → Fˣ) : consOneHom u = Fin.cons (1 : Fˣ) u := rfl

theorem consOneHom_mulSingle (k : Fin r) (x : Fˣ) :
    consOneHom (Pi.mulSingle k x) = (Pi.mulSingle k.succ x : Fin (r + 1) → Fˣ) := by
  funext i
  rw [consOneHom_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero k).symm]
  · rw [Fin.cons_succ, Pi.mulSingle_apply, Pi.mulSingle_apply]
    simp only [Fin.succ_inj]

theorem consOneHom_tail {t : Fin (r + 1) → Fˣ} (ht : t 0 = 1) : consOneHom (Fin.tail t) = t := by
  rw [consOneHom_apply, ← ht, Fin.cons_self_tail]

end Diag

section Eigen

variable {K : Type} [Field K] [CharP K 2] [Finite K] {r : ℕ} {F : Type} [Field F] [Finite F]
  [CharP F 2] (E : EnnolaParam K F)

theorem rotOmega_mem_stabSub (hr : 2 ≤ r) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) (k : Fin r)
    (x : Fˣ) :
    (((isEnnolaFrame_minus hr hirr).rotOmega E k.succ x : orthDerived _) :
      (Fin (2 * (r + 2)) → K) ≃ₗ[K] (Fin (2 * (r + 2)) → K)) ∈
      stabSub (anisoCoordLeft (by omega : 1 ≤ r + 2)) (anisoCoordRight (by omega : 1 ≤ r + 2)) := by
  set hF := isEnnolaFrame_minus hr hirr
  have h0 : (0 : Fin (r + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
  refine ⟨?_, ?_⟩
  · rw [IsEnnolaFrame.coe_rotOmega, ← minusFrameA_zero]
    exact E.rotHom_of_perp (hF.unit k.succ) x (hF.orth_aa 0 k.succ h0) (hF.orth_aa' 0 k.succ h0)
  · rw [IsEnnolaFrame.coe_rotOmega, ← minusFrameA'_zero]
    exact E.rotHom_of_perp (hF.unit k.succ) x (hF.orth_a'a h0) (hF.orth_a'a' 0 k.succ h0)

theorem rotOmega_mem_anisoPerp (hr : 2 ≤ r) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) (k : Fin r)
    (x : Fˣ) :
    projHom _ ((isEnnolaFrame_minus hr hirr).rotOmega E k.succ x) ∈
      anisoPerp (K := K) (n := r + 2) (by omega) 1 1 :=
  ⟨_, mem_subgroupOf.2 (rotOmega_mem_stabSub E hr hirr k x), rfl⟩

theorem minusChain_mulVec_minusW (hr : 2 ≤ r) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    {k₀ : Subfield F} [CharP k₀ 2] (φ : K ≃+* k₀) (hE : ∀ p, E.ι p = ((φ p : k₀) : F))
    (k : Fin r) (x : Fˣ) (l : Fin (r + 1) ⊕ Fin (r + 1)) :
    ((minusChainHom (by omega) hirr φ ⟨_, rotOmega_mem_anisoPerp E hr hirr k x⟩ :
        GL (Fin (r + 1) ⊕ Fin (r + 1)) F) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) F) *ᵥ
        minusW E (by omega) l =
      SymplecticPilot.diagSpEntry (Pi.mulSingle k.castSucc x) l • minusW E (by omega) l := by
  have hsq := E.sq
  have hn : 1 ≤ r + 2 := by omega
  set hF := isEnnolaFrame_minus hr hirr
  set G := hF.rotOmega E k.succ x with hGdef
  have hfix : ∀ v, polar (coordinateQuadMinus (r + 2) K hn 1 1) v (minusFrameA hn k.succ) = 0 →
      polar (coordinateQuadMinus (r + 2) K hn 1 1) v (minusFrameA' hn k.succ) = 0 →
      (G : (Fin (2 * (r + 2)) → K) ≃ₗ[K] (Fin (2 * (r + 2)) → K)) v = v :=
    fun v h1 h2 => E.rotHom_of_perp (hF.unit k.succ) x h1 h2
  have hv := minusPair_vanish (K := K) hn (minusIdx l)
  have hM := fun (v : Fin (2 * (r + 2)) → K) (hv : v (anisoCoordLeft hn) = 0 ∧
      v (anisoCoordRight hn) = 0) =>
    minusChain_mulVec E (by omega) hirr φ hE ⟨_, rotOmega_mem_anisoPerp E hr hirr k x⟩ G
      (rotOmega_mem_stabSub E hr hirr k x) rfl hv
  rw [minusW, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hM _ hv.1, hM _ hv.2]
  have hA : minusPairA (K := K) hn k.val = minusFrameA hn k.succ := by
    rw [minusFrameA_succ, minusPairA_of_lt hn k.2]
  have hB : minusPairB (K := K) hn k.val = minusFrameA' hn k.succ := by
    rw [minusFrameA'_succ, minusPairB_of_lt hn k.2]
  by_cases hidx : minusIdx l = k.val
  · rw [hidx, hA, hB, hGdef, IsEnnolaFrame.coe_rotOmega, E.rotHom_left, E.rotHom_right, minusJ_add, minusJ_add, minusJ_smul, minusJ_smul, minusJ_smul,
      minusJ_smul, map_add]
    have hu : 2 * (k.val / 2) + 1 < r + 1 := by omega
    rcases l with k' | k' <;> simp only [minusIdx, Sum.elim_inl, Sum.elim_inr, id] at hidx <;>
      obtain rfl : k' = k.castSucc := Fin.ext hidx
    · have hx := E.ell_param x
      simp only [minusCoefA, minusCoefB, Sum.elim_inl, Fin.val_castSucc, hu, ↓reduceIte,
        SymplecticPilot.diagSpEntry_inl, Pi.mulSingle_eq_same]
      rw [← hx]
      match_scalars <;> grind
    · have hx := E.ell_conj_param x.ne_zero
      simp only [minusCoefA, minusCoefB, Sum.elim_inr, Fin.val_castSucc, hu, ↓reduceIte,
        SymplecticPilot.diagSpEntry_inr, Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val]
      rw [← hx]
      match_scalars <;> grind
  · have ho := polar_minusPair_ne (K := K) hn (minusIdx_lt l) (by omega : k.val < r + 1) hidx
    rw [hA, hB] at ho
    rw [hfix _ ho.1 ho.2.1, hfix _ ho.2.2.1 ho.2.2.2]
    have h1 : SymplecticPilot.diagSpEntry (Pi.mulSingle k.castSucc x) l = 1 := by
      rcases l with k' | k' <;> simp only [minusIdx, Sum.elim_inl, Sum.elim_inr, id] at hidx <;>
        have hk' : k' ≠ k.castSucc := fun h => hidx (by rw [h, Fin.val_castSucc]) <;>
        simp [SymplecticPilot.diagSpEntry, Pi.mulSingle_eq_of_ne hk']
    rw [h1, one_smul]

theorem minus_chart (hr : 2 ≤ r) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) {k₀ : Subfield F}
    [CharP k₀ 2] (φ : K ≃+* k₀) (hE : ∀ p, E.ι p = ((φ p : k₀) : F)) :
    ∃ g ∈ normalizer (StatedOmega (StatedQuadPlus (r + 1) F) :
        Set (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)),
      ∀ t : Fin (r + 1) → Fˣ, t 0 = 1 →
        ∃ hD : (isEnnolaFrame_minus hr hirr).torus E t ∈ anisoPerp (K := K) (n := r + 2) (by omega) 1 1,
          g * minusChainHom (by omega) hirr φ ⟨_, hD⟩ * g⁻¹ = minusNeighbourDiag (RingHom.id F) 0 t := by
  set hF := isEnnolaFrame_minus hr hirr with hFdef
  obtain ⟨P, hP, hPiso⟩ := exists_gl_of_hypBasis (minusW E (by omega : 1 ≤ r + 2))
    (quadPlus_minusW E _) (polar_minusW E _)
  refine ⟨P⁻¹, mem_normalizer_statedOmega_of_mem_isometryClosure (inv_mem hPiso), ?_⟩
  have hmem : ∀ t : Fin (r + 1) → Fˣ, t 0 = 1 →
      hF.torus E t ∈ anisoPerp (K := K) (n := r + 2) _ 1 1 := by
    intro t ht
    have h := hF.torus_mem_fixVecBar E ht
    rw [minusFrameA_zero, minusFrameA'_zero, ← pairPerpOf_eq_fixVecBar] at h
    exact h
  set T : (Fin r → Fˣ) →* anisoPerp (K := K) (n := r + 2) _ 1 1 :=
    ((hF.torus E).comp consOneHom).codRestrict _
      (fun u => hmem _ (by rw [consOneHom_apply, Fin.cons_zero])) with hTdef
  have key : (MulAut.conj P⁻¹).toMonoidHom.comp ((minusChainHom (by omega) hirr φ).comp T) =
      (minusNeighbourDiag (RingHom.id F) 0).comp consOneHom := by
    refine MonoidHom.pi_ext fun k x => ?_
    have hT : T (Pi.mulSingle k x) = ⟨_, rotOmega_mem_anisoPerp E hr hirr k x⟩ := by
      apply Subtype.ext
      change hF.torus E (consOneHom (Pi.mulSingle k x)) = _
      rw [consOneHom_mulSingle, hF.torus_mulSingle]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hT, consOneHom_mulSingle]
    refine inv_mul_mul_eq_of_eigen P _ _ _ (minusNeighbourDiag_mulSingle_succ k x) fun l => ?_
    have hcol : (fun s => (P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) F) s l) =
        minusW E (by omega) l := funext fun s => hP s l
    rw [hcol]
    exact minusChain_mulVec_minusW E hr hirr φ hE k x l
  intro t ht
  refine ⟨hmem t ht, ?_⟩
  have h := DFunLike.congr_fun key (Fin.tail t)
  have hTt : T (Fin.tail t) = ⟨_, hmem t ht⟩ := by
    apply Subtype.ext
    change hF.torus E (consOneHom (Fin.tail t)) = _
    rw [consOneHom_tail ht]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [hTt, consOneHom_tail ht] at h
  exact h

end Eigen

theorem omegaMinusTwoEnnolaModelInput_holds : OmegaMinusTwoEnnolaModelInput := by
  intro r hr K _ _ _ b c hirr hK2 F _ _ _ hF σ hσ k₀ _ hσk φ
  have hone : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by
    have := Fintype.ofFinite K
    have h := FiniteField.pow_card x
    rw [Fintype.card_eq_nat_card, hK2, _root_.sq] at h
    exact mul_left_cancel₀ hx (by rw [h, mul_one])
  obtain rfl : b = 1 := hone b (coeff_ne_zero_of_irreducible' hirr)
  obtain rfl : c = 1 := hone c (fun h0 => hirr 0 (by rw [h0]; ring))
  obtain ⟨E, hE⟩ := exists_ennolaParam hK2 hF hσ hσk φ
  set hFr := isEnnolaFrame_minus (K := K) (by omega : 2 ≤ r) hirr
  refine ⟨hFr.torus E, map_rootParam_minusTorus E (by omega) hirr,
    fun k => hFr.exists_weyl E (Fin.cycleRange k), ?_, top_le_iSup_minusTorus E hr hirr⟩
  obtain ⟨g, hg, hgt⟩ := minus_chart E (by omega : 2 ≤ r) hirr φ hE
  exact ⟨g, hg, fun t ht => hgt t ht⟩

end CFSG.SeitzReduction.OmegaPilot
