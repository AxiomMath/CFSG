module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaPlus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaEigen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaMinusChart

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

section Chart

variable {K : Type} [Field K] [CharP K 2] [Finite K] {m : ℕ}

theorem plusAnisoPerpEquiv_apply (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x : plusAnisoPerp (K := K) m b c) (G : orthDerived (plusAnisoQuad K m b c))
    (hG : (G : (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K)) ∈
      stabSub (plusAnisoLeft m) (plusAnisoRight m))
    (hxG : (x : matrixProjectiveDerived (plusAnisoQuad K m b c)) = projHom _ G)
    (w : Fin (2 * (m + 1)) → K) (y : Fin (2 * (m + 1))) :
    ((plusAnisoPerpEquiv hm hirr x : orthDerived (coordinateQuadMinus (m + 1) K (by omega) b c)) :
        (Fin (2 * (m + 1)) → K) ≃ₗ[K] (Fin (2 * (m + 1)) → K)) w y =
      (G : (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K))
        (Function.extend (plusAnisoPerpCoord m) w 0) (plusAnisoPerpCoord m y) := by
  have hsymm : ((stabDerived (plusAnisoQuad K m b c) (plusAnisoLeft m)
      (plusAnisoRight m)).equivMapOfInjective (projHom _) (projHom_injective
        (isAnisoCoord_plusAnisoQuad (K := K) (m := m) hirr).exists_ne_zero)).symm x = ⟨G, hG⟩ :=
    (MulEquiv.symm_apply_eq _).mpr (Subtype.ext hxG)
  have e1 : plusAnisoPerpEquiv hm hirr x =
      orthDerivedCongr (plusAnisoPerpIsometry m b c)
        ((isAnisoCoord_plusAnisoQuad (K := K) (m := m) hirr).stabDerivedEquiv
          (regular_plusAnisoQuad (coeff_ne_zero_of_irreducible' hirr) (by omega)).1
          (regular_plusAnisoPerp hm hirr).1 (regular_plusAnisoPerp hm hirr).2 ⟨G, hG⟩) := by
    rw [← hsymm]
    rfl
  rw [e1, orthDerivedCongr_apply]
  rfl

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem plusChain_entry (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    {k₀ : Subfield F} [CharP k₀ 2] (φ : K ≃+* k₀) (x : plusAnisoPerp (K := K) m 1 1)
    (G : orthDerived (plusAnisoQuad K m 1 1))
    (hG : (G : (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K)) ∈
      stabSub (plusAnisoLeft m) (plusAnisoRight m))
    (hxG : (x : matrixProjectiveDerived (plusAnisoQuad K m 1 1)) = projHom _ G) :
    ∃ B : matrixDerived (coordinateQuadMinus (m + 1) F (by omega) ((φ 1 : k₀) : F)
        ((φ 1 : k₀) : F)),
      incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ 1) (φ 1))
          (plusAnisoPerpModelFieldEquiv hm hirr φ x) = matrixProjectiveProjection _ B ∧
        ∀ i j, (B : GL (Fin (2 * (m + 1))) F).val i j =
          ((φ ((G : (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K))
            (Pi.single (plusAnisoPerpCoord m j) 1) (plusAnisoPerpCoord m i)) : k₀) : F) := by
  set X := plusAnisoPerpEquiv hm hirr x with hX
  set A := (derivedEquiv (coordinateQuadMinus (m + 1) K (by omega) 1 1)).symm X with hA
  have hBmem : glCongr φ (A : GL (Fin (2 * (m + 1))) K) ∈
      matrixDerived (coordinateQuadMinus (m + 1) k₀ (by omega) (φ 1) (φ 1)) := by
    rw [← map_matrixDerived_glCongr φ (coordinateQuadMinus_comp_ringEquiv φ (by omega) 1 1)]
    exact ⟨_, A.2, rfl⟩
  set B : matrixDerived (coordinateQuadMinus (m + 1) k₀ (by omega) (φ 1) (φ 1)) := ⟨_, hBmem⟩
    with hB
  have h1 : plusAnisoPerpModelFieldEquiv hm hirr φ x =
      minusCongr φ (by omega) 1 1 (matrixProjectiveProjection _ A) := rfl
  have h2 : minusCongr φ (by omega : 1 ≤ m + 1) 1 1 (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ B :=
    matrixProjectiveCongr_mk φ _ A B rfl
  refine ⟨inclHom k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ 1) (φ 1)) B,
    by rw [h1, h2, incl_mk], fun i j => ?_⟩
  rw [inclHom_val, glIncl_val, Matrix.map_apply]
  change ((((glCongr φ (A : GL (Fin (2 * (m + 1))) K) : GL (Fin (2 * (m + 1))) k₀) :
    Matrix _ _ k₀) i j : k₀) : F) = _
  rw [glCongr_coe, Matrix.map_apply, hA, derivedEquiv_symm_entry, hX,
    plusAnisoPerpEquiv_apply hm hirr x G hG hxG, extend_single_eq plusAnisoPerpCoord_injective]

variable (m) in
@[expose] noncomputable def plusCoord (s : Fin (m + 1) ⊕ Fin (m + 1)) : Fin (2 * (m + 2)) :=
  plusAnisoPerpCoord m (plusIndexEquiv (m + 1) s)

theorem plusCoord_injective : Function.Injective (plusCoord m) :=
  plusAnisoPerpCoord_injective.comp (plusIndexEquiv (m + 1)).injective

theorem eq_sum_plusCoord {v : Fin (2 * (m + 2)) → K}
    (hv : v ∈ perpSub K (plusAnisoLeft m) (plusAnisoRight m)) :
    v = ∑ j, v (plusCoord m j) • Pi.single (plusCoord m j) 1 := by
  funext t
  rw [Finset.sum_apply]
  by_cases ht : ∃ j, plusCoord m j = t
  · obtain ⟨j, rfl⟩ := ht
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [Pi.single_apply, (plusCoord_injective (m := m)).eq_iff, hj']
    · simp
  · have h0 : v t = 0 := by
      by_cases h1 : t = plusAnisoLeft m
      · rw [h1]
        exact hv.1
      by_cases h2 : t = plusAnisoRight m
      · rw [h2]
        exact hv.2
      obtain ⟨x, hx⟩ := exists_plusAnisoPerpCoord_eq h1 h2
      exact absurd ⟨(plusIndexEquiv (m + 1)).symm x, by
        rw [plusCoord, Equiv.apply_symm_apply, hx]⟩ ht
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => ht ⟨j, h.symm⟩), smul_zero]

theorem extend_plusAnisoPerpCoord_eq {v : Fin (2 * (m + 2)) → K}
    (hv : v ∈ perpSub K (plusAnisoLeft m) (plusAnisoRight m)) :
    Function.extend (plusAnisoPerpCoord m) (v ∘ plusAnisoPerpCoord m) 0 = v := by
  funext t
  by_cases ht : ∃ x, plusAnisoPerpCoord m x = t
  · obtain ⟨x, rfl⟩ := ht
    rw [plusAnisoPerpCoord_injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ ht]
    by_cases h1 : t = plusAnisoLeft m
    · rw [h1]
      exact hv.1.symm
    by_cases h2 : t = plusAnisoRight m
    · rw [h2]
      exact hv.2.symm
    exact absurd (exists_plusAnisoPerpCoord_eq h1 h2) ht

variable (E : EnnolaParam K F)

variable (m) in
@[expose] noncomputable def plusJ : (Fin (2 * (m + 2)) → K) →+ (Fin (m + 1) ⊕ Fin (m + 1) → F) where
  toFun v s := E.ι (v (plusCoord m s))
  map_zero' := by
    funext s
    simp
  map_add' v w := by
    funext s
    simp

theorem plusJ_apply (v : Fin (2 * (m + 2)) → K) (s : Fin (m + 1) ⊕ Fin (m + 1)) :
    plusJ m E v s = E.ι (v (plusCoord m s)) := rfl

theorem plusJ_smul (c : K) (v : Fin (2 * (m + 2)) → K) :
    plusJ m E (c • v) = E.ι c • plusJ m E v := by
  funext s
  simp [plusJ_apply]

variable (m) in
@[expose] noncomputable def plusQ₂ (β γ : F) : QuadraticForm F (Fin (m + 1) ⊕ Fin (m + 1) → F) :=
  (coordinateQuadMinus (m + 1) F (by omega) β γ).comp
    (LinearMap.funLeft F F (plusIndexEquiv (m + 1)).symm)

theorem plusQ₂_apply (β γ : F) (u : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    plusQ₂ m β γ u = coordinateQuadMinus (m + 1) F (by omega) β γ
      (u ∘ (plusIndexEquiv (m + 1)).symm) := rfl

theorem coordinateQuadMinus_comp_ringHom {n : ℕ} (hn : 1 ≤ n) (w : Fin (2 * n) → K) :
    coordinateQuadMinus n F hn (E.ι 1) (E.ι 1) (E.ι ∘ w) =
      E.ι (coordinateQuadMinus n K hn 1 1 w) := by
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp only [Function.comp_apply, map_add, map_mul, map_sum, map_pow]

theorem plusQ₂_plusJ {β γ : F} (hβ : β = E.ι 1) (hγ : γ = E.ι 1) {v : Fin (2 * (m + 2)) → K}
    (hv : v ∈ perpSub K (plusAnisoLeft m) (plusAnisoRight m)) :
    plusQ₂ m β γ (plusJ m E v) = E.ι (plusAnisoQuad K m 1 1 v) := by
  have h1 : (plusJ m E v) ∘ (plusIndexEquiv (m + 1)).symm = E.ι ∘ (v ∘ plusAnisoPerpCoord m) := by
    funext c
    simp [plusJ_apply, plusCoord]
  rw [plusQ₂_apply, h1, hβ, hγ, coordinateQuadMinus_comp_ringHom, ← plusAnisoQuad_extend_perp,
    extend_plusAnisoPerpCoord_eq hv]

@[expose] noncomputable def plusStated {k₀ : Subfield F} (φ : K ≃+* k₀)
    (G : (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K)) :
    Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F :=
  Matrix.of fun s s' => ((φ (G (Pi.single (plusCoord m s') 1) (plusCoord m s)) : k₀) : F)

theorem plusStated_mulVec_plusJ {k₀ : Subfield F} (φ : K ≃+* k₀)
    (hE : ∀ p, E.ι p = ((φ p : k₀) : F))
    (G : (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K)) {v : Fin (2 * (m + 2)) → K}
    (hv : v ∈ perpSub K (plusAnisoLeft m) (plusAnisoRight m)) :
    plusStated φ G *ᵥ plusJ m E v = plusJ m E (G v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, plusStated, Matrix.of_apply, plusJ_apply, ← hE,
    ← map_mul, ← map_sum]
  congr 1
  conv_rhs => rw [eq_sum_plusCoord hv]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

end Chart

section HypPair

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {N : ℕ}
  {e f : ℕ → Fin d → K}

@[expose] noncomputable def hypPairA (e f : ℕ → Fin d → K) (N k : ℕ) : Fin d → K :=
  if 2 * (k / 2) + 1 < N then blockVec e f k else e k

@[expose] noncomputable def hypPairB (e f : ℕ → Fin d → K) (N k : ℕ) : Fin d → K :=
  if 2 * (k / 2) + 1 < N then blockVec' e f k else f k

theorem hypPairA_of_block {k : ℕ} (h : 2 * (k / 2) + 1 < N) :
    hypPairA e f N k = blockVec e f k := by
  simp only [hypPairA, h, ↓reduceIte]

theorem hypPairB_of_block {k : ℕ} (h : 2 * (k / 2) + 1 < N) :
    hypPairB e f N k = blockVec' e f k := by
  simp only [hypPairB, h, ↓reduceIte]

namespace IsHypSystem

variable (hS : IsHypSystem Q N e f)
include hS

theorem isUnitPlane_hypPair {k : ℕ} (h : 2 * (k / 2) + 1 < N) :
    IsUnitPlane Q (hypPairA e f N k) (hypPairB e f N k) := by
  rw [hypPairA_of_block h, hypPairB_of_block h]
  exact hS.isUnitPlane_blockVec h

theorem hyp_hypPair {k : ℕ} (hk : k < N) (h : ¬2 * (k / 2) + 1 < N) :
    Q (hypPairA e f N k) = 0 ∧ Q (hypPairB e f N k) = 0 ∧
      polar Q (hypPairA e f N k) (hypPairB e f N k) = 1 := by
  simp only [hypPairA, hypPairB, h, ↓reduceIte]
  exact ⟨hS.map_e k, hS.map_f k, hS.ef_self k hk⟩

theorem polar_hypPair_of_perp (k : ℕ) {w : Fin d → K}
    (hw : ∀ l, polar Q w (e l) = 0 ∧ polar Q w (f l) = 0) :
    polar Q w (hypPairA e f N k) = 0 ∧ polar Q w (hypPairB e f N k) = 0 := by
  unfold hypPairA hypPairB
  split_ifs
  · exact hS.polar_blockVec_of_perp k fun l _ => hw l
  · exact hw k

theorem polar_hypPair_ne {k k' : ℕ} (hk : k < N) (hk' : k' < N) (hne : k ≠ k') :
    polar Q (hypPairA e f N k) (hypPairA e f N k') = 0 ∧
      polar Q (hypPairA e f N k) (hypPairB e f N k') = 0 ∧
      polar Q (hypPairB e f N k) (hypPairA e f N k') = 0 ∧
      polar Q (hypPairB e f N k) (hypPairB e f N k') = 0 := by
  unfold hypPairA hypPairB
  by_cases h : 2 * (k / 2) + 1 < N <;> by_cases h' : 2 * (k' / 2) + 1 < N
  · simp only [h, h', ↓reduceIte]
    obtain ⟨a1, a2, a3⟩ := hS.polar_blockVec_ne h hne
    obtain ⟨-, b2, -⟩ := hS.polar_blockVec_ne h' (Ne.symm hne)
    exact ⟨a1, a2, by rw [polar_comm]; exact b2, a3⟩
  · simp only [h, h', ↓reduceIte]
    obtain ⟨a1, a2, a3, a4⟩ := hS.polar_blockVec_of_ne k (l := k') (by omega) (by omega)
    exact ⟨a1, a2, a3, a4⟩
  · simp only [h, h', ↓reduceIte]
    obtain ⟨a1, a2, a3, a4⟩ := hS.polar_blockVec_of_ne k' (l := k) (by omega) (by omega)
    exact ⟨by rw [polar_comm]; exact a1, by rw [polar_comm]; exact a3,
      by rw [polar_comm]; exact a2, by rw [polar_comm]; exact a4⟩
  · exact absurd (by omega : k = k') hne

end IsHypSystem

end HypPair

section PlusPairs

variable {K : Type} [Field K] [CharP K 2] [Finite K] {m : ℕ}

variable (K m) in
@[expose] noncomputable def plusPairA : Fin (m + 1) → Fin (2 * (m + 2)) → K :=
  Fin.cases (Pi.single (plusIndexEquiv (m + 2) (.inl 1)) 1) fun i : Fin m =>
    hypPairA (plusHypE (K := K) (m := m)) plusHypF m i

variable (K m) in
@[expose] noncomputable def plusPairB : Fin (m + 1) → Fin (2 * (m + 2)) → K :=
  Fin.cases (Pi.single (plusIndexEquiv (m + 2) (.inr 1)) 1) fun i : Fin m =>
    hypPairB (plusHypE (K := K) (m := m)) plusHypF m i

variable (m) in
@[expose] def plusPairUnit : Fin (m + 1) → Bool :=
  Fin.cases true fun i : Fin m => decide (2 * (i.val / 2) + 1 < m)

theorem plusHyp_mem_perp (l : ℕ) :
    plusHypE (K := K) (m := m) l ∈ perpSub K (plusAnisoLeft m) (plusAnisoRight m) ∧
      plusHypF (K := K) (m := m) l ∈ perpSub K (plusAnisoLeft m) (plusAnisoRight m) := by
  by_cases h : l < m
  · rw [plusHypE_of_lt h, plusHypF_of_lt h]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> exact Pi.single_eq_of_ne (plusIndex_ne (by simp)) _
  · rw [plusHypE_of_not_lt h, plusHypF_of_not_lt h]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩

theorem blockVec_plus_mem_perp (i : ℕ) :
    blockVec (plusHypE (K := K) (m := m)) plusHypF i ∈
        perpSub K (plusAnisoLeft m) (plusAnisoRight m) ∧
      blockVec' (plusHypE (K := K) (m := m)) plusHypF i ∈
        perpSub K (plusAnisoLeft m) (plusAnisoRight m) := by
  have h1 := plusHyp_mem_perp (K := K) (m := m) (2 * (i / 2))
  have h2 := plusHyp_mem_perp (K := K) (m := m) (2 * (i / 2) + 1)
  unfold blockVec blockVec'
  split_ifs
  · exact ⟨Submodule.add_mem _ h1.1 h1.2, Submodule.add_mem _ (Submodule.add_mem _ h1.2 h2.1) h2.2⟩
  · exact ⟨Submodule.add_mem _ (Submodule.add_mem _ h1.1 h1.2) h2.2, Submodule.add_mem _ h2.1 h2.2⟩

theorem plusPair_mem (k : Fin (m + 1)) :
    plusPairA K m k ∈ perpSub K (plusAnisoLeft m) (plusAnisoRight m) ∧
      plusPairB K m k ∈ perpSub K (plusAnisoLeft m) (plusAnisoRight m) := by
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · simp only [plusPairA, plusPairB, Fin.cases_zero]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      exact Pi.single_eq_of_ne (plusIndex_ne (by simp [fin_one_ne_zero'.symm])) _
  · simp only [plusPairA, plusPairB, Fin.cases_succ, hypPairA, hypPairB]
    split_ifs
    · exact blockVec_plus_mem_perp _
    · exact plusHyp_mem_perp _

variable {F : Type} [Field F] [Finite F] [CharP F 2] (E : EnnolaParam K F)

@[expose] noncomputable def plusPairData (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) {k₀ : Subfield F}
    (φ : K ≃+* k₀) (hE : ∀ p, E.ι p = ((φ p : k₀) : F)) :
    EnnolaPairData (plusAnisoQuad K m 1 1) E m (plusQ₂ m ((φ 1 : k₀) : F) ((φ 1 : k₀) : F))
      (perpSub K (plusAnisoLeft m) (plusAnisoRight m)) where
  pa := plusPairA K m
  pb := plusPairB K m
  unit := plusPairUnit m
  pa_mem k := (plusPair_mem k).1
  pb_mem k := (plusPair_mem k).2
  unit_plane k hk := by
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · simp only [plusPairA, plusPairB, Fin.cases_zero]
      exact (isAnisoCoord_plusAnisoQuad_one (K := K) (m := m) hirr).isUnitPlane
    · simp only [plusPairUnit, Fin.cases_succ, decide_eq_true_eq] at hk
      simp only [plusPairA, plusPairB, Fin.cases_succ]
      exact (isHypSystem_plus (K := K) (m := m) 1 1).isUnitPlane_hypPair hk
  hyp k hk := by
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · simp [plusPairUnit] at hk
    · simp only [plusPairUnit, Fin.cases_succ, decide_eq_false_iff_not] at hk
      simp only [plusPairA, plusPairB, Fin.cases_succ]
      exact (isHypSystem_plus (K := K) (m := m) 1 1).hyp_hypPair i.2 hk
  orth k k' hkk := by
    have hS := isHypSystem_plus (K := K) (m := m) 1 1
    have h1 := polar_aniso_plusHyp (isAnisoCoord_plusAnisoQuad_one (K := K) (m := m) hirr)
      (fun j => fin_succ_succ_ne_one j)
    have hx := fun i : ℕ => hS.polar_hypPair_of_perp i (w := Pi.single
      (plusIndexEquiv (m + 2) (.inl 1)) 1) fun l => (h1 l).1
    have hy := fun i : ℕ => hS.polar_hypPair_of_perp i (w := Pi.single
      (plusIndexEquiv (m + 2) (.inr 1)) 1) fun l => (h1 l).2
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ k' with rfl | ⟨i', rfl⟩
    · exact absurd rfl hkk
    · simp only [plusPairA, plusPairB, Fin.cases_zero, Fin.cases_succ]
      exact ⟨(hx i').1, (hx i').2, (hy i').1, (hy i').2⟩
    · simp only [plusPairA, plusPairB, Fin.cases_zero, Fin.cases_succ]
      exact ⟨by rw [polar_comm]; exact (hx i).1, by rw [polar_comm]; exact (hy i).1,
        by rw [polar_comm]; exact (hx i).2, by rw [polar_comm]; exact (hy i).2⟩
    · simp only [plusPairA, plusPairB, Fin.cases_succ]
      exact hS.polar_hypPair_ne i.2 i'.2 fun h => hkk (by rw [Fin.ext h])
  J := plusJ m E
  J_smul := plusJ_smul E
  quad_J v hv := plusQ₂_plusJ E (by rw [hE, map_one]) (by rw [hE, map_one]) hv

end PlusPairs

section PlusLink

variable {K : Type} [Field K] [CharP K 2] [Finite K] {m' : ℕ}

theorem plusPairA_castSucc (k : Fin (m' + 1)) :
    plusPairA K (m' + 1) k.castSucc = plusFrameA m' k.succ := by
  rw [plusFrameA_succ]
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · simp only [Fin.castSucc_zero, plusPairA, Fin.cases_zero, Fin.cons_zero]
  · rw [Fin.castSucc_succ, Fin.cons_succ]
    simp only [plusPairA, Fin.cases_succ, Fin.val_castSucc]
    exact hypPairA_of_block (by omega)

theorem plusPairB_castSucc (k : Fin (m' + 1)) :
    plusPairB K (m' + 1) k.castSucc = plusFrameA' m' k.succ := by
  rw [plusFrameA'_succ]
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · simp only [Fin.castSucc_zero, plusPairB, Fin.cases_zero, Fin.cons_zero]
  · rw [Fin.castSucc_succ, Fin.cons_succ]
    simp only [plusPairB, Fin.cases_succ, Fin.val_castSucc]
    exact hypPairB_of_block (by omega)

theorem plusPairUnit_castSucc (k : Fin (m' + 1)) : plusPairUnit (m' + 1) k.castSucc = true := by
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · rfl
  · rw [Fin.castSucc_succ]
    simp only [plusPairUnit, Fin.cases_succ, Fin.val_castSucc, decide_eq_true_eq]
    omega

variable {F : Type} [Field F] [Finite F] [CharP F 2] (E : EnnolaParam K F)

theorem plus_rotOmega_mem_stabSub (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) (k : Fin (m' + 1))
    (x : Fˣ) :
    (((isEnnolaFrame_plus (m' := m') hirr).rotOmega E k.succ x : orthDerived _) :
      (Fin (2 * (m' + 1 + 2)) → K) ≃ₗ[K] (Fin (2 * (m' + 1 + 2)) → K)) ∈
      stabSub (plusAnisoLeft (m' + 1)) (plusAnisoRight (m' + 1)) := by
  set hF := isEnnolaFrame_plus (m' := m') hirr
  have h0 : (0 : Fin (m' + 2)) ≠ k.succ := (Fin.succ_ne_zero k).symm
  refine ⟨?_, ?_⟩
  · rw [IsEnnolaFrame.coe_rotOmega]
    have := E.rotHom_of_perp (hF.unit k.succ) x (hF.orth_aa 0 k.succ h0) (hF.orth_aa' 0 k.succ h0)
    rwa [plusFrameA_zero] at this
  · rw [IsEnnolaFrame.coe_rotOmega]
    have := E.rotHom_of_perp (hF.unit k.succ) x (hF.orth_a'a h0) (hF.orth_a'a' 0 k.succ h0)
    rwa [plusFrameA'_zero] at this

theorem plus_rotOmega_mem_plusAnisoPerp (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    (k : Fin (m' + 1)) (x : Fˣ) :
    projHom _ ((isEnnolaFrame_plus (m' := m') hirr).rotOmega E k.succ x) ∈
      plusAnisoPerp (K := K) (m' + 1) 1 1 :=
  ⟨_, mem_subgroupOf.2 (plus_rotOmega_mem_stabSub E hirr k x), rfl⟩

variable (F) in
@[expose] noncomputable def plusReindexGL (m : ℕ) :
    GL (Fin (2 * (m + 1))) F ≃* GL (Fin (m + 1) ⊕ Fin (m + 1)) F :=
  Units.mapEquiv (Matrix.reindexAlgEquiv F F (plusIndexEquiv (m + 1)).symm).toMulEquiv

theorem plusReindexGL_apply {m : ℕ} (A : GL (Fin (2 * (m + 1))) F) (i j : Fin (m + 1) ⊕ Fin (m + 1)) :
    (plusReindexGL F m A : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) i j =
      (A : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) F) (plusIndexEquiv (m + 1) i)
        (plusIndexEquiv (m + 1) j) := by
  simp [plusReindexGL, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem plusReindexGL_mulVec {m : ℕ} (A : GL (Fin (2 * (m + 1))) F) (v : Fin (2 * (m + 1)) → F) :
    (plusReindexGL F m A : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) *ᵥ
        (v ∘ plusIndexEquiv (m + 1)) =
      ((A : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) F) *ᵥ v) ∘ plusIndexEquiv (m + 1) := by
  have h : (plusReindexGL F m A : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) =
      (A : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) F).submatrix (plusIndexEquiv (m + 1))
        (plusIndexEquiv (m + 1)) := by
    ext i j
    rw [plusReindexGL_apply, Matrix.submatrix_apply]
  rw [h, Matrix.submatrix_mulVec_equiv]
  congr 2
  funext c
  simp

end PlusLink

section PlusMain

variable {K : Type} [Field K] [CharP K 2] [Finite K] {m' : ℕ} {F : Type} [Field F] [Finite F]
  [CharP F 2] (E : EnnolaParam K F)

theorem plus_chart (hm' : 3 ≤ m') (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) {k₀ : Subfield F}
    [CharP k₀ 2] (φ : K ≃+* k₀) (hE : ∀ p, E.ι p = ((φ p : k₀) : F)) :
    ∃ ρ : matrixProjectiveDerived (coordinateQuadMinus (m' + 1 + 1) F (by omega)
        ((φ 1 : k₀) : F) ((φ 1 : k₀) : F)) ≃* StatedOmega (StatedQuadPlus (m' + 1 + 1) F),
      ∀ t : Fin (m' + 1 + 1) → Fˣ, t 0 = 1 →
        ∃ hD : (isEnnolaFrame_plus (m' := m') hirr).torus E t ∈
            plusAnisoPerp (K := K) (m' + 1) 1 1,
          ((ρ (incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ 1) (φ 1))
              (plusAnisoPerpModelFieldEquiv (by omega) hirr φ ⟨_, hD⟩)) :
              StatedOmega (StatedQuadPlus (m' + 1 + 1) F)) :
              GL (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) =
            minusNeighbourDiag (RingHom.id F) 0 t := by
  set hF := isEnnolaFrame_plus (m' := m') hirr with hFdef
  set D := plusPairData (m := m' + 1) E hirr φ hE with hDdef
  obtain ⟨P, hPcol, hPiso⟩ := exists_gl_of_hypBasis' _ D.w D.quad_w D.polar_w
  set S : GL (Fin (2 * (m' + 1 + 1))) F := (plusReindexGL F (m' + 1)).symm P⁻¹ with hSdef
  have hRS : plusReindexGL F (m' + 1) S = P⁻¹ := MulEquiv.apply_symm_apply _ _
  have hS : ∀ v, coordinateQuadPlus (m' + 1 + 1) F
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso S v) =
      ((1 : Fˣ) : F) * coordinateQuadMinus (m' + 1 + 1) F (by omega) ((φ 1 : k₀) : F)
        ((φ 1 : k₀) : F) v := by
    intro v
    rw [Units.val_one, one_mul]
    change coordinateQuadPlus (m' + 1 + 1) F ((S : Matrix _ _ F) *ᵥ v) = _
    have h1 : coordinateQuadPlus (m' + 1 + 1) F ((S : Matrix _ _ F) *ᵥ v) =
        StatedQuadPlus (m' + 1 + 1) F (((S : Matrix _ _ F) *ᵥ v) ∘ plusIndexEquiv (m' + 1 + 1)) := by
      rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus_apply]
      rfl
    rw [h1, ← plusReindexGL_mulVec, hRS]
    have h2 := hPiso ((P⁻¹ : GL _ F) *ᵥ (v ∘ plusIndexEquiv (m' + 1 + 1)))
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h2
    rw [← h2, plusQ₂_apply]
    congr 1
    funext c
    simp
  set ρ := (CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv _ _ S 1
    hS).trans (statedOmegaPlusEquiv F (m' + 1 + 1) (by omega)).symm with hρ
  refine ⟨ρ, ?_⟩
  have hmem : ∀ t : Fin (m' + 1 + 1) → Fˣ, t 0 = 1 →
      hF.torus E t ∈ plusAnisoPerp (K := K) (m' + 1) 1 1 := by
    intro t ht
    have h := hF.torus_mem_fixVecBar E ht
    rw [plusFrameA_zero, plusFrameA'_zero, ← pairPerpOf_eq_fixVecBar] at h
    exact h
  set Ch : plusAnisoPerp (K := K) (m' + 1) 1 1 →* GL (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F :=
    (StatedOmega (StatedQuadPlus (m' + 1 + 1) F)).subtype.comp
      (ρ.toMonoidHom.comp ((incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega)
        (φ 1) (φ 1))).comp (plusAnisoPerpModelFieldEquiv (by omega) hirr φ).toMonoidHom)) with hCh
  set T : (Fin (m' + 1) → Fˣ) →* plusAnisoPerp (K := K) (m' + 1) 1 1 :=
    ((hF.torus E).comp consOneHom).codRestrict _
      (fun u => hmem _ (by rw [consOneHom_apply, Fin.cons_zero])) with hTdef
  have key : Ch.comp T = (minusNeighbourDiag (RingHom.id F) 0).comp consOneHom := by
    refine MonoidHom.pi_ext fun k x => ?_
    have hT : T (Pi.mulSingle k x) = ⟨_, plus_rotOmega_mem_plusAnisoPerp E hirr k x⟩ := by
      apply Subtype.ext
      change hF.torus E (consOneHom (Pi.mulSingle k x)) = _
      rw [consOneHom_mulSingle, hF.torus_mulSingle]
    simp only [MonoidHom.comp_apply]
    rw [hT, consOneHom_mulSingle]
    set G := hF.rotOmega E k.succ x with hG
    obtain ⟨B, hBmk, hBent⟩ := plusChain_entry (m := m' + 1) (F := F) (by omega) hirr φ
      ⟨_, plus_rotOmega_mem_plusAnisoPerp E hirr k x⟩ G (plus_rotOmega_mem_stabSub E hirr k x) rfl
    obtain ⟨C, hC⟩ := CFSG.RankThree.PartOne.KCOrthogonalDescent.exists_conj_mem_matrixDerived _ _
      S 1 hS B
    have hChv : Ch ⟨_, plus_rotOmega_mem_plusAnisoPerp E hirr k x⟩ =
        (((statedDerivedPlusEquiv F (m' + 1 + 1)).symm C : StatedOmega (StatedQuadPlus (m' + 1 + 1) F)) :
          GL (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) := by
      rw [hCh]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [hBmk, hρ, MulEquiv.trans_apply,
        CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv_mk _ _ S 1 hS B C hC]
      congr 1
      rw [MulEquiv.symm_apply_eq]
      simp only [statedOmegaPlusEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
    rw [hChv]
    set M := plusReindexGL F (m' + 1) (B : GL (Fin (2 * (m' + 1 + 1))) F) with hM
    have hMv : (M : Matrix (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) =
        plusStated φ (G.1 : (Fin (2 * (m' + 1 + 2)) → K) ≃ₗ[K] (Fin (2 * (m' + 1 + 2)) → K)) := by
      ext i j
      rw [hM, plusReindexGL_apply, hBent]
      rfl
    have hpa : D.pa k.castSucc = plusFrameA m' k.succ := plusPairA_castSucc k
    have hpb : D.pb k.castSucc = plusFrameA' m' k.succ := plusPairB_castSucc k
    have heig : ∀ l, (M : Matrix (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1))
        (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) *ᵥ (fun s => (P : Matrix (Fin (m' + 1 + 1) ⊕
          Fin (m' + 1 + 1)) (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) s l) =
        SymplecticPilot.diagSpEntry (Pi.mulSingle k.castSucc x) l • fun s =>
          (P : Matrix (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F)
            s l := by
      intro l
      have hcol : (fun s => (P : Matrix (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1))
          (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) s l) = D.w l := funext fun s => hPcol s l
      rw [hcol, hMv]
      refine D.mulVec_w (G.1 : (Fin (2 * (m' + 1 + 2)) → K) ≃ₗ[K] (Fin (2 * (m' + 1 + 2)) → K)).toLinearMap
        k.castSucc (plusPairUnit_castSucc k) x ?_ ?_ ?_ _
        (fun v hv => plusStated_mulVec_plusJ E φ hE _ hv) l
      · simp only [LinearEquiv.coe_coe]
        rw [hpa, hpb, hG, IsEnnolaFrame.coe_rotOmega, E.rotHom_left]
      · simp only [LinearEquiv.coe_coe]
        rw [hpa, hpb, hG, IsEnnolaFrame.coe_rotOmega, E.rotHom_right]
      · intro k' hk'
        have ho := D.orth k' k.castSucc hk'
        rw [hpa, hpb] at ho
        simp only [LinearEquiv.coe_coe]
        rw [hG, IsEnnolaFrame.coe_rotOmega]
        exact ⟨E.rotHom_of_perp (hF.unit k.succ) x ho.1 ho.2.1,
          E.rotHom_of_perp (hF.unit k.succ) x ho.2.2.1 ho.2.2.2⟩
    have hconj := inv_mul_mul_eq_of_eigen P M _ _ (minusNeighbourDiag_mulSingle_succ k x) heig
    have hRC : plusReindexGL F (m' + 1) (C : GL (Fin (2 * (m' + 1 + 1))) F) = P⁻¹ * M * P := by
      have hC' : (C : GL (Fin (2 * (m' + 1 + 1))) F) = S * (B : GL _ F) * S⁻¹ := hC
      rw [hC', map_mul, map_mul, map_inv, hRS, inv_inv]
    apply Units.ext
    ext i j
    rw [statedDerivedPlusEquiv_symm_entry, ← plusReindexGL_apply, hRC, hconj]
  intro t ht
  refine ⟨hmem t ht, ?_⟩
  have h := DFunLike.congr_fun key (Fin.tail t)
  have hTt : T (Fin.tail t) = ⟨_, hmem t ht⟩ := by
    apply Subtype.ext
    change hF.torus E (consOneHom (Fin.tail t)) = _
    rw [consOneHom_tail ht]
  simp only [MonoidHom.comp_apply] at h
  rw [hTt, consOneHom_tail ht] at h
  exact h

end PlusMain

theorem omegaPlusTwoEnnolaModelInput_holds : OmegaPlusTwoEnnolaModelInput := by
  intro m hm K _ _ _ b c hirr hK2 F _ _ _ hF σ hσ k₀ _ hσk φ
  have hone : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by
    have := Fintype.ofFinite K
    have h := FiniteField.pow_card x
    rw [Fintype.card_eq_nat_card, hK2, _root_.sq] at h
    exact mul_left_cancel₀ hx (by rw [h, mul_one])
  obtain rfl : b = 1 := hone b (coeff_ne_zero_of_irreducible' hirr)
  obtain rfl : c = 1 := hone c (fun h0 => hirr 0 (by rw [h0]; ring))
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨E, hE⟩ := exists_ennolaParam hK2 hF hσ hσk φ
  set hFr := isEnnolaFrame_plus (K := K) (m' := m') hirr
  refine ⟨hFr.torus E, map_rootParam_plusTorus E hirr,
    fun k => hFr.exists_weyl E (Fin.cycleRange k), ?_, top_le_iSup_plusTorus E (by omega) hirr⟩
  obtain ⟨ρ, hρ⟩ := plus_chart E (by omega : 3 ≤ m') hirr φ hE
  exact ⟨ρ, fun t ht => hρ t ht⟩

end CFSG.SeitzReduction.OmegaPilot
