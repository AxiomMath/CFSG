module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataOne
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldCTRecog
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.Quasithin (perfectCore)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL spIncl inclMat mat_leviEmbedSL)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear consecutiveBlock mem_consecutiveBlock)
open CFSG.SeitzReduction.SymplecticPilot (permSp siegelBlock diagSp mat_permSp liftParam)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] {m : ℕ}

theorem permMatrix_swap_apply (a b i j : Fin m) :
    (Equiv.swap a b).permMatrix F i j = if Equiv.swap a b i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem inclMat_swap (a b : Fin m) :
    inclMat (Equiv.swap a b : Fin m → Fin m) = (Equiv.swap a b).permMatrix F := by
  ext i j
  rw [permMatrix_swap_apply]
  simp only [inclMat, Matrix.of_apply]
  congr 1
  apply propext
  constructor
  · intro h
    rw [h, Equiv.swap_apply_self]
  · intro h
    rw [← h, Equiv.swap_apply_self]

variable [CharP F 2]

@[expose] noncomputable def q2SwapSL (a b : Fin m) : SL(m, F) :=
  ⟨(Equiv.swap a b).permMatrix F, by
    rw [det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap a b)) with h | h <;>
      simp [h, CharTwo.neg_eq]⟩

theorem q2SwapSL_mul_self (a b : Fin m) : q2SwapSL (F := F) a b * q2SwapSL a b = 1 := by
  apply Subtype.ext
  change (Equiv.swap a b).permMatrix F * (Equiv.swap a b).permMatrix F = 1
  rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]

theorem permSp_swap_eq (a b : Fin m) :
    permSp F (Equiv.swap a b) = leviEmbedSL F m (q2SwapSL a b) := by
  apply mat_injective
  rw [mat_permSp, mat_leviEmbedSL, spIncl, inclMat_swap]
  have hinv : (q2SwapSL (F := F) a b)⁻¹ = q2SwapSL a b :=
    inv_eq_of_mul_eq_one_right (q2SwapSL_mul_self a b)
  rw [hinv]
  change _ = fromBlocks ((Equiv.swap a b).permMatrix F) 0 0 ((Equiv.swap a b).permMatrix F)ᵀ
  rw [transpose_permMatrix, Equiv.swap_inv]

theorem q2SwapSL_mem_blockSpecialLinear (a b : Fin m) :
    q2SwapSL (F := F) a b ∈ blockSpecialLinear (K := F) ({a, b} : Finset (Fin m)) := by
  intro i j hij
  change (Equiv.swap a b).permMatrix F i j = (1 : Matrix (Fin m) (Fin m) F) i j
  rw [permMatrix_swap_apply, Matrix.one_apply]
  rcases hij with hi | hj
  · have hi' : i ≠ a ∧ i ≠ b := by simpa [not_or] using hi
    rw [Equiv.swap_apply_of_ne_of_ne hi'.1 hi'.2]
  · have hj' : j ≠ a ∧ j ≠ b := by simpa [not_or] using hj
    simp only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hj'.1 hj'.2]

theorem permSp_swap_mem_siegelBlockGL (a b : Fin m) :
    ((permSp F (Equiv.swap a b) : StatedSp m F) : GL (Fin m ⊕ Fin m) F) ∈
      siegelBlockGL F ({a, b} : Finset (Fin m)) :=
  ⟨permSp F (Equiv.swap a b), ⟨q2SwapSL a b, q2SwapSL_mem_blockSpecialLinear a b,
    (permSp_swap_eq a b).symm⟩, rfl⟩

omit [CharP F 2] in
theorem permSp_swap_mul_diagOmega_mul_inv (a b : Fin m) (u : Fin m → Fˣ) :
    ((permSp F (Equiv.swap a b) : StatedSp m F) : GL (Fin m ⊕ Fin m) F) * diagOmega F m u *
        ((permSp F (Equiv.swap a b) : StatedSp m F) : GL (Fin m ⊕ Fin m) F)⁻¹ =
      diagOmega F m (u ∘ Equiv.swap a b) := by
  have h := congrArg (fun x : StatedSp m F => (x : GL (Fin m ⊕ Fin m) F))
    (CFSG.SeitzReduction.SymplecticPilot.conj_permSp_diagSp (K := F) (Equiv.swap a b) u)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_diagSp_eq_diagOmega, Equiv.symm_swap] at h
  exact h

end Model

section Valued

variable {G : Type} [Group G] {F : Type} [Field F] {r : ℕ} {τ : (Fin (r + 1) → Fˣ) →* G}

structure Q2ValuedChart (τ : (Fin (r + 1) → Fˣ) →* G) (k : Fin (r + 1)) where
  chart : Q2FrameChart τ k
  mem : ∀ t : Fin (r + 1) → Fˣ, t k = 1 → τ t ∈ q2NbrCore τ k
  val : ∀ (t : Fin (r + 1) → Fˣ) (ht : t k = 1),
    ((chart.π ⟨τ t, mem t ht⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
      GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = minusNeighbourDiag (RingHom.id F) k t

@[expose] noncomputable def Q2ValuedChart.ofNormalized {k : Fin (r + 1)}
    (π : q2NbrCore τ k ≃* StatedOmega (StatedQuadPlus (r + 1) F))
    (hD : ∀ t : Fin (r + 1) → Fˣ, t k = 1 → τ t ∈ q2NbrCore τ k)
    (hnorm : ∀ (t : Fin (r + 1) → Fˣ) (ht : t k = 1),
      ((π ⟨τ t, hD t ht⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
        GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = minusNeighbourDiag (RingHom.id F) k t) :
    Q2ValuedChart τ k :=
  ⟨Q2FrameChart.ofNormalized π hD hnorm, hD, hnorm⟩

variable [Finite G]

theorem q2NbrCore_map_conj {k : Fin (r + 1)} {w : G}
    (hw : ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) :
    (q2NbrCore τ 0).map (MulAut.conj w).toMonoidHom = q2NbrCore τ k := by
  rw [q2NbrCore, q2FrameCore, F4Pilot.map_centralizerPerfectCore, map_conj_rootParam_zero hw]
  rfl

@[expose] noncomputable def q2ConjEquiv {k : Fin (r + 1)} {w : G}
    (hw : ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) : q2NbrCore τ 0 ≃* q2NbrCore τ k :=
  ((MulAut.conj w).subgroupMap (q2NbrCore τ 0)).trans
    (MulEquiv.subgroupCongr (q2NbrCore_map_conj hw))

theorem coe_q2ConjEquiv_symm {k : Fin (r + 1)} {w : G}
    (hw : ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) (y : q2NbrCore τ k) :
    (((q2ConjEquiv hw).symm y : q2NbrCore τ 0) : G) = w⁻¹ * y * w := by
  have h1 : (((q2ConjEquiv hw) ((q2ConjEquiv hw).symm y) : q2NbrCore τ k) : G) =
      w * ((q2ConjEquiv hw).symm y : G) * w⁻¹ := rfl
  rw [MulEquiv.apply_symm_apply] at h1
  rw [h1]
  group

theorem inv_mul_frame_mul_of_conj {k : Fin (r + 1)} {w : G}
    (hw : ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) (t : Fin (r + 1) → Fˣ) :
    w⁻¹ * τ t * w = τ (t ∘ (Fin.cycleRange k).symm) := by
  have h1 := hw (t ∘ (Fin.cycleRange k).symm)
  have h2 : (t ∘ (Fin.cycleRange k).symm) ∘ Fin.cycleRange k = t := by
    funext i
    simp
  rw [h2] at h1
  rw [← h1]
  group

@[expose] noncomputable def Q2ValuedChart.conj (V₀ : Q2ValuedChart τ 0) {k : Fin (r + 1)} {w : G}
    (hw : ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) : Q2ValuedChart τ k := by
  have hmem0 : ∀ t : Fin (r + 1) → Fˣ, t k = 1 →
      (t ∘ (Fin.cycleRange k).symm) 0 = 1 := fun t ht => by
    rw [Function.comp_apply, Fin.cycleRange_symm_zero]
    exact ht
  have hmem : ∀ t : Fin (r + 1) → Fˣ, t k = 1 → τ t ∈ q2NbrCore τ k := by
    intro t ht
    rw [← q2NbrCore_map_conj hw]
    refine ⟨τ (t ∘ (Fin.cycleRange k).symm), V₀.mem _ (hmem0 t ht), ?_⟩
    change w * τ (t ∘ (Fin.cycleRange k).symm) * w⁻¹ = τ t
    rw [← inv_mul_frame_mul_of_conj hw t]
    group
  refine Q2ValuedChart.ofNormalized ((q2ConjEquiv hw).symm.trans V₀.chart.π) hmem ?_
  intro t ht
  have hφ : (q2ConjEquiv hw).symm ⟨τ t, hmem t ht⟩ =
      ⟨τ (t ∘ (Fin.cycleRange k).symm), V₀.mem _ (hmem0 t ht)⟩ := by
    apply Subtype.ext
    rw [coe_q2ConjEquiv_symm]
    exact inv_mul_frame_mul_of_conj hw t
  change ((V₀.chart.π ((q2ConjEquiv hw).symm ⟨τ t, hmem t ht⟩) :
    StatedOmega (StatedQuadPlus (r + 1) F)) : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = _
  rw [hφ, V₀.val _ (hmem0 t ht), minusNeighbourDiag_zero_comp_cycleRange_symm]

end Valued

section Weyl

variable {G : Type} [Group G] {F : Type} [Field F] {r : ℕ} {τ : (Fin (r + 1) → Fˣ) →* G}

theorem castSuccPlanes_preimagePlanes_pair (k : Fin (r + 1)) (a b : Fin r) :
    castSuccPlanes (preimagePlanes k {k.succAbove a, k.succAbove b}) =
      {a.castSucc, b.castSucc} := by
  ext y
  rw [mem_castSuccPlanes, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [mem_preimagePlanes, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · left
      rw [Fin.succAbove_right_inj.1 h]
    · right
      rw [Fin.succAbove_right_inj.1 h]
  · rintro (rfl | rfl)
    · exact ⟨a, by rw [mem_preimagePlanes]; simp, rfl⟩
    · exact ⟨b, by rw [mem_preimagePlanes]; simp, rfl⟩

theorem restrictParam_comp_swap (k : Fin (r + 1)) (a b : Fin r) (s : Fin (r + 1) → Fˣ) :
    restrictParam k (s ∘ Equiv.swap (k.succAbove a) (k.succAbove b)) =
      restrictParam k s ∘ Equiv.swap a b := by
  funext i
  simp only [restrictParam_apply, Function.comp_apply]
  rw [(Fin.succAbove_right_injective (p := k)).swap_apply]

theorem snocOneParam_comp_swap_castSucc (a b : Fin r) (u : Fin r → Fˣ) :
    snocOneParam F r u ∘ Equiv.swap a.castSucc b.castSucc =
      snocOneParam F r (u ∘ Equiv.swap a b) := by
  funext x
  refine Fin.lastCases ?_ (fun i => ?_) x
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last a).symm
      (Fin.castSucc_ne_last b).symm, snocOneParam_last, snocOneParam_last]
  · rw [Function.comp_apply, (Fin.castSucc_injective r).swap_apply, snocOneParam_castSucc,
      snocOneParam_castSucc]
    rfl

theorem minusNeighbourDiag_comp_swap (k : Fin (r + 1)) (a b : Fin r) (s : Fin (r + 1) → Fˣ) :
    minusNeighbourDiag (RingHom.id F) k (s ∘ Equiv.swap (k.succAbove a) (k.succAbove b)) =
      diagOmega F (r + 1) (snocOneParam F r (liftParam (RingHom.id F) (restrictParam k s)) ∘
        Equiv.swap a.castSucc b.castSucc) := by
  rw [minusNeighbourDiag_apply, restrictParam_comp_swap, snocOneParam_comp_swap_castSucc]
  rfl

theorem mulSingle_comp_swap_q2 (i j : Fin (r + 1)) (v : Fˣ) :
    (Pi.mulSingle i v : Fin (r + 1) → Fˣ) ∘ Equiv.swap i j = Pi.mulSingle j v := by
  funext x
  simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_left]

theorem exists_weyl_mem_q2LevelCore [Finite G] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {k : Fin (r + 1)} (V : Q2ValuedChart τ k) {a b : Fin r} (hab : a ≠ b) :
    ∃ n ∈ q2LevelCore τ {k.succAbove a, k.succAbove b},
      ∀ s, n * τ s * n⁻¹ = τ (s ∘ Equiv.swap (k.succAbove a) (k.succAbove b)) := by
  set J : Finset (Fin (r + 1)) := {k.succAbove a, k.succAbove b} with hJ
  have hka : k ≠ k.succAbove a := (Fin.succAbove_ne k a).symm
  have hkb : k ≠ k.succAbove b := (Fin.succAbove_ne k b).symm
  have hkJ : k ∉ J := by
    rw [hJ, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hka, hkb⟩
  have hJ2 : 2 ≤ J.card := by
    rw [hJ, Finset.card_pair (fun h => hab (Fin.succAbove_right_injective h))]
  have hU := V.chart.map_levelCore hF hkJ hJ2
  rw [castSuccPlanes_preimagePlanes_pair] at hU
  set W : GL (Fin (r + 1) ⊕ Fin (r + 1)) F :=
    ((permSp F (Equiv.swap a.castSucc b.castSucc) : StatedSp (r + 1) F) :
      GL (Fin (r + 1) ⊕ Fin (r + 1)) F) with hW
  have hWU : W ∈ (((q2LevelCore τ J).subgroupOf (q2NbrCore τ k)).map
      V.chart.π.toMonoidHom).map (StatedOmega (StatedQuadPlus (r + 1) F)).subtype := by
    rw [hU]
    exact permSp_swap_mem_siegelBlockGL _ _
  obtain ⟨x, ⟨y, hy, hyx⟩, hxW⟩ := hWU
  have hπy : ((V.chart.π y : StatedOmega (StatedQuadPlus (r + 1) F)) :
      GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = W := by
    rw [← hxW, ← hyx]
    rfl
  refine ⟨(y : G), hy, fun s => ?_⟩
  set σ := Equiv.swap (k.succAbove a) (k.succAbove b) with hσ
  set c' : Fin (r + 1) → Fˣ := Pi.mulSingle k (s k) with hc'
  set s' : Fin (r + 1) → Fˣ := s * c'⁻¹ with hs'
  have hs'k : s' k = 1 := mul_mulSingle_inv_apply_self k s
  have hss : s = s' * c' := by rw [hs', inv_mul_cancel_right]
  have hσk : σ k = k := Equiv.swap_apply_of_ne_of_ne hka hkb
  have hs'σk : (s' ∘ σ) k = 1 := by rw [Function.comp_apply, hσk, hs'k]
  have hc'σ : c' ∘ σ = c' := by
    funext i
    simp only [hc', Function.comp_apply, Pi.mulSingle_apply]
    congr 1
    apply propext
    constructor
    · intro h
      rw [← hσk] at h
      exact σ.injective h
    · intro h
      rw [h, hσk]
  have hcX : τ c' ∈ (rootParam k).map τ := ⟨c', mulSingle_mem_rootParam k (s k), rfl⟩
  have hcomm : (y : G) * τ c' = τ c' * y :=
    (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ y.2) _ hcX).symm
  have hkey : (y : G) * τ s' * (y : G)⁻¹ = τ (s' ∘ σ) := by
    have h1 : V.chart.π (y * ⟨τ s', V.mem s' hs'k⟩ * y⁻¹) =
        V.chart.π ⟨τ (s' ∘ σ), V.mem _ hs'σk⟩ := by
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hπy, V.val s' hs'k, V.val (s' ∘ σ) hs'σk, hσ, minusNeighbourDiag_comp_swap,
        minusNeighbourDiag_apply, permSp_swap_mul_diagOmega_mul_inv]
    have h2 := congrArg Subtype.val (V.chart.π.injective h1)
    simpa using h2
  have hcomm' : τ c' * (y : G)⁻¹ = (y : G)⁻¹ * τ c' := by
    calc τ c' * (y : G)⁻¹ = (y : G)⁻¹ * ((y : G) * τ c') * (y : G)⁻¹ := by group
      _ = (y : G)⁻¹ * (τ c' * y) * (y : G)⁻¹ := by rw [hcomm]
      _ = (y : G)⁻¹ * τ c' := by group
  calc (y : G) * τ s * (y : G)⁻¹ = (y : G) * τ s' * (τ c' * (y : G)⁻¹) := by
        rw [hss, map_mul]
        group
    _ = (y : G) * τ s' * (y : G)⁻¹ * τ c' := by rw [hcomm']; group
    _ = τ (s' ∘ σ) * τ c' := by rw [hkey]
    _ = τ (s ∘ σ) := by
        rw [← map_mul]
        congr 1
        rw [hss]
        funext i
        simp only [Pi.mul_apply, Function.comp_apply]
        rw [← Function.comp_apply (f := c'), hc'σ]

theorem map_conj_q2NbrCore_of_weyl [Finite G] {i j : Fin (r + 1)} {n : G}
    (hn : ∀ s, n * τ s * n⁻¹ = τ (s ∘ Equiv.swap i j)) :
    (q2NbrCore τ i).map (MulAut.conj n).toMonoidHom = q2NbrCore τ j := by
  have hX : ((rootParam i).map τ).map (MulAut.conj n).toMonoidHom = (rootParam j).map τ := by
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩
      refine ⟨Pi.mulSingle j v, ⟨v, rfl⟩, ?_⟩
      change τ (Pi.mulSingle j v) = n * τ (Pi.mulSingle i v) * n⁻¹
      rw [hn, mulSingle_comp_swap_q2]
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨τ (Pi.mulSingle i v), ⟨Pi.mulSingle i v, ⟨v, rfl⟩, rfl⟩, ?_⟩
      change n * τ (Pi.mulSingle i v) * n⁻¹ = τ (Pi.mulSingle j v)
      rw [hn, mulSingle_comp_swap_q2]
  rw [q2NbrCore, q2FrameCore, F4Pilot.map_centralizerPerfectCore, hX]
  rfl

end Weyl

section Global

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G}

theorem consecutiveBlock_two_eq_pair_q2 {j : ℕ} (hj : j + 1 ≤ r) :
    consecutiveBlock (r + 1) j 2 = {(⟨j, by omega⟩ : Fin (r + 1)), ⟨j + 1, by omega⟩} := by
  ext x
  rw [mem_consecutiveBlock, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
  simp only
  omega

theorem exists_weyl_mem_q2Node (hr : 2 ≤ r) (hF : 4 ≤ Nat.card F) (C₀ : Q2FrameChart τ 0)
    (V₀ : Q2ValuedChart τ 0) (Vr : Q2ValuedChart τ (Fin.last r)) {j : ℕ} (hj : j + 1 ≤ r) :
    ∃ n ∈ q2Node C₀ ⟨j, by omega⟩, ∀ s, n * τ s * n⁻¹ =
      τ (s ∘ Equiv.swap (⟨j, by omega⟩ : Fin (r + 1)) ⟨j + 1, by omega⟩) := by
  rw [q2Node_of_le C₀ (j := ⟨j, by omega⟩) hj, consecutiveBlock_two_eq_pair_q2 hj]
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have h := exists_weyl_mem_q2LevelCore hF Vr (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩)
      (by simp [Fin.ext_iff])
    have ha : (Fin.last r).succAbove ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin (r + 1)) :=
      Fin.ext (by simp)
    have hb : (Fin.last r).succAbove ⟨1, by omega⟩ = (⟨0 + 1, by omega⟩ : Fin (r + 1)) :=
      Fin.ext (by simp)
    rw [ha, hb] at h
    exact h
  · have h := exists_weyl_mem_q2LevelCore hF V₀ (a := ⟨j - 1, by omega⟩) (b := ⟨j, by omega⟩)
      (by simp [Fin.ext_iff]; omega)
    have ha : (0 : Fin (r + 1)).succAbove ⟨j - 1, by omega⟩ = (⟨j, by omega⟩ : Fin (r + 1)) :=
      Fin.ext (by simp; omega)
    have hb : (0 : Fin (r + 1)).succAbove ⟨j, by omega⟩ = (⟨j + 1, by omega⟩ : Fin (r + 1)) :=
      Fin.ext (by simp)
    rw [ha, hb] at h
    exact h

theorem map_conj_le_of_mem_q2 {H A : Subgroup G} (hA : A ≤ H) {n : G} (hn : n ∈ H) :
    A.map (MulAut.conj n).toMonoidHom ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  exact H.mul_mem (H.mul_mem hn (hA hx)) (H.inv_mem hn)

theorem q2NbrCore_le_iSup_q2Node (hr : 3 ≤ r) (hC : ∀ k, Q2FrameChart τ k)
    (V₀ : Q2ValuedChart τ 0) (Vr : Q2ValuedChart τ (Fin.last r)) {f' : ℕ}
    (hF' : Nat.card F = 2 ^ f') (hF : 4 ≤ Nat.card F) (k : Fin (r + 1)) :
    q2NbrCore τ k ≤ ⨆ j, q2Node (hC 0) j := by
  have key : ∀ j : ℕ, ∀ hj : j ≤ r, q2NbrCore τ ⟨j, by omega⟩ ≤ ⨆ j, q2Node (hC 0) j := by
    intro j
    induction j with
    | zero =>
      intro _
      exact (q2NbrCore_zero_le_iSup (by omega) hC hF' hF).trans
        (iSup_le fun j => le_iSup (q2Node (hC 0)) j.succ)
    | succ j ih =>
      intro hj
      obtain ⟨n, hn, hconj⟩ := exists_weyl_mem_q2Node (by omega) hF (hC 0) V₀ Vr (j := j)
        (by omega)
      rw [← map_conj_q2NbrCore_of_weyl hconj]
      exact map_conj_le_of_mem_q2 (ih (by omega)) (le_iSup (q2Node (hC 0)) _ hn)
  exact key k.val (by have := k.isLt; omega)

theorem le_iSup_q2Node_of_le (hr : 3 ≤ r) (hC : ∀ k, Q2FrameChart τ k)
    (V₀ : Q2ValuedChart τ 0) (Vr : Q2ValuedChart τ (Fin.last r)) {f' : ℕ}
    (hF' : Nat.card F = 2 ^ f') (hF : 4 ≤ Nat.card F) {L : Subgroup G}
    (hL : L ≤ ⨆ k, perfectCore (L ⊓ centralizer ((rootParam k).map τ : Set G))) :
    L ≤ ⨆ j, q2Node (hC 0) j := by
  refine hL.trans (iSup_le fun k => ?_)
  refine le_trans ?_ (q2NbrCore_le_iSup_q2Node hr hC V₀ Vr hF' hF k)
  exact CFSG.Quasithin.perfectCore_mono inf_le_right

end Global

section Gen

variable {G : Type} [Group G]

@[expose] def Q2FrameDataGen (L X : Subgroup G) (r : ℕ) (F : Type) [Field F] : Prop :=
  ∃ τ : (Fin (r + 1) → Fˣ) →* G, (rootParam 0).map τ = X ∧
    (∀ k : Fin (r + 1), ∃ w ∈ L, ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) ∧
    (∃ π : centralizerPerfectCore X ≃* StatedOmega (StatedQuadPlus (r + 1) F),
      ∀ t : Fin (r + 1) → Fˣ, t 0 = 1 → ∃ hmem : τ t ∈ centralizerPerfectCore X,
        ((π ⟨τ t, hmem⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
          GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = minusNeighbourDiag (RingHom.id F) 0 t) ∧
    L ≤ ⨆ k, perfectCore (L ⊓ centralizer ((rootParam k).map τ : Set G))

variable [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem anisoCTData_of_q2FrameDataGen {L X : Subgroup G} {r : ℕ} (hr : 4 ≤ r)
    (hF : Nat.card F = 4) (h : Q2FrameDataGen L X r F) : AnisoCTData L X (r + 2) F := by
  obtain ⟨τ, hX, hW, ⟨π, hπ⟩, hL⟩ := h
  subst hX
  choose w hwL hw using hW
  let V₀ : Q2ValuedChart τ 0 :=
    Q2ValuedChart.ofNormalized π (fun t ht => (hπ t ht).1) (fun t ht => (hπ t ht).2)
  let C : ∀ k, Q2FrameChart τ k := fun k => (V₀.conj (hw k)).chart
  have hF4 : 4 ≤ Nat.card F := hF.ge
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hE0 : q2NbrCore τ 0 ≤ ⨆ j, q2Node (C 0) j :=
    (q2NbrCore_zero_le_iSup (by omega) C hF' hF4).trans
      (iSup_le fun j => le_iSup (q2Node (C 0)) j.succ)
  refine ⟨q2Node (C 0), ?_, ?_, ?_, hE0, ?_⟩
  · intro i j hij h1 h2
    exact q2Node_le_centralizer hr C hF4 hij h1 h2
  · intro i j hij
    exact exists_theta_q2Node (by omega) C hF4 hij
  · intro j
    obtain ⟨k, hk⟩ := exists_q2Node_le_q2NbrCore (by omega) C j
    exact hk.trans (q2NbrCore_le_anisoNeighbourJoin (l := ⟨w k, hwL k⟩)
      (map_conj_rootParam_zero (hw k)).symm)
  · exact le_iSup_q2Node_of_le (by omega) C V₀ (V₀.conj (hw (Fin.last r))) hF' hF4 hL

end Gen

@[expose] def OmegaMinusTwoFieldFrameGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (hn : 6 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))) (n - 1) 1) →
        OmegaRowAt t (modelToG e (anisoTorus (K := K) (by omega) b c))
          (modelToG e (anisoPerp (K := K) (by omega) b c)) .field →
        (∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
          Nonempty (centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by omega) b c)) ≃*
            matrixProjectiveDerived (coordinateQuadPlus (n - 1) F))) →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
          Q2FrameDataGen L (modelToG e (anisoTorus (K := K) (by omega) b c)) (n - 2) F

@[expose] def OmegaPlusTwoFieldFrameGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m : ℕ), 4 ≤ m → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoPerp (K := K) m b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoTorus m hirr) : Set G))) ⟨t, htX⟩)
            (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoPerp (K := K) m b c)).subgroupOf
                (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                  (plusAnisoTorus m hirr) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                  (plusAnisoTorus m hirr) : Set G))))) (m + 1) 1) →
        OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoTorus m hirr))
          (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c))
          .field →
        (∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
          Nonempty (centralizerPerfectCore (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr)) ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) F))) →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
          Q2FrameDataGen L (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr)) m F

theorem omegaMinusTwoFieldCTDataInput_of_gen (h : OmegaMinusTwoFieldFrameGenInput) :
    OmegaMinusTwoFieldCTDataInput := by
  intro G _ _ L hset n hn K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow hpar
  obtain ⟨F, _, _, _, hF4, hD⟩ := h G L hset n hn K b c hirr hK2 e t ht hKt hnn hN hrow hpar
  have hn2 : n - 2 + 2 = n := by omega
  have hCT := anisoCTData_of_q2FrameDataGen (by omega) hF4 hD
  rw [hn2] at hCT
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF4, hCT⟩

theorem omegaPlusTwoFieldCTDataInput_of_gen (h : OmegaPlusTwoFieldFrameGenInput) :
    OmegaPlusTwoFieldCTDataInput := by
  intro G _ _ L hset m hm K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow hpar
  obtain ⟨F, _, _, _, hF4, hD⟩ := h G L hset m hm K b c hirr hK2 e t ht hKt hnn hN hrow hpar
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF4,
    anisoCTData_of_q2FrameDataGen hm hF4 hD⟩

section Rows

theorem omegaMinusTwoInput_of_frameGen (h10 : OmegaMinusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) (h : OmegaMinusTwoFieldFrameGenInput) :
    OmegaMinusTwoInput :=
  omegaMinusTwoInput_of_recognitionInput h10 hcat
    (omegaMinusTwoFieldRecognitionInput_of_ctData (omegaMinusTwoFieldCTDataInput_of_gen h))

theorem omegaPlusTwoInput_of_frameGen (h10 : OmegaPlusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) (h : OmegaPlusTwoFieldFrameGenInput) :
    OmegaPlusTwoInput :=
  omegaPlusTwoInput_of_recognitionInput h10 hcat
    (omegaPlusTwoFieldRecognitionInput_of_ctData (omegaPlusTwoFieldCTDataInput_of_gen h))

end Rows

end CFSG.SeitzReduction.OmegaPilot
