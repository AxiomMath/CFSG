module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)

theorem centralizer_pairTorus_singleton {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hq : 4 ≤ Nat.card K) {k : Fin n} {x : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hx : x ∈ pairTorus (K := K) k) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (matrixProjectiveDerived (coordinateQuadPlus n K))) =
      pairTorus (K := K) k ⊔ pairPerp (K := K) k := by
  classical
  set Q := coordinateQuadPlus n K with hQ
  set a := plusIndexEquiv n (.inl k) with ha
  set b := plusIndexEquiv n (.inr k) with hb
  have h := isHypCoord_coordinateQuadPlus (K := K) k
  have hne := h.exists_ne_zero
  rw [pairTorus, pairTorusOf] at hx
  obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.1 hx
  rw [Subgroup.mem_subgroupOf] at ht
  obtain ⟨c, hc⟩ := ht
  have ht_eq : t = ⟨torusLin a b c, h.torusLin_mem_orthDerived c⟩ := Subtype.ext hc.symm
  have hc1 : c ≠ 1 := by
    intro hc1
    have ht1 : t = 1 := by
      rw [ht_eq, hc1]
      exact Subtype.ext (map_one (torusLin a b))
    exact hx1 (by rw [← htx, ht1, map_one])
  subst htx
  apply le_antisymm
  · intro y hy
    obtain ⟨g, rfl⟩ := projHom_surjective Q y
    have hcomm : g * t = t * g := by
      have h1 : projHom Q (g * t) = projHom Q (t * g) := by
        rw [map_mul, map_mul]
        exact mem_centralizer_singleton_iff.1 hy
      exact projHom_injective hne h1
    have hcomm' : (g : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) * torusLin a b c =
        torusLin a b c * (g : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) := by
      simpa [ht_eq] using congrArg Subtype.val hcomm
    obtain ⟨α, hα⟩ := h.exists_torusLin_inv_mul_mem_stabSub hc1
      (Subgroup.commutator_le_self _ g.2) hcomm'
    set tα : orthDerived Q := ⟨torusLin a b α, h.torusLin_mem_orthDerived α⟩ with htα
    set g' : orthDerived Q := tα⁻¹ * g with hg'
    have hg'stab : (g' : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈ stabSub a b := by
      have hg'val : (g' : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
          (torusLin a b α)⁻¹ * (g : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) := rfl
      rw [hg'val]
      exact hα
    have hx_mem : projHom Q tα ∈ pairTorus (K := K) k := by
      rw [pairTorus, pairTorusOf]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨α, rfl⟩)
    have hy_mem : projHom Q g' ∈ pairPerp (K := K) k := by
      rw [pairPerp, pairPerpOf]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg'stab)
    have hg_eq : (g : orthDerived Q) = tα * g' := by
      rw [hg']; group
    rw [hg_eq, map_mul]
    exact Subgroup.mul_mem (pairTorus (K := K) k ⊔ pairPerp (K := K) k)
      (Subgroup.mem_sup_left hx_mem) (Subgroup.mem_sup_right hy_mem)
  · rw [sup_le_iff]
    constructor
    · haveI : IsMulCommutative ↥(pairTorus (K := K) k) := (isCyclic_pairTorus k).isMulCommutative
      refine (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (Subgroup.centralizer_le ?_)
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hx
    · refine (h.pairPerpOf_le_centralizer hq).trans (Subgroup.centralizer_le ?_)
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hx

theorem commutator_mem_pairPerp_of_mem_centralizer_pairTorus_singleton {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} (hq : 4 ≤ Nat.card K) {k : Fin n}
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hx : x ∈ pairTorus (K := K) k) (hx1 : x ≠ 1) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set (matrixProjectiveDerived (coordinateQuadPlus n K))),
      ∀ h ∈ Subgroup.centralizer ({x} : Set (matrixProjectiveDerived (coordinateQuadPlus n K))),
        g * h * g⁻¹ * h⁻¹ ∈ pairPerp (K := K) k := by
  intro g hg h hh
  rw [centralizer_pairTorus_singleton hq hx hx1] at hg hh
  rw [← centralizer_pairTorus hq k] at hg hh
  exact (isHypCoord_coordinateQuadPlus k).commutator_mem_pairPerpOf hq hg hh

theorem omegaLeviGL_four_le_statedOmega {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) :
    omegaLeviGL F 4 ≤ StatedOmega (StatedQuadPlus 4 F) := by
  intro x hx
  obtain ⟨A, rfl⟩ := mem_omegaLeviGL.1 hx
  classical
  set f : Fin 4 → Fˣ := fun i => if i = 0 then Matrix.GeneralLinearGroup.det A else 1 with hf
  set D : GL (Fin 4) F := TauCeti.diagGL f with hD
  have hdetD : Matrix.GeneralLinearGroup.det D = Matrix.GeneralLinearGroup.det A := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hD, TauCeti.diagGL_coe, Matrix.det_diagonal]
    rw [hf]
    rw [Finset.prod_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin 4)) h
  set B : GL (Fin 4) F := D⁻¹ * A with hB
  have hdetB : Matrix.GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, map_inv, hdetD, inv_mul_cancel]
  have hA : A = D * B := by rw [hB]; group
  rw [hA, map_mul]
  refine Subgroup.mul_mem _ ?_ ?_
  · have hD_eq : ((leviEmbedGL F 4 D : StatedSp 4 F) : GL (Fin 4 ⊕ Fin 4) F) =
        diagOmega F 4 f := by
      apply Units.ext
      rw [coe_leviEmbedGL, hD, TauCeti.diagGL_coe, diagOmega_coe]
      have hDinv : ((TauCeti.diagGL f)⁻¹ : GL (Fin 4) F) =
          TauCeti.diagGL (fun i => (f i)⁻¹) := (map_inv (TauCeti.diagGL) f).symm
      rw [hDinv, TauCeti.diagGL_coe, Matrix.diagonal_transpose]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          CFSG.SeitzReduction.SymplecticPilot.diagSpEntry]
    have hDmem : ((leviEmbedGL F 4 D : StatedSp 4 F) : GL (Fin 4 ⊕ Fin 4) F) ∈
        StatedOmega (StatedQuadPlus 4 F) := by
      rw [hD_eq]
      exact CFSG.SeitzReduction.F4Pilot.diagOmega_mem_statedOmega f
    exact hDmem
  · have hdetB' : (B : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      simpa using congrArg Units.val hdetB
    have htoGL : Matrix.SpecialLinearGroup.toGL (⟨B, hdetB'⟩ : Matrix.SpecialLinearGroup
        (Fin 4) F) = B := Units.ext rfl
    have hEq : (leviEmbedSL F 4 ⟨B, hdetB'⟩ : StatedSp 4 F) = leviEmbedGL F 4 B := by
      rw [leviEmbedSL]
      exact congrArg (leviEmbedGL F 4) htoGL
    have hmemSp : leviEmbedGL F 4 B ∈ siegelLevi F 4 := ⟨⟨B, hdetB'⟩, hEq⟩
    have hmem : ((leviEmbedGL F 4 B : StatedSp 4 F) : GL (Fin 4 ⊕ Fin 4) F) ∈
        omegaLeviSL F 4 := by
      rw [omegaLeviSL]
      exact Subgroup.mem_map_of_mem _ hmemSp
    have hle := omegaLeviSL_le_statedOmega (F := F) (k := 4) hF (by norm_num)
    exact hle hmem

theorem centralizer_siegelTorus_singleton {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) {s : Fˣ} (hs : s * s ≠ 1) :
    Subgroup.centralizer
        ({⟨diagOmega F 4 (fun _ => s),
            CFSG.SeitzReduction.F4Pilot.diagOmega_mem_statedOmega _⟩} :
          Set (StatedOmega (StatedQuadPlus 4 F))) =
      (omegaLeviGL F 4).subgroupOf (StatedOmega (StatedQuadPlus 4 F)) := by
  classical
  set Ω := StatedOmega (StatedQuadPlus 4 F)
  set x : Ω := ⟨diagOmega F 4 (fun _ => s),
    CFSG.SeitzReduction.F4Pilot.diagOmega_mem_statedOmega _⟩ with hx
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hySp : (⟨(y : GL (Fin 4 ⊕ Fin 4) F),
        CFSG.RankThree.PartOne.KFU.statedOmega_quadPlus_le_statedSp y.2⟩ : StatedSp 4 F) ∈
        siegelLeviGL F 4 := by
      have hcommSp : (⟨(y : GL (Fin 4 ⊕ Fin 4) F),
          CFSG.RankThree.PartOne.KFU.statedOmega_quadPlus_le_statedSp y.2⟩ : StatedSp 4 F) *
            diagSp F 4 (fun _ => s) = diagSp F 4 (fun _ => s) *
            ⟨(y : GL (Fin 4 ⊕ Fin 4) F),
              CFSG.RankThree.PartOne.KFU.statedOmega_quadPlus_le_statedSp y.2⟩ := by
        apply Subtype.ext
        have h := congrArg (fun z : Ω => (z : GL (Fin 4 ⊕ Fin 4) F))
          (mem_centralizer_singleton_iff.1 hy)
        simpa [hx, CFSG.SeitzReduction.OmegaPilot.coe_diagSp_eq_diagOmega] using h
      exact mem_siegelLeviGL_of_commute hs hcommSp
    rw [omegaLeviGL]
    exact Subgroup.mem_map_of_mem _ hySp
  · intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨A, hA⟩ := mem_omegaLeviGL.1 hy
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hySp_mem : (⟨(y : GL (Fin 4 ⊕ Fin 4) F),
        CFSG.RankThree.PartOne.KFU.statedOmega_quadPlus_le_statedSp y.2⟩ : StatedSp 4 F) ∈
        siegelLeviGL F 4 := ⟨A, Subtype.ext hA⟩
    have hcommSp := mem_centralizer_iff.1
      (siegelLeviGL_le_centralizer_siegelTorus hySp_mem) _ (diagSp_const_mem_siegelTorus s)
    have h := congrArg (fun z : StatedSp 4 F => (z : GL (Fin 4 ⊕ Fin 4) F)) hcommSp
    simpa [hx, CFSG.SeitzReduction.OmegaPilot.coe_diagSp_eq_diagOmega] using h.symm

theorem isQuasisimple_omegaLeviSL_subgroupOf {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple
      ((omegaLeviSL F 4).subgroupOf (StatedOmega (StatedQuadPlus 4 F))) := by
  have hSL : CFSG.IsQuasisimple (omegaLeviSL F 4) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (siegelLeviEquiv.symm.trans omegaLeviSLEquiv)
      (isQuasisimple_siegelLevi hF (by norm_num))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe
      (omegaLeviSL_le_omegaLeviGL.trans (omegaLeviGL_four_le_statedOmega hF))).symm hSL

end CFSG.LocalAnalysis.GLTheoremA.Y10F
