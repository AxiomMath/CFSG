module

public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.RankThree.PartTwo.KFacts


variable {K : Type} [Field K]

theorem g2FieldHom_eq_entrywise (σ : K ≃+* K) : g2FieldHom K σ = entrywiseAdjointAut .G2 σ :=
  MulEquiv.ext fun h => Subtype.ext (by rw [coe_g2FieldHom, coe_entrywiseAdjointAut])

theorem g2FieldHom_xPar (σ : K ≃+* K) (γ : Fin (Tag.rank .G2) → ℤ) (c : K) :
    g2FieldHom K σ (xPar (rootOperatorFamily .G2) γ c) =
      xPar (rootOperatorFamily .G2) γ (σ c) := by
  rw [g2FieldHom_eq_entrywise, CFSG.StandardType.AutSt.entrywiseAdjointAut_xPar]

theorem g2FieldHom_mem_rootGroup (σ : K ≃+* K) {γ : Fin (Tag.rank .G2) → ℤ}
    {x : adjointGroup .G2 K} (hx : x ∈ (g2Datum K).rootGroup γ) :
    g2FieldHom K σ x ∈ (g2Datum K).rootGroup γ := by
  change x ∈ rootGroup (rootOperatorFamily .G2) K γ at hx
  change g2FieldHom K σ x ∈ rootGroup (rootOperatorFamily .G2) K γ
  by_cases hγ : IsRoot .G2 γ
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
    rw [g2FieldHom_xPar]
    exact (mem_rootGroup_iff hγ _).2 ⟨σ c, rfl⟩
  · rw [rootGroup_of_not_isRoot hγ, Subgroup.mem_bot] at hx ⊢
    rw [hx, map_one]

theorem g2FieldHom_mem_posUnipotent (σ : K ≃+* K) {x : adjointGroup .G2 K}
    (hx : x ∈ posUnipotent (g2Datum K)) : g2FieldHom K σ x ∈ posUnipotent (g2Datum K) := by
  have hle : posUnipotent (g2Datum K) ≤
      (posUnipotent (g2Datum K)).comap (g2FieldHom K σ).toMonoidHom :=
    iSup₂_le fun γ hγ y hy =>
      rootGroup_le_posUnipotent hγ.1 hγ.2 (g2FieldHom_mem_rootGroup σ hy)
  exact hle hx

variable [Finite K]

theorem g2FieldHom_mem_borel (σ : K ≃+* K) {x : adjointGroup .G2 K}
    (hx : x ∈ borel (g2Datum K) (torus (τ := .G2) K)) :
    g2FieldHom K σ x ∈ borel (g2Datum K) (torus (τ := .G2) K) := by
  haveI : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 _
  have hN : x ∈ Subgroup.normalizer (posUnipotent (g2Datum K) : Set (adjointGroup .G2 K)) :=
    borel_le_normalizer_posUnipotent (g2_isCTGroupDatum K) hx
  apply CFSG.ClassicalInvolution.WeakCT.normalizer_posUnipotent_le_borel (g2_isCTGroupDatum K)
    (g2_steinbergExtras K)
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  set e := g2FieldHom K σ with he
  have hu' : e⁻¹ u ∈ posUnipotent (g2Datum K) := by
    rw [he, ← map_inv]
    exact g2FieldHom_mem_posUnipotent σ⁻¹ hu
  have hxu := g2FieldHom_mem_posUnipotent σ ((Subgroup.mem_normalizer_iff.1 hN _).1 hu')
  rw [← he] at hxu
  have h1 : e (x * e⁻¹ u * x⁻¹) = e x * u * (e x)⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  rwa [h1] at hxu

theorem g2FieldHom_mem_of_borel_le (σ : K ≃+* K) {A : Subgroup (adjointGroup .G2 K)}
    (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A) {x : adjointGroup .G2 K} (hx : x ∈ A) :
    g2FieldHom K σ x ∈ A := by
  have hA := eq_borel_sup_rankOne (g2_isCTGroupDatum K) (g2_steinbergExtras K) hBA
  have hle : A ≤ A.comap (g2FieldHom K σ).toMonoidHom := by
    conv_lhs => rw [hA]
    refine sup_le (fun y hy => hBA (g2FieldHom_mem_borel σ hy)) (iSup₂_le fun j hj => ?_)
    have hL := rankOne_le_of_mem_negIndices hBA hj
    exact sup_le (fun y hy => hL (le_sup_left (a := (g2Datum K).rootGroup (Pi.single j 1))
        (g2FieldHom_mem_rootGroup σ hy)))
      (fun y hy => hL (le_sup_right (b := (g2Datum K).rootGroup (-Pi.single j 1))
        (g2FieldHom_mem_rootGroup σ hy)))
  exact hle hx

theorem mem_of_mem_normalizer_of_borel_le [CharP K 2] {A : Subgroup (adjointGroup .G2 K)}
    (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A) {g : adjointGroup .G2 K}
    (hg : g ∈ Subgroup.normalizer (A : Set (adjointGroup .G2 K))) : g ∈ A := by
  haveI : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := borelQuotient_g2 (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  let S : Sylow 2 ↥(adjointGroup .G2 K) :=
    (isPGroup_iSup_pos hB.extras hB.pGroup).toSylow hB.not_dvd_index
  exact CFSG.AGLEmbedding.ParabAutIrr.mem_of_mem_normalizer S
    (posUnipotent_le_borel.trans hBA)
    ((CFSG.ClassicalInvolution.WeakCT.normalizer_posUnipotent_le_borel hB.ct hB.extras).trans
      hBA) hg

theorem exists_torus_conj_xPar (i : Fin (Tag.rank .G2)) {t : adjointGroup .G2 K}
    (ht : t ∈ ⨆ k, torus (τ := .G2) K k) :
    ∃ u : Kˣ, ∀ c : K, t * xPar (rootOperatorFamily .G2) (Pi.single i 1) c * t⁻¹ =
      xPar (rootOperatorFamily .G2) (Pi.single i 1) (u * c) := by
  refine Subgroup.iSup_induction (torus (τ := .G2) K) (C := fun t => ∃ u : Kˣ, ∀ c : K,
      t * xPar (rootOperatorFamily .G2) (Pi.single i 1) c * t⁻¹ =
        xPar (rootOperatorFamily .G2) (Pi.single i 1) (u * c)) ht ?_ ?_ ?_
  · intro k x hx
    obtain ⟨s, rfl⟩ := hx
    exact ⟨_, fun c => by
      rw [xPar_simple, xPar_simple]
      exact (rootOperatorFamily .G2).torusElement_mul_eltElement_mul_inv k s _ c⟩
  · exact ⟨1, fun c => by simp⟩
  · rintro x y ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u * v, fun c => ?_⟩
    calc x * y * xPar (rootOperatorFamily .G2) (Pi.single i 1) c * (x * y)⁻¹ =
        x * (y * xPar (rootOperatorFamily .G2) (Pi.single i 1) c * y⁻¹) * x⁻¹ := by group
      _ = xPar (rootOperatorFamily .G2) (Pi.single i 1) (u * (v * c)) := by rw [hv, hu]
      _ = xPar (rootOperatorFamily .G2) (Pi.single i 1) ((u * v : Kˣ) * c) := by
        rw [Units.val_mul, mul_assoc]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo
