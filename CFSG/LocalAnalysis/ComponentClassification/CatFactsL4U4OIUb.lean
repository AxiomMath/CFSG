module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUCase

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem fixSub_eq_fixedSubgroup {X : Type*} [Group X] (φ : MulAut X) :
    OutInv.fixSub φ = FixedCommutingProduct.fixedSubgroup φ :=
  Subgroup.ext fun _ => Iff.rfl

theorem exists_lift_component {φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψ : ∀ g, φ (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {c : K} (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      c • 1)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hJφ : J' ≤ OutInv.fixSub φ)
    (hJ : CFSG.IsComponent (J'.subgroupOf (OutInv.fixSub φ))) :
    ∃ Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4)),
      CFSG.Assembly.IsComponentOf Y
        (FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu)) ∧
      ∃ σ : Y →* J'.map (GSThmB.Catalog7L4EU.ιU h), Function.Surjective σ ∧
        σ.ker ≤ Subgroup.center Y ∧
        ∀ y : Y, (σ y : sesqProjUnitary h (stdHermForm h 4)) =
          QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))
            (y : sesqUnitaryGroup (stdHermForm h 4)) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hX' : CFSG.Assembly.IsComponentOf J' (FixedCommutingProduct.fixedSubgroup φ) := by
    rw [← fixSub_eq_fixedSubgroup]
    exact (isComponentOf_iff_isComponent_subgroupOf hJφ).2 hJ
  have hτ := StabU.antiunitaryMap_bijective h A
  have hτB := StabU.stdHermForm_antiunitaryMap h hAu
  have he : ∀ y, GSThmB.Catalog7L4EU.ιU h (φ y) =
      antiProjConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)) hτ hτB
        (GSThmB.Catalog7L4EU.ιU h y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hψ, GSThmB.Catalog7L4EU.ιU_mk, GSThmB.Catalog7L4EU.ιU_mk, antiProjConj_mk]
    congr 1
    exact (GSThmB.Catalog7L4EU.toSesqUnitary_antiConj h hAu g (ψ g) (hψA g)).symm
  have key := GSThmB.Catalog7L4EU.isComponentOf_map_of_intertwine (GSThmB.Catalog7L4EU.ιU h)
    (GSThmB.Catalog7L4EU.ιU_injective h) (GSThmB.Catalog7L4EU.ιU_range_normal h) he hX'
  have hz0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hZc := sesqNormOneScalars_le_center h (stdHermForm h 4)
  obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, hσYv⟩, -⟩ := OddClassSelector.central_lift _ hZc _
    (map_scalars_unitaryConj h _ _ hτB)
    (unitaryConj_unitaryConj h _ _ hτB (Units.mk0 c hz0)
      (StabU.antiunitaryMap_sq h _ hAA)) key
  exact ⟨Y, hY, σY, hσYs, hσYk, hσYv⟩

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
