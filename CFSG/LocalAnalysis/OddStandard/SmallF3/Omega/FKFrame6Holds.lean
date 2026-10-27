module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame6Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactFrame6_holds : Asc82FactFrame6 := by
  intro G _ _ L ρ hL hρ hcomm hinn x hx σ hσ
  obtain ⟨_, V, _, _, _, Q, hQ, e, _, hdim, hsgn, _, _⟩ := (hρ 0).2
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.mp hL.1.1
  have hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := ⟨hdim, hsgn⟩
  have hN : ∀ i, ρ i ∈ Subgroup.normalizer (L : Set G) := fun i => (hρ i).1
  let Φ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q := ffInducesHom hm e (L := L)
  have hlift : ∀ i, ∃ t : OGroup Q, t * t = 1 ∧ invDim t = 1 ∧
      projOrthToProjSim Q (toProj Q t) = Φ ⟨ρ i, hN i⟩ :=
    fun i => simHasDim_of_inducesTypeSome hm e (hN i) (hρ i).2.choose_spec
  choose t ht2 ht1 htΦ using hlift
  have hΦcomm : ∀ i j, Φ ⟨ρ i, hN i⟩ * Φ ⟨ρ j, hN j⟩ =
      Φ ⟨ρ j, hN j⟩ * Φ ⟨ρ i, hN i⟩ := by
    intro i j
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm i j)
  have hcomm' : ∀ i j, phiSim Q (t i) * phiSim Q (t j) =
      phiSim Q (t j) * phiSim Q (t i) := by
    intro i j
    change projOrthToProjSim Q (toProj Q (t i)) *
        projOrthToProjSim Q (toProj Q (t j)) =
      projOrthToProjSim Q (toProj Q (t j)) *
        projOrthToProjSim Q (toProj Q (t i))
    rw [htΦ i, htΦ j]
    exact hΦcomm i j
  have hne' : ∀ i j, i ≠ j → phiSim Q (t i) ≠ phiSim Q (t j) := by
    intro i j hij h
    apply (hinn i j hij).2
    have hy : Φ ⟨ρ i, hN i⟩ = Φ ⟨ρ j, hN j⟩ := by
      rw [← htΦ i, ← htΦ j]
      exact h
    have hprod : Φ (⟨ρ i, hN i⟩ * ⟨ρ j, hN j⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hy, mul_inv_cancel]
    exact (ffInducesHom_eq_one_iff hm e hperf _).mp hprod
  have hinn' : ∀ i j, i ≠ j → t i * t j ∈ omegaGroup hQ := by
    intro i j hij
    have hρijN : ρ i * ρ j ∈ Subgroup.normalizer (L : Set G) := mul_mem (hN i) (hN j)
    have hs : SimInOmegaStar hQ (Φ ⟨ρ i * ρ j, hρijN⟩) :=
      (innerOn_iff_simInOmegaStar hm e hperf hρijN).mp (hinn i j hij).1
    have hsub : (⟨ρ i * ρ j, hρijN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨ρ i, hN i⟩ * ⟨ρ j, hN j⟩ := Subtype.ext rfl
    have hΦeq : Φ ⟨ρ i * ρ j, hρijN⟩ = phiSim Q (t i * t j) := by
      rw [hsub, map_mul]
      change Φ ⟨ρ i, hN i⟩ * Φ ⟨ρ j, hN j⟩ =
        projOrthToProjSim Q (toProj Q (t i)) *
          projOrthToProjSim Q (toProj Q (t j))
      rw [htΦ i, htΦ j]
    exact fk_fr_mem_omega_of_simInOmegaStar hQ hdim hsgn (by rw [← hΦeq]; exact hs)
  have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
    (sup_le Subgroup.le_normalizer
      (Subgroup.centralizer_le_normalizer (L : Set G))) hx
  have hxSim : SimInOmegaStar hQ (Φ ⟨x, hxN⟩) :=
    (innerOn_iff_simInOmegaStar hm e hperf hxN).mp hx
  obtain ⟨g, hg, hgΦ⟩ := fk_fr_exists_lift_omega hQ hxSim
  have hσ' : ∀ i, phiSim Q (g⁻¹ * t i * g⁻¹⁻¹) = phiSim Q (t (σ i)) := by
    intro i
    have h1 : Φ (⟨x, hxN⟩⁻¹ * ⟨ρ i, hN i⟩ * ⟨x, hxN⟩ *
        ⟨ρ (σ i), hN (σ i)⟩⁻¹) = 1 :=
      (ffInducesHom_eq_one_iff hm e hperf _).mpr (hσ i)
    have h2 : (Φ ⟨x, hxN⟩)⁻¹ * Φ ⟨ρ i, hN i⟩ * Φ ⟨x, hxN⟩ *
        (Φ ⟨ρ (σ i), hN (σ i)⟩)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    have hΦx : Φ ⟨x, hxN⟩ = phiSim Q g := hgΦ.symm
    have hΦti : Φ ⟨ρ i, hN i⟩ = phiSim Q (t i) := (htΦ i).symm
    have hΦtσi : Φ ⟨ρ (σ i), hN (σ i)⟩ = phiSim Q (t (σ i)) := (htΦ (σ i)).symm
    have h3 : (phiSim Q g)⁻¹ * phiSim Q (t i) * phiSim Q g =
        phiSim Q (t (σ i)) := by
      have h3' : (Φ ⟨x, hxN⟩)⁻¹ * Φ ⟨ρ i, hN i⟩ * Φ ⟨x, hxN⟩ =
          Φ ⟨ρ (σ i), hN (σ i)⟩ := mul_inv_eq_one.mp h2
      rw [hΦx, hΦti, hΦtσi] at h3'
      exact h3'
    have h4 : phiSim Q (g⁻¹ * t i * g⁻¹⁻¹) =
        (phiSim Q g)⁻¹ * phiSim Q (t i) * phiSim Q g := by
      simp only [inv_inv, map_mul, map_inv]
    exact h4.trans h3
  exact fk_fr_core hQ hdim t ht2 ht1 hcomm' hne' hinn' g⁻¹
    ((omegaGroup hQ).inv_mem hg) σ hσ'

end CFSG.OddStandard.SmallF3.Omega
