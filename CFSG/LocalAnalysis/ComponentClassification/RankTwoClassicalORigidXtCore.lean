module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidXt
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidIso

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups commutatorElement

section Perf

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit hQ [CharP K 2] [Fintype ι₂] [Fintype ι] [DecidableEq ι] in
theorem exists_polarBilin_eq_one [Nonempty ι₂] (hnd : Q₂.polarBilin.Nondegenerate) :
    ∃ w w' : ι₂ → K, Q₂.polarBilin w w' = 1 := by
  obtain ⟨a⟩ := (inferInstance : Nonempty ι₂)
  have hw : (Pi.single a 1 : ι₂ → K) ≠ 0 := by
    intro h
    have := congrFun h a
    simp at this
  obtain ⟨w'', hw''⟩ : ∃ w'', Q₂.polarBilin (Pi.single a 1) w'' ≠ 0 := by
    by_contra! h
    exact hw (hnd.1 _ h)
  exact ⟨Pi.single a 1, (Q₂.polarBilin (Pi.single a 1) w'')⁻¹ • w'', by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw'']⟩

omit hQ [Fintype ι₂] in
theorem qEGL_zero_mem_commutator [Nonempty ι₂] (hnd : Q₂.polarBilin.Nondegenerate) (e : K) :
    qEGL oe Q₂ 0 e ∈ ⁅oQE oe Q₂, oQE oe Q₂⁆ := by
  obtain ⟨w, w', hww⟩ := exists_polarBilin_eq_one hnd
  have h := qE_commutator oe Q₂ (fun s => if s = 0 then w else 0)
    (fun s => if s = 0 then 0 else e • w') 0 0
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, map_zero, map_smul, smul_eq_mul, hww,
    mul_one, zero_add] at h
  rw [← h]
  exact commutator_mem_commutator (qEGL_mem_oQE oe Q₂ _ _) (qEGL_mem_oQE oe Q₂ _ _)

omit hQ [CharP K 2] in
theorem commutator_oL₀ (hSL : commutator SL(2, K) = ⊤)
    (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤) : ⁅oL₀ oe Q₂, oL₀ oe Q₂⁆ = oL₀ oe Q₂ := by
  refine le_antisymm (commutator_le_self _) (sup_le ?_ ?_)
  · rw [← commutator_range_of_perfect _ hSL]
    exact commutator_mono le_sup_left le_sup_left
  · have h1 : (StatedOmega ⇑Q₂).map (oKappaGL oe) = ((oKappaGL oe).comp
        (StatedOmega ⇑Q₂).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← commutator_range_of_perfect _ hperf₂, ← h1]
    exact commutator_mono le_sup_right le_sup_right

theorem oXt_perfect (hSL : commutator SL(2, K) = ⊤) (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤)
    [Nonempty ι₂] (hnd : Q₂.polarBilin.Nondegenerate) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ⁅oXt oe Q₂, oXt oe Q₂⁆ = oXt oe Q₂ := by
  refine le_antisymm (commutator_le_self _) (sup_le ?_ ?_)
  · rintro _ ⟨⟨u, c⟩, rfl⟩
    obtain ⟨A, u', e, -, h⟩ := exists_qE_eq_commutator hQ ht0 ht1 u c
    show qEGL oe Q₂ u c ∈ _
    rw [h, ← qEGL_zero oe Q₂]
    refine mul_mem (commutator_mem_commutator (mem_sup_right (mem_sup_left ⟨A, rfl⟩))
      (mem_sup_left (qEGL_mem_oQE oe Q₂ u' 0))) ?_
    exact commutator_mono le_sup_left le_sup_left (qEGL_zero_mem_commutator hnd e)
  · rw [← commutator_oL₀ hSL hperf₂]
    exact commutator_mono le_sup_right le_sup_right

end Perf

section Core

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit [CharP K 2] in
theorem uBlkHom_mem_statedOmega {g : GL ι K} (hgC : g ∈ cenM₀ K oe)
    (hg : g ∈ perfectCore (StatedOmega ⇑Q ⊓ cenM₀ K oe)) :
    (uBlkHom K oe).toHomUnits ⟨g, hgC⟩ ∈ StatedOmega ⇑Q₂ := by
  set C := cenM₀ K oe
  set P₀ := (StatedOmega ⇑Q ⊓ C).subgroupOf C
  set φ : C →* GL ι₂ K := (uBlkHom K oe).toHomUnits
  have h1 : (perfectCore P₀).map C.subtype = perfectCore (StatedOmega ⇑Q ⊓ C) := by
    rw [CFSG.Quasithin.map_perfectCore, subgroupOf_map_subtype, inf_assoc, inf_idem]
  have h2 : (⟨g, hgC⟩ : C) ∈ perfectCore P₀ := by
    rw [← h1] at hg
    obtain ⟨x, hx, hxg⟩ := hg
    have : x = ⟨g, hgC⟩ := Subtype.ext hxg
    rwa [← this]
  have h3 : φ ⟨g, hgC⟩ ∈ perfectCore (P₀.map φ) := by
    rw [← CFSG.Quasithin.map_perfectCore]
    exact ⟨_, h2, rfl⟩
  have h4 : P₀.map φ ≤ closure {Y : GL ι₂ K | ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w} := by
    rintro _ ⟨x, hx, rfl⟩
    have hxΩ : (x : GL ι K) ∈ StatedOmega ⇑Q := (mem_inf.mp hx).1
    exact subset_closure (isometry_uBlk hQ (commute_oN₀_of_mem x.2)
      (quad_mulVec_of_mem_statedOmega hxΩ))
  have h5 := CFSG.Quasithin.perfectCore_le_derivedSeriesOf (P₀.map φ) 1 h3
  unfold StatedOmega
  exact commutator_mono h4 h4 h5

theorem perfectCore_le_oXt :
    perfectCore (StatedOmega ⇑Q ⊓ cenM₀ K oe) ≤ oXt oe Q₂ := by
  intro g hg
  have hg' := CFSG.Quasithin.perfectCore_le _ hg
  obtain ⟨hgΩ, hgC⟩ := mem_inf.mp hg'
  obtain ⟨A, u, c, -, hdec⟩ := eq_levi_mul_qE hQ hgC (quad_mulVec_of_mem_statedOmega hgΩ)
  have hY := uBlkHom_mem_statedOmega hQ hgC hg
  rw [hdec]
  refine mul_mem (mul_mem (mem_sup_right (mem_sup_right ⟨_, hY, rfl⟩))
    (mem_sup_right (mem_sup_left ⟨A, rfl⟩))) (mem_sup_left (qEGL_mem_oQE oe Q₂ u c))

theorem perfectCore_eq_oXt (hSL : commutator SL(2, K) = ⊤)
    (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤) [Nonempty ι₂]
    (hnd : Q₂.polarBilin.Nondegenerate) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    perfectCore (StatedOmega ⇑Q ⊓ cenM₀ K oe) = oXt oe Q₂ :=
  le_antisymm (perfectCore_le_oXt hQ) (CFSG.Quasithin.le_perfectCore_of_perfect
    (le_inf (oXt_le_statedOmega hQ hSL ht0 ht1) (oXt_le_cenM₀ oe Q₂))
    (oXt_perfect hQ hSL hperf₂ hnd ht0 ht1))

end Core

end CFSG.ComponentClassification.RankTwoClassical.ORigid
