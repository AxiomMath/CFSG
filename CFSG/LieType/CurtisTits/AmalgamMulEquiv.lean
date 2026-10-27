module

public import CFSG.LieType.CurtisTits.AmalgamStrip

public section

namespace CFSG.LieType.CurtisTits

open Subgroup

universe u u' v w

theorem IsUniversalCompletion.map_mulEquiv {K : Type u} [Group K] {K' : Type u'}
    [Group K'] {ι : Type v} [Preorder ι] {L : ι → Subgroup K}
    (h : IsUniversalCompletion.{u, v, w} L) (e : K ≃* K') :
    IsUniversalCompletion.{u', v, w} (fun i => (L i).map e.toMonoidHom) := by
  intro G _ φ hφ
  let φ' : ∀ i, L i →* G :=
    fun i => (φ i).comp (e.subgroupMap (L i)).toMonoidHom
  have hφ' : IsCompatible L φ' := by
    intro i j hij x y hxy
    exact hφ i j hij (e.subgroupMap (L i) x) (e.subgroupMap (L j) y)
      (by simpa using congrArg e hxy)
  obtain ⟨ψ, hψ, huniq⟩ := h G φ' hφ'
  refine ⟨ψ.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro i x
    have hx : e.symm (x : K') ∈ L i := (Subgroup.mem_map_equiv).mp x.2
    have h1 := hψ i ⟨e.symm (x : K'), hx⟩
    change ψ (e.symm (x : K')) = φ i x
    rw [h1]
    change φ i (e.subgroupMap (L i) ⟨e.symm (x : K'), hx⟩) = φ i x
    congr 1
    apply Subtype.ext
    rw [MulEquiv.coe_subgroupMap_apply]
    exact e.apply_symm_apply (x : K')
  · intro ψ' hψ'
    have hcomp : ψ'.comp e.toMonoidHom = ψ := by
      apply huniq
      intro i y
      change ψ' (e y) = φ i (e.subgroupMap (L i) y)
      exact hψ' i (e.subgroupMap (L i) y)
    ext x
    calc ψ' x = ψ' (e (e.symm x)) := by rw [MulEquiv.apply_symm_apply]
      _ = (ψ'.comp e.toMonoidHom) (e.symm x) := rfl
      _ = ψ (e.symm x) := by rw [hcomp]
      _ = (ψ.comp e.symm.toMonoidHom) x := rfl

theorem StripData.map_mulEquiv {K : Type u} [Group K] {K' : Type u'} [Group K']
    {I : Type v} [Fintype I] [DecidableEq I] {𝒮 : Set (Set I)} {P L : Set I → Subgroup K}
    {T : I → Subgroup K} (d : StripData 𝒮 P L T) (e : K ≃* K') :
    StripData 𝒮 (fun C => (P C).map e.toMonoidHom)
      (fun C => (L C).map e.toMonoidHom) (fun i => (T i).map e.toMonoidHom) where
  small := d.small
  L_mono := fun _ _ h => Subgroup.map_mono (d.L_mono h)
  L_le := fun C hC => Subgroup.map_mono (d.L_le C hC)
  T_le := fun i => Subgroup.map_mono (d.T_le i)
  T_comm := by
    rintro i j hij x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, d.T_comm i j hij a ha b hb]
  T_indep := by
    have hT : (fun i => (T i).map e.toMonoidHom) =
        (MulEquiv.mapSubgroup e) ∘ T := by
      funext i
      exact (congrFun (MulEquiv.coe_mapSubgroup e) (T i)).symm
    rw [hT]
    exact d.T_indep.map_orderIso (MulEquiv.mapSubgroup e)
  norm := by
    rintro C hC t ht l hl
    rw [← Subgroup.map_iSup (s := T) e.toMonoidHom] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    simpa only [map_mul, map_inv] using
      Subgroup.mem_map_of_mem e.toMonoidHom (d.norm C hC t₀ ht₀ l₀ hl₀)
  prod := by
    rintro C hC x ⟨x₀, hx₀, rfl⟩
    obtain ⟨t, ht, l, hl, rfl⟩ := d.prod C hC x₀ hx₀
    refine ⟨e t, ?_, e l, ?_, by simp⟩
    · rw [← Subgroup.map_iSup (s := T) e.toMonoidHom]
      exact Subgroup.mem_map_of_mem e.toMonoidHom ht
    · exact Subgroup.mem_map_of_mem e.toMonoidHom hl
  inter := by
    intro C hC
    have h := Subgroup.map_mono (f := e.toMonoidHom) (d.inter C hC)
    rw [Subgroup.map_inf_eq _ _ _ e.injective] at h
    simpa only [Subgroup.map_iSup] using h
  gen := by
    intro C hC
    rw [d.gen C hC]
    simp only [Subgroup.map_iSup]

end CFSG.LieType.CurtisTits
