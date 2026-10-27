module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Rank
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Flag

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace EL3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem false_of_graph_normalized {A : Type} [Group A] [Finite A] {J : Subgroup A} [J.Normal]
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (e : ↥J ≃* projectiveSL 3 F) {Sb Pb : Subgroup A} (hSb : IsSylowOf 2 Sb ⊤)
    (hPbp : IsPGroup p ↥Pb) (hSP : ∀ s ∈ Sb, ∀ x ∈ Pb, s * x * s⁻¹ ∈ Pb)
    (hPJ : ∃ x ∈ Pb, x ∈ J ∧ x ≠ 1) {u : A} (huSb : u ∈ Sb) (B : GL (Fin 3) F)
    (σ : F ≃+* F) (hu : actP e u = conjAut 3 F B * fieldAut 3 F σ * dualAut 3 F) : False := by
  have hSbJ : IsSylowOf 2 (Sb ⊓ J) J :=
    hSb.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  obtain ⟨Q, hQ⟩ := hSbJ.exists_sylow_eq_subgroupOf
  let Q' : Sylow 2 (projectiveSL 3 F) := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ' : (Q' : Subgroup (projectiveSL 3 F)) = (Q : Subgroup ↥J).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hT : IsSylowOf 2 (Q' : Subgroup (projectiveSL 3 F)) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, Q'.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q'.not_dvd_index
  let U : Subgroup (projectiveSL 3 F) := (Pb.subgroupOf J).map e.toMonoidHom
  have hUp : IsPGroup p ↥U := hPbp.comap_subtype.map e.toMonoidHom
  have hU1 : U ≠ ⊥ := by
    obtain ⟨x, hxP, hxJ, hx1⟩ := hPJ
    refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨e ⟨x, hxJ⟩, ⟨⟨x, hxJ⟩, hxP, rfl⟩⟩, ?_⟩
    intro h
    have h1 : e ⟨x, hxJ⟩ = 1 := congrArg Subtype.val h
    have h2 : (⟨x, hxJ⟩ : ↥J) = 1 := e.injective (h1.trans (map_one e).symm)
    exact hx1 (congrArg Subtype.val h2)
  have hTU : ∀ t ∈ (Q' : Subgroup (projectiveSL 3 F)), ∀ w ∈ U, t * w * t⁻¹ ∈ U := by
    intro t ht w hw
    rw [hQ'] at ht
    obtain ⟨x, hxQ, rfl⟩ := ht
    obtain ⟨y, hy, rfl⟩ := hw
    have hxS : ((x : ↥J) : A) ∈ Sb := by
      have : x ∈ (Sb ⊓ J).subgroupOf J := hQ ▸ hxQ
      exact (Subgroup.mem_inf.mp this).1
    refine ⟨x * y * x⁻¹, ?_, ?_⟩
    · exact hSP _ hxS _ hy
    · simp [map_mul, map_inv]
  have hα : ∀ w ∈ U, (conjAut 3 F B * fieldAut 3 F σ * dualAut 3 F) w ∈ U := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [← hu]
    change actP e u (e y) ∈ U
    rw [actP_apply]
    refine ⟨MulAut.conjNormal u y, ?_, rfl⟩
    show ((MulAut.conjNormal u y : ↥J) : A) ∈ Pb
    rw [MulAut.conjNormal_apply]
    exact hSP u huSb _ hy
  exact false_of_graph_flag hp2 U hU1 hUp (Q' : Subgroup (projectiveSL 3 F)) hT hTU B σ hα

end EL3

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
