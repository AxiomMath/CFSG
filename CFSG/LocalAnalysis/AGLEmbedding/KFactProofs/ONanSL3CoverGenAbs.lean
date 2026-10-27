module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenBase
public import CFSG.LocalAnalysis.AGLEmbedding.KGenTwoModAbFix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

open CFSG CFSG.AGLEmbedding

section Transport

variable {S K : Type*} [Group S] [Group K]

theorem mem_mapAut_symm {ψ : S ≃* K} {E : Subgroup (MulAut K)} {e : MulAut S} :
    e ∈ mapAut ψ.symm E ↔ MulAut.congr ψ e ∈ E := by
  rw [mem_mapAut, MulEquiv.symm_symm]

theorem closure_image_eq_top_iff (ψ : S ≃* K) (A : Set S) :
    Subgroup.closure (ψ '' A) = ⊤ ↔ Subgroup.closure A = ⊤ := by
  have hmap : Subgroup.closure (ψ '' A) = (Subgroup.closure A).map ψ.toMonoidHom :=
    (MonoidHom.map_closure ψ.toMonoidHom _).symm
  rw [hmap]
  constructor
  · intro h
    have := Subgroup.comap_map_eq_self_of_injective (f := ψ.toMonoidHom) ψ.injective
      (Subgroup.closure A)
    rw [h, Subgroup.comap_top] at this
    exact this.symm
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ ψ.surjective

theorem closure_modCenter_of_mapAut_symm (ψ : S ≃* K) (E : Subgroup (MulAut K))
    (h : Subgroup.closure {s : S | ∃ e ∈ mapAut ψ.symm E, e ≠ 1 ∧
      e s * s⁻¹ ∈ Subgroup.center S} = ⊤) :
    Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k * k⁻¹ ∈ Subgroup.center K} = ⊤ := by
  rw [eq_top_iff]
  have h1 := (closure_image_eq_top_iff ψ _).2 h
  rw [← h1]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨s, ⟨e', he', he'1, hes⟩, rfl⟩
  refine ⟨MulAut.congr ψ e', mem_mapAut_symm.1 he', fun hh => he'1 ?_, ?_⟩
  · exact (MulAut.congr ψ).injective (by rw [hh, map_one])
  · have h2 : MulAut.congr ψ e' (ψ s) * (ψ s)⁻¹ = ψ (e' s * s⁻¹) := by
      rw [congr_apply', MulEquiv.symm_apply_apply, map_mul, map_inv]
    rw [h2]
    rw [Subgroup.mem_center_iff] at hes ⊢
    intro g
    obtain ⟨g', rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, hes g']

end Transport

section TransportType

variable {S K : Type} [Group S] [Group K]

theorem kGenTwoModAbFix_of_equiv (ψ : S ≃* K)
    (h : ∀ E : Subgroup (MulAut S), Open.IsElemAbelian 3 E → Nat.card E = 9 → FixCube E →
      Subgroup.closure (fixSet E) = ⊤) : KGenTwoModAbFix 3 K := by
  intro E hE hcard _ hfix
  exact closure_modCenter_of_mapAut_symm ψ E (closure_mod_center_eq_top
    (h _ (isElemAbelian_mapAut hE ψ.symm) (by rw [card_mapAut]; exact hcard)
      (FixCube.mapAut hfix ψ.symm)))

end TransportType

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
