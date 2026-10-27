module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallLocal

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

section Transport

variable {K K' : Type} [Group K] [Group K'] {p : ℕ}

theorem AutFixInner.of_equiv (e : K ≃* K') {T : Sylow p K} {T' : Sylow p K'}
    (hT : (T : Subgroup K).map e.toMonoidHom = (T' : Subgroup K')) (D : AutFixInner p K' T') :
    AutFixInner p K T := by
  intro f hf
  let f' : MulAut K' := (e.symm.trans f).trans e
  have hf' : ∀ t' ∈ (T' : Subgroup K'), f' t' = t' := by
    intro t' ht'
    rw [← hT] at ht'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ht'
    change e (f (e.symm (e t))) = e t
    rw [MulEquiv.symm_apply_apply, hf t ht]
  obtain ⟨g', hg'⟩ := D f' hf'
  refine ⟨e.symm g', MulEquiv.ext fun x => ?_⟩
  have h1 := DFunLike.congr_fun hg' (e x)
  simp only [MulAut.conj_apply] at h1
  change g' * e x * g'⁻¹ = e (f (e.symm (e x))) at h1
  rw [MulEquiv.symm_apply_apply] at h1
  have h2 := congrArg e.symm h1
  rw [MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h2
  simpa only [MulAut.conj_apply] using h2

variable [Finite K]

theorem AutFixInner.of_sylow (hp : p.Prime) {T₀ : Sylow p K} (D : AutFixInner p K T₀)
    (T : Sylow p K) : AutFixInner p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  refine AutFixInner.of_equiv (MulAut.conj g⁻¹) (T' := T₀) ?_ D
  have h1 : (T : Subgroup K) = (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact coe_smul_sylow_eq_map T₀ g
  rw [h1, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id (T₀ : Subgroup K)]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.id_apply]
  group

theorem AutFixInner.of_equiv_all [Finite K'] (hp : p.Prime) (e : K ≃* K')
    (hD : ∃ T₀ : Sylow p K', AutFixInner p K' T₀) (T : Sylow p K) : AutFixInner p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₀, D⟩ := hD
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  have D' := D.of_sylow hp (Sylow.mapSurjective hf T)
  exact AutFixInner.of_equiv e (T' := Sylow.mapSurjective hf T) rfl D'

end Transport

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
