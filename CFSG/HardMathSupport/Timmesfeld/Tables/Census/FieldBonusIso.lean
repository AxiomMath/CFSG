module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {G G' : Type} [Group G] [Group G']

theorem normalizer_map_mulEquiv (e : G ≃* G') (P : Subgroup G) :
    (Subgroup.normalizer (P : Set G)).map e.toMonoidHom =
      Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_normalizer_iff, map_mul, map_inv]
  constructor
  · intro H h'
    exact H _
  · intro H h
    have := H (e h)
    simpa using this

theorem isTwoLocal_map (e : G ≃* G') {K : Subgroup G} (h : IsTwoLocal K) :
    IsTwoLocal (K.map e.toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := h
  exact ⟨P.map e.toMonoidHom, by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P e.injective],
    hP2.map e.toMonoidHom, normalizer_map_mulEquiv e P⟩

theorem isElemAbelian_map {p : ℕ} (e : G ≃* G') {E : Subgroup G} (h : IsElemAbelian p E) :
    IsElemAbelian p (E.map e.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map h _

variable [Finite G] [Finite G']

theorem glaTwoLocalRank_congr {p : ℕ} (hp : 1 < p) (e : G ≃* G') :
    GLATwoLocalRank p G' = GLATwoLocalRank p G := by
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
  congr 1
  ext k
  constructor
  · rintro ⟨K', hK', rfl⟩
    exact ⟨K'.map e.symm.toMonoidHom, isTwoLocal_map e.symm hK',
      pRank_map_mulEquiv hp e.symm K'⟩
  · rintro ⟨K, hK, rfl⟩
    exact ⟨K.map e.toMonoidHom, isTwoLocal_map e hK, (pRank_map_mulEquiv hp e K)⟩

theorem fieldBonus_of_mulEquiv {p : ℕ} (hp : 1 < p) (e : G ≃* G') (H : Subgroup (MulAut G))
    (h : FieldBonus G' p (H.map (MulAut.congr e).toMonoidHom)) : FieldBonus G p H := by
  obtain ⟨ψ', hψ', hni, T', hT', hT2, hTinv, E₁', E₂', ha1, ha2, hn, hc1, hc2, hf1, hf2⟩ := h
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.1 hψ'
  have hcongr : ∀ x : G', (MulAut.congr e ψ) x = e (ψ (e.symm x)) := fun x => rfl
  have hfix : ∀ x : G', (MulAut.congr e ψ) x = x → ψ (e.symm x) = e.symm x := fun x hx => by
    have := congrArg e.symm (hcongr x ▸ hx)
    simpa using this
  refine ⟨ψ, hψ, ?_, T'.map e.symm.toMonoidHom, ?_, hT2.map e.symm.toMonoidHom, ?_,
    E₁'.map e.symm.toMonoidHom, E₂'.map e.symm.toMonoidHom,
    isElemAbelian_map e.symm ha1, isElemAbelian_map e.symm ha2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    apply hni
    refine ⟨e g, fun t => ?_⟩
    show (MulAut.congr e ψ) t = e g * t * (e g)⁻¹
    rw [hcongr, hg]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective T' e.symm.injective]
  · ext x
    simp only [Subgroup.mem_map_equiv]
    have hTinv' : T'.map (MulAut.congr e ψ).toMonoidHom = T' := hTinv
    have hx : ∀ y : G', y ∈ T' ↔ (MulAut.congr e ψ).symm y ∈ T' := fun y => by
      rw [← Subgroup.mem_map_equiv (f := MulAut.congr e ψ), hTinv']
    have := (hx (e x)).symm
    simpa [MulAut.congr_symm_apply] using this
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    rw [← normalizer_map_mulEquiv e.symm T']
    exact Subgroup.mem_map.2 ⟨y', hn hy', rfl⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hc1, glaTwoLocalRank_congr hp e]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hc2,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp e]
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    exact hfix x' (hf1 x' hx')
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    exact hfix x' (hf2 x' hx')

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
