module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield mem_fixedSubfield)

theorem outerFalseNS_l2 : ∀ (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → ∀ (Y : Type) [Group Y]
    [Finite Y], Blueprint.LieModel Y .PSL 2 p f → OuterFalseNS p Y := by
  classical
  intro p f hp hp2 _ Y _ _ h
  obtain ⟨-, hf, -, -, F, _, _, hcard, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data h
  have : Fact p.Prime := ⟨hp⟩
  intro α hαinn hαp hHH
  have hα1 : α ≠ 1 := fun h1 => hαinn (h1 ▸ (MonoidHom.range _).one_mem)
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hgord : orderOf (AutL2Facts.autEquiv e α) = p := by
    rw [MulEquiv.orderOf_eq]
    exact hαord
  have hgnot := autEquiv_not_psl e hαinn
  obtain ⟨hpf, x, σ, hσord, hconj, hfix⟩ := outer_conj_fieldAut hp hp2 hp hp2 hf hcard hgord hgnot
  have hα : α = (AutL2Facts.autEquiv e).symm (SemidirectProduct.inl x) *
      (AutL2Facts.autEquiv e).symm (SemidirectProduct.inr σ) *
      ((AutL2Facts.autEquiv e).symm (SemidirectProduct.inl x))⁻¹ := by
    have := congrArg (AutL2Facts.autEquiv e).symm hconj
    simpa only [MulEquiv.symm_apply_apply, map_mul, map_inv] using this
  have hff : ∀ y : Y, e ((AutL2Facts.autEquiv e).symm (SemidirectProduct.inr σ) y) =
      psl2RingEquiv σ (e y) := by
    intro y
    have := AutL2Facts.semilinearAction_autEquiv_apply e
      ((AutL2Facts.autEquiv e).symm (SemidirectProduct.inr σ)) y
    rw [MulEquiv.apply_symm_apply, semilinearAction_inr, psl2FieldAut_apply] at this
    exact this.symm
  have he1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hcard' : Nat.card F = (p ^ (f / p)) ^ p := by
    rw [hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have hfix' : Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) =
      p ^ (f / p) := by
    have : CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ = fixedSubfield F σ := by
      ext z
      rw [mem_fixedSubfield, RingHom.mem_eqLocusField]
      simp
    rw [this]
    exact hfix
  obtain ⟨r, c, hr, hr2, hrp, hcr, hσc⟩ := exists_torsion_moved hp hp2 he1 σ hcard' hfix'
  have hσp : σ ^ p = 1 := hσord ▸ pow_orderOf_eq_one σ
  let T₀ : Subgroup (PSL2 F) := (rootsOfUnity r F).map l2Tor
  let T : Subgroup Y := T₀.map e.symm.toMonoidHom
  have hT₀ : IsPGroup r ↥T₀ := by
    rintro ⟨_, t, ht, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, (mem_rootsOfUnity _ _).mp ht, map_one]
  have hT : IsPGroup r ↥T := hT₀.map e.symm.toMonoidHom
  have hfT : ∀ z ∈ T, (AutL2Facts.autEquiv e).symm (SemidirectProduct.inr σ) z ∈ T := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨l2Tor (Units.map σ.toRingHom.toMonoidHom t), ⟨_, ?_, rfl⟩, ?_⟩
    · have ht' := (mem_rootsOfUnity _ _).mp ht
      refine (mem_rootsOfUnity _ _).mpr ?_
      rw [← map_pow, ht', map_one]
    · apply e.injective
      rw [hff]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact (fieldAut_l2Tor σ t).symm
  have hcT : e.symm (l2Tor c) ∈ T := ⟨l2Tor c, ⟨c, (mem_rootsOfUnity _ _).mpr hcr, rfl⟩, rfl⟩
  refine false_of_torus_moved hα hr hr2 hrp hT hfT hcT ?_ hHH
  intro hfix
  have h1 := hff (e.symm (l2Tor c))
  rw [hfix, MulEquiv.apply_symm_apply, fieldAut_l2Tor] at h1
  rcases l2Tor_eq_iff h1 with h2 | h2
  · exact hσc h2.symm
  · have h4 : (c : F) = -σ (c : F) := h2
    exact fieldAut_ne_neg (hp.odd_of_ne_two hp2) σ hσp hσc (by linear_combination h4)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
