module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftModel

public section

open scoped Classical

namespace CFSG.Wreathed.NormalComponentLift

open Matrix CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.TorusSplitting

variable {G : Type} [Group G] {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)} {p f : ℕ} {F : Type} [Field F]
  {Sigma : Subgroup (F ≃+* F)} {b : Fˣ} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

@[expose] noncomputable def liftMap (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)) :
    involutionCentralizer n S e →*
      SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma :=
  (MulAut.conj (SemidirectProduct.inl h)⁻¹).toMonoidHom.comp
    (Ψ.symm.toMonoidHom.comp (centralizerOddCoreMap n S e))

variable {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}
  {h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)}

abbrev modelInl (F : Type) [Field F] (b : Fˣ) (n : ℕ) (hn : 2 ≤ n) (Sigma : Subgroup (F ≃+* F))
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) :
    CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) →*
      SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma :=
  SemidirectProduct.inl

theorem modelInl_injective (F : Type) [Field F] (b : Fˣ) (n : ℕ) (hn : 2 ≤ n)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) :
    Function.Injective (modelInl F b n hn Sigma hSigma) :=
  SemidirectProduct.inl_injective

theorem liftMap_apply (k : involutionCentralizer n S e) :
    liftMap n hn S e Ψ h k = (modelInl F b n hn Sigma hSigma h)⁻¹ *
      Ψ.symm (centralizerOddCoreMap n S e k) * modelInl F b n hn Sigma hSigma h := by
  simp [liftMap]

theorem liftMap_eq_iff (a b : involutionCentralizer n S e) :
    liftMap n hn S e Ψ h a = liftMap n hn S e Ψ h b ↔
      centralizerOddCoreMap n S e a = centralizerOddCoreMap n S e b := by
  rw [liftMap_apply, liftMap_apply, mul_left_inj, mul_right_inj, Ψ.symm.injective.eq_iff]

theorem liftMap_eq_one_iff (k : involutionCentralizer n S e) :
    liftMap n hn S e Ψ h k = 1 ↔ k ∈ centralizerOddCore n S e := by
  have hk : (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e := QuotientGroup.ker_mk' _
  rw [← map_one (liftMap n hn S e Ψ h), liftMap_eq_iff, map_one, ← MonoidHom.mem_ker, hk]

theorem liftMap_right [Finite G] [Finite F] {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (k : involutionCentralizer n S e) :
    (liftMap n hn S e Ψ h k).right = fieldCharacter n hn S e F Sigma ρ hdata.rho_range k := by
  rw [fieldCharacter_eq hdata, liftMap_apply]
  simp

abbrev modelLayer (F : Type) [Field F] (b : Fˣ) (n : ℕ) (hn : 2 ≤ n) (Sigma : Subgroup (F ≃+* F))
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) :
    Subgroup (SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      Sigma hSigma) :=
  ((modelInl F b n hn Sigma hSigma).comp
    (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))).range

section Layer

variable [Finite G] [IsSimpleGroup G] [Finite F]
  {ρ : centralizerFullQuotient n hn S e →* coordinateE F}

theorem modelLayer_eq_map
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    modelLayer F b n hn Sigma hSigma =
      (CFSG.layer (centralizerOddCoreQuotient n S e)).map Ψ.symm.toMonoidHom := by
  rw [← map_specialInclusion_eq_layer hnonab hfour hp hpodd hf hmodel hdata]
  ext z
  simp only [modelLayer, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply]
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨_, ⟨X, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    exact ⟨X, by simp⟩

theorem modelLayer_normal
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    (modelLayer F b n hn Sigma hSigma).Normal := by
  rw [modelLayer_eq_map hnonab hfour hp hpodd hf hmodel hdata]
  have : (CFSG.layer (centralizerOddCoreQuotient n S e)).Characteristic :=
    (ActualCentralizerSemilinear.actual_layer_component_data hnonab n hn S e hfour).2.2.1
  have : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal :=
    Subgroup.normal_of_characteristic _
  exact this.map _ Ψ.symm.surjective

theorem liftMap_mem_modelLayer_iff
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (k : involutionCentralizer n S e) :
    liftMap n hn S e Ψ h k ∈ modelLayer F b n hn Sigma hSigma ↔
      centralizerOddCoreMap n S e k ∈ CFSG.layer (centralizerOddCoreQuotient n S e) := by
  have hN := modelLayer_normal hnonab hfour hp hpodd hf hmodel hdata
  have hconj : liftMap n hn S e Ψ h k ∈ modelLayer F b n hn Sigma hSigma ↔
      Ψ.symm (centralizerOddCoreMap n S e k) ∈ modelLayer F b n hn Sigma hSigma := by
    rw [liftMap_apply]
    constructor
    · intro hm
      have := hN.conj_mem _ hm (modelInl F b n hn Sigma hSigma h)
      simpa [mul_assoc] using this
    · intro hm
      have := hN.conj_mem _ hm (modelInl F b n hn Sigma hSigma h)⁻¹
      simpa [mul_assoc] using this
  rw [hconj, modelLayer_eq_map hnonab hfour hp hpodd hf hmodel hdata]
  constructor
  · rintro ⟨z, hz, hzk⟩
    have : z = centralizerOddCoreMap n S e k := Ψ.symm.injective hzk
    rw [← this]
    exact hz
  · intro hk
    exact ⟨_, hk, rfl⟩

theorem exists_liftMap_eq
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (J : Subgroup (involutionCentralizer n S e))
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    {g} (hg : g ∈ modelLayer F b n hn Sigma hSigma) :
    ∃ j ∈ J, liftMap n hn S e Ψ h j = g := by
  have hN := modelLayer_normal hnonab hfour hp hpodd hf hmodel hdata
  set g' := modelInl F b n hn Sigma hSigma h * g * (modelInl F b n hn Sigma hSigma h)⁻¹ with hg'
  have hg'M : g' ∈ modelLayer F b n hn Sigma hSigma := hN.conj_mem _ hg _
  rw [modelLayer_eq_map hnonab hfour hp hpodd hf hmodel hdata, ← hJM] at hg'M
  obtain ⟨z, ⟨j, hj, rfl⟩, hzg⟩ := hg'M
  refine ⟨j, hj, ?_⟩
  rw [liftMap_apply]
  change _ * Ψ.symm.toMonoidHom _ * _ = _
  rw [hzg, hg']
  group

theorem liftMap_x
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    liftMap n hn S e Ψ h (centralInvolution n S e) = modelInl F b n hn Sigma hSigma
      (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
        (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F)) := by
  have hc : centralizerOddCoreMap n S e (centralInvolution n S e) ∈
      Subgroup.center (centralizerOddCoreQuotient n S e) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := centralizerOddCoreMap_surjective n S e z
    rw [← map_mul, ← map_mul,
      Subgroup.mem_center_iff.mp (centralInvolution_mem_center n S e) k]
  have hc' : Ψ.symm (centralizerOddCoreMap n S e (centralInvolution n S e)) ∈
      Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.mp hc]
  rw [liftMap_apply, mul_assoc,
    ← Subgroup.mem_center_iff.mp hc' (modelInl F b n hn Sigma hSigma h), inv_mul_cancel_left,
    ← psi_minusIdentity hnonab hfour hp hpodd hf hmodel hdata, MulEquiv.symm_apply_apply]

end Layer

end CFSG.Wreathed.NormalComponentLift
