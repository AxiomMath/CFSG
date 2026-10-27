module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

open Matrix CFSG.Open CFSG.Fischer CFSG.LieType.BorelTits CFSG.AGLEmbedding
  CFSG.LocalAnalysis.GLTheoremA.LevelLieU6 CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer

@[expose] noncomputable def hform : ReflForm F4 (Fin 6 → F4) := unitaryForm 2 1 hF4card 6

theorem hform_β (u v : Fin 6 → F4) : hform.β u v = ∑ i, u i ^ 2 * v i := by
  rw [hform, unitaryForm_β]
  simp only [unitaryInvolution_apply, pow_one]

@[expose] noncomputable def isoU : Subgroup (GL (Fin 6) F4) where
  carrier := {A | ∀ u v : Fin 6 → F4,
    hform.β ((A : Matrix (Fin 6) (Fin 6) F4) *ᵥ u) ((A : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) = hform.β u v}
  one_mem' := by
    intro u v
    simp
  mul_mem' := by
    intro A B hA hB u v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hB]
  inv_mem' := by
    intro A hA u v
    have h := hA ((A⁻¹ : GL (Fin 6) F4) *ᵥ u) ((A⁻¹ : GL (Fin 6) F4) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
    have hinv : (A : Matrix (Fin 6) (Fin 6) F4) * ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hinv, Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact h.symm

theorem statedSU_le_isoU : StatedSU 6 (2 ^ 1) F4 ≤ isoU := by
  intro A hA u v
  exact statedSU_preserves hF4card hA u v

theorem flag_exists (T : Subgroup M6) (hT0 : T ≠ ⊥) (hT2 : IsPGroup 2 ↥T) :
    ∃ W : Submodule F4 (Fin 6 → F4), W ≠ ⊥ ∧ IsTotallyIsotropicSU 2 W ∧
      ∀ g : GL (Fin 6) F4, g ∈ isoU →
        (∀ t ∈ T, ∃ t' ∈ T, (t' : GL (Fin 6) F4) = g * (t : GL (Fin 6) F4) * g⁻¹) →
        (∀ t ∈ T, ∃ t' ∈ T, (t' : GL (Fin 6) F4) = g⁻¹ * (t : GL (Fin 6) F4) * g) →
        ∀ w ∈ W, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ w ∈ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let i : M6 →* ↥isoU := Subgroup.inclusion statedSU_le_isoU
  have hi : Function.Injective i := Subgroup.inclusion_injective _
  let R : Subgroup ↥isoU := T.map i
  have hρ : IsIsometric hform (natRep isoU) := by
    intro h u v
    rw [natRep_apply, natRep_apply]
    exact h.2 u v
  have hinj : Function.Injective (natRep isoU) := natRep_injective _
  have hR2 : IsPGroup 2 ↥R := hT2.map i
  have hR0 : R ≠ ⊥ := fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective T hi).1 h)
  refine ⟨isoSeq hform (natRep isoU) R 1, isoSeq_one_ne_bot hform (natRep isoU) 2 hρ hinj R hR2 hR0,
    ?_, ?_⟩
  · intro v hv w hw
    have hperp : w ∈ hform.perp (isoSeq hform (natRep isoU) R 1) :=
      isoSeq_isTotallyIsotropic hform (natRep isoU) R 1 hw
    have h1 := (ReflForm.mem_perp hform).1 hperp v hv
    rw [hform_β] at h1
    exact h1
  · intro g hg hgT hgT' w hw
    have hnorm : (⟨g, hg⟩ : ↥isoU) ∈ Subgroup.normalizer (R : Set ↥isoU) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · rintro ⟨t, ht, rfl⟩
        obtain ⟨t', ht', e⟩ := hgT t ht
        exact ⟨t', ht', Subtype.ext e⟩
      · rintro ⟨s, hs, hse⟩
        obtain ⟨t', ht', e⟩ := hgT' s hs
        refine ⟨t', ht', ?_⟩
        have h1 : (s : GL (Fin 6) F4) = g * (n : GL (Fin 6) F4) * g⁻¹ := congrArg Subtype.val hse
        apply Subtype.ext
        show (t' : GL (Fin 6) F4) = (n : GL (Fin 6) F4)
        rw [e, h1]
        group
    have hmem := apply_mem_isoSeq hform (natRep isoU) hρ R 1 hnorm hw
    rwa [natRep_apply] at hmem

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

end
