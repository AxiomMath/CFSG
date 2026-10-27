module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.Fischer.Classification.Recognition.PSU6

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K] [Finite K]

theorem map_fixedSubgroup_fieldActor_eq
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hK : Nat.card K = (p ^ a) ^ 6)
    (σ δ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ((p ^ a) ^ 2)) (hδ : ∀ c, δ c = c ^ ((p ^ a) ^ 3)) :
    (fixedSubgroup (fieldActor σ δ (t := TwistTag.D4))).map
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype =
      (graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
        (baseChangeGL (fixSubfield δ).subtype) := by
  classical
  set K₀ := fixSubfield δ with hK₀
  set σ₀ := fixSubfieldRestrict σ δ with hσ₀def
  have : Fact p.Prime := ⟨hp⟩
  have hK6 : Nat.card K = p ^ (6 * a) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK6
  have hK₀c : Nat.card K₀ = (p ^ a) ^ 3 := by
    have h := card_fixSubfield_of_sq_pow hp (e := 3 * a) (by omega)
      (by rw [hK]; ring) δ (fun c => by rw [hδ]; ring_nf)
    rw [h]
    ring
  have hσ₀ : ∀ c : K₀, σ₀.toRingHom c = c ^ ((p ^ a) ^ 2) := fun c => Subtype.ext (by
    rw [SubmonoidClass.coe_pow]
    exact (coe_fixSubfieldRestrict σ δ c).trans (hσ c))
  have hP3 : ∀ (M : Type) [Field M], diagramMap TwistTag.D4 M ^ 3 = 1 :=
    fun M _ => diagramMap_pow_order TwistTag.D4 M
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    set Ω := AlgebraicClosure K₀ with hΩ
    have : CharP Ω p := charP_of_injective_algebraMap (algebraMap K₀ Ω).injective p
    let ιA : K →ₐ[K₀] Ω := IsAlgClosed.lift
    set ι : K →+* Ω := ιA.toRingHom with hιdef
    have hι : ∀ c : K₀, ι (c : K) = algebraMap K₀ Ω c := fun c => ιA.commutes c
    have hιK₀ : ι.comp K₀.subtype = algebraMap K₀ Ω := RingHom.ext fun c => hι c
    set Fr := iterateFrobenius Ω p a with hFrdef
    have hFr : ∀ c, Fr c = c ^ (p ^ a) := fun c => by rw [hFrdef, iterateFrobenius_def]
    have h1 : Fr.comp (ι.comp σ.toRingHom) = ι.comp δ.toRingHom := RingHom.ext fun c => by
      change Fr (ι (σ c)) = ι (δ c)
      rw [hFr, ← map_pow, hσ, hδ, ← pow_mul, ← pow_succ]
    have h2 : (Fr.comp Fr).comp ι = ι.comp σ.toRingHom := RingHom.ext fun c => by
      change Fr (Fr (ι c)) = ι (σ c)
      rw [hFr, hFr, ← pow_mul, ← sq, hσ, map_pow]
    have huδ : baseChangeGL δ.toRingHom (u : ModGL TwistTag.D4.tag K) = u := by
      rw [← units_map_entrywiseHom_eq_baseChangeGL, ← coe_fieldActor σ δ u]
      exact congrArg Subtype.val hu
    have huT := (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom) u.2
    rw [mem_twistedFixedGroup_iff_twistHom, twistHom_apply,
      units_map_entrywiseHom_eq_baseChangeGL] at huT
    obtain ⟨huC, huP⟩ := huT
    have huσ : baseChangeGL σ.toRingHom (u : ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * u * diagramMap TwistTag.D4 K := by
      calc baseChangeGL σ.toRingHom (u : ModGL TwistTag.D4.tag K) =
          (diagramMap TwistTag.D4 K)⁻¹ * (diagramMap TwistTag.D4 K *
            baseChangeGL σ.toRingHom (u : ModGL TwistTag.D4.tag K) *
              (diagramMap TwistTag.D4 K)⁻¹) * diagramMap TwistTag.D4 K := by group
        _ = _ := by rw [huP]
    have hPσ : baseChangeGL σ.toRingHom (diagramMap TwistTag.D4 K) = diagramMap TwistTag.D4 K :=
      baseChangeGL_diagramMap σ.toRingHom TwistTag.D4
    set U := baseChangeGL ι (u : ModGL TwistTag.D4.tag K) with hU
    have hσσ : baseChangeGL σ.toRingHom (baseChangeGL σ.toRingHom
        (u : ModGL TwistTag.D4.tag K)) = (diagramMap TwistTag.D4 K ^ 2)⁻¹ * u *
          diagramMap TwistTag.D4 K ^ 2 := by
      rw [huσ, map_mul, map_mul, map_inv, hPσ, huσ]
      simp only [sq, mul_inv_rev, mul_assoc]
    have e1 : baseChangeGL Fr (baseChangeGL ι
        (baseChangeGL σ.toRingHom (u : ModGL TwistTag.D4.tag K))) = U := by
      rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, RingHom.comp_assoc, h1,
        ← baseChangeGL_baseChangeGL, huδ]
    have hFrU : Units.map (entrywiseHom Fr) U = (diagramMap TwistTag.D4 Ω ^ 2)⁻¹ * U *
        diagramMap TwistTag.D4 Ω ^ 2 := by
      rw [units_map_entrywiseHom_eq_baseChangeGL]
      conv_lhs => rw [← e1]
      rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h2, ← baseChangeGL_baseChangeGL,
        hσσ, map_mul, map_mul, map_inv, map_pow, baseChangeGL_diagramMap ι TwistTag.D4]
    have hUC : U ∈ adjointGroup TwistTag.D4.tag Ω := baseChangeGL_mem_adjointGroup ι huC
    have hUS : diagramMap TwistTag.D4 Ω ^ 2 * Units.map (entrywiseHom Fr) U *
        (diagramMap TwistTag.D4 Ω ^ 2)⁻¹ = U := by
      rw [hFrU]
      simp [mul_assoc]
    obtain ⟨-, hset, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group p a hp
      ha K₀ hK₀c Ω 2 (Or.inr rfl) σ₀.toRingHom hσ₀ Fr hFr
    have hUJ : U ∈ ((graphFixedRootGroup TwistTag.D4 K₀ σ₀.toRingHom).map
        (baseChangeGL (algebraMap K₀ Ω)) : Set (ModGL TwistTag.D4.tag Ω)) := by
      rw [← hset]
      exact ⟨hUC, hUS⟩
    obtain ⟨j, hj, hjU⟩ := hUJ
    refine ⟨j, hj, ?_⟩
    apply baseChangeGL_injective ι
    rw [baseChangeGL_baseChangeGL, hιK₀, hjU]
    rfl
  · rintro _ ⟨j, hj, rfl⟩
    have hJC : baseChangeGL K₀.subtype j ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      map_baseChangeGL_graphFixedRootGroup_le σ₀.surjective
        (fun c => (coe_fixSubfieldRestrict σ δ c).symm) ⟨j, hj, rfl⟩
    refine ⟨⟨_, hJC⟩, ?_, rfl⟩
    change fieldActor σ δ ⟨_, hJC⟩ = ⟨_, hJC⟩
    refine Subtype.ext ?_
    rw [coe_fieldActor, units_map_entrywiseHom_eq_baseChangeGL]
    change baseChangeGL δ.toRingHom (baseChangeGL K₀.subtype j) = baseChangeGL K₀.subtype j
    rw [baseChangeGL_baseChangeGL,
      show δ.toRingHom.comp K₀.subtype = K₀.subtype from RingHom.ext fun c => c.2]

end CFSG.ComponentClassification.CatLeafProof
