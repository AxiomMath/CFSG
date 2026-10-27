module

public import CFSG.RankThree.Chevalley.SteinbergBIE6D4Layers
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley


theorem baseChangeGL_trialityTransposition {K L : Type} [Field K] [Field L] (f : K →+* L) :
    baseChangeGL f (trialityTransposition K) = trialityTransposition L := by
  refine Units.ext ((baseChange_baseChangeEnd f _).unique fun b => ?_)
  simp [trialityTransposition, permModuleMap, Finsupp.mapRange_single]

theorem baseChangeGL_trialityTranspositionAut {K L : Type} [Field K] [Field L] (f : K →+* L)
    (g : ModGL TwistTag.D4.tag K) :
    baseChangeGL f (trialityTranspositionAut K g) =
      trialityTranspositionAut L (baseChangeGL f g) := by
  rw [trialityTranspositionAut_apply, trialityTranspositionAut_apply, map_mul, map_mul, map_inv,
    baseChangeGL_trialityTransposition]

def d4ResTw {Ω : Type} [Field Ω] (e : ℕ) (x : subsystemGroup Tag.E6 Ω d4Support) :
    ModGL TwistTag.D4.tag Ω :=
  if e = 1 then d4Res Ω x else trialityTranspositionAut Ω (d4Res Ω x)

def d4ThetaFixedEquivLayer {Ω : Type} [Field Ω] (Fr : Ω →+* Ω) (e : ℕ) :
    d4ThetaFixed Ω Fr e ≃* d4Layer Fr e :=
  Subgroup.equivMapOfInjective _ (subsystemGroup Tag.E6 Ω d4Support).subtype
    Subtype.val_injective

section Bridge

variable {ℓ d : ℕ} {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {σ : K →+* K} {Fr : Ω →+* Ω}

theorem exists_d4Layer_equiv_one (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hK : Nat.card K = (ℓ ^ d) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ d)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    ∃ φ : d4Layer Fr 1 ≃* graphFixedRootGroup TwistTag.D4 K σ,
      ∀ x : d4ThetaFixed Ω Fr 1,
        baseChangeGL (algebraMap K Ω) (φ (d4ThetaFixedEquivLayer Fr 1 x) : ModGL TwistTag.D4.tag K)
          = d4ResTw 1 x := by
  obtain ⟨φ, hφ⟩ := exists_d4ThetaFixed_equiv hℓ hd hK (Or.inl rfl) (σ := σ) (Fr := Fr)
    (K := K) (Ω := Ω) (fun c => by rw [pow_one]; exact hσ c) hFr
  refine ⟨(d4ThetaFixedEquivLayer Fr 1).symm.trans φ, fun x => ?_⟩
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hφ x]
  simp only [d4ResTw, ↓reduceIte]
  rfl

theorem exists_d4Layer_equiv_two (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hK : Nat.card K = (ℓ ^ d) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ d)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    ∃ φ : d4Layer Fr 2 ≃* graphFixedRootGroup TwistTag.D4 K σ,
      ∀ x : d4ThetaFixed Ω Fr 2,
        baseChangeGL (algebraMap K Ω) (φ (d4ThetaFixedEquivLayer Fr 2 x) : ModGL TwistTag.D4.tag K)
          = d4ResTw 2 x := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  let σe : K ≃+* K := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσe : σe.toRingHom = σ := RingHom.ext fun _ => rfl
  have hcard : ∀ c : K, c ^ ((ℓ ^ d) ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card]; exact FiniteField.pow_card c
  have hσs : ∀ c, σe.symm.toRingHom c = c ^ ((ℓ ^ d) ^ 2) := fun c => by
    change σe.symm c = _
    rw [RingEquiv.symm_apply_eq]
    change c = σ _
    have h3 : (ℓ ^ d) ^ 2 * ℓ ^ d = (ℓ ^ d) ^ 3 := by ring
    rw [hσ, ← pow_mul, h3, hcard]
  obtain ⟨φ, hφ⟩ := exists_d4ThetaFixed_equiv hℓ hd hK (Or.inr rfl) (σ := σe.symm.toRingHom)
    (Fr := Fr) (K := K) (Ω := Ω) hσs hFr
  have hmap := map_trialityTranspositionAut_graphFixedRootGroup (K := K) σe
  rw [hσe] at hmap
  let χ : graphFixedRootGroup TwistTag.D4 K σ ≃* graphFixedRootGroup TwistTag.D4 K σe.symm.toRingHom :=
    (Subgroup.equivMapOfInjective _ (trialityTranspositionAut K).toMonoidHom
      (trialityTranspositionAut K).injective).trans (MulEquiv.subgroupCongr hmap)
  have hχ : ∀ y, (χ y : ModGL TwistTag.D4.tag K) = trialityTranspositionAut K y := fun y => rfl
  refine ⟨(d4ThetaFixedEquivLayer Fr 2).symm.trans (φ.trans χ.symm), fun x => ?_⟩
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have h1 : (χ (χ.symm (φ x)) : ModGL TwistTag.D4.tag K) = φ x := by rw [MulEquiv.apply_symm_apply]
  rw [hχ] at h1
  have h2 := congrArg (fun z => trialityTranspositionAut Ω (baseChangeGL (algebraMap K Ω) z)) h1
  simp only [← baseChangeGL_trialityTranspositionAut (algebraMap K Ω),
    trialityTranspositionAut_apply_apply, hφ] at h2
  simpa [d4ResTw] using h2

theorem exists_d4Layer_equiv (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hK : Nat.card K = (ℓ ^ d) ^ 3)
    {e : ℕ} (he : e = 1 ∨ e = 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ d)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    ∃ φ : d4Layer Fr e ≃* graphFixedRootGroup TwistTag.D4 K σ,
      ∀ x : d4ThetaFixed Ω Fr e,
        baseChangeGL (algebraMap K Ω) (φ (d4ThetaFixedEquivLayer Fr e x) : ModGL TwistTag.D4.tag K)
          = d4ResTw e x := by
  rcases he with rfl | rfl
  · exact exists_d4Layer_equiv_one hℓ hd hK hσ hFr
  · exact exists_d4Layer_equiv_two hℓ hd hK hσ hFr

theorem nonempty_d4Layer_equiv (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hK : Nat.card K = (ℓ ^ d) ^ 3)
    {e : ℕ} (he : e = 1 ∨ e = 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ d)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    Nonempty (d4Layer Fr e ≃* graphFixedRootGroup TwistTag.D4 K σ) :=
  (exists_d4Layer_equiv (Ω := Ω) hℓ hd hK he hσ hFr).elim fun φ _ => ⟨φ⟩

end Bridge

end CFSG.HardMathSupport.Malle.SeitzCube
