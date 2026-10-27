module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Shape
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Trace
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Galois
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Residue
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4Native

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


variable {K : Type} [Field K] [Finite K]

theorem burgOddCoreFor_conj_aLong
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hc₁ : BurgE1D4OrderThreeInput)
    {t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (aLongTD4 K)) :
    BurgOddCoreFor (MulAut.conj t) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hD : D4Data K σ.toRingHom (p ^ f) := ⟨hodd, hK, hσ⟩
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hD.sigma3
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  let ι : twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (MonoidHom.ofInjective (twistedIncl_injective σ.toRingHom)).trans
      (MulEquiv.subgroupCongr hD.range)
  have hι : ∀ x, (ι x : ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom x := fun _ => rfl
  have htι : ι (τL hσ3) = t := Subtype.ext (by rw [hι, twistedIncl_slLong_neg_one hσ3, ht])
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hmap : (fixedSubgroup (MulAut.conj t)).map ι.symm.toMonoidHom =
      Subgroup.centralizer ({τL hσ3} : Set (twistedGroup σ.toRingHom)) := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : t * x * t⁻¹ = x := hx
      rw [← htι] at h1
      have h2 := congrArg ι.symm h1
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at h2
      change ι.symm x * τL hσ3 = τL hσ3 * ι.symm x
      calc ι.symm x * τL hσ3 = τL hσ3 * ι.symm x * (τL hσ3)⁻¹ * τL hσ3 := by rw [h2]
        _ = τL hσ3 * ι.symm x := by group
    · intro hy
      refine ⟨ι y, ?_, ι.symm_apply_apply y⟩
      change t * ι y * t⁻¹ = ι y
      rw [← htι, ← map_mul, ← map_inv, ← map_mul]
      congr 1
      calc τL hσ3 * y * (τL hσ3)⁻¹ = y * τL hσ3 * (τL hσ3)⁻¹ := by rw [hy]
        _ = y := by group
  let e : fixedSubgroup (MulAut.conj t) ≃* Yd hσ3 :=
    ((fixedSubgroup (MulAut.conj t)).equivMapOfInjective ι.symm.toMonoidHom ι.symm.injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨S, -⟩ := exists_native_shape_d4 hσ3 hD
  have : CharP (fixedField σ.toRingHom) p := Subfield.charP _ p
  have hF2 : ringChar (fixedField σ.toRingHom) ≠ 2 := by
    rw [ringChar.eq (fixedField σ.toRingHom) p]
    exact hp2
  have : Finite (twistedGroup σ.toRingHom) :=
    Finite.of_injective _ (twistedIncl_injective σ.toRingHom)
  have hF1 : pPrimeCore 2 (fixedSubgroup (MulAut.conj t)) = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 e.symm
    rw [pPrimeCore_eq_bot_of_shape hK2 hF2 S, Subgroup.map_bot] at h1
    exact h1.symm
  have hτ2 : orderOf (τL hσ3) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul, neg_one_mul, neg_neg, map_one]
    · intro h
      have h1 := slLong_injective hσ3 (h.trans (map_one _).symm)
      have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom) =>
        ((A : Matrix (Fin 2) (Fin 2) (fixedField σ.toRingHom)) 0 0)) h1
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        Matrix.neg_apply, Matrix.one_apply_eq] at h2
      exact Ring.neg_one_ne_one_of_char_ne_two hF2 h2
  have ht2 : orderOf t = 2 := by
    rw [← htι, MulEquiv.orderOf_eq]
    exact hτ2
  obtain ⟨hcoe, huniq, -⟩ := odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hq : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = p ^ f :=
    card_fixedField_eq (σ := σ.toRingHom) hp hf hK hσ
  refine burgOddCoreFor_of_inner hZ hF1 fun β hβ hαβ hfix => ?_
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := huniq β
  dsimp only at hgδ
  have htr : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom),
      δ (LinearMap.trace K (RootModule d4 K)
        ((twistedIncl σ.toRingHom (slLong σ.toRingHom hσ3 A) : ModGL d4 K) :
          Module.End K (RootModule d4 K))) =
      LinearMap.trace K (RootModule d4 K)
        ((twistedIncl σ.toRingHom (slLong σ.toRingHom hσ3 A) : ModGL d4 K) :
          Module.End K (RootModule d4 K)) := by
    intro A
    set x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ι (slLong σ.toRingHom hσ3 A)
      with hxdef
    have hx : x ∈ fixedSubgroup (MulAut.conj t) := by
      change t * x * t⁻¹ = x
      rw [hxdef, ← htι, ← map_mul, ← map_inv, ← map_mul]
      congr 1
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (slLong_mem_cent hσ3 A)
      calc τL hσ3 * slLong σ.toRingHom hσ3 A * (τL hσ3)⁻¹ =
          slLong σ.toRingHom hσ3 A * τL hσ3 * (τL hσ3)⁻¹ := by rw [h1]
        _ = slLong σ.toRingHom hσ3 A := by group
    have h1 := hfix x hx
    rw [hgδ, MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 := congrArg (fun u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      (u : ModGL TwistTag.D4.tag K)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcoe] at h2
    have h3 := congrArg (fun u : ModGL TwistTag.D4.tag K =>
      LinearMap.trace K (RootModule d4 K) (u : Module.End K (RootModule d4 K))) h2
    simp only [Units.val_mul, LinearMap.trace_conj, units_map_entrywiseHom_eq_baseChangeGL,
      trace_baseChangeGL] at h3
    rw [← hι, ← hxdef]
    exact h3
  have hδF : ∀ c, σ c = c → δ c = c := fun c hc =>
    fixes_fixedField_of_fixes_slLong_traces hσ3 δ htr c hc
  rcases eq_one_or_eq_or_eq_inv_of_fixes_eqLocus hK σ hσ hq δ hδF with rfl | hδσ
  ·
    exact MonoidHom.mem_range.2 ⟨g, by rw [hgδ, fieldActor_one, mul_one]⟩
  ·
    exfalso
    refine hc₁ (p ^ f) K σ hodd hK hσ t g δ ht2 hδσ ?_ ?_ ?_
    · rw [← hgδ]
      exact hβ
    · rw [← hgδ]
      exact hαβ
    · rw [← hgδ]
      exact hfix

end CFSG.ComponentClassification.CatLeafProof
