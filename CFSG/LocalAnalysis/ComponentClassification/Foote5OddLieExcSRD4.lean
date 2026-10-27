module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRBridge
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcD4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1D4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Row
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Three
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem fieldPart_eq_one_of_fix_short
    {q : ℕ} (σ : K ≃+* K) (hD : D4Data K σ.toRingHom q)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K)
    (hfix : ∀ (A : SL(2, K)) (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (y : ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom (slShort σ.toRingHom hσ3 A) →
        (MulAut.conj h * fieldActor (t := .D4) σ δ) y = y) : δ = 1 := by
  have hodd : Odd (Nat.card K) := by
    rw [hD.card]
    exact hD.odd.pow
  have hK2 : ringChar K ≠ 2 := CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hodd
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  let ι : twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (MonoidHom.ofInjective (twistedIncl_injective σ.toRingHom)).trans
      (MulEquiv.subgroupCongr hD.range)
  have hι : ∀ x, (ι x : ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom x := fun _ => rfl
  have hδι : ∀ A : SL(2, K), fieldActor (t := .D4) σ δ (ι (slShort σ.toRingHom hσ3 A)) =
      ι (slShort σ.toRingHom hσ3 (Matrix.SpecialLinearGroup.map δ.toRingHom A)) := fun A =>
    Subtype.ext (by
      rw [coe_fieldActor, hι, hι]
      exact CFSG.ClassicalInvolution.Disconnected.AschTight.S19F.slShort_entrywise hσ3 δ
        (ringEquiv_comm_of_finite σ δ) A)
  have hmap1 : Matrix.SpecialLinearGroup.map δ.toRingHom (-1 : SL(2, K)) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg]
  have hfix' : ∀ A : SL(2, K), (MulAut.conj h * fieldActor (t := .D4) σ δ)
      (ι (slShort σ.toRingHom hσ3 A)) = ι (slShort σ.toRingHom hσ3 A) :=
    fun A => hfix A _ (hι _)
  obtain ⟨h', rfl⟩ := ι.surjective h
  have hh't : h' * slShort σ.toRingHom hσ3 (-1) = slShort σ.toRingHom hσ3 (-1) * h' := by
    have h1 := hfix' (-1)
    rw [MulAut.mul_apply, MulAut.conj_apply, hδι, hmap1, ← map_inv, ← map_mul,
      ← map_mul] at h1
    have h3 := ι.injective h1
    calc h' * slShort σ.toRingHom hσ3 (-1) =
        h' * slShort σ.toRingHom hσ3 (-1) * h'⁻¹ * h' := by group
      _ = slShort σ.toRingHom hσ3 (-1) * h' := by rw [h3]
  obtain ⟨D, hD'⟩ := linAct_of_centralizes_short hσ3 hD.neg_one h2 hD.hC₀ hD.hgF hh't
  have key : ∀ A : SL(2, K), glConjSL D (Matrix.SpecialLinearGroup.map δ.toRingHom A) = A := by
    intro A
    have h1 := hfix' A
    rw [MulAut.mul_apply, MulAut.conj_apply, hδι, ← map_inv, ← map_mul, ← map_mul] at h1
    have h3 := ι.injective h1
    rw [hD'] at h3
    exact slShort_injective hσ3 h3
  refine RingEquiv.ext fun c => ?_
  let A : SL(2, K) := ⟨!![c, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
  have h1 := congrArg (fun B : SL(2, K) => Matrix.trace (B : Matrix (Fin 2) (Fin 2) K)) (key A)
  simp only [glConjSL_coe, Matrix.trace_units_conj, Matrix.trace_fin_two,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at h1
  simpa [A] using h1

theorem mem_range_conj_of_fix_slB
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {r : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hfix : ∀ (C : SL(2, K)) (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (y : ModGL TwistTag.D4.tag K) = (c : ModGL TwistTag.D4.tag K)⁻¹ *
        twistedIncl σ.toRingHom (slB σ.toRingHom hσ3 C) * (c : ModGL TwistTag.D4.tag K) →
          r y = y) :
    r ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
  classical
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hD : D4Data K σ.toRingHom (p ^ f) := ⟨hodd, hK, hσ⟩
  obtain ⟨-, huniq, -⟩ := odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨⟨h, δ⟩, hhδ, -⟩ := huniq r
  dsimp only at hhδ
  let ι : twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (MonoidHom.ofInjective (twistedIncl_injective σ.toRingHom)).trans
      (MulEquiv.subgroupCongr hD.range)
  have hι : ∀ x, (ι x : ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom x := fun _ => rfl
  set c' := (ι (nB σ.toRingHom))⁻¹ * c with hc'def
  have hδ : δ = 1 := by
    refine fieldPart_eq_one_of_fix_short σ hD hσ3
      (c' * h * fieldActor (t := .D4) σ δ c'⁻¹) δ fun A y hy => ?_
    have hy' : ((c'⁻¹ * y * c' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) = (c : ModGL TwistTag.D4.tag K)⁻¹ *
          twistedIncl σ.toRingHom (slB σ.toRingHom hσ3 A) * (c : ModGL TwistTag.D4.tag K) := by
      rw [coe_mul, coe_mul, coe_inv, hy, hc'def, coe_mul, coe_inv, hι, slB_apply, map_mul,
        map_mul, map_inv]
      group
    have h1 := hfix A _ hy'
    rw [hhδ, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    rw [MulAut.mul_apply, MulAut.conj_apply, map_inv]
    calc c' * h * (fieldActor (t := .D4) σ δ c')⁻¹ * fieldActor (t := .D4) σ δ y *
          (c' * h * (fieldActor (t := .D4) σ δ c')⁻¹)⁻¹ =
        c' * (h * ((fieldActor (t := .D4) σ δ c')⁻¹ * fieldActor (t := .D4) σ δ y *
          fieldActor (t := .D4) σ δ c') * h⁻¹) * c'⁻¹ := by group
      _ = c' * (c'⁻¹ * y * c') * c'⁻¹ := by rw [h1]
      _ = y := by group
  rw [hhδ, hδ, fieldActor_one, mul_one]
  exact ⟨h, rfl⟩

theorem trialityInnerCoreInput_holds
    : TrialityInnerCoreInput := by
  intro p f hp hp2 hf K _ _ hK σ hσ g hg2 hg1
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hD : D4Data K σ.toRingHom (p ^ f) := ⟨hodd, hK, hσ⟩
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hD.sigma3
  have hZ : center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hx : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  obtain ⟨c, ψ, -, hψ, hcomp⟩ := HarrisLit.L33.SR.E1.triality_slB_component hp hp2 hf hK σ hσ hσ3 hx
  have hα2 : orderOf (MulAut.conj g) = 2 := by
    rw [orderOf_injective _ (conj_injective hZ) g]
    exact hx
  have hO := (burgOddCoreRow_triality hp hp2 hf hK σ hσ burgE1D4OrderThreeInput_holds
    (MulAut.conj g) hα2).1
  refine (outerCoreTrivAt_of_component hZ hO hcomp fun r _ _ hrX => ?_).outerCoreAt
  refine mem_range_conj_of_fix_slB hp hp2 hf hK σ hσ hσ3 c fun C y hy => ?_
  have hyψ : y = ψ C := Subtype.ext (by rw [hy, hψ])
  rw [hyψ]
  exact hrX _ ⟨C, rfl⟩

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
