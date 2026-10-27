module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4Native
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem orderOf_slLong_neg_one
    {K : Type} [Field K] {σ : K →+* K} (hσ3 : ∀ c, σ (σ (σ c)) = c)
    (hF2 : ringChar (fixedField σ) ≠ 2) : orderOf (slLong σ hσ3 (-1)) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul, neg_one_mul, neg_neg, map_one]
  · intro h
    have h1 := slLong_injective hσ3 (h.trans (map_one _).symm)
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) =>
      ((A : Matrix (Fin 2) (Fin 2) (fixedField σ)) 0 0)) h1
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h2
    exact Ring.neg_one_ne_one_of_char_ne_two hF2 h2

theorem exists_conj_eq_aLong_of_twisted
    {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ} (hD : D4Data K σ q)
    (htw : ∀ x x' : twistedGroup σ, x * x = 1 → x' * x' = 1 → x ≠ 1 → x' ≠ 1 →
      ∃ g, g * x * g⁻¹ = x')
    (s : graphFixedRootGroup TwistTag.D4 K σ) (hs : orderOf s = 2) :
    ∃ c : graphFixedRootGroup TwistTag.D4 K σ,
      ((c * s * c⁻¹ : graphFixedRootGroup TwistTag.D4 K σ) : ModGL TwistTag.D4.tag K) =
        rootDiagUnit TwistTag.D4.tag (aLongTD4 K) := by
  classical
  have hσ3 := hD.sigma3
  have hodd : Odd (Nat.card K) := by rw [hD.card]; exact hD.odd.pow
  have hK2 : ringChar K ≠ 2 := CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hodd
  have hF2 : ringChar (fixedField σ) ≠ 2 := by
    obtain ⟨p, hpc⟩ := CharP.exists K
    have hp : ringChar K = p := ringChar.eq K p
    have : CharP (fixedField σ) p := Subfield.charP _ p
    rw [ringChar.eq (fixedField σ) p, ← hp]
    exact hK2
  let ι : twistedGroup σ ≃* graphFixedRootGroup TwistTag.D4 K σ :=
    (MonoidHom.ofInjective (twistedIncl_injective σ)).trans (MulEquiv.subgroupCongr hD.range)
  have hx : ι.symm s * ι.symm s = 1 := by
    rw [← map_mul, ← sq, ← hs, pow_orderOf_eq_one, map_one]
  have hx1 : ι.symm s ≠ 1 := fun h => by
    have h1 : s = 1 := ι.symm.injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at hs
    exact absurd hs (by decide)
  have hτ : orderOf (τL hσ3) = 2 := orderOf_slLong_neg_one hσ3 hF2
  have hτ2 : τL hσ3 * τL hσ3 = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hτ1 : τL hσ3 ≠ 1 := fun h => by
    rw [h, orderOf_one] at hτ
    exact absurd hτ (by decide)
  obtain ⟨y, hy⟩ := htw _ _ hx hτ2 hx1 hτ1
  refine ⟨ι y, ?_⟩
  have h1 : ι y * s * (ι y)⁻¹ = ι (τL hσ3) := by
    rw [← hy, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [h1]
  exact twistedIncl_slLong_neg_one hσ3

theorem exists_conj_eq_aLong
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hs : orderOf s = 2) :
    ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ((c * s * c⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (aLongTD4 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set L := GaloisField p (3 * f) with hL
  set Fr := iterateFrobenius L p f with hFr
  have : Fintype K := Fintype.ofFinite K
  have : Fintype L := Fintype.ofFinite L
  have hLc : Nat.card L = (p ^ f) ^ 3 := by
    rw [hL, GaloisField.card p (3 * f) (by omega), pow_mul']
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hDL : D4Data L Fr (p ^ f) := ⟨hodd, hLc, fun c => iterateFrobenius_def p f c⟩
  have hconjL := exists_conj_eq_aLong_of_twisted hDL (fun x x' hx hx' hx1 hx1' =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf hx hx' hx1 hx1')
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hLc]
  let θ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  have hmap := map_baseChangeGL_graphFixedRootGroup_eq TwistTag.D4 hp hf K hK σ.toRingHom hσ
    θ.toRingHom (Fr := Fr) (fun c => iterateFrobenius_def p f c)
    (Finite.surjective_of_injective Fr.injective)
  let e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 L Fr :=
    ((graphFixedRootGroup TwistTag.D4 K σ.toRingHom).equivMapOfInjective
      (baseChangeGL (τ := TwistTag.D4.tag) θ.toRingHom) (baseChangeGL_injective _)).trans
      (MulEquiv.subgroupCongr hmap)
  have he : ∀ x, (e x : ModGL TwistTag.D4.tag L) =
      baseChangeGL θ.toRingHom (x : ModGL TwistTag.D4.tag K) := fun _ => rfl
  obtain ⟨c', hc'⟩ := hconjL (e s) (by rw [MulEquiv.orderOf_eq]; exact hs)
  refine ⟨e.symm c', baseChangeGL_injective θ.toRingHom ?_⟩
  rw [← he, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc', baseChangeGL_rootDiagUnit]
  congr 1
  funext i
  fin_cases i
  · show (-1 : Lˣ) = Units.map θ.toRingHom.toMonoidHom (-1)
    exact Units.ext (by simp)
  · show (-1 : Lˣ) = Units.map θ.toRingHom.toMonoidHom (-1)
    exact Units.ext (by simp)
  · show (1 : Lˣ) = Units.map θ.toRingHom.toMonoidHom 1
    exact Units.ext (by simp)
  · show (-1 : Lˣ) = Units.map θ.toRingHom.toMonoidHom (-1)
    exact Units.ext (by simp)

end CFSG.ComponentClassification.CatLeafProof
