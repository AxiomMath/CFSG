module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Transfer
public import CFSG.LieType.Steinberg.TwistedE6.Defs
import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
import CFSG.ClassicalInvolution.Q3.Q3E6TLayer
import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6SU6
import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.LeviBasic
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUModel
import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
import CFSG.LocalAnalysis.StandardType.SUCenterOdd
import CFSG.RankThree.PartOne.CTP.SuSpin
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
import CFSG.RankThree.PartOne.CTP.SU4EvenBridge

public section

namespace CFSG.GroupTheory.GomiLeviExc.TwistedE6

open Subgroup CFSG.Blueprint.Chevalley CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.Steinberg.TwistedE6

open CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.Q3.Q3E6T
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.CTP.SU4Even
open scoped Matrix MatrixGroups

private theorem unitaryJInv_eq_antidiag {K : Type} [Field K] [CharP K 2] :
    (unitaryJInv : Matrix (Fin 4) (Fin 4) K) = antidiag 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryJInv, antidiag, Fin.rev, CharTwo.neg_eq]

private theorem involEquiv_toRingHom {K : Type} [Field K] (σ : K ≃+* K)
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c) : involEquiv σ.toRingHom hσ = σ := by
  ext c
  rfl

private theorem involutive_toRingHom {K : Type} [Field K] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
  change σ (σ c) = c
  exact hσ c

private noncomputable def suToUnitary {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) : SU σ 4 →* unitaryGroup σ.toRingHom (involutive_toRingHom σ hσ) where
  toFun g := ⟨⟨matS σ g, (mem_SU.mp g.2).1⟩, by
    refine mem_unitaryGroup_of_mat σ.toRingHom (involutive_toRingHom σ hσ) _ ?_
    rw [unitaryJInv_eq_antidiag]
    exact (mem_SU.mp g.2).2⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

private theorem suToUnitary_injective {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) : Function.Injective (suToUnitary σ hσ) := by
  intro g g' h
  have h1 : matS σ g = matS σ g' :=
    congrArg (fun x : unitaryGroup σ.toRingHom (involutive_toRingHom σ hσ) =>
      ((x : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
  exact Subtype.ext (Units.ext h1)

private theorem suToUnitary_surjective {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) : Function.Surjective (suToUnitary σ hσ) := by
  intro h
  set g : Matrix.SpecialLinearGroup (Fin 4) K := h.1 with hg
  have hform : conjTr σ ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      antidiag 4 * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = antidiag 4 := by
    have h1 := CFSG.ClassicalInvolution.RouteD.conjTr_mul_unitaryJInv_mul_of_sigmaA σ h.2
    rwa [unitaryJInv_eq_antidiag] at h1
  refine ⟨⟨g, ?_, hform⟩, ?_⟩
  · exact g.2
  · refine Subtype.ext (Subtype.ext ?_)
    rfl

private theorem suToUnitary_comp_sbEmb {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) :
    (suToUnitary σ hσ).comp (sbEmb σ hσ) = usb σ.toRingHom (involutive_toRingHom σ hσ) := by
  refine MonoidHom.ext fun B => Subtype.ext (Subtype.ext ?_)
  rw [MonoidHom.comp_apply]
  change matS σ (sbElt σ hσ B) =
    (usb σ.toRingHom (involutive_toRingHom σ hσ) B).1.1
  rw [matS_sbElt, coe_usb, coe_usbSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sbMat, CharTwo.neg_eq]

private theorem ulb_mem_range_comp_lbEmb {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) (A : SL(2, fixedField σ.toRingHom)) :
    ulb σ.toRingHom (involutive_toRingHom σ hσ) A ∈
      ((suToUnitary σ hσ).comp (lbEmb σ)).range := by
  let h := ulb σ.toRingHom (involutive_toRingHom σ hσ) A
  have hform : conjTr σ h.1.1 * antidiag 4 * h.1.1 = antidiag 4 := by
    have h1 := CFSG.ClassicalInvolution.RouteD.conjTr_mul_unitaryJInv_mul_of_sigmaA
      (involEquiv σ.toRingHom (involutive_toRingHom σ hσ)) h.2
    rw [involEquiv_toRingHom, unitaryJInv_eq_antidiag] at h1
    exact h1
  let g : SU σ 4 := ⟨h.1, h.1.2, hform⟩
  have hmat : matS σ g = h.1.1 := rfl
  have hfix0 : g ∈ stabVec σ (Pi.single 0 1) := by
    rw [mem_stabVec]
    change ((ulb σ.toRingHom (involutive_toRingHom σ hσ) A : unitaryGroup _ _) :
      SL(4, K)).1 *ᵥ Pi.single 0 1 = Pi.single 0 1
    rw [coe_ulb]
    change CFSG.ClassicalInvolution.Phan.blockMat 4 1
      (liftSL σ.toRingHom 2 A).1 *ᵥ Pi.single 0 1 = Pi.single 0 1
    funext a
    fin_cases a <;>
      simp [Matrix.mulVec, CFSG.ClassicalInvolution.Phan.blockMat_apply]
  have hfix3 : g ∈ stabVec σ (Pi.single 3 1) := by
    rw [mem_stabVec]
    change ((ulb σ.toRingHom (involutive_toRingHom σ hσ) A : unitaryGroup _ _) :
      SL(4, K)).1 *ᵥ Pi.single 3 1 = Pi.single 3 1
    rw [coe_ulb]
    change CFSG.ClassicalInvolution.Phan.blockMat 4 1
      (liftSL σ.toRingHom 2 A).1 *ᵥ Pi.single 3 1 = Pi.single 3 1
    funext a
    fin_cases a <;>
      simp [Matrix.mulVec, CFSG.ClassicalInvolution.Phan.blockMat_apply]
  obtain ⟨X, hX⟩ := mem_range_lbEmb_of_fix (σ := σ) g hfix0 hfix3
  refine ⟨X, ?_⟩
  rw [MonoidHom.comp_apply, hX]
  exact Subtype.ext (Subtype.ext rfl)

private theorem card_range_comp_lbEmb {k : Type} [Field k] [Finite k] [CharP k 2] {f : ℕ}
    (hk : Nat.card k = (2 ^ f) ^ 2) :
    Nat.card ((suToUnitary (unitaryInvolution k 2 f)
      (unitaryInvolution_involutive hk)).comp
        (lbEmb (unitaryInvolution k 2 f))).range = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [MonoidHom.range_comp,
    Subgroup.card_map_of_injective
      (suToUnitary_injective (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk)),
    natCard_range_lbEmb, CFSG.LieType.Steinberg.card_SU_two (p := 2) (F := k) (f := f) hk]

private theorem card_range_ulb {k : Type} [Field k] [Finite k] [CharP k 2] {f : ℕ}
    (hk : Nat.card k = (2 ^ f) ^ 2) :
    Nat.card (ulb (unitaryInvolution k 2 f).toRingHom
      (involutive_toRingHom (unitaryInvolution k 2 f)
        (unitaryInvolution_involutive hk))).range = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hfix : Nat.card (fixedField (unitaryInvolution k 2 f).toRingHom) = 2 ^ f := by
    refine CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_fixedSubfield_of_card
      (θ := (unitaryInvolution k 2 f).toRingHom) (q := 2 ^ f) hk ?_
    intro c
    exact unitaryInvolution_apply (K := k) (p := 2) (f := f) c
  have hdom : Nat.card (ulb (unitaryInvolution k 2 f).toRingHom
      (involutive_toRingHom (unitaryInvolution k 2 f)
        (unitaryInvolution_involutive hk))).range =
      Nat.card (SL(2, fixedField (unitaryInvolution k 2 f).toRingHom)) :=
    (Nat.card_congr (MonoidHom.ofInjective (ulb_injective _ _)).toEquiv).symm
  rw [hdom, CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hfix]

private theorem range_comp_lbEmb_eq_ulb {k : Type} [Field k] [Finite k] [CharP k 2] {f : ℕ}
    (hk : Nat.card k = (2 ^ f) ^ 2) :
    ((suToUnitary (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk)).comp
      (lbEmb (unitaryInvolution k 2 f))).range =
      (ulb (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk))).range := by
  have hle : (ulb (unitaryInvolution k 2 f).toRingHom
      (involutive_toRingHom (unitaryInvolution k 2 f)
        (unitaryInvolution_involutive hk))).range ≤
      ((suToUnitary (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk)).comp
        (lbEmb (unitaryInvolution k 2 f))).range := by
    rintro _ ⟨A, rfl⟩
    exact ulb_mem_range_comp_lbEmb _ _ A
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_range_comp_lbEmb hk, card_range_ulb hk]

local instance twistedE6SU4NeZeroRank : NeZero (Tag.rank .F4) := ⟨by decide⟩

variable {k : Type} [Field k] [Finite k] [CharP k 2] {θ : k →+* k} {q : ℕ}

private instance instNeZeroTwistedDatumRank {θ : k →+* k} :
    NeZero (twistedDatum k θ).rank :=
  ⟨by have h : (twistedDatum k θ).rank = Tag.rank .F4 := rfl; rw [h]; decide⟩

omit θ q
  in
private theorem range_ulb_sup_range_usb_eq_top {f : ℕ} (hk : Nat.card k = (2 ^ f) ^ 2) :
    (ulb (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk))).range ⊔
      (usb (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk))).range = ⊤ := by
  let σ := unitaryInvolution k 2 f
  have hσ := unitaryInvolution_involutive hk
  have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield k 2 f) = 2 ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield hk
  have : CharP (CFSG.LieType.Steinberg.fixedSubfield k 2 f) 2 :=
    RingHom.charP (CFSG.LieType.Steinberg.fixedSubfield k 2 f).subtype
      (CFSG.LieType.Steinberg.fixedSubfield k 2 f).subtype.injective 2
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic
    (CFSG.LieType.Steinberg.fixedSubfield k 2 f)
  have := CFSG.LieType.Universal.Spin.Twisted.fact_shortField hirr
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hF hk hirr
  have htop := spinMinusModel_blocks_sup_eq_top_even hirr
  change (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ at htop
  have hgen : (lbEmb σ).range ⊔ (sbEmb σ hσ).range = ⊤ := by
    rw [← map_minusLongBlock_eq_lbEmb D hF hk hirr, ← map_shortBlock_eq_sbEmb D hF hk hirr,
      ← Subgroup.map_sup, htop, ← MonoidHom.range_eq_map, D.range_PhiSUEven_eq_top hk hirr]
  have hmap : ((lbEmb σ).range.map (suToUnitary σ hσ)) ⊔
      ((sbEmb σ hσ).range.map (suToUnitary σ hσ)) = ⊤ := by
    rw [← Subgroup.map_sup, hgen]
    exact Subgroup.map_top_of_surjective _ (suToUnitary_surjective σ hσ)
  rw [← MonoidHom.range_comp, ← MonoidHom.range_comp,
    range_comp_lbEmb_eq_ulb hk, suToUnitary_comp_sbEmb σ hσ] at hmap
  exact hmap

omit θ q in
private theorem range_comp_suToUnitary_eq_leviM {f : ℕ} (hk : Nat.card k = (2 ^ f) ^ 2)
    (emb : unitaryGroup (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk)) →*
      fixedGroup k (unitaryInvolution k 2 f).toRingHom)
    (hlb : emb.comp (ulb (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk))) =
      CFSG.ClassicalInvolution.WeakCT.nodeHom1 (unitaryInvolution k 2 f).toRingHom)
    (hsb : emb.comp (usb (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk))) =
      CFSG.ClassicalInvolution.WeakCT.nodeHom2 (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk)))
    (hunit : (ulb (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk))).range ⊔
      (usb (unitaryInvolution k 2 f).toRingHom
        (involutive_toRingHom (unitaryInvolution k 2 f)
          (unitaryInvolution_involutive hk))).range = ⊤) :
    (emb.comp (suToUnitary (unitaryInvolution k 2 f)
      (unitaryInvolution_involutive hk))).range =
      leviM (twistedDatum k (unitaryInvolution k 2 f).toRingHom)
        ({(1 : Fin (twistedDatum k (unitaryInvolution k 2 f).toRingHom).rank),
          (2 : Fin (twistedDatum k (unitaryInvolution k 2 f).toRingHom).rank)} :
          Set (Fin (twistedDatum k (unitaryInvolution k 2 f).toRingHom).rank)) := by
  let σ := unitaryInvolution k 2 f
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hk
  have hθ2 : ∀ c, σ.toRingHom (σ.toRingHom c) = c := involutive_toRingHom σ hσ
  have hrange : (emb.comp (suToUnitary σ hσ)).range =
      leviM (twistedDatum k σ.toRingHom)
        ({(1 : Fin (twistedDatum k σ.toRingHom).rank),
          (2 : Fin (twistedDatum k σ.toRingHom).rank)} :
          Set (Fin (twistedDatum k σ.toRingHom).rank)) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (suToUnitary_surjective σ hσ),
      ← MonoidHom.range_eq_map]
    have hemb : emb.range = (ulb σ.toRingHom hθ2).range.map emb ⊔
        (usb σ.toRingHom hθ2).range.map emb := by
      rw [← Subgroup.map_sup, hunit, ← MonoidHom.range_eq_map]
    rw [hemb, ← MonoidHom.range_comp, ← MonoidHom.range_comp, hlb, hsb,
      ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_one,
      ← CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_two σ.toRingHom hθ2]
    exact (CFSG.GroupTheory.GomiLeviExc.leviM_pair (twistedDatum k σ.toRingHom)
      (1 : Fin (twistedDatum k σ.toRingHom).rank)
      (2 : Fin (twistedDatum k σ.toRingHom).rank)).symm
  simpa [σ] using hrange

theorem gomiLeviFactor_leviM_one_two (hk : Nat.card k = q ^ 2) (hθ : ∀ c, θ c = c ^ q) :
    GomiLeviFactor ↥(leviM (twistedDatum k θ) ({1, 2} : Set (Fin (Tag.rank .F4)))) := by
  obtain ⟨f, hf1, rfl⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hk
  have hθeq : θ = (unitaryInvolution k 2 f).toRingHom := by
    ext c
    rw [hθ]
    exact (unitaryInvolution_apply (K := k) (p := 2) (f := f) c).symm
  subst hθeq
  let σ := unitaryInvolution k 2 f
  change GomiLeviFactor ↥(leviM (twistedDatum k σ.toRingHom)
    ({(1 : Fin (twistedDatum k σ.toRingHom).rank),
      (2 : Fin (twistedDatum k σ.toRingHom).rank)} : Set (Fin (twistedDatum k σ.toRingHom).rank)))
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hk
  have hθ2 : ∀ c, σ.toRingHom (σ.toRingHom c) = c := involutive_toRingHom σ hσ
  obtain ⟨emb, hinj, hlb, hsb⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_levi12 σ.toRingHom hθ2
  have hunit : (ulb σ.toRingHom hθ2).range ⊔ (usb σ.toRingHom hθ2).range = ⊤ :=
    range_ulb_sup_range_usb_eq_top hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsu := CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_su
    (F := k) (f := f) hk (n' := 4) (by norm_num) (by simp)
  have hodd := CFSG.StandardType.odd_natCard_of_le_center_SU σ
    (H := Subgroup.center (SU σ 4)) le_rfl
  have hchev :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isChevTwo_of_classicalTwoOrG2 hsu.2
  have hrange := range_comp_suToUnitary_eq_leviM hk emb hlb hsb hunit
  have := CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
    CFSG.LieType.Steinberg.Minuscule.e6Data_valid k
  have : Finite ↥(fixedGroup k σ.toRingHom) := Subtype.finite
  exact gomiLeviFactor_of_injective hsu.1 hodd hchev (emb.comp (suToUnitary σ hσ))
    (hinj.comp (suToUnitary_injective σ hσ)) hrange

end CFSG.GroupTheory.GomiLeviExc.TwistedE6
