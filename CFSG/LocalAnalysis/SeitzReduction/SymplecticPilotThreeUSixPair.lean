module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSixCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOmegaOrth
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
public import CFSG.RankThree.PartOne.CTP.SuSpin

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockStandardPair minusLongBlock
  shortBlock finOne)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.Universal.Spin (quadMinus)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.CTP (lbEmb sbEmb)
open CFSG.RankThree.PartOne.CTP.SU4Even (exists_kleinDataEven map_minusLongBlock_eq_lbEmb
  map_shortBlock_eq_sbEmb minusLongBlock_injective)
open CFSG.SeitzReduction.F4Pilot (statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Faithful

theorem injective_comp_of_ker_le_center {A B X : Type*} [Group A] [Group B] [Group X]
    {φ : A →* B} (hφ : Function.Injective φ) (hA : center A = ⊥) {g : B →* X}
    (hg : g.ker ≤ center B) : Function.Injective (g.comp φ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : φ a ∈ center B := hg ha
  have hac : a ∈ center A := by
    rw [mem_center_iff]
    intro x
    apply hφ
    rw [map_mul, map_mul]
    exact mem_center_iff.1 hc (φ x)
  rw [hA] at hac
  exact hac

theorem charP_shortField {F : Type} [Field F] [CharP F 2] {b c : F}
    [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] :
    CharP (CFSG.LieType.Universal.Spin.Twisted.ShortField b c) 2 :=
  charP_of_injective_algebraMap (algebraMap F _).injective 2

end Faithful

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem pieceCore_one_eq_map_lbEmb_of_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2] {C₀ : GL (Fin (2 * 2)) K'}
    (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
    (ι : K ≃+* h.fixedField) (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G)
    (hrange : Φ.range = neighbourCore e 0)
    (hker : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))
    (hN1 : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (tauSp x))) =
        ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G)) :
    pieceCore e ({1} : Finset (Fin 3)) =
      ((lbEmb (unitaryInvolution K' 2 f)).range.map
        (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom).map Φ := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hY : (uStdTorus h hC₀).map Φ =
      modelToG e ((siegelTorus K 2).map (complSpHom (K := K) 0)) := by
    have h1 := map_uModelSU_map_eq_of_N1 e 0 h hC₀ ι tauSp Φ hN1 (siegelTorus K 2)
    rwa [map_tauSp_siegelTorus_eq ι] at h1
  rw [pieceCore_eq_map_perfectCore_centralizer e hK4 (k := 0) (by decide)
    leviTorusSp_one_le_sup map_siegelTorus_zero_le_leviTorusSp_one Φ hrange hker
    (uStdTorus h hC₀) hY, perfectCore_centralizer_uStdTorus_eq h hC₀ (four_le_two_pow hf)]

end Pieces

section Pair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem twistedPair_of_unitary_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (hn : SpThreeUnitaryNormalized e t f 0 true) :
    ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (W : Subgroup G),
      TwistedB2BlockStandardPair hirr W (modelToG e (simpleRootSL2 K 1))
        (pieceCore e ({2} : Finset (Fin 3))) := by
  have hone := pieceCore_one_eq_of_unitary_twisted hKc hf hn
  obtain ⟨K', _, h, _, C₀, -, hC₀, ι₀, Φ, hrange, hker, hN1, -⟩ := hn
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have hN1' : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι₀ : K →+* h.fixedField) 2 (tauSp x))) =
        ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G) := fun x => hN1 x
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic K
  have := CFSG.LieType.Universal.Spin.Twisted.fact_shortField hirr
  have := charP_shortField (b := b) (c := c)
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hKc h.card_eq_sq hirr
  set χ := ctuGramEquiv h hC₀ (RingEquiv.refl K') with hχ
  set ψ₀ := D.phiSUEven h.card_eq_sq hirr with hψ₀
  set θ : spinGroup (quadMinus 3 K b c) →* G :=
    Φ.comp (χ.toMonoidHom.comp ψ₀.toMonoidHom) with hθ
  have hψ₀hom : ψ₀.toMonoidHom = D.PhiSUEven hirr := MonoidHom.ext fun _ => rfl
  have hθker : θ.ker ≤ center _ := fun x hx =>
    mem_center_of_mulEquiv_mem_center (ψ₀.trans χ) (hker hx)
  have hmap : ∀ H : Subgroup (spinGroup (quadMinus 3 K b c)),
      H.map θ = ((H.map (D.PhiSUEven hirr)).map χ.toMonoidHom).map Φ := by
    intro H
    rw [Subgroup.map_map, Subgroup.map_map, hθ, ← hψ₀hom]
    rfl
  refine ⟨b, c, hirr, θ.range, θ, rfl, hθker,
    injective_comp_of_ker_le_center minusLongBlock_injective center_SL_two_eq_bot_of_charTwo
      hθker,
    injective_comp_of_ker_le_center
      (CFSG.RankThree.PartOne.CTP.shortBlock_injective_even hirr 3 finOne)
      center_SL_two_eq_bot_of_charTwo hθker, ?_, ?_⟩
  · change (minusLongBlock b c).range.map θ = _
    rw [hmap, map_minusLongBlock_eq_lbEmb D hKc h.card_eq_sq hirr, ← hone,
      pieceCore_one_eq_map_lbEmb_of_twisted hKc hf e h hC₀ ι₀ Φ hrange hker hN1']
  · change (shortBlock hirr 3 finOne).range.map θ = _
    rw [hmap, map_shortBlock_eq_sbEmb D hKc h.card_eq_sq hirr, map_range_sbEmb_ctuGramEquiv,
      pieceCore_two_eq_map_lambdaU_of_N1 hKc hf e h hC₀ ι₀ Φ hrange hker hN1']

theorem spThreeOmegaMinusTwistedPairInput_holds : SpThreeOmegaMinusTwistedPairInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot htw
  have htC : t ∈ centralizer (L : Set G) := by
    have h1 : t ∈ zpowers t := mem_zpowers t
    rw [← hKt] at h1
    exact h1.1
  exact twistedPair_of_unitary_twisted hKc hf e
    (spThreeUnitaryNormalized_of_twisted hset hKc hf e htC hto 0 (hroot 0) htw)

theorem spThreeUnitaryEvenRecognitionInput_of_standardInput
    (hs : SpThreeUnitaryEvenStandardInput) : SpThreeUnitaryEvenRecognitionInput :=
  spThreeUnitaryEvenRecognitionInput_of_twistedPair hs spThreeOmegaMinusTwistedPairInput_holds

end Pair

end CFSG.SeitzReduction.SymplecticPilot
