module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09StdSubFU4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB
  CFSG.GH74.Exceptional CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer StdU4

namespace StdU5

theorem pow_mod3 {M : Type} [Monoid M] {y : M} (hy : y ^ 3 = 1) (n : ℕ) :
    y ^ n = y ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hy, one_pow, one_mul]

theorem pow_val_add {M : Type} [Monoid M] {y : M} (hy : y ^ 3 = 1) (a b : ZMod 3) :
    y ^ (a + b).val = y ^ a.val * y ^ b.val := by
  rw [ZMod.val_add, ← pow_mod3 hy, pow_add]

theorem comm_helper {M : Type} [Group M] (K1 K2 y1 y2 : M) (h : K2 * y1 = y1 * K2) :
    K1 * K2 * (y1 * y2) = K1 * y1 * (K2 * y2) := by
  simp only [mul_assoc]
  rw [← mul_assoc K2 y1 y2, h, mul_assoc y1 K2 y2]

theorem stdSub_u5_data : ∃ (τ : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* M5) (TM : Subgroup M5),
    Function.Injective τ ∧ IsPGroup 2 TM ∧ 8 < Nat.card TM ∧
    (∀ x : Multiplicative (ZMod 3 × ZMod 3), ∀ t ∈ TM,
      τ (emb13 x) * t * (τ (emb13 x))⁻¹ ∈ TM) ∧
    (∃ t ∈ TM, ∃ x : Multiplicative (ZMod 3 × ZMod 3), t * τ (emb13 x) ≠ τ (emb13 x) * t) := by
  obtain ⟨Kb, hKc, -, hKz, -, -, -, hKcat⟩ := m5_u4_layer
  obtain ⟨ε⟩ := bridge_u4two hKcat
  set κ : PSp43 →* M5 := Kb.subtype.comp ε.symm.toMonoidHom with hκdef
  have hκinj : Function.Injective κ := (Subgroup.subtype_injective Kb).comp ε.symm.injective
  have hκmem : ∀ s : PSp43, κ s ∈ Kb := fun s => (ε.symm s).2
  have hcomm : ∀ s : PSp43, Commute (κ s) yM5 := fun s =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKc (hκmem s))
  have hy3 : yM5 ^ 3 = 1 := yM5_pow_three
  have hF : ∀ a c a' c' : ZMod 3,
      κ (TphiQ (emb13 (Multiplicative.ofAdd (a + a', c + c')))) =
        κ (TphiQ (emb13 (Multiplicative.ofAdd (a, c)))) *
          κ (TphiQ (emb13 (Multiplicative.ofAdd (a', c')))) := by
    intro a c a' c'
    rw [← Prod.mk_add_mk, ofAdd_add, map_mul, map_mul, map_mul]
  let f : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) → M5 := fun v =>
    κ (TphiQ (emb13 (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.2)))) * yM5 ^ (v.toAdd.2.1).val
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    show κ (TphiQ (emb13 (Multiplicative.ofAdd (x.toAdd.1 + y.toAdd.1, x.toAdd.2.2 + y.toAdd.2.2))))
        * yM5 ^ (x.toAdd.2.1 + y.toAdd.2.1).val =
      (κ (TphiQ (emb13 (Multiplicative.ofAdd (x.toAdd.1, x.toAdd.2.2)))) * yM5 ^ (x.toAdd.2.1).val) *
        (κ (TphiQ (emb13 (Multiplicative.ofAdd (y.toAdd.1, y.toAdd.2.2)))) * yM5 ^ (y.toAdd.2.1).val)
    rw [hF, pow_val_add hy3]
    exact comm_helper _ _ _ _ ((hcomm (TphiQ (emb13 (Multiplicative.ofAdd
      (y.toAdd.1, y.toAdd.2.2))))).pow_right _).eq
  have hτF : ∀ x : Multiplicative (ZMod 3 × ZMod 3),
      MonoidHom.mk' f hmul (emb13 x) = κ (TphiQ (emb13 x)) := by
    intro x
    show κ (TphiQ (emb13 x)) * yM5 ^ (0 : ZMod 3).val = κ (TphiQ (emb13 x))
    simp
  have hinj : Function.Injective (MonoidHom.mk' f hmul) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : κ (TphiQ (emb13 (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.2)))) *
        yM5 ^ (v.toAdd.2.1).val = 1 := hv
    have hyb : yM5 ^ (v.toAdd.2.1).val =
        (κ (TphiQ (emb13 (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.2)))))⁻¹ :=
      eq_inv_of_mul_eq_one_right hv'
    have hmemK : yM5 ^ (v.toAdd.2.1).val ∈ Kb := by
      rw [hyb]; exact Kb.inv_mem (hκmem _)
    have hmemZ : yM5 ^ (v.toAdd.2.1).val ∈ Subgroup.zpowers yM5 :=
      Subgroup.pow_mem _ (Subgroup.mem_zpowers yM5) _
    have h1 : yM5 ^ (v.toAdd.2.1).val = 1 := by
      have hmem : yM5 ^ (v.toAdd.2.1).val ∈ Kb ⊓ Subgroup.zpowers yM5 :=
        Subgroup.mem_inf.2 ⟨hmemK, hmemZ⟩
      rw [hKz, Subgroup.mem_bot] at hmem
      exact hmem
    have hb : v.toAdd.2.1 = 0 := by
      have h3 : 3 ∣ (v.toAdd.2.1).val := by
        have := (orderOf_dvd_iff_pow_eq_one).2 h1
        rwa [orderOf_eq_prime hy3 yM5_ne_one] at this
      have hlt : (v.toAdd.2.1).val < 3 := ZMod.val_lt _
      have h0 : (v.toAdd.2.1).val = 0 := by omega
      exact (ZMod.val_eq_zero _).1 h0
    have hF1 : κ (TphiQ (emb13 (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.2)))) = 1 := by
      rw [hb, ZMod.val_zero, pow_zero, mul_one] at hv'
      exact hv'
    have hF2 : TphiQ (emb13 (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.2))) = 1 :=
      hκinj (by rw [hF1, map_one])
    have hF3 : emb13 (Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.2)) = 1 :=
      TphiQ_injective (by rw [hF2, map_one])
    have hF4 : Multiplicative.ofAdd (v.toAdd.1, v.toAdd.2.2) =
        (1 : Multiplicative (ZMod 3 × ZMod 3)) :=
      emb13_injective (by rw [hF3, map_one])
    have h5 : (v.toAdd.1, v.toAdd.2.2) = (0, 0) := congrArg Multiplicative.toAdd hF4
    have e1 : v.toAdd.1 = 0 := congrArg Prod.fst h5
    have e3 : v.toAdd.2.2 = 0 := congrArg Prod.snd h5
    apply Multiplicative.toAdd.injective
    show (v.toAdd.1, v.toAdd.2.1, v.toAdd.2.2) = (0, 0, 0)
    rw [e1, hb, e3]
  refine ⟨MonoidHom.mk' f hmul, Psi.range.map κ, hinj, isPGroup_T4.map κ, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hκinj, card_T4]
    norm_num
  · intro x t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    rw [hτF, ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem κ (hFN_T4 x s hs)
  · obtain ⟨t, ht, x, hx⟩ := hTc_T4
    refine ⟨κ t, Subgroup.mem_map_of_mem κ ht, x, ?_⟩
    rw [hτF]
    intro h
    apply hx
    apply hκinj
    rw [map_mul, map_mul]
    exact h

theorem card_center_dvd_two_u5two (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G]
    [Finite G] {K : Subgroup G} (hK : CFSG.Open.IsQuasisimple ↥K)
    (h : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU5two) :
    Nat.card (Subgroup.center ↥K) ∣ 2 := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isU5two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := lieModel_twistedA' 4 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hK hm (a := 1) (b := 1) (c := 1) (d := 1)
    (by decide) (by decide) (by norm_num)
  exact hdvd.trans (by norm_num)

end StdU5

end CFSG.LocalAnalysis.GLTheoremA.CatB
