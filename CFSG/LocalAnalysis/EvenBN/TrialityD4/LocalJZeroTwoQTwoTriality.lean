module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExTwoPartE
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
import CFSG.LieType.Chevalley.GraphFixedF4Canonical
import CFSG.RankThree.PartOne.KGD.D4T36Core
import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_conj_mem_of_odd_index {C : Type*} [Group C] [Finite C] {J : Subgroup C}
    {m : ℕ} (hm : Odd m) (hcard : Nat.card C = Nat.card J * m) {x : C}
    (hx : IsPGroup 2 (zpowers x)) : ∃ g : C, g * x * g⁻¹ ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 2 J))
  have hP₀ := P₀.card_eq_multiplicity
  set P : Subgroup C := (P₀ : Subgroup J).map J.subtype with hP
  have hPcard : Nat.card P = 2 ^ (Nat.card C).factorization 2 := by
    rw [hP, card_map_of_injective J.subtype_injective, hP₀, hcard,
      Nat.factorization_mul (Nat.card_pos (α := J)).ne' (by obtain ⟨r, rfl⟩ := hm; omega)]
    have hm2 : m.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => by
        obtain ⟨r, rfl⟩ := hm
        omega)
    simp [hm2]
  set S : Sylow 2 C := Sylow.ofCard P hPcard with hS
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q S
  have hxQ : x ∈ (Q : Subgroup C) := hQ (mem_zpowers x)
  have hxS : g * x * g⁻¹ ∈ (S : Subgroup C) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨x, hxQ, rfl⟩
  rw [hS, Sylow.coe_ofCard] at hxS
  obtain ⟨y, -, hy⟩ := hxS
  exact ⟨g, hy ▸ y.2⟩

theorem center_eq_bot_of_isSimpleGroup' {X : Type*} [Group X] (hX : IsSimpleGroup X)
    (hna : ¬ ∀ a b : X, a * b = b * a) : center X = ⊥ := by
  rcases hX.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    apply hna
    intro a b
    exact (mem_center_iff.1 (h ▸ mem_top a : a ∈ center X) b).symm

theorem card_centralizer_conj {C : Type*} [Group C] (g c : C) :
    Nat.card (centralizer ({g * c * g⁻¹} : Set C)) = Nat.card (centralizer ({c} : Set C)) := by
  refine (Nat.card_congr ((MulAut.conj g).toEquiv.subtypeEquiv fun y => ?_)).symm
  simp only [mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    MulAut.conj_apply]
  constructor
  · intro h
    calc g * y * g⁻¹ * (g * c * g⁻¹) = g * (y * c) * g⁻¹ := by group
      _ = g * (c * y) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * (g * y * g⁻¹) := by group
  · intro h
    have h' : g * (y * c) * g⁻¹ = g * (c * y) * g⁻¹ := by
      calc g * (y * c) * g⁻¹ = g * y * g⁻¹ * (g * c * g⁻¹) := by group
        _ = g * c * g⁻¹ * (g * y * g⁻¹) := h
        _ = g * (c * y) * g⁻¹ := by group
    simpa using h'

theorem sixteen_dvd_seven_pow_sq_sub_one' (f : ℕ) : 2 ^ 4 ∣ (7 ^ f) ^ 2 - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow (7 ^ 2) 1 f
  rw [one_pow, ← pow_mul, mul_comm, pow_mul] at h
  exact (by norm_num : 2 ^ 4 ∣ 7 ^ 2 - 1).trans h

section Cert

theorem involutionTwoPart_G2_adjoint {K : Type} [Field K] [Finite K] {p f k s : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hK : Nat.card K = p ^ f)
    (hs : 2 ^ s ∣ (p ^ f) ^ 2 - 1) (hks : k ≤ 2 * s - 1) (hk : k ≤ 6) :
    SeitzReduction.RankOne.InvolutionTwoPart (adjointGroup .G2 K) k := by
  have hKodd := SeitzReduction.RankOne.FiveEx.odd_card hp hp2 hK
  refine SeitzReduction.RankOne.involutionTwoPart_F4_E8_G2_of_innerDiag (Or.inr (Or.inr rfl)) hp
    hp2 (fun _ => hp3) (SeitzReduction.RankOne.FiveEx.one_le_of_card hK) hK hk
    fun α g a hαg hα => ?_
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα
    exact absurd hα (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    ComponentClassification.CatLeafProof.exists_toralCentralizer_equiv_of_innerDiag
      (Or.inl rfl) hKodd hαg hα2
  rw [Nat.card_congr Θ.toEquiv]
  exact (pow_dvd_pow 2 hks).trans
    (SeitzReduction.RankOne.two_pow_dvd_card_toralCentralizer_G2 hKodd (hK ▸ hs) b hb (hb1 hα1))

theorem trialityInnerTwoPartInput_of_pow {p f k s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hs : 2 ^ s ∣ (p ^ f) ^ 2 - 1) (hks : k ≤ 2 * s - 1) (hk : k ≤ 6) :
    SeitzReduction.RankOne.TrialityInnerTwoPartInput p f k := by
  classical
  intro J _ hm α hα hαi
  have hadm := SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hm
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  have hK3' : Nat.card K = p ^ (3 * f) := by rw [hK3, ← pow_mul, mul_comm]
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3'
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  obtain ⟨a, rfl⟩ := hαi
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  set c : C := e a with hc
  have hβc : MulAut.congr e (MulAut.conj a) = MulAut.conj c := by
    ext x
    simp [hc, MulAut.congr_apply, MulAut.conj_apply]
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hβ2 : MulAut.conj c ^ 2 = 1 := by
    rw [← hβc, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hc2 : c ^ 2 = 1 := hinj (by rw [map_pow, hβ2, map_one])
  have hc1 : c ≠ 1 := by
    intro h1
    have hα1 : MulAut.conj c = 1 := by rw [h1, map_one]
    rw [← hβc] at hα1
    have hα1' : MulAut.conj a = 1 := (MulAut.congr e).injective (by rw [hα1, map_one])
    rw [hα1', orderOf_one] at hα
    exact absurd hα (by norm_num)
  have hfix : Nat.card (fixedSubgroup (MulAut.conj a)) =
      Nat.card (centralizer ({c} : Set C)) := by
    rw [Nat.card_congr
      (ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv e (MulAut.conj a)).toEquiv,
      hβc, SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf]
  rw [hfix]
  have hσ3 := ringEquiv_cube_apply_eq hK3 hσ
  have hJC := GH74.GLS.Stage2.Bender.Thm1.d4_trialityFieldImage_self_le σ
  set Jg : Subgroup C := (trialityFieldImage σ σ).subgroupOf C with hJg
  have hJgcard : Nat.card Jg =
      ComponentClassification.CatLeaf.lieOrderNumerator .G2 0 (p ^ f) := by
    rw [hJg, Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv,
      ← Nat.card_congr (HardMathSupport.Lang.Triality.fixedEquivTrialityFieldImage σ hσ3),
      HardMathSupport.Lang.Triality.card_fixed_fieldActor_D4_of_frobenius hp hf hK3 σ hσ]
  have hCcard : Nat.card C =
      ComponentClassification.CatLeaf.lieOrderNumerator .trialityD4 0 (p ^ f) := by
    have h1 := SeitzReduction.CrossChar.card_mul_lieOrderDivisor_of_ne_Tits hadm hm (by decide)
    rw [Nat.card_congr e.toEquiv] at h1
    simpa [ComponentClassification.CatLeaf.lieOrderDivisor] using h1
  have hidx : Nat.card C = Nat.card Jg * ((p ^ f) ^ 6 * ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1)) := by
    rw [hCcard, hJgcard]
    simp only [ComponentClassification.CatLeaf.lieOrderNumerator]
    ring
  have hqodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hodd : Odd ((p ^ f) ^ 6 * ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1)) := by
    refine (hqodd.pow).mul ?_
    have h8 : Even ((p ^ f) ^ 8 + (p ^ f) ^ 4) :=
      (hqodd.pow (n := 8)).add_odd (hqodd.pow (n := 4))
    exact h8.add_one
  have hcp : IsPGroup 2 (zpowers c) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hc2 hc1, pow_one]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_odd_index hodd hidx hcp
  set x : Jg := ⟨g * c * g⁻¹, hg⟩ with hxdef
  have hkq : Nat.card (fixSubfield σ) = p ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hp hf hK3 σ hσ
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, hkq]
    have h5 : 3 ≤ p ^ f := by
      have h3 : 3 ≤ p := by
        rcases hp.eq_two_or_odd' with h | h
        · exact absurd h hp2
        · have := hp.two_le
          obtain ⟨r, hr⟩ := h
          omega
      exact h3.trans (Nat.le_self_pow (by omega) p)
    exact_mod_cast h5
  have hG2 : SeitzReduction.RankOne.InvolutionTwoPart Jg k :=
    (involutionTwoPart_G2_adjoint hp hp2 hp3 hkq hs hks hk).of_mulEquiv
      ((subgroupOfEquivOfLe hJC).trans
        (HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivG2 σ hk3))
  obtain ⟨hsimp, hnab⟩ := GH74.GLS.Stage2.Bender.Thm1.d4_trialityFieldImage_self_simple hp2 σ
  have hZJ : center Jg = ⊥ := by
    have e' := subgroupOfEquivOfLe hJC
    rw [← map_center_eq e'.symm, center_eq_bot_of_isSimpleGroup' hsimp hnab, Subgroup.map_bot]
  have hx2 : x ^ 2 = 1 := Subtype.ext (by
    change (g * c * g⁻¹) ^ 2 = 1
    rw [conj_pow, hc2, mul_one, mul_inv_cancel])
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : g * c * g⁻¹ = 1 := congrArg Subtype.val h1
    apply hc1
    have h3 : c = g⁻¹ * (g * c * g⁻¹) * g := by group
    rw [h3, h2]
    group
  have hαx : orderOf (MulAut.conj x) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [← map_pow, hx2, map_one]) fun h1 => hx1 ?_
    exact mulAut_conj_injective_of_center_eq_bot hZJ (by rw [h1, map_one])
  have h2x := hG2 _ hαx
  rw [SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf] at h2x
  have hle : (centralizer ({x} : Set Jg)).map Jg.subtype ≤
      centralizer ({g * c * g⁻¹} : Set C) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy
  have hdvd : Nat.card (centralizer ({x} : Set Jg)) ∣
      Nat.card (centralizer ({g * c * g⁻¹} : Set C)) := by
    rw [← card_map_of_injective Jg.subtype_injective]
    exact card_dvd_of_le hle
  rw [← card_centralizer_conj g c]
  exact h2x.trans hdvd

end Cert

end CFSG.LocalAnalysis.EvenBN.TrialityD4
