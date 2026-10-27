module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3TriD4Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.InvolConjTransport
import CFSG.LieType.Steinberg.CentralExt.TrialityClosed
import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
import CFSG.GH74.Uniqueness.SU.SU7Gen3
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Quot
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Omega268
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3TriD4Short
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
import CFSG.ClassicalInvolution.Generic.InductionMain
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Chain
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Chain
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
import CFSG.ClassicalInvolution.ModelFacts.OddCover
import CFSG.ClassicalInvolution.Models.LinearFrames
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryFrames
import CFSG.ClassicalInvolution.RouteD.TypeAChain
import CFSG.GH74.Uniqueness.SU.SU7Gen2
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Facts
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley (TwistTag)
open scoped commutatorElement

section Center

theorem triD4_ker_eq_bot_of_section {E T : Type} [Group E] [Group T] (hE : commutator E = ⊤)
    (π : E →* T) (hcen : π.ker ≤ Subgroup.center E) (s : T →* E) (hs : ∀ g, π (s g) = g) :
    π.ker = ⊥ := by
  have hsup : ∀ x : E, ∃ z ∈ π.ker, x = s (π x) * z := fun x =>
    ⟨(s (π x))⁻¹ * x, by rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel], by group⟩
  have hrange : commutator E ≤ s.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨z, hz, hx⟩ := hsup x
    obtain ⟨w, hw, hy⟩ := hsup y
    have e : ⁅x, y⁆ = ⁅s (π x), s (π y)⁆ := by
      have h := CFSG.LocalAnalysis.GLTheoremA.T2021.t2021TD4_commutatorElement_mul_central
        (x := s (π x)) (y := s (π y)) (hcen hz) (hcen hw)
      rwa [← hx, ← hy] at h
    rw [e, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨y, rfl⟩ := hrange (hE ▸ Subgroup.mem_top x)
  have hy : y = 1 := by rw [← hs y, MonoidHom.mem_ker.1 hx]
  rw [hy, map_one]

end Center

section Main

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem triD4_center_eq_bot (H : P3Hyp q S B) {K : Type} [Field K] [Finite K] {Q : ℕ}
    {σ : K ≃+* K} (hK2 : ringChar K ≠ 2) (hQ : 3 ≤ Q) (hK : Nat.card K = Q ^ 3)
    (hσ : ∀ c, σ c = c ^ Q) (e : PSimple 3 S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    Subgroup.center ↥S = ⊥ := by
  set f : ↥S ⧸ Subgroup.center ↥S ≃*
      CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom :=
    ((psimpleEquivCenterQuot H).symm.trans e).trans
      (CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.twistedGroupEquivFixed hK2 (by omega) hK
        σ.toRingHom hσ).symm
  set π : ↥S →* CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom :=
    f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))
  have hker : π.ker = Subgroup.center ↥S := by
    ext x
    rw [MonoidHom.mem_ker]
    change f (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective π := f.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.TrialityClosed.triality_exists_section_of_central hQ hK hσ
      hsurj hker.le
  rw [← hker]
  exact triD4_ker_eq_bot_of_section (S267.perfect_of_commutator_self_eq H.perfect) π hker.le s hs

theorem triD4_modelB {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hf : 1 ≤ f) {σ δ : K ≃+* K} (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1) :
    ModelB (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (fieldActor σ δ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hQ2 : ¬ 2 ∣ p ^ f := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hQ3 : ¬ 3 ∣ p ^ f := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have h5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hQ4 : 4 ≤ p ^ f := (by omega : 4 ≤ p).trans (Nat.le_self_pow (by omega) p)
  have hσ3 : σ ^ 3 = 1 := triD4_sigma_cube hK hσ
  obtain ⟨t, htJ, ht1, ht2, htc, htfix⟩ := triD4_exists_short_involution hK2 hσ3
  exact triD4_modelB_of hK hσ hQ2 hQ3 hδ3 hδ1 (fun x hx => triD4_fieldActor_mem_short hx)
    ⟨t, htJ, ht1, ht2, htc, htfix δ⟩ (triD4_glaPLayer_short_fix hK hσ hQ4 hQ3 hδ3 hδ1)

theorem concA_of_triD4 (H : P3Hyp q S B) {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) {σ : K ≃+* K}
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (e : PSimple 3 S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    S267ConcA 3 S B := by
  classical
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  haveI : S.Normal := H.normal
  haveI : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h3p : 3 ≤ p := by have := hp.two_le; omega
  have hQ3 : 3 ≤ p ^ f := h3p.trans (Nat.le_self_pow (by omega) p)
  have hZ : Subgroup.center ↥S = ⊥ := triD4_center_eq_bot H hK2 hQ3 hK hσ e
  set ι : C₀ ≃* ↥S := e.symm.trans (psimpleEquiv H hZ)
  set φ : C₀ →* Ω := S.subtype.comp ι.toMonoidHom with hφdef
  have hφ : Function.Injective φ := S.subtype_injective.comp ι.injective
  have hφS : φ.range = S := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 ι.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hφmem : ∀ x, φ x ∈ S := fun x => (ι x).2
  have hNS : ∀ b : Ω, b ∈ Subgroup.normalizer (S : Set Ω) := fun b => by
    rw [Subgroup.normalizer_eq_top_iff.2 H.normal]
    exact Subgroup.mem_top b
  set ρ : Ω →* MulAut C₀ :=
    (MulAut.congr ι.symm).toMonoidHom.comp (MulAut.conjNormal (H := S))
  have hρ : ∀ b x, φ (ρ b x) = b * φ x * b⁻¹ := by
    intro b x
    change ((ι (ι.symm (MulAut.conjNormal b (ι x))) : ↥S) : Ω) = b * ((ι x : ↥S) : Ω) * b⁻¹
    rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]
  have hρker : ∀ b, b ∈ ρ.ker ↔ ∀ s ∈ S, b * s = s * b := by
    intro b
    rw [MonoidHom.mem_ker]
    constructor
    · intro h s hs
      rw [← hφS] at hs
      obtain ⟨x, rfl⟩ := hs
      have h1 := hρ b x
      rw [h, MulAut.one_apply] at h1
      calc b * φ x = b * φ x * b⁻¹ * b := by group
        _ = φ x * b := by rw [← h1]
    · intro h
      refine MulEquiv.ext fun x => hφ ?_
      rw [hρ, MulAut.one_apply, h _ (hφmem x)]
      group
  have hB₀ : B ⊓ ρ.ker = B ⊓ centModSubgroup 3 S := by
    ext b
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hb, hk⟩
      exact ⟨hb, S267.mem_centModSubgroup_of_commute (hNS b) fun l hl =>
        ((hρker b).1 hk l hl).symm⟩
    · rintro ⟨hb, hc⟩
      exact ⟨hb, (hρker b).2 fun s hs => H.comm_of_mem_centMod hc hs⟩
  have hcard : Nat.card (B.map ρ) = 3 ^ 3 := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker ρ B
    rw [hB₀, H.cent, H.card] at h
    norm_num at h ⊢
    omega
  obtain ⟨-, hnf, ⟨Θ, hΘ, -, hΘker, -⟩, -, -, -, hZC, -⟩ :=
    CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hconj : Function.Injective (MulAut.conj : C₀ →* MulAut C₀) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center C₀ := Subgroup.mem_center_iff.2 fun x => by
      have h1 := congrArg (fun α : MulAut C₀ => α x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hZC, Subgroup.mem_bot] at hgc
    exact hgc
  have hout : ∃ b₁ ∈ B, ρ b₁ ∉ (MulAut.conj : C₀ →* MulAut C₀).range := by
    by_contra hall
    push Not at hall
    have hle : B.map ρ ≤ (MulAut.conj : C₀ →* MulAut C₀).range := by
      rintro _ ⟨b, hb, rfl⟩
      exact hall b hb
    set F := (B.map ρ).comap (MulAut.conj : C₀ →* MulAut C₀)
    have hFmap : F.map MulAut.conj = B.map ρ := Subgroup.map_comap_eq_self hle
    have hFc : Nat.card F = 3 ^ 3 := by
      rw [← hcard, ← hFmap, Subgroup.card_map_of_injective hconj]
    have hFel : IsElemAbelian 3 F := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hconj ?_)⟩⟩, fun x hx => hconj ?_⟩
      · obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 a.2)
        obtain ⟨v, hv, hvb⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 b.2)
        have huv : u * v = v * u := congrArg Subtype.val (H.elem.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
        simp only [Subgroup.coe_mul, map_mul]
        rw [← hua, ← hvb, ← map_mul, ← map_mul, huv]
      · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hx)
        rw [map_pow, ← hux, ← map_pow, H.elem.2 u hu, map_one, map_one]
    have h9 := CFSG.HardMathSupport.Timmesfeld.CrossChar.card_le_nine_of_graphFixedRootGroup_odd hp
      hp2 hp3 hf (K := K) hK (σ := σ.toRingHom) hσ F hFel
    rw [hFc] at h9
    norm_num at h9
  obtain ⟨b₁, hb₁, hb₁out⟩ := hout
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hnf (ρ b₁)
  change ρ b₁ = MulAut.conj g * fieldActor σ δ at hgδ
  have hΘb : Θ (ρ b₁) = δ := hΘ _ g δ hgδ
  have hb₁3 : b₁ ^ 3 = 1 := H.elem.2 b₁ hb₁
  have hδ3 : δ ^ 3 = 1 := by rw [← hΘb, ← map_pow, ← map_pow, hb₁3, map_one, map_one]
  have hδ1 : δ ≠ 1 := by
    intro h
    apply hb₁out
    rw [← hΘker, MonoidHom.mem_ker, hΘb, h]
  set ψ : MulAut C₀ := fieldActor σ δ
  have hMB := triD4_modelB hp hp2 hp3 hf hK hσ hδ3 hδ1
  have hψ3 : ψ ^ 3 = 1 := hMB.1
  set b' : Ω := (φ g)⁻¹ * b₁ with hb'
  have hb'φ : ∀ x, b' * φ x * b'⁻¹ = φ (ψ x) := by
    intro x
    have h1 := hρ b₁ x
    rw [hgδ, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    calc b' * φ x * b'⁻¹ = (φ g)⁻¹ * (b₁ * φ x * b₁⁻¹) * φ g := by rw [hb']; group
      _ = φ (ψ x) := by rw [← h1]; group
  have hψψψ : ∀ y, ψ (ψ (ψ y)) = y := fun y => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hψ3, MulAut.one_apply]
  have hb'S : b' ^ 3 ∈ S := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hb', QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff (N := S) (φ g)).2 (hφmem g), inv_one,
      one_mul, ← QuotientGroup.mk_pow, hb₁3, QuotientGroup.mk_one]
  have hb'c : ∀ s ∈ S, s * b' ^ 3 = b' ^ 3 * s := by
    intro s hs
    rw [← hφS] at hs
    obtain ⟨x, rfl⟩ := hs
    have h3 : b' ^ 3 * φ x * (b' ^ 3)⁻¹ = φ x := by
      have e1 : b' ^ 3 * φ x * (b' ^ 3)⁻¹ = b' * (b' * (b' * φ x * b'⁻¹) * b'⁻¹) * b'⁻¹ := by
        rw [pow_three']
        simp only [mul_inv_rev, mul_assoc]
      rw [e1, hb'φ, hb'φ, hb'φ, hψψψ]
    calc φ x * b' ^ 3 = b' ^ 3 * φ x * (b' ^ 3)⁻¹ * b' ^ 3 := by rw [h3]
      _ = b' ^ 3 * φ x := by group
  have hb'3 : b' ^ 3 = 1 :=
    H.eq_one_of_mem_centMod hZ hb'S (S267.mem_centModSubgroup_of_commute (hNS _) hb'c)
  have hb'B₀ : ∀ b ∈ B ⊓ centModSubgroup 3 S, b' * b = b * b' := by
    intro b hb
    have h1 : Commute b (φ g) := H.comm_of_mem_centMod hb.2 (hφmem g)
    have h2 : Commute b b₁ :=
      congrArg Subtype.val (H.elem.1.is_comm.comm ⟨b, hb.1⟩ ⟨b₁, hb₁⟩)
    have hc : Commute b b' := by
      rw [hb']
      exact h1.inv_right.mul_right h2
    exact hc.eq.symm
  exact concA_of_modelB H hZ φ hφ hφS hb'3 hb'B₀ hb'φ hMB

theorem p3At_trialityD4 (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 Q).Valid) : P3At ⟨.trialityD4 Q, hv⟩ := by
  rintro q Ω _ _ S B H hchar ⟨e⟩
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 Q hv
  have hQp : Q.p = q := by
    change (TauCeti.LieTypeIndex.trialityD4 Q).characteristic = q at hchar
    rwa [TauCeti.LieTypeIndex.characteristic_trialityD4] at hchar
  exact Or.inl (concA_of_triD4 H Q.prime_p (hQp ▸ H.two) (hQp ▸ H.three) Q.exponent_pos hK hσ
    (e.trans eC))

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end


