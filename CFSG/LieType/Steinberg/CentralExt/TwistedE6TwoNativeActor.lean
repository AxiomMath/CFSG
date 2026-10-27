module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoPairKernel
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6TwoDiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7BaseChange
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Cover
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import Certificates.Certificate17002
public import Certificates.Certificate17951

public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType CFSG.StandardType.TwE6KG7 CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Overlap CFSG.StandardType.GGQ2Frame.ExcPlacement
open CFSG.EvenSmallLie.TwoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PerfectCover
open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

variable
  [Finite ↥stdGroup] [Group.IsPerfect ↥stdGroup]

@[expose] noncomputable def barEquivStd : K ≃+* K :=
  RingEquiv.ofBijective barHom barHom_bijective

theorem levi34Diag_not_mem_inner_std
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    levi34Diag ∉ (MulAut.conj : ↥stdGroup →* MulAut ↥stdGroup).range := by
  rintro ⟨g, hg⟩
  apply levi34Diag_sylow_action_ne P Q3
  apply MulEquiv.ext
  intro p
  apply Subtype.ext
  apply Subtype.ext
  rw [hopfCoverAutOnSylowTwo_coe]
  rw [← hg]
  exact hopfCoverAut_inner_apply_eq g _ (p : hopfMultiplier ↥stdGroup).2

theorem exists_std_transport_of_card_four
    {L : Type} [Field L] [Finite L] (hL4 : Nat.card L = 4)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2) :
    ∃ e : twistedE6RootGroup L σ ≃* stdGroup,
      ∀ φ, φ ∈ (RecipeExcLang.twConj L σ).range ↔
        MulAut.congr e φ ∈ (RecipeExcLang.twConj K barEquivStd).range := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  let τ : L ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hL4, natCard_K])
  have hbar : ∀ c : K, barEquivStd c = c ^ 2 := by
    intro c
    change barEquivStd.toRingHom c = c ^ 2
    rw [show barEquivStd.toRingHom = barHom from rfl, barHom_apply, bar]
  have hτ : ∀ c : L, τ (σ c) = barEquivStd (τ c) := by
    intro c
    rw [hσ c, map_pow, hbar]
  obtain ⟨e, he⟩ :=
    exists_twConj_range_baseChange (k := L) (K := K) τ σ barEquivStd hτ
  exact ⟨e, he⟩

theorem exists_inner_mul_levi_pow_of_std_outer
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    {φ : MulAut ↥stdGroup}
    (hφ : φ ∈ (RecipeExcLang.twConj K barEquivStd).range)
    (hout : φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥stdGroup) :
    ∃ g : ↥stdGroup,
      φ = MulAut.conj g * levi34Diag ∨
        φ = MulAut.conj g * levi34Diag ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup (MulAut ↥stdGroup) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner ↥stdGroup
  haveI : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  let D : Subgroup (MulAut ↥stdGroup) :=
    (compatDiagAutHom TwistTag.E6 K barHom).range
  let J : Subgroup (MulAut ↥stdGroup) := I ⊔ D
  let π : MulAut ↥stdGroup →* MulAut ↥stdGroup ⧸ I := QuotientGroup.mk' I
  have hDcompat : D = (RootCentExc.compatParamAut barEquivStd.toRingHom).range := by
    change (compatDiagAutHom TwistTag.E6 K barHom).range =
      (RootCentExc.compatParamAut barEquivStd.toRingHom).range
    rw [show (compatDiagAutHom TwistTag.E6 K barHom).range =
      twistedE6Diag K barEquivStd from rfl,
      ← CFSG.StandardType.NoOffTwE6Three.range_compatParamAut_eq_twistedE6Diag
        (K := K) (σ := barEquivStd)]
  have hJeq : J = (RecipeExcLang.twConj K barEquivStd).range := by
    change I ⊔ D = _
    rw [show I = (MulAut.conj : ↥stdGroup →* MulAut ↥stdGroup).range from rfl,
      hDcompat]
    exact inn_sup_compatParamAut_eq_range_twConj (K := K) (σ := barEquivStd)
  have hφJ : φ ∈ J := by
    rw [hJeq]
    exact hφ
  have hleviD : levi34Diag ∈ D := ⟨levi34Unit, rfl⟩
  have hleviOut : levi34Diag ∉ I := by
    change levi34Diag ∉ (MulAut.conj : ↥stdGroup →* MulAut ↥stdGroup).range
    exact levi34Diag_not_mem_inner_std P Q3
  have hDcard_le : Nat.card (D.map π) ≤ 3 := by
    rw [show D = twistedE6Diag K barEquivStd from rfl]
    exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.card_twistedE6Diag_map_le_three
      K natCard_K barEquivStd (fun c => by
        change barEquivStd.toRingHom c = c ^ 2
        rw [show barEquivStd.toRingHom = barHom from rfl, barHom_apply, bar])
  have hIbot : I.map π = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact (QuotientGroup.eq_one_iff y).2 hy
  have hJmap : J.map π = D.map π := by
    change (I ⊔ D).map π = D.map π
    rw [Subgroup.map_sup, hIbot, bot_sup_eq]
  have hφD : π φ ∈ D.map π := by
    have h := Subgroup.mem_map_of_mem π hφJ
    rwa [hJmap] at h
  have hπlevi3 : (π levi34Diag) ^ 3 = 1 := by
    rw [← map_pow, levi34Diag_pow_three, map_one]
  have hπlevi1 : π levi34Diag ≠ 1 := by
    intro h
    exact hleviOut ((QuotientGroup.eq_one_iff levi34Diag).1 h)
  have hord : orderOf (π levi34Diag) = 3 :=
    orderOf_eq_prime hπlevi3 hπlevi1
  have hzle : Subgroup.zpowers (π levi34Diag) ≤ D.map π := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map_of_mem π hleviD
  have hDcard_ge : 3 ≤ Nat.card (D.map π) := by
    calc 3 = orderOf (π levi34Diag) := hord.symm
      _ = Nat.card (Subgroup.zpowers (π levi34Diag)) := (Nat.card_zpowers _).symm
      _ ≤ Nat.card (D.map π) := Subgroup.card_le_of_le hzle
  have hDcard_eq : Nat.card (D.map π) = 3 := le_antisymm hDcard_le hDcard_ge
  have hz_eq : Subgroup.zpowers (π levi34Diag) = D.map π := by
    apply Subgroup.eq_of_le_of_card_ge hzle
    rw [hDcard_eq, Nat.card_zpowers, hord]
  have hφz : π φ ∈ Subgroup.zpowers (π levi34Diag) := by
    rw [hz_eq]
    exact hφD
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hφz
  set r : ℤ := m % 3 with hr
  have hmod : (π levi34Diag) ^ m = (π levi34Diag) ^ r := by
    rw [hr]
    exact zpow_eq_zpow_emod' m hπlevi3
  have hφr : π φ = (π levi34Diag) ^ r := by
    rw [← hm]
    exact hmod
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact Int.emod_nonneg _ (by norm_num)
  have hrlt : r < 3 := by
    rw [hr]
    exact Int.emod_lt_of_pos _ (by norm_num)
  interval_cases r
  · exfalso
    apply hout
    rw [show φ ∈ I ↔ π φ = 1 from (QuotientGroup.eq_one_iff (N := I) φ).symm]
    simpa using hφr
  · have hπeq : π φ = π levi34Diag := by simpa using hφr
    have hmem : φ * levi34Diag⁻¹ ∈ I := by
      rw [show φ * levi34Diag⁻¹ ∈ I ↔ π (φ * levi34Diag⁻¹) = 1 from
        (QuotientGroup.eq_one_iff (N := I) _).symm]
      rw [map_mul, map_inv, hπeq, mul_inv_cancel]
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, Or.inl ?_⟩
    calc φ = (φ * levi34Diag⁻¹) * levi34Diag := by group
      _ = MulAut.conj g * levi34Diag := by rw [hg]
  · have hπeq : π φ = π (levi34Diag ^ 2) := by
      simpa [map_pow] using hφr
    have hmem : φ * (levi34Diag ^ 2)⁻¹ ∈ I := by
      rw [show φ * (levi34Diag ^ 2)⁻¹ ∈ I ↔ π (φ * (levi34Diag ^ 2)⁻¹) = 1 from
        (QuotientGroup.eq_one_iff (N := I) _).symm]
      rw [map_mul, map_inv, hπeq, mul_inv_cancel]
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, Or.inr ?_⟩
    calc φ = (φ * (levi34Diag ^ 2)⁻¹) * levi34Diag ^ 2 := by group
      _ = MulAut.conj g * levi34Diag ^ 2 := by rw [hg]

theorem congr_not_mem_inner
    {L : Type} [Field L] (σ : L ≃+* L)
    (eC : twistedE6RootGroup L σ ≃* stdGroup)
    {φ : MulAut (twistedE6RootGroup L σ)} (hout : φ ∉ twistedE6Inn L σ) :
    MulAut.congr eC φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥stdGroup := by
  intro h
  obtain ⟨g, hg⟩ := h
  apply hout
  have hconj : MulAut.congr eC.symm (MulAut.conj g) = MulAut.conj (eC.symm g) :=
    CFSG.ComponentClassification.OuterAutomorphisms.congr_conj eC.symm g
  have hφconj : φ = MulAut.conj (eC.symm g) := by
    calc φ = MulAut.congr eC.symm (MulAut.congr eC φ) := by
          ext x
          simp [MulAut.congr_apply, MulEquiv.trans_apply]
      _ = MulAut.congr eC.symm (MulAut.conj g) := by
          rw [show (MulAut.congr eC) φ = MulAut.conj g from hg.symm]
      _ = MulAut.conj (eC.symm g) := hconj
  exact ⟨eC.symm g, hφconj.symm⟩

theorem native_actor_Z_map_inf_centralizer_eq_bot
    {G : Type} [Group G] [Finite G] {H E Hr Hs : Subgroup G} [Group.IsPerfect ↥H]
    {Z : Subgroup ↥H}
    {L : Type} [Field L] [Finite L] (hL4 : Nat.card L = 4)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    (ψ : ↥H →* twistedE6RootGroup L σ) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker ≤ Subgroup.center ↥H)
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (e0 : ↥E) (he : (e0 : G) ∈ Hr ⊓ Hs) (he3 : e0 ^ 3 = 1)
    (φ : MulAut (twistedE6RootGroup L σ))
    (hφrange : φ ∈ (RecipeExcLang.twConj L σ).range)
    (hφeq : ∀ x : ↥H, φ (ψ x) = ψ (ggGamma H hEN e0 x))
    (hout : φ ∉ twistedE6Inn L σ)
    (hZ : Z ≤ ψ.ker) (hZ2 : IsPGroup 2 Z)
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    Z.map H.subtype ⊓ Subgroup.centralizer (Hr ⊓ Hs : Set G) = ⊥ := by
  classical
  obtain ⟨eC, heC⟩ := exists_std_transport_of_card_four hL4 σ hσ
  let ψstd : ↥H →* ↥stdGroup := eC.toMonoidHom.comp ψ
  have hψstd : Function.Surjective ψstd := eC.surjective.comp hψ
  have hker_eq : ψstd.ker = ψ.ker := by
    ext x
    simp [ψstd]
  have hψkerstd : ψstd.ker ≤ Subgroup.center ↥H := hker_eq.le.trans hψker
  let φstd : MulAut ↥stdGroup := MulAut.congr eC φ
  have hφstdRange : φstd ∈ (RecipeExcLang.twConj K barEquivStd).range := (heC φ).1 hφrange
  have houtstd : φstd ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥stdGroup :=
    congr_not_mem_inner σ eC hout
  have hσstd : ∀ x : ↥H, ψstd (ggGamma H hEN e0 x) = φstd (ψstd x) := by
    intro x
    simp only [ψstd, φstd, MonoidHom.comp_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.coe_toMonoidHom]
    rw [eC.symm_apply_apply, hφeq]
  apply Z_map_inf_centralizer_eq_bot_of_two_subkernel ψstd hψstd hψkerstd hEN
    e0 he he3 φstd hσstd (hZ.trans hker_eq.ge) hZ2
  obtain ⟨g, hg | hg⟩ := exists_inner_mul_levi_pow_of_std_outer P Q3 hφstdRange houtstd
  · rw [hg]
    exact fixed_free_base_mul_inner_left levi34Diag
      (levi34Diag_hopfCoverAut_fixed_two P Q3) g
  · rw [hg]
    exact fixed_free_base_mul_inner_left (levi34Diag ^ 2)
      (fixed_free_base_pow_two levi34Diag levi34Diag_pow_three
        (levi34Diag_hopfCoverAut_fixed_two P Q3)) g

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
