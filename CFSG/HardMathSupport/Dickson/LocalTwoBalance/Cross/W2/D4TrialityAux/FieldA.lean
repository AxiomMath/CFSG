module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Classes
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthMain
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthD4
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical.SteinbergBY CFSG.RankThree.PartOne
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section FieldA


theorem isSimpleGroup_adjointGroup_D4 (k : Type) [Field k] [Finite k] :
    IsSimpleGroup ↥(adjointGroup Tag.D4 k) := by
  obtain ⟨e⟩ := nonempty_matrixProjective_equiv_adjointGroup k
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 k (by norm_num)
  have : IsSimpleGroup (matrixProjectiveDerived (coordinateQuadPlus 4 k)) :=
    CFSG.SignalizerFunctorTheorem.NonLocal.Orth.matrixProjectiveDerived_simple (by norm_num) hnd hT
  exact e.symm.isSimpleGroup

theorem three_dvd_card_adjointGroup_D4 (k : Type) [Field k] [Finite k] (hk3 : ¬ 3 ∣ Nat.card k) :
    3 ∣ Nat.card ↥(adjointGroup Tag.D4 k) := by
  have hle : graphFixedRootGroup TwistTag.D4 k (RingHom.id k) ≤ adjointGroup TwistTag.D4.tag k :=
    fun g hg =>
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 k (RingHom.id k)).1
        (graphFixedRootGroup_le TwistTag.D4 k (RingHom.id k) hg)).1
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [CFSG.HardMathSupport.Lang.Triality.card_graphFixedRootGroup_D4_id] at hdvd
  have hq : Nat.card k % 3 = 1 ∨ Nat.card k % 3 = 2 := by omega
  have hq2 : (Nat.card k ^ 2) % 3 = 1 := by
    rcases hq with h | h <;> simp [Nat.pow_mod, h]
  have hq2' : 1 ≤ Nat.card k ^ 2 := Nat.one_le_pow _ _ Finite.card_pos
  exact dvd_trans (Dvd.dvd.mul_left (by omega) _) hdvd

theorem mem_fixSub_entrywise_iff {K : Type} [Field K] (T : K ≃+* K)
    (x : adjointGroup Tag.D4 K) :
    x ∈ fixSub (entrywiseAdjointAut Tag.D4 T) ↔
      (x : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 T := by
  rw [mem_fixSub]
  constructor
  · intro h
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    have h1 := congrArg Subtype.val h
    rw [coe_entrywiseAdjointAut] at h1
    exact h1
  · intro h
    exact Subtype.ext (by rw [coe_entrywiseAdjointAut]; exact (Subgroup.mem_inf.1 h).2)

theorem noNormalCop_fixSub_entrywise_aux {ℓ e : ℕ} [Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3) (he : 1 ≤ e)
    {K : Type} [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) :
    NoNormalCop (K := ↥(adjointGroup Tag.D4 K)) 3 (fixSub (entrywiseAdjointAut Tag.D4 T)) := by
  classical
  have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, ← pow_mul]
  have hk : Nat.card (fixSubfield T) = ℓ ^ e :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube (Fact.out) he hK' T hT
  have hk3 : ¬ 3 ∣ Nat.card (fixSubfield T) := by
    rw [hk]
    exact fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  intro N hNF hNn hcop
  set F := fixSub (entrywiseAdjointAut Tag.D4 T) with hF
  set J : Subgroup (adjointGroup Tag.D4 K) :=
    (fixedFieldImage Tag.D4 T).subgroupOf (adjointGroup Tag.D4 K) with hJ
  have hJmem : ∀ x : adjointGroup Tag.D4 K, x ∈ J ↔
      (x : ModGL Tag.D4 K) ∈ fixedFieldImage Tag.D4 T := fun x => Iff.rfl
  have hJF : J ≤ F := fun x hx => (mem_fixSub_entrywise_iff T x).2 (fixedFieldImage_le hx)
  have hJnorm : ∀ f ∈ F, ∀ j ∈ J, f * j * f⁻¹ ∈ J := by
    intro f hf j hj
    have hfΓ : (f : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 T :=
      (mem_fixSub_entrywise_iff T f).1 hf
    have hjΓ : (j : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 T :=
      fixedFieldImage_le ((hJmem j).1 hj)
    have hn := (fixedFieldImage_normal (τ := Tag.D4) (σ := T)).conj_mem ⟨j, hjΓ⟩
      (Subgroup.mem_subgroupOf.2 ((hJmem j).1 hj)) ⟨f, hfΓ⟩
    exact Subgroup.mem_subgroupOf.1 hn
  let eJ : ↥J ≃* ↥(adjointGroup Tag.D4 (fixSubfield T)) :=
    (Subgroup.subgroupOfEquivOfLe (fun x hx => (fixedFieldImage_le hx).1)).trans
      (fixedFieldImageEquiv (τ := Tag.D4) (σ := T)).symm
  haveI : IsSimpleGroup ↥(adjointGroup Tag.D4 (fixSubfield T)) :=
    isSimpleGroup_adjointGroup_D4 _
  haveI : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hJ3 : 3 ∣ Nat.card J := by
    rw [Nat.card_congr eJ.toEquiv]
    exact three_dvd_card_adjointGroup_D4 _ hk3
  have hNJ : ∀ n ∈ N, n ∈ J → n = 1 := by
    intro n hn hnJ
    let N₁ : Subgroup ↥J := N.subgroupOf J
    have hN₁mem : ∀ m : ↥J, m ∈ N₁ ↔ (m : adjointGroup Tag.D4 K) ∈ N := fun m => Iff.rfl
    haveI : N₁.Normal := ⟨fun m hm g => by
      rw [hN₁mem] at hm ⊢
      simpa using hNn g.1 (hJF g.2) m.1 hm⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₁ with h | h
    · have hmem : (⟨n, hnJ⟩ : ↥J) ∈ N₁ := hn
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      have hJN : J ≤ N := fun j hj => by
        have : (⟨j, hj⟩ : ↥J) ∈ N₁ := by rw [h]; exact Subgroup.mem_top _
        exact this
      exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) dvd_rfl
        (dvd_trans hJ3 (Subgroup.card_dvd_of_le hJN))) hcop
  have hcomm : ∀ n ∈ N, ∀ j ∈ J, n * j = j * n := by
    intro n hn j hj
    have h1 : n * j * n⁻¹ ∈ J := hJnorm n (hNF hn) j hj
    have h2 : j * n⁻¹ * j⁻¹ ∈ N := hNn j (hJF hj) n⁻¹ (inv_mem hn)
    have h3 : n * j * n⁻¹ * j⁻¹ ∈ J := mul_mem h1 (inv_mem hj)
    have h4 : n * j * n⁻¹ * j⁻¹ ∈ N := by
      have := mul_mem hn h2
      simpa [mul_assoc] using this
    have h5 := hNJ _ h4 h3
    calc n * j = (n * j * n⁻¹ * j⁻¹) * (j * n) := by group
      _ = j * n := by rw [h5, one_mul]
  refine eq_bot_iff.2 fun n hn => Subgroup.mem_bot.2 ?_
  by_cases h4 : 4 ≤ Nat.card (fixSubfield T)
  ·
    have hfaith := (Chevalley_large_finite_root_centralizer_faithfulness_of_four_le Tag.D4
      (fixSubfield T) h4 K (fixSubfield T).subtype).2.2.1
    have h1 : (n : ModGL Tag.D4 K) = 1 := by
      refine hfaith n n.2 fun h hh => ?_
      have hhJ : h ∈ fixedFieldImage Tag.D4 T := hh
      have h2 := hcomm n hn ⟨h, (fixedFieldImage_le hhJ).1⟩ hhJ
      exact congrArg Subtype.val h2
    exact Subtype.ext h1
  ·
    have hk2 : ℓ = 2 := by
      have hk' : Nat.card (fixSubfield T) = 2 := by
        have := Finite.one_lt_card (α := fixSubfield T)
        have h3 : Nat.card (fixSubfield T) ≠ 3 := fun h => hk3 (h ▸ dvd_rfl)
        omega
      have hdvd : ℓ ∣ 2 := by
        rw [← hk', hk]
        exact dvd_pow_self ℓ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd
    have hchar : ringChar K = 2 := by rw [ringChar.eq K ℓ, hk2]
    have hFJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
      (τ := Tag.D4) (Or.inr (Or.inr (Or.inl rfl))) hchar T
    have hnJ : n ∈ J := by
      have := (mem_fixSub_entrywise_iff T n).1 (hNF hn)
      rw [hFJ] at this
      exact this
    exact hNJ n hn hnJ


theorem noNormalCop_fixSub_entrywise {ℓ e : ℕ} [Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3) (he : 1 ≤ e)
    {K : Type} [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) :
    NoNormalCop 3 (fixSub (twistedEntrywiseAut TwistTag.D4 0 T)) := by
  have e0 : twistedEntrywiseAut TwistTag.D4 0 T = entrywiseAdjointAut Tag.D4 T := by
    unfold twistedEntrywiseAut
    rw [zpow_zero, one_mul]
    rfl
  rw [e0]
  exact noNormalCop_fixSub_entrywise_aux hℓ3 he hK T hT

end FieldA

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
