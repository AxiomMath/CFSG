module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelCover
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LieType.HighestRoot.GenBasic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelCommuting
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate119
public import Certificates.Certificate12
public import Certificates.Certificate122
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ClassicalInvolution CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.LieType.HighestRoot CFSG.LieType.Universal
open CFSG.LieType.RootSystem (form_pos toRat toRat_injective ne_zero_of_mem_roots)
open CFSG.ClassicalInvolution.Generic (IsLongestRoot)
open scoped MatrixGroups

section Gen

variable {K G : Type*} [Group K] [Group G]

theorem eq_one_of_pow_prime_pow {p : ℕ} {N : Subgroup K} (hN : ∀ z ∈ N, z ^ p = 1 → z = 1)
    {z : K} (hz : z ∈ N) : ∀ k : ℕ, z ^ (p ^ k) = 1 → z = 1
  | 0, h => by simpa using h
  | k + 1, h => eq_one_of_pow_prime_pow hN hz k
      (hN _ (pow_mem hz _) (by rw [← pow_mul, ← pow_succ]; exact h))

theorem normalizer_map_le {p : ℕ} (φ : K →* G) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ center K) (hkp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1) {V : Subgroup K}
    (hV : IsPGroup p V) :
    normalizer ((V.map φ : Subgroup G) : Set G) ≤ (normalizer (V : Set K)).map φ := by
  have key : ∀ k : K, φ k ∈ normalizer ((V.map φ : Subgroup G) : Set G) →
      ∀ v ∈ V, k * v * k⁻¹ ∈ V := by
    intro k hk v hv
    obtain ⟨v', hv', hv'e⟩ : φ (k * v * k⁻¹) ∈ V.map φ := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hk _).mp (mem_map_of_mem φ hv)
    set c := v'⁻¹ * (k * v * k⁻¹)
    have hc : c ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hv'e, inv_mul_cancel]
    have hw : k * v * k⁻¹ = v' * c := by simp [c]
    obtain ⟨a, ha⟩ := hV ⟨v, hv⟩
    obtain ⟨b, hb⟩ := hV ⟨v', hv'⟩
    have ha' : v ^ (p ^ a) = 1 := by simpa using congrArg Subtype.val ha
    have hb' : v' ^ (p ^ b) = 1 := by simpa using congrArg Subtype.val hb
    have hcN : c ^ (p ^ (a + b)) = 1 := by
      have h1 : (k * v * k⁻¹) ^ (p ^ (a + b)) = 1 := by
        rw [conj_pow, pow_add, pow_mul, ha', one_pow, mul_one, mul_inv_cancel]
      rw [hw, (show Commute v' c from Subgroup.mem_center_iff.mp (hker hc) v').mul_pow, add_comm,
        pow_add, pow_mul, hb', one_pow, one_mul] at h1
      rw [add_comm, pow_add]
      exact h1
    rw [hw, eq_one_of_pow_prime_pow hkp hc _ hcN, mul_one]
    exact hv'
  intro g hg
  obtain ⟨k, rfl⟩ := hφ g
  refine ⟨k, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_normalizer_iff]
  intro v
  refine ⟨key k hg v, fun hv => ?_⟩
  have hk' : φ k⁻¹ ∈ normalizer ((V.map φ : Subgroup G) : Set G) := by
    rw [map_inv]
    exact inv_mem hg
  have := key k⁻¹ hk' _ hv
  simpa [mul_assoc] using this

theorem gen_map {p : ℕ} (φ : K →* G) (hφ : Function.Surjective φ) (hker : φ.ker ≤ center K)
    (hkp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1) {V J Q : Subgroup K} (hV : IsPGroup p V)
    (hQ : IsPGroup p Q) (hQV : Q ≤ normalizer (V : Set K))
    (hNQ : normalizer (V : Set K) ≤ normalizer (Q : Set K)) (hgen : Q ⊔ J = ⊤) :
    pCoreOf p (normalizer ((V.map φ : Subgroup G) : Set G)) ⊔ J.map φ = ⊤ := by
  have hN := normalizer_map_le φ hφ hker hkp hV
  have hQN : Q.map φ ≤ pCoreOf p (normalizer ((V.map φ : Subgroup G) : Set G)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p ?_ ?_ (hQ.map φ)
    · exact (map_mono hQV).trans (le_normalizer_map φ)
    · exact hN.trans ((map_mono hNQ).trans (le_normalizer_map φ))
  rw [eq_top_iff, ← map_top_of_surjective φ hφ, ← hgen, Subgroup.map_sup]
  exact sup_le_sup_right hQN _

end Gen

section Commuting

variable {K : Type} [Group K]

theorem oddCenter_le_ker {G : Type*} [Group G] (hZ : IsPGroup 2 (center G)) (φ : K →* G)
    (hφ : Function.Surjective φ) : oddCenter (⊤ : Subgroup K) ≤ φ.ker := by
  intro z hz
  have hzc := oddCenter_top_le_center hz
  have hφz : φ z ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := hφ g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc k]
  obtain ⟨a, ha⟩ := hZ ⟨φ z, hφz⟩
  have ha' : (φ z) ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have hodd : Odd (orderOf (φ z)) :=
    (mem_oddCenter_top.mp hz).2.of_dvd_nat (orderOf_map_dvd φ z)
  have hcop : Nat.Coprime (orderOf (φ z)) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hodd)
  rw [MonoidHom.mem_ker]
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one ha'))

theorem isPGroup_center_quot [Finite K] [Group.IsPerfect K] :
    IsPGroup 2 (center (K ⧸ oddCenter (⊤ : Subgroup K))) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (oddCenter (⊤ : Subgroup K)) x
  have hk : k ∈ center K := by
    have h1 : QuotientGroup.mk' (center K) k ∈ center (K ⧸ center K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center K) y
      have hc := Subgroup.mem_center_iff.mp hx (QuotientGroup.mk' _ y)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hc ⊢
      exact oddCenter_top_le_center hc
    rwa [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  have hmem : k ^ (2 ^ a) ∈ oddCenter (⊤ : Subgroup K) := by
    rw [mem_oddCenter_top]
    refine ⟨Subgroup.pow_mem _ hk _, hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)⟩
    rw [← pow_mul, ← hord, pow_orderOf_eq_one]
  refine ⟨a, Subtype.ext ?_⟩
  show (QuotientGroup.mk' _ k) ^ (2 ^ a) = 1
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hmem

theorem commuting_of_univ (h3 : SL2OuterComm) [Finite K] [Group.IsPerfect K] {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hFp : Nat.card F = p ^ e)
    (hO : ∀ z ∈ center K, z ^ p = 1 → z = 1)
    (hAut : ∀ (X G : Type) [Group X] [Group G] [Finite X] [Finite G] (ψ₀ : K →* X)
      (ψ : X →* G), Function.Surjective ψ₀ → ψ₀.ker ≤ center K → Odd (Nat.card ψ₀.ker) →
      IsPGroup 2 (center X) → Function.Surjective ψ → ψ.ker ≤ center X →
      ∀ τ : MulAut G, ∃ τ' : MulAut X, ∀ x, ψ (τ' x) = τ (ψ x))
    {G : Type} [Group G] [Finite G] (hZ : IsPGroup 2 (center G)) (φ : K →* G)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center K) {J B : Subgroup K}
    (eJ : J ≃* SL(2, F)) (hCZ : centralizer ({centralInv eJ} : Set K) ≤ normalizer (J : Set K))
    (hU : ∀ L : Subgroup K, L ≤ centralizer ({centralInv eJ} : Set K) →
      centralizer ({centralInv eJ} : Set K) ≤ normalizer (L : Set K) →
      Nonempty (L ≃* SL(2, F)) → centralInv eJ ∈ L → L = J ∨ L = B)
    (hB : B = J ∨ ((∀ a ∈ J, ∀ b ∈ B, a * b = b * a) ∧
      ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y))
    (𝒯 : Subgroup (MulAut G)) (h𝒯 : IsPGroup 2 𝒯) :
    ∃ g : G, ∀ τ ∈ 𝒯, (conjSubgroup g (J.map φ)).map τ.toMonoidHom = conjSubgroup g (J.map φ) ∨
      ∀ a ∈ conjSubgroup g (J.map φ), ∀ b ∈ (conjSubgroup g (J.map φ)).map τ.toMonoidHom,
        a * b = b * a := by
  set O := oddCenter (⊤ : Subgroup K)
  set π := QuotientGroup.mk' O
  have hF : Odd (Nat.card F) := by
    rw [hFp]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hOφ : O ≤ φ.ker := oddCenter_le_ker hZ φ hφ
  set ψ : K ⧸ O →* G := QuotientGroup.lift O φ hOφ
  have hψπ : ψ.comp π = φ := MonoidHom.ext fun _ => rfl
  have hψ : Function.Surjective ψ := fun g => by
    obtain ⟨k, rfl⟩ := hφ g
    exact ⟨π k, rfl⟩
  have hψker : ψ.ker ≤ center (K ⧸ O) := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O x
    have hk : k ∈ center K := hker hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk y]
  have : Finite (K ⧸ O) := Finite.of_surjective _ (QuotientGroup.mk'_surjective O)
  have hlift := hAut (K ⧸ O) G π ψ (QuotientGroup.mk'_surjective O)
    (by rw [QuotientGroup.ker_mk']; exact oddCenter_top_le_center)
    (by rw [QuotientGroup.ker_mk']; exact odd_card_oddCenter _) isPGroup_center_quot hψ hψker
  have hO' : ∀ z ∈ O, z ^ p = 1 → z = 1 := fun z hz => hO z (oddCenter_top_le_center hz)
  have hCZ' := centralizer_le_normalizer_quot eJ hF hCZ
  have hU' := eq_or_eq_quot eJ hp2 hFp hO' hU hF
  have hmap : (J.map π).map ψ = J.map φ := by rw [Subgroup.map_map, hψπ]
  rw [← hmap]
  rcases hB with rfl | ⟨hJB, hconj⟩
  · refine commuting_of_cover h3 ψ hψker hF (mapOddCenterEquiv eJ hF) hCZ'
      (fun L h1 h2 h3' h4 => ?_) hlift 𝒯 h𝒯
    exact (hU' L h1 h2 h3' h4).elim id id
  · refine commuting_of_cover_pair ψ hψker hF (mapOddCenterEquiv eJ hF) (isConj_quot hconj) hCZ'
      ?_ hU' hlift 𝒯 h𝒯
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hJB a ha b hb]

theorem commuting_conjSubgroup {G : Type} [Group G] {J : Subgroup G} (c : G)
    (h : ∀ 𝒯 : Subgroup (MulAut G), IsPGroup 2 𝒯 → ∃ g : G, ∀ τ ∈ 𝒯,
      (conjSubgroup g J).map τ.toMonoidHom = conjSubgroup g J ∨
        ∀ a ∈ conjSubgroup g J, ∀ b ∈ (conjSubgroup g J).map τ.toMonoidHom, a * b = b * a) :
    ∀ 𝒯 : Subgroup (MulAut G), IsPGroup 2 𝒯 → ∃ g : G, ∀ τ ∈ 𝒯,
      (conjSubgroup g (conjSubgroup c J)).map τ.toMonoidHom = conjSubgroup g (conjSubgroup c J) ∨
        ∀ a ∈ conjSubgroup g (conjSubgroup c J),
          ∀ b ∈ (conjSubgroup g (conjSubgroup c J)).map τ.toMonoidHom, a * b = b * a := by
  intro 𝒯 h𝒯
  obtain ⟨g, hg⟩ := h 𝒯 h𝒯
  refine ⟨g * c⁻¹, ?_⟩
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
  exact hg

end Commuting

theorem nonempty_map_equiv {K G : Type*} [Group K] [Group G] {F : Type*} [Field F]
    (φ : K →* G) {J : Subgroup K} (h : ∀ x ∈ J, φ x = 1 → x = 1) (eJ : J ≃* SL(2, F)) :
    Nonempty (J.map φ ≃* SL(2, F)) := by
  have hinj : Function.Injective (φ.comp J.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr (Subtype.ext (h x x.2 hx))
  exact ⟨((MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])).trans
    (MonoidHom.ofInjective hinj).symm).trans eJ⟩

@[expose] def SL2CentralizerData {K : Type*} [Group K] (F : Type*) [Field F] (R : Subgroup K) :
    Prop :=
  ∀ z ∈ R, orderOf z = 2 → centralizer ({z} : Set K) ≤ normalizer (R : Set K) ∧
    ∃ B : Subgroup K, (∀ L : Subgroup K, L ≤ centralizer ({z} : Set K) →
      centralizer ({z} : Set K) ≤ normalizer (L : Set K) → Nonempty (L ≃* SL(2, F)) → z ∈ L →
        L = R ∨ L = B) ∧
      (B = R ∨ ((∀ a ∈ R, ∀ b ∈ B, a * b = b * a) ∧
        ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y))

theorem highestRootData_of_datum (h3 : SL2OuterComm) {K : Type} [Group K] [Finite K]
    [Group.IsPerfect K] {D : UniversalRootDatum K} {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : e ≠ 0) (hO : ∀ z ∈ center K, z ^ p = 1 → z = 1)
    (hAut : ∀ (X G : Type) [Group X] [Group G] [Finite X] [Finite G] (ψ₀ : K →* X)
      (ψ : X →* G), Function.Surjective ψ₀ → ψ₀.ker ≤ center K → Odd (Nat.card ψ₀.ker) →
      IsPGroup 2 (center X) → Function.Surjective ψ → ψ.ker ≤ center X →
      ∀ τ : MulAut G, ∃ τ' : MulAut X, ∀ x, ψ (τ' x) = τ (ψ x))
    (hgen : HighestRootGen D p)
    (hconj : ∀ γ γ', IsLongestRoot D γ → IsLongestRoot D γ' →
      ∃ c : K, (rankOneGroup D γ).map (MulAut.conj c).toMonoidHom = rankOneGroup D γ')
    (hSL2 : ∀ γ, IsLongestRoot D γ → Nonempty (rankOneGroup D γ ≃* SL(2, GaloisField p e)))
    (hZ0 : ∀ γ, IsLongestRoot D γ → ∀ x ∈ rankOneGroup D γ, x ∈ center K → x = 1)
    (hCZ : ∃ γ, IsLongestRoot D γ ∧ SL2CentralizerData (GaloisField p e) (rankOneGroup D γ))
    {G : Type} [Group G] [Finite G] (hZ : IsPGroup 2 (center G)) (φ : K →* G)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center K) : Nonempty (HighestRootData G) := by
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hF : Odd (Nat.card (GaloisField p e)) := by
    rw [hcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hkp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1 := fun z hz => hO z (hker hz)
  obtain ⟨r, hr, hXr, hQp, hQN, hNQ, hQJ⟩ := hgen
  have hrL : IsLongestRoot D r := ⟨hr.mem_roots, hr.longest⟩
  have hinj : ∀ x ∈ rankOneGroup D r, φ x = 1 → x = 1 := fun x hx h1 =>
    hZ0 r hrL x hx (hker h1)
  obtain ⟨eJ⟩ := hSL2 r hrL
  have hrpos : 0 < rootForm D r r := by
    refine form_pos D.isFiniteType fun h => ne_zero_of_mem_roots _ _ hr.mem_roots ?_
    exact toRat_injective (h.trans (map_zero toRat).symm)
  have hVp : IsPGroup p (D.rootGroup r) :=
    hQp.to_le (rootGroup_le_highestRootRadical hr.mem_roots hrpos)
  obtain ⟨γ, hγ, hCZγ⟩ := hCZ
  obtain ⟨eγ⟩ := hSL2 γ hγ
  obtain ⟨hCZ', B, hU, hB⟩ :=
    hCZγ (centralInv eγ) (centralInv_mem eγ) (orderOf_centralInv eγ hF)
  have hcomm := fun 𝒯 h𝒯 =>
    commuting_of_univ h3 hp2 hcard hO hAut hZ φ hφ hker eγ hCZ' hU hB 𝒯 h𝒯
  obtain ⟨c, hc⟩ := hconj γ r hγ hrL
  have hJr : (rankOneGroup D r).map φ = conjSubgroup (φ c) ((rankOneGroup D γ).map φ) := by
    rw [← hc]
    simp only [conjSubgroup, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    simp [map_mul, map_inv]
  have hVne : (D.rootGroup r).map φ ≠ ⊥ := by
    intro hV
    apply hXr
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    refine hinj x (mem_sup_left hx) ?_
    have : φ x ∈ (D.rootGroup r).map φ := mem_map_of_mem φ hx
    rwa [hV, mem_bot] at this
  exact ⟨{
    p := p
    e := e
    odd := hp2
    J := (rankOneGroup D r).map φ
    equivJ := nonempty_map_equiv φ hinj eJ
    V := (D.rootGroup r).map φ
    V_le := map_mono le_sup_left
    V_ne := hVne
    V_pGroup := hVp.map φ
    gen := gen_map φ hφ hker hkp hVp hQp hQN hNQ hQJ
    commuting := hJr ▸ commuting_conjSubgroup (φ c) hcomm }⟩

end CFSG.ComponentClassification.RankTwoOddLie
