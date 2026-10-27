module

public import CFSG.LocalAnalysis.ABGTheoremB.IV9Constrained
import CFSG.GroupTheory.ABGDGroups.LinearQuotient
import CFSG.GroupTheory.ABGDGroups.LinearASeven
import CFSG.GroupTheory.QuasiDihedralFusion.Structure
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
public import Certificates.Certificate7
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7SylowCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.GroupTheory.QuasiDihedralFusion.Basic
import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeNormalExtension
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion
open CFSG.GorensteinWalter (PGammaL2 PSL2 pGammaL2PSLRange)
open CFSG.ABGDGroups (IsLinearDecomposition linearCore)
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G]

private theorem ii34_le_oddCoreIn_of_subgroupOf {H Y : Subgroup G} (hYH : Y ≤ H)
    (h : Y.subgroupOf H ≤ CFSG.oddCore H) : Y ≤ oddCoreIn H :=
  fun y hy => ⟨⟨y, hYH hy⟩, h hy, rfl⟩

private theorem ii34_subgroupOf_le_normalizer {H A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf H ≤ Subgroup.normalizer ((B.subgroupOf H : Subgroup H) : Set H) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (h ha) b

private theorem ii34_odd_card_subgroupOf {H Y : Subgroup G} (hYH : Y ≤ H)
    (hY : Odd (Nat.card Y)) : Odd (Nat.card (Y.subgroupOf H)) := by
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]

private theorem ii34_isKleinFour_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsKleinFour A) : IsKleinFour B :=
  ⟨by rw [← Nat.card_congr e.toEquiv]; exact hA.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact hA.exponent_two⟩

private noncomputable def ii34_mulEquivMap {A B : Type*} [Group A] [Group B] (f : A →* B)
    (P : Subgroup A) (hP : P ⊓ f.ker = ⊥) : P ≃* P.map f :=
  MulEquiv.ofBijective (f.subgroupMap P) ⟨fun x y hxy => by
    have h1 : f x = f y := congrArg Subtype.val hxy
    have h2 : ((x⁻¹ * y : P) : A) ∈ P ⊓ f.ker :=
      Subgroup.mem_inf.mpr ⟨(x⁻¹ * y).2, MonoidHom.mem_ker.mpr (by simp [h1])⟩
    rw [hP, Subgroup.mem_bot] at h2
    have h3 : x⁻¹ * y = 1 := Subtype.ext h2
    rw [inv_mul_eq_one] at h3
    exact h3, f.subgroupMap_surjective P⟩

private theorem ii34_inf_eq_bot_of_two_of_odd [Finite G] {P Q : Subgroup G} (hP : IsPGroup 2 P)
    (hQ : Odd (Nat.card Q)) : P ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
  rw [hk]
  exact (Nat.coprime_two_left.mpr hQ).pow_left k

private theorem ii34_mem_of_mul_self_mem {K : Subgroup G} {y : G} (hy : Odd (orderOf y))
    (h : y * y ∈ K) : y ∈ K := by
  obtain ⟨m, hm⟩ := hy
  have : y = (y * y) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [this]
  exact K.pow_mem h _

private theorem ii34_hasWreathedSylow_of_le [Finite G] {n : ℕ} (hW : HasWreathedSylow G n)
    (S : Sylow 2 G) {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H) : HasWreathedSylow H n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hW.1, fun P => ?_⟩
  obtain ⟨e⟩ := hW.2 S
  exact ⟨((P.equiv (S.subtype hSH)).trans ((MulEquiv.subgroupCongr (Sylow.coe_subtype S hSH)).trans
    (Subgroup.subgroupOfEquivOfLe hSH))).trans e⟩

end Elementary

section Automizer

variable {K : Type*} [Group K] [Finite K]

private theorem ii34_exists_of_three_dvd_automizerIndex {T : Subgroup K}
    (h : 3 ∣ automizerIndex T) :
    ∃ g ∈ Subgroup.normalizer (T : Set K), g ^ 3 ∈ Subgroup.centralizer (T : Set K) ∧
      g ∉ Subgroup.centralizer (T : Set K) := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer T)
  have h3 : 3 ∣ Nat.card (Nt ⧸ Ct.subgroupOf Nt) := by
    rw [← Subgroup.index_eq_card]
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, g.2, ?_, ?_⟩
  · have : ((g ^ 3 : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hg
    have : ((g : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)

private theorem ii34_le_commutator {T : Subgroup K} (hT : IsKleinFour T)
    (h : 3 ∣ automizerIndex T) : T ≤ commutator K := by
  obtain ⟨g, hgN, hg3, hg1⟩ := ii34_exists_of_three_dvd_automizerIndex h
  have hconj : ∀ u ∈ T, g * u * g⁻¹ ∈ T := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hgN u).mp hu
  have hfix : ∀ a ∈ T, g * a * g⁻¹ = a → a = 1 := by
    intro a ha hga
    by_contra ha1
    obtain ⟨b, hb, hgb⟩ : ∃ b ∈ T, g * b * g⁻¹ ≠ b := by
      by_contra hcon
      push Not at hcon
      apply hg1
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have e := hcon t ht
      calc t * g = g * t * g⁻¹ * g := by rw [e]
        _ = g * t := by group
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hgb (by group)
    have hab : a ≠ b := by
      rintro rfl
      exact hgb hga
    set c := g * b * g⁻¹ with hc
    have hcT : c ∈ T := hconj b hb
    have hc1 : c ≠ 1 := by
      intro h1
      apply hb1
      calc b = g⁻¹ * c * g := by rw [hc]; group
        _ = 1 := by rw [h1]; group
    have hca : c ≠ a := by
      intro h1
      apply hab
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = g⁻¹ * c * g := by rw [hga, h1]
        _ = b := by rw [hc]; group
    have := hT
    have hcab : (⟨c, hcT⟩ : T) = ⟨a, ha⟩ * ⟨b, hb⟩ :=
      IsKleinFour.eq_mul_of_ne_all (fun h1 => ha1 (congrArg Subtype.val h1))
        (fun h1 => hb1 (congrArg Subtype.val h1))
        (fun h1 => hab (congrArg Subtype.val h1)) (fun h1 => hc1 (congrArg Subtype.val h1))
        (fun h1 => hca (congrArg Subtype.val h1)) (fun h1 => hgb (congrArg Subtype.val h1))
    have hcab' : c = a * b := congrArg Subtype.val hcab
    have haa : a * a = 1 := congrArg Subtype.val (IsKleinFour.mul_self (⟨a, ha⟩ : T))
    have hgc : g * c * g⁻¹ = b := by
      calc g * c * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by rw [hcab']; group
        _ = a * (a * b) := by rw [hga, ← hc, hcab']
        _ = (a * a) * b := by group
        _ = b := by rw [haa, one_mul]
    have h3b : g * (g * g) * b * (g * (g * g))⁻¹ = c := by
      calc g * (g * g) * b * (g * (g * g))⁻¹ = g * (g * (g * b * g⁻¹) * g⁻¹) * g⁻¹ := by
            group
        _ = c := by rw [← hc, hgc]
    rw [pow_three] at hg3
    have hcomm := (Subgroup.mem_centralizer_iff.mp hg3) b hb
    apply hgb
    rw [← h3b, ← hcomm]
    group
  let φ : T → T := fun s => ⟨g * s * g⁻¹ * s⁻¹, T.mul_mem (hconj s s.2) (T.inv_mem s.2)⟩
  have hinj : Function.Injective φ := by
    intro s₁ s₂ h12
    have h' : g * (s₁ : K) * g⁻¹ * (s₁ : K)⁻¹ = g * (s₂ : K) * g⁻¹ * (s₂ : K)⁻¹ :=
      congrArg Subtype.val h12
    have e1 : g * (s₁ : K) * g⁻¹ = g * (s₂ : K) * g⁻¹ * (s₂ : K)⁻¹ * s₁ := by
      calc g * (s₁ : K) * g⁻¹ = (g * (s₁ : K) * g⁻¹ * (s₁ : K)⁻¹) * s₁ := by group
        _ = _ := by rw [h']
    have hu : g * ((s₂ : K)⁻¹ * s₁) * g⁻¹ = (s₂ : K)⁻¹ * s₁ := by
      calc g * ((s₂ : K)⁻¹ * s₁) * g⁻¹ = (g * (s₂ : K) * g⁻¹)⁻¹ * (g * (s₁ : K) * g⁻¹) := by
            group
        _ = (g * (s₂ : K) * g⁻¹)⁻¹ * (g * (s₂ : K) * g⁻¹ * (s₂ : K)⁻¹ * s₁) := by rw [e1]
        _ = (s₂ : K)⁻¹ * s₁ := by group
    have h1 := hfix _ (T.mul_mem (T.inv_mem s₂.2) s₁.2) hu
    rw [inv_mul_eq_one] at h1
    exact Subtype.ext h1.symm
  have : Finite T := inferInstance
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro t ht
  obtain ⟨s, hs⟩ := hsurj ⟨t, ht⟩
  have ht' : t = g * s * g⁻¹ * (s : K)⁻¹ := (congrArg Subtype.val hs).symm
  rw [ht', commutator_def, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top _)

end Automizer

section Quotient

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
private theorem ii34_linearCore_le_of_normal {F : Type} [Field F] [Finite F]
    {ι : K →* PGammaL2 F} {L E : Subgroup K} {S : Sylow 2 K} (hd : IsLinearDecomposition ι L E S)
    (h3 : 3 < Nat.card F) (N : Subgroup K) [hN : N.Normal] (hN1 : N ≠ ⊥) : linearCore ι ≤ N := by
  set L₀ := linearCore ι with hL₀
  have hL₀n : L₀.Normal := hd.linearCore_normal
  obtain ⟨e⟩ := hd.nonempty_linearCore_mulEquiv
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hsimple : IsSimpleGroup L₀ := e.isSimpleGroup
  have hNL : (N.subgroupOf L₀).Normal := hN.subgroupOf L₀
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf L₀) with hbot | htop
  · exfalso
    apply hN1
    have hinf : N ⊓ L₀ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hy' : (⟨y, hy.2⟩ : L₀) ∈ N.subgroupOf L₀ := hy.1
      rw [hbot, Subgroup.mem_bot] at hy'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hy')
    have hcomm : ⁅N, L₀⁆ = ⊥ := le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf N L₀)
    have hcent : N ≤ Subgroup.centralizer (L₀ : Set K) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
    rw [eq_bot_iff]
    intro c hc
    have hιc : ι c ∈ Subgroup.centralizer (pGammaL2PSLRange F : Set (PGammaL2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hd.map_linearCore] at hy
      obtain ⟨l, hl, rfl⟩ := hy
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hcent hc)) l hl]
    rw [CFSG.GorensteinWalter.pGammaL2_pslRange_centralizer_eq_bot F hd.isOddPrimePower_card h3,
      Subgroup.mem_bot] at hιc
    exact (Subgroup.mem_bot).mpr (hd.injective (hιc.trans (map_one ι).symm))
  · intro y hy
    have hy' : (⟨y, hy⟩ : L₀) ∈ N.subgroupOf L₀ := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hy'

private theorem ii34_eq_bot_of_card_eq_three {F : Type} [Field F] [Finite F]
    {ι : K →* PGammaL2 F} {L E : Subgroup K} {S : Sylow 2 K} (hd : IsLinearDecomposition ι L E S)
    (h3 : Nat.card F = 3) {T X : Subgroup K} (hT : IsKleinFour T) (hTL : T ≤ linearCore ι)
    (hX : Odd (Nat.card X)) (hTX : T ≤ Subgroup.normalizer (X : Set K)) : X = ⊥ := by
  set L₀ := linearCore ι with hL₀
  have hL₀n : L₀.Normal := hd.linearCore_normal
  obtain ⟨eL₀⟩ := hd.nonempty_linearCore_mulEquiv
  have hF := hd.isOddPrimePower_card
  have hAut : Nat.card (F ≃+* F) = 1 :=
    CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card F (p := 3) Nat.prime_three
      (by rw [h3, pow_one])
  have hΓ : Nat.card (PGammaL2 F) = 24 := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
      CFSG.GorensteinWalter.pgl2_card_formula, hAut, h3]
    norm_num
  have hKle : Nat.card K ≤ 24 := hΓ ▸ Nat.card_le_card_of_injective ι hd.injective
  have hL₀card : Nat.card L₀ = 12 := by
    rw [Nat.card_congr eL₀.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hF, h3]
    norm_num
  have hidx : L₀.index ≤ 2 := by
    have h := L₀.card_mul_index
    rw [hL₀card] at h
    omega
  have hXL : X ≤ L₀ := by
    intro x hx
    have hsq : x * x ∈ L₀ := by
      have hpos : L₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (show L₀.index = 1 ∨ L₀.index = 2 by omega) with h1 | h2
      · rw [Subgroup.index_eq_one.mp h1]
        exact Subgroup.mem_top _
      · have := Subgroup.sq_mem_of_index_two h2 x
        rwa [pow_two] at this
    exact ii34_mem_of_mul_self_mem (hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx)) hsq
  have hX3 : Nat.card X ∣ 3 := by
    have hdvd : Nat.card X ∣ 3 * 4 := by
      rw [show 3 * 4 = 12 by norm_num, ← hL₀card]
      exact Subgroup.card_dvd_of_le hXL
    have hcop : Nat.Coprime (Nat.card X) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_right.mpr hX).pow_right 2
    exact hcop.dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hX3 with h1 | h3X
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    set N := L₀ ⊓ Subgroup.normalizer (X : Set K) with hN
    have h4 : 4 ∣ Nat.card N := hT.card_four ▸ Subgroup.card_dvd_of_le (le_inf hTL hTX)
    have h3' : 3 ∣ Nat.card N := h3X ▸ Subgroup.card_dvd_of_le (le_inf hXL Subgroup.le_normalizer)
    have h12 : 3 * 4 ∣ Nat.card N := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3' h4
    have hNL : N = L₀ := Subgroup.eq_of_le_of_card_ge inf_le_left
      (by rw [hL₀card]; exact Nat.le_of_dvd Nat.card_pos h12)
    have hL₀X : L₀ ≤ Subgroup.normalizer (X : Set K) := hNL ▸ inf_le_right
    have hXn : (X.subgroupOf L₀).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr hL₀X
    have : ((X.subgroupOf L₀).map eL₀.toMonoidHom).Normal := hXn.map _ eL₀.surjective
    have hbot := CFSG.ABGDGroups.eq_bot_of_normal_of_odd_card_psl2 hF
      ((X.subgroupOf L₀).map eL₀.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective eL₀.injective]; exact ii34_odd_card_subgroupOf hXL hX)
    rw [Subgroup.map_eq_bot_iff_of_injective _ eL₀.injective, Subgroup.subgroupOf_eq_bot] at hbot
    have hX0 : X = ⊥ := by
      have h := disjoint_iff.mp hbot
      rwa [inf_eq_left.mpr hXL] at h
    rw [hX0, Subgroup.card_bot] at h3X
    exact absurd h3X (by norm_num)

private theorem ii34_aSeven_exists_kleinFour (e : K ≃* alternatingGroup (Fin 7))
    {D X : Subgroup K} (hD : IsPGroup 2 D) (hD8 : 8 ≤ Nat.card D) (hX : Odd (Nat.card X))
    (hDX : D ≤ Subgroup.normalizer (X : Set K)) :
    ∃ V : Subgroup K, V ≤ D ∧ IsKleinFour V ∧ X ≤ Subgroup.centralizer (V : Set K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hDP⟩ := hD.exists_le_sylow
  have hP8 : Nat.card (P : Subgroup K) = 8 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv,
      CFSG.ABGDGroups.card_alternatingGroup_fin_seven, CFSG.GorensteinWalter.factorization_two_2520]
    norm_num
  have hDP' : D = P := Subgroup.eq_of_le_of_card_ge hDP (by rw [hP8]; exact hD8)
  have hPX : (P : Subgroup K) ≤ Subgroup.normalizer (X : Set K) := hDP' ▸ hDX
  have hXP : X ⊓ P = ⊥ := by
    rw [inf_comm]
    exact ii34_inf_eq_bot_of_two_of_odd P.isPGroup' hX
  obtain ⟨-, V, hVP, hV, hXV⟩ :=
    CFSG.ABGDGroups.exists_kleinFour_centralizing_sylow_signalizer e P hPX hXP
  exact ⟨V, hDP' ▸ hVP, hV, hXV⟩

end Quotient

section Wreath

open CFSG.Open CFSG.Semidihedral
open CFSG.Wreathed (Wreath)

private theorem ii34_wreath_half_involution (k : ℕ) :
    orderOf (Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0) = 2 ∧
      Wreathed.element (2 ^ (k + 1)) 0 0 1 *
          Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 *
          (Wreathed.element (2 ^ (k + 1)) 0 0 1)⁻¹ ≠
        Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 := by
  refine ⟨(Wreathed.element_base_involution_iff k _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
  rw [Wreathed.conjugate_base_by_swap]
  intro h
  rw [Wreathed.element_eq_iff] at h
  exact Wreathed.half_residue_ne_zero k h.1.symm

private theorem ii34_wreath_not_embed {n k : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k)
    (ι : Wreath (2 ^ (k + 1)) →* SemidihedralGroup n) (hι : Function.Injective ι) : False := by
  have := presentation_finite n (by omega)
  obtain ⟨hx2, hxw⟩ := ii34_wreath_half_involution k
  set x := Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 with hx
  set y := Wreathed.element (2 ^ (k + 1)) 1 0 0 with hy
  set w := Wreathed.element (2 ^ (k + 1)) 0 0 1 with hw
  have hxy : x * y = y * x := by
    rw [hx, hy, Wreathed.element_base_mul, Wreathed.element_base_mul, Wreathed.element_eq_iff]
    exact ⟨add_comm _ _, rfl, rfl⟩
  have hy2 : y ^ 2 ≠ 1 := by
    rw [hy, Wreathed.element_base_pow]
    intro h2
    rw [Wreathed.element_base_eq_one_iff] at h2
    have h2' : ((2 : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by simpa [nsmul_eq_mul] using h2.1
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have hle := Nat.le_of_dvd (by norm_num) h2'
    have h4 : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hX2 : orderOf (ι x) = 2 := by rw [orderOf_injective ι hι, hx2]
  have hXz : ι x ∉ Subgroup.zpowers (z n) := by
    intro h
    rcases (KleinFourOddKernel.mem_zpowers_involution _ _ (orderOf_z n (by omega))).mp h with
      h1 | h1
    · rw [h1, orderOf_one] at hX2
      omega
    · apply hxw
      apply hι
      rw [map_mul, map_mul, map_inv, h1,
        Subgroup.mem_center_iff.mp (z_mem_center n hn) (ι w), mul_inv_cancel_right]
  obtain ⟨h1, -, -⟩ := Local.semidihedral_four_subgroup_centralizers n hn
    (MulEquiv.refl (SemidihedralGroup n))
  have hz : (MulEquiv.refl (SemidihedralGroup n)) (r n) ^ (2 ^ (n - 1) / 2) = z n := by
    rw [MulEquiv.refl_apply, two_pow_div_two hn]
    rfl
  rw [hz] at h1
  obtain ⟨hC, hK⟩ := h1 (ι x) hX2 hXz
  have hYC : ι y ∈ Subgroup.centralizer ({ι x} : Set (SemidihedralGroup n)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxy]
  rw [hC] at hYC
  have hYsq := congrArg Subtype.val (IsKleinFour.mul_self (⟨ι y, hYC⟩ :
    Subgroup.closure ({z n, ι x} : Set (SemidihedralGroup n))))
  apply hy2
  apply hι
  rw [map_pow, map_one, pow_two]
  exact hYsq

private theorem ii34_not_hasWreathedSylow {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : HasSemidihedralSylow G n) (K : Subgroup G) (m : ℕ) : ¬ HasWreathedSylow K m := by
  rintro ⟨hm, hW⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨e⟩ := hW P
  have hP' : IsPGroup 2 ((P : Subgroup K).map K.subtype) := P.isPGroup'.map K.subtype
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  obtain ⟨f'⟩ := hG.2 S'
  let ι : Wreath (2 ^ m) →* SemidihedralGroup n :=
    f'.symm.toMonoidHom.comp ((Subgroup.inclusion hS').comp
      (((P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom.comp
        e.symm.toMonoidHom))
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 := congrArg Subtype.val (f'.symm.injective hab)
    apply e.symm.injective
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  exact ii34_wreath_not_embed hG.1 (by omega) ι hι

end Wreath

namespace Setting

variable {G : Type} [Group G] [Finite G] (σ : Setting G)

private theorem ii34_le_oddCoreIn_of_wreathed (hσ : σ.IsValid) (hh : σ.height ≠ 1)
    {H : Subgroup G} (hDH : σ.D ≤ H) (hHD : IsDGroup H) (hT : IsKleinFour (σ.T.subgroupOf H))
    {X : Subgroup G} (hXH : X ≤ H) (hX : Odd (Nat.card X))
    (hTX : σ.T ≤ Subgroup.normalizer (X : Set G)) : X ≤ oddCoreIn H := by
  have hWG : HasWreathedSylow G σ.height := by
    rcases hσ.sylow with ⟨h1, -⟩ | h
    · exact absurd h1 hh
    · exact h
  have hSH : (σ.S : Subgroup G) ≤ H := by
    have hDS : σ.D = σ.S := inf_eq_left.mpr (hσ.T_normal hh)
    rw [← hDS]
    exact hDH
  have hWH := ii34_hasWreathedSylow_of_le hWG σ.S hSH
  rcases hHD with ⟨hdih, -⟩ | ⟨K, hK⟩
  · exact (not_hasWreathedSylow_and_dihedral hWH hdih).elim
  · exact ii34_le_oddCoreIn_of_subgroupOf hXH
      (CFSG.ABGDGroups.wreathed_dGroup_odd_four_invariant_le_oddCore hK hWH hT
        (ii34_odd_card_subgroupOf hXH hX) (ii34_subgroupOf_le_normalizer hTX))

private theorem ii34_eight_le_card_D (hσ : σ.IsValid) {n : ℕ} (hSD : HasSemidihedralSylow G n)
    (hT4 : Nat.card σ.T = 4) : 8 ≤ Nat.card σ.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS : σ.T ≤ (σ.S : Subgroup G) := σ.T_le_S hσ
  obtain ⟨f⟩ := hSD.2 σ.S
  have hS : Nat.card (σ.S : Subgroup G) = 2 ^ n := by
    rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n (by have := hSD.1; omega)]
  have h16 : 2 ^ 4 ≤ Nat.card (σ.S : Subgroup G) := by
    rw [hS]
    exact Nat.pow_le_pow_right (by norm_num) hSD.1
  have hnil : Group.IsNilpotent (σ.S : Subgroup G) := σ.S.isPGroup'.isNilpotent
  have hT'top : σ.T.subgroupOf (σ.S : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have h1 : Nat.card (σ.T.subgroupOf (σ.S : Subgroup G)) = Nat.card (σ.S : Subgroup G) := by
      rw [h, Subgroup.card_top]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv, hT4] at h1
    omega
  have hlt := Group.normalizerCondition_of_isNilpotent _ hT'top
  have hD : Subgroup.normalizer ((σ.T.subgroupOf (σ.S : Subgroup G) : Subgroup _) : Set _) =
      σ.D.subgroupOf (σ.S : Subgroup G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTS, Setting.D, Subgroup.inf_subgroupOf_left]
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [hD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv, hT4,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe σ.D_le_S).toEquiv] at hcard
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (σ.S.isPGroup'.to_le σ.D_le_S)
  rw [hk] at hcard ⊢
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    interval_cases k <;> simp at hcard
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3

omit [Finite G] in
private theorem ii34_isLinearTypeWrt {T H : Subgroup G} (hTH : T ≤ H) {F : Type} [Field F]
    [Finite F] {ι : H ⧸ CFSG.oddCore H →* PGammaL2 F} {L E : Subgroup (H ⧸ CFSG.oddCore H)}
    {S : Sylow 2 (H ⧸ CFSG.oddCore H)} (hd : IsLinearDecomposition ι L E S)
    (h3 : 3 < Nat.card F)
    (hTL : (T.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore H)) ≤ linearCore ι)
    (hT1 : (T.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore H)) ≠ ⊥) :
    IsLinearTypeWrt T H (Nat.card F) := by
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set L₀ := linearCore ι with hL₀
  have hL₀n : L₀.Normal := hd.linearCore_normal
  obtain ⟨eL₀⟩ := hd.nonempty_linearCore_mulEquiv
  set K := L₀.comap π with hK
  have hKn : K.Normal := hL₀n.comap π
  have hOK : CFSG.oddCore H ≤ K := by
    intro h hh
    change π h ∈ L₀
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff h).mpr hh]
    exact L₀.one_mem
  set L₁ := K.map H.subtype with hL₁
  refine ⟨L₁, Subgroup.map_mono hOK, Subgroup.map_subtype_le K, le_normalizer_map_subtype H K,
    ?_, ?_, F, inferInstance, inferInstance, rfl, ?_, ?_⟩
  · intro t ht
    exact ⟨⟨t, hTH ht⟩, hTL ⟨⟨t, hTH ht⟩, ht, rfl⟩, rfl⟩
  · intro Y hYH hHY hOY hTY
    have hY'n : (Y.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr hHY
    have hYbar : ((Y.subgroupOf H).map π).Normal := hY'n.map π hπs
    have hne : (Y.subgroupOf H).map π ≠ ⊥ := by
      intro hbot
      apply hT1
      rw [eq_bot_iff, ← hbot]
      exact Subgroup.map_mono (fun t ht => hTY ht)
    have hle := ii34_linearCore_le_of_normal hd h3 _ hne
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨y, hy, hyk⟩ := hle hk
    have hyk' : y⁻¹ * k ∈ CFSG.oddCore H := by
      rw [← QuotientGroup.ker_mk' (CFSG.oddCore H), MonoidHom.mem_ker, map_mul, map_inv, hyk,
        inv_mul_cancel]
    have e : H.subtype k = (y : G) * ((y⁻¹ * k : H) : G) := by simp
    rw [e]
    exact Y.mul_mem hy (hOY ⟨_, hyk', rfl⟩)
  · obtain ⟨p, f, -, hpodd, -, hq⟩ := hd.isOddPrimePower_card
    rw [hq]
    exact hpodd.pow
  · let eK : K ≃* L₁ := K.equivMapOfInjective H.subtype H.subtype_injective
    let ρ : K →* L₀ := (π.comp K.subtype).codRestrict L₀ (fun k => k.2)
    refine ⟨(eL₀.toMonoidHom.comp ρ).comp eK.symm.toMonoidHom, ?_, ?_⟩
    · intro z
      obtain ⟨y, rfl⟩ := eL₀.surjective z
      obtain ⟨h, hh⟩ := hπs (y : H ⧸ CFSG.oddCore H)
      have hhK : h ∈ K := by
        change π h ∈ L₀
        rw [hh]
        exact y.2
      refine ⟨eK ⟨h, hhK⟩, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      congr 1
      exact Subtype.ext hh
    · ext l
      obtain ⟨k, rfl⟩ := eK.surjective l
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        MulEquiv.map_eq_one_iff]
      have hcoe : ((eK k : L₁) : G) = ((k : H) : G) := rfl
      rw [hcoe]
      constructor
      · intro h1
        have h2 : π (k : H) = 1 := congrArg Subtype.val h1
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
        exact ⟨k, h2, rfl⟩
      · rintro ⟨h, hh, hhk⟩
        have hk' : h = (k : H) := H.subtype_injective hhk
        apply Subtype.ext
        change π (k : H) = 1
        rw [← hk', hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hh

private theorem ii34_aSeven_case (hσ : σ.IsValid) {n : ℕ} (hSD : HasSemidihedralSylow G n)
    {H : Subgroup G} (hDH : σ.D ≤ H) (hT : IsKleinFour (σ.T.subgroupOf H))
    (e7 : H ⧸ CFSG.oddCore H ≃* alternatingGroup (Fin 7)) :
    (∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
        Y = oddCoreIn H ∨ Y = H) ∧
      ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
        ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H := by
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  have hsimple : IsSimpleGroup (H ⧸ CFSG.oddCore H) := e7.isSimpleGroup
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  constructor
  · intro Y hYH hHY hOY
    have hY'n : (Y.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr hHY
    have hYbar : ((Y.subgroupOf H).map π).Normal := hY'n.map π hπs
    have hOY' : CFSG.oddCore H ≤ Y.subgroupOf H := fun h hh => hOY ⟨h, hh, rfl⟩
    rcases hsimple.eq_bot_or_eq_top_of_normal ((Y.subgroupOf H).map π) with hbot | htop
    · left
      apply le_antisymm _ hOY
      apply ii34_le_oddCoreIn_of_subgroupOf hYH
      rwa [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
    · right
      apply le_antisymm hYH
      have h1 : Y.subgroupOf H = ⊤ := by
        have h2 := congrArg (Subgroup.comap π) htop
        rw [hπ, QuotientGroup.comap_map_mk', Subgroup.comap_top, sup_eq_right.mpr hOY'] at h2
        exact h2
      intro h hh
      have h3 : (⟨h, hh⟩ : H) ∈ Y.subgroupOf H := h1 ▸ Subgroup.mem_top _
      exact h3
  · intro X hXH hX hDX
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hT4 : Nat.card σ.T = 4 := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv]
      exact hT.card_four
    set D' := σ.D.subgroupOf H with hD'
    have hD'2 : IsPGroup 2 D' := (σ.S.isPGroup'.to_le σ.D_le_S).comap_subtype
    have hD'O : D' ⊓ π.ker = ⊥ := by
      rw [hπ, QuotientGroup.ker_mk']
      exact ii34_inf_eq_bot_of_two_of_odd hD'2 (odd_card_oddCore H)
    have hDbar8 : 8 ≤ Nat.card (D'.map π) := by
      rw [← Nat.card_congr (ii34_mulEquivMap π D' hD'O).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv]
      exact σ.ii34_eight_le_card_D hσ hSD hT4
    have hXbar : Odd (Nat.card ((X.subgroupOf H).map π)) :=
      (ii34_odd_card_subgroupOf hXH hX).of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hDXbar : D'.map π ≤ Subgroup.normalizer (((X.subgroupOf H).map π : Subgroup _) : Set _) :=
      (Subgroup.map_mono (ii34_subgroupOf_le_normalizer hDX)).trans (Subgroup.le_normalizer_map π)
    obtain ⟨V, hVD, hV, hXV⟩ := ii34_aSeven_exists_kleinFour e7 (hD'2.map π) hDbar8 hXbar hDXbar
    set T₁' : Subgroup H := V.comap π ⊓ D' with hT₁'
    have hT₁'O : T₁' ⊓ π.ker = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_right).trans hD'O.le)
    have hT₁'map : T₁'.map π = V := by
      apply le_antisymm
      · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le _ _)
      · intro v hv
        obtain ⟨d, hd, rfl⟩ := hVD hv
        exact ⟨d, ⟨hv, hd⟩, rfl⟩
    have hT₁'K : IsKleinFour T₁' := ii34_isKleinFour_of_mulEquiv
      ((ii34_mulEquivMap π T₁' hT₁'O).trans (MulEquiv.subgroupCongr hT₁'map)).symm hV
    refine ⟨T₁'.map H.subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    · exact ii34_isKleinFour_of_mulEquiv
        (T₁'.equivMapOfInjective H.subtype H.subtype_injective) hT₁'K
    · rw [Subgroup.commutator_le]
      rintro x hx _ ⟨t', ht', rfl⟩
      have hxH := hXH hx
      have h1 : π ⟨x, hxH⟩ ∈ Subgroup.centralizer (V : Set _) := hXV ⟨⟨x, hxH⟩, hx, rfl⟩
      have hcomm : π t' * π ⟨x, hxH⟩ = π ⟨x, hxH⟩ * π t' :=
        (Subgroup.mem_centralizer_iff.mp h1) (π t') ht'.1
      have hmem : ⁅(⟨x, hxH⟩ : H), t'⁆ ∈ CFSG.oddCore H := by
        rw [← QuotientGroup.ker_mk' (CFSG.oddCore H), MonoidHom.mem_ker, commutatorElement_def,
          map_mul, map_mul, map_mul, map_inv, map_inv, ← hπ, ← hcomm]
        group
      exact ⟨_, hmem, by simp [commutatorElement_def]⟩

theorem dGroup_trichotomy (hσ : σ.IsValid) (_hII : σ.ChapterIIFacts) :
    ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁) := by
  intro H hDH hDW
  obtain ⟨hHD, hT, h3⟩ := hDW
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  by_cases hh : σ.height = 1
  swap
  · exact Or.inl fun X hXH hX hTX => σ.ii34_le_oddCoreIn_of_wreathed hσ hh hDH hHD hT hXH hX hTX
  obtain ⟨m, hSD⟩ : ∃ m, HasSemidihedralSylow G m := by
    rcases hσ.sylow with ⟨-, h⟩ | h
    · exact h
    · exact absurd h.1 (by rw [hh]; norm_num)
  have hW : ¬ ∃ k, HasWreathedSylow (H ⧸ CFSG.oddCore H) k := by
    rintro ⟨k, hk⟩
    rw [CFSG.ABGDGroups.hasWreathedSylow_quotient_oddCore_iff] at hk
    exact ii34_not_hasWreathedSylow hSD H k hk
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  have hT'O : σ.T.subgroupOf H ⊓ π.ker = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hπ, QuotientGroup.ker_mk']
    exact ii34_inf_eq_bot_of_two_of_odd
      ((σ.S.isPGroup'.to_le (σ.T_le_S hσ)).comap_subtype) (odd_card_oddCore H)
  have hTbar : IsKleinFour ((σ.T.subgroupOf H).map π) :=
    ii34_isKleinFour_of_mulEquiv (ii34_mulEquivMap π _ hT'O) hT
  have hTbar1 : (σ.T.subgroupOf H).map π ≠ ⊥ := by
    intro h
    have h4 := hTbar.card_four
    rw [h, Subgroup.card_bot] at h4
    norm_num at h4
  have hTcomm : (σ.T.subgroupOf H).map π ≤ commutator (H ⧸ CFSG.oddCore H) := by
    refine (Subgroup.map_mono (ii34_le_commutator hT h3)).trans ?_
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  rcases CFSG.ABGDGroups.aSeven_or_linearDecomposition
      (CFSG.ABGDGroups.isDGroup_quotient_oddCore hHD)
      (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot H) hW with he7 | hlin
  · obtain ⟨e7⟩ := he7
    exact Or.inr (Or.inl (σ.ii34_aSeven_case hσ hSD hDH hT e7))
  obtain ⟨S⟩ : Nonempty (Sylow 2 (H ⧸ CFSG.oddCore H)) := inferInstance
  obtain ⟨F, _, _, ι, L, E, hd⟩ := hlin S
  have hTL : (σ.T.subgroupOf H).map π ≤ linearCore ι :=
    hTcomm.trans hd.commutator_le_linearCore
  by_cases hq : 3 < Nat.card F
  · exact Or.inr (Or.inr ⟨hh, Nat.card F, hq, ii34_isLinearTypeWrt hTH hd hq hTL hTbar1⟩)
  left
  have hq3 : Nat.card F = 3 := by
    obtain ⟨p, f, -, hpodd, -, hcard⟩ := hd.isOddPrimePower_card
    have hodd : Odd (Nat.card F) := by
      rw [hcard]
      exact hpodd.pow
    have hone : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  intro X hXH hX hTX
  apply ii34_le_oddCoreIn_of_subgroupOf hXH
  have hXbar : Odd (Nat.card ((X.subgroupOf H).map π)) :=
    (ii34_odd_card_subgroupOf hXH hX).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hTXbar : (σ.T.subgroupOf H).map π ≤
      Subgroup.normalizer (((X.subgroupOf H).map π : Subgroup _) : Set _) :=
    (Subgroup.map_mono (ii34_subgroupOf_le_normalizer hTX)).trans (Subgroup.le_normalizer_map π)
  have hbot := ii34_eq_bot_of_card_eq_three hd hq3 hTbar hTL hXbar hTXbar
  rwa [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot

end Setting

end CFSG.ABGTheoremB
