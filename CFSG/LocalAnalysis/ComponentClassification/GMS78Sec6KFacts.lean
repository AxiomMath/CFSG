module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Main
public import CFSG.GroupTheory.SolvableHallNodes
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.Adapters.FrobeniusKernel
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.Foundations
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313L2
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push29Defs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Local
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Schreier.J4SProfileNode
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
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.OStar
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open CFSG.ComponentClassification.RankTwoStandard CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement Pointwise

theorem map_commutator_centralizer_comap {M P : Type*} [Group M] [Group P] (ρ : M →* P)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center M) {A J : Subgroup P}
    (hC : centralizer (A : Set P) = J ⊔ A) (hJA : ∀ x ∈ J, ∀ y ∈ A, x * y = y * x)
    (hJ : ⁅J, J⁆ = J) :
    (⁅centralizer ((A.comap ρ : Subgroup M) : Set M),
      centralizer ((A.comap ρ : Subgroup M) : Set M)⁆).map ρ = J := by
  set K := A.comap ρ
  set C := centralizer (K : Set M)
  set Q := (centralizer (A : Set P)).comap ρ
  have hAJ : A ≤ normalizer (J : Set P) := fun a ha => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun j hj => ?_)
    exact hJA j hj a ha
  have hJC : J ≤ centralizer (A : Set P) := hC ▸ le_sup_left
  have hAC : A ≤ centralizer (A : Set P) := hC ▸ le_sup_right
  have hCQ : C ≤ Q := by
    intro x hx
    rw [mem_comap, mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := hρ a
    have hk : k ∈ K := ha
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hx) k hk]
  have hcen : ∀ x ∈ Q, ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ center M := by
    intro x hx k hk
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [(mem_centralizer_iff.mp hx) (ρ k) hk]
    group
  have hQQ : ⁅Q, Q⁆ ≤ C := by
    rw [commutator_le]
    intro x hx y hy
    rw [mem_centralizer_iff]
    intro k hk
    set e₁ := k * x * k⁻¹ * x⁻¹ with he₁
    set e₂ := k * y * k⁻¹ * y⁻¹ with he₂
    have hc₁ : ∀ g : M, g * e₁ = e₁ * g := mem_center_iff.mp (hcen x hx k hk)
    have hc₂ : ∀ g : M, g * e₂ = e₂ * g := mem_center_iff.mp (hcen y hy k hk)
    have hkx : k * x * k⁻¹ = x * e₁ := by
      rw [hc₁ x, he₁]
      group
    have hky : k * y * k⁻¹ = y * e₂ := by
      rw [hc₂ y, he₂]
      group
    rw [commutatorElement_def]
    calc k * (x * y * x⁻¹ * y⁻¹) =
          (k * x * k⁻¹) * (k * y * k⁻¹) * (k * x * k⁻¹)⁻¹ * (k * y * k⁻¹)⁻¹ * k := by group
      _ = x * e₁ * (y * e₂) * (x * e₁)⁻¹ * (y * e₂)⁻¹ * k := by rw [hkx, hky]
      _ = x * (e₁ * y) * e₂ * e₁⁻¹ * x⁻¹ * e₂⁻¹ * y⁻¹ * k := by group
      _ = x * (y * e₁) * e₂ * e₁⁻¹ * x⁻¹ * e₂⁻¹ * y⁻¹ * k := by rw [hc₁ y]
      _ = x * y * (e₁ * e₂ * e₁⁻¹) * x⁻¹ * e₂⁻¹ * y⁻¹ * k := by group
      _ = x * y * e₂ * x⁻¹ * e₂⁻¹ * y⁻¹ * k := by
          rw [show e₁ * e₂ * e₁⁻¹ = e₂ by rw [← hc₁ e₂]; group]
      _ = x * y * (e₂ * x⁻¹) * e₂⁻¹ * y⁻¹ * k := by group
      _ = x * y * (x⁻¹ * e₂) * e₂⁻¹ * y⁻¹ * k := by rw [hc₂ x⁻¹]
      _ = x * y * x⁻¹ * y⁻¹ * k := by group
  have hJAJ : ⁅J ⊔ A, J ⊔ A⁆ ≤ J := by
    rw [commutator_le]
    intro u hu v hv
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left J A hAJ,
      Set.mem_mul] at hu hv
    obtain ⟨j, hj, a, ha, rfl⟩ := hu
    obtain ⟨j', hj', a', ha', rfl⟩ := hv
    have h1 : a * j' = j' * a := (hJA j' hj' a ha).symm
    have h2 : a * a' = a' * a := (mem_centralizer_iff.mp (hAC ha')) a ha
    have h3 : a' * j = j * a' := (hJA j hj a' ha').symm
    have h4 : a' * j' = j' * a' := (hJA j' hj' a' ha').symm
    have h5 : a * j = j * a := (hJA j hj a ha).symm
    have e : ⁅j * a, j' * a'⁆ = j * j' * j⁻¹ * j'⁻¹ := by
      rw [commutatorElement_def]
      calc j * a * (j' * a') * (j * a)⁻¹ * (j' * a')⁻¹ =
            j * (a * j') * a' * a⁻¹ * j⁻¹ * a'⁻¹ * j'⁻¹ := by group
        _ = j * (j' * a) * a' * a⁻¹ * j⁻¹ * a'⁻¹ * j'⁻¹ := by rw [h1]
        _ = j * j' * (a * a') * a⁻¹ * j⁻¹ * a'⁻¹ * j'⁻¹ := by group
        _ = j * j' * (a' * a) * a⁻¹ * j⁻¹ * a'⁻¹ * j'⁻¹ := by rw [h2]
        _ = j * j' * (a' * j⁻¹) * a'⁻¹ * j'⁻¹ := by group
        _ = j * j' * (j⁻¹ * a') * a'⁻¹ * j'⁻¹ := by
          rw [show a' * j⁻¹ = j⁻¹ * a' by
            calc a' * j⁻¹ = j⁻¹ * (j * a') * j⁻¹ := by group
              _ = j⁻¹ * (a' * j) * j⁻¹ := by rw [h3]
              _ = j⁻¹ * a' := by group]
        _ = j * j' * j⁻¹ * j'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hj hj') (inv_mem hj)) (inv_mem hj')
  have hQmap : Q.map ρ = centralizer (A : Set P) := map_comap_eq_self_of_surjective hρ _
  have hle : ⁅C, C⁆.map ρ ≤ J := by
    rw [map_commutator]
    refine le_trans (commutator_mono (map_mono hCQ) (map_mono hCQ)) ?_
    rw [hQmap, hC]
    exact hJAJ
  have hge : J ≤ ⁅C, C⁆.map ρ := by
    have h1 : ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ ≤ ⁅C, C⁆ := commutator_mono hQQ hQQ
    have h2 := map_mono (f := ρ) h1
    rw [map_commutator, map_commutator, hQmap] at h2
    refine le_trans ?_ h2
    have h3 : ⁅J, J⁆ ≤ ⁅centralizer (A : Set P), centralizer (A : Set P)⁆ :=
      commutator_mono hJC hJC
    calc J = ⁅⁅J, J⁆, ⁅J, J⁆⁆ := by rw [hJ, hJ]
      _ ≤ _ := commutator_mono h3 h3
  exact le_antisymm hle hge

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_of_sup_eq {P H K K₁ : Subgroup G} (hP : IsSylowOf 2 P H)
    (hHN : H ≤ normalizer (P : Set G)) (hK : P ⊔ K = H) (hK₁ : P ⊔ K₁ = H)
    (hKo : Odd (Nat.card K)) (hK₁o : Odd (Nat.card K₁)) :
    ∃ g ∈ P, K = K₁.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPH : P ≤ H := hP.le
  have hKH : K ≤ H := hK ▸ le_sup_right
  have hK₁H : K₁ ≤ H := hK₁ ▸ le_sup_right
  set N : Subgroup H := P.subgroupOf H with hNdef
  have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hPH).mpr hHN
  have hN2 : IsPGroup 2 N := hP.isPGroup.comap_subtype
  have : Group.IsNilpotent N := hN2.isNilpotent
  have hNsolv : Group.IsSolvable N := inferInstance
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNdef, ← hQ]
    exact Q.card_coprime_index
  have hmul : ∀ {K' : Subgroup G}, P ⊔ K' = H → K' ≤ H →
      (N : Set H) * ((K'.subgroupOf H : Subgroup H) : Set H) = Set.univ := by
    intro K' hK' hK'H
    apply Set.eq_univ_of_forall
    intro x
    have hx : (x : G) ∈ ((P ⊔ K' : Subgroup G) : Set G) := by
      rw [hK']
      exact x.2
    rw [coe_mul_of_right_le_normalizer_left P K' (hK'H.trans hHN)] at hx
    obtain ⟨p, hp, k, hk, hpk⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr ⟨⟨p, hPH hp⟩, hp, ⟨k, hK'H hk⟩, hk, Subtype.ext hpk⟩
  have hinf : ∀ {K' : Subgroup G}, Odd (Nat.card K') → N ⊓ K'.subgroupOf H = ⊥ := by
    intro K' hK'o
    have h1 : P ⊓ K' = ⊥ := AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ K'
      hP.isPGroup.to_inf_left hK'o inf_le_right
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ P ⊓ K' := mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
    rw [h1, mem_bot] at hx'
    exact Subtype.ext hx'
  obtain ⟨n, hn, hn'⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N hNsolv
    hcop (hmul hK₁ hK₁H) (hmul hK hKH) (hinf hK₁o) (hinf hKo)
  refine ⟨((n : H) : G)⁻¹, inv_mem hn, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : (⟨x, hKH hx⟩ : H) ∈ K.subgroupOf H := hx
    rw [hn'] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    refine ⟨(y : G), hy, ?_⟩
    have h := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using h
  · rintro ⟨y, hy, rfl⟩
    have hyH : y ∈ H := hK₁H hy
    have hmem : (MulAut.conj n⁻¹).toMonoidHom ⟨y, hyH⟩ ∈ K.subgroupOf H := by
      rw [hn']
      exact ⟨⟨y, hyH⟩, hy, rfl⟩
    simpa [MulAut.conj_apply, mem_subgroupOf] using hmem

omit [Finite G] in
theorem mem_of_eq_mul_central_of_odd {S : Subgroup G} {a c z : G} (hc : c ∈ S)
    (hz : ∀ g : G, g * z = z * g) (hzo : Odd (orderOf z)) (ha : ∃ n : ℕ, a ^ 2 ^ n = 1)
    (h : a = c * z) : a ∈ S := by
  obtain ⟨n, hn⟩ := ha
  have hca : c = a * z⁻¹ := by rw [h, mul_inv_cancel_right]
  have hcomm : Commute a z⁻¹ := by
    have : a * z = z * a := hz a
    exact (Commute.inv_right this)
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [pow_zero, pow_one] at hn
    rw [hn]
    exact one_mem _
  have hcop : Nat.Coprime (orderOf z) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hzo)
  have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
  have hcz : c ^ (orderOf z * u) = a := by
    rw [hca, hcomm.mul_pow, inv_pow, pow_mul z, pow_orderOf_eq_one, one_pow, inv_one, mul_one]
    rw [← Nat.mod_add_div (orderOf z * u) (2 ^ n), hu, pow_add, pow_one, pow_mul, hn, one_pow,
      mul_one]
  rw [← hcz]
  exact pow_mem hc _

omit [Finite G] in
theorem u3_card_SL2 (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.GorensteinWalter.sl2_card_formula F

theorem u3K_facts {L T K : Subgroup G} (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    (∀ z ∈ center L, (z : G) ∈ K) ∧
    (∀ x ∈ u3X₀ L K, ∃ c ∈ ⁅u3X₀ L K, u3X₀ L K⁆, ∃ z ∈ center L, x = c * (z : G)) ∧
    gmsA L T ≤ ⁅u3X₀ L K, u3X₀ L K⁆ ∧
    (T ⊓ L) ⊓ centralizer (K : Set G) ≤ gmsA L T ∧
    Odd (Nat.card (center (u3X₀ L K))) ∧
    Odd (Nat.card (center (⁅u3X₀ L K, u3X₀ L K⁆ : Subgroup G))) ∧
    Nonempty (rankTwoQuot (u3X₀ L K) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) ∧
    Nonempty (rankTwoQuot ⁅u3X₀ L K, u3X₀ L K⁆ ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h3.hyp.standard.1.1 hf e
  have hP : IsSylowOf 2 (T ⊓ L) L := h3.isSylowOf_T₁
  set P : Subgroup G := T ⊓ L with hPdef
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  obtain ⟨Kf, _, _, _, J, hJ, hcard, hfixed, φ, S, hS, hRS⟩ := exists_mulEquiv_root hf e R
  set ρ : L →* ProjectiveSpecialUnitaryMatrixGroup J :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hρdef
  have hρ : Function.Surjective ρ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker, hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set P' : Subgroup L := P.subgroupOf L
  set A₁ : Subgroup G := P ⊓ centralizer (P : Set G)
  have hKH' : P ⊔ K = L ⊓ normalizer (P : Set G) ⊓ centralizer (A₁ : Set G) := hKH
  have hP' : IsPGroup 2 P' := hP.isPGroup.comap_subtype
  have hroot : P'.map ρ = unitaryCoverRoot J hJ := by
    rw [← hS, ← hRS, hρdef, ← map_map, ← hR]
    congr 1
    ext y
    rw [MonoidHom.mem_range, mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hP.le x.2⟩, x.2, rfl⟩
  have hPZ : P' ⊓ center L = ⊥ :=
    AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ (center L) hP'.to_inf_left hZ
      inf_le_right
  have hinjP : ∀ p ∈ P', ρ p = 1 → p = 1 := fun p hp h1 => by
    have : p ∈ P' ⊓ center L := mem_inf.mpr ⟨hp, hker ▸ MonoidHom.mem_ker.mpr h1⟩
    rwa [hPZ, mem_bot] at this
  have hrootP : ∀ x ∈ unitaryCoverRoot J hJ, ∃ p ∈ P', ρ p = x := fun x hx => by
    rw [← hroot] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp, rfl⟩
  have hNA := u3_torusK_le_normalizer J hJ
  have hCA := u3_torusK_le_centralizer J hJ hf hcard hfixed
  set K₁' : Subgroup L := (u3TorusK J hJ).comap ρ
  set K₁ : Subgroup G := K₁'.map L.subtype
  have hZK : center L ≤ K₁' := fun z hz => by
    rw [← hker] at hz
    show ρ z ∈ u3TorusK J hJ
    rw [MonoidHom.mem_ker.mp hz]
    exact one_mem _
  have hKP : ∀ k ∈ K₁', ∀ p ∈ P', k * p * k⁻¹ ∈ P' := by
    intro k hk p hp
    have h1 : ρ (k * p * k⁻¹) ∈ unitaryCoverRoot J hJ := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (hNA hk) _).mp (by rw [← hroot]; exact ⟨p, hp, rfl⟩)
    obtain ⟨p₂, hp₂, hp₂e⟩ := hrootP _ h1
    have hz : p₂⁻¹ * (k * p * k⁻¹) ∈ center L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hp₂e, inv_mul_cancel]
    have hpow : ∃ n : ℕ, (k * p * k⁻¹) ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hP' ⟨p, hp⟩
      refine ⟨n, ?_⟩
      have hn' : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      rw [conj_pow, hn', mul_one, mul_inv_cancel]
    have := eq_of_mul_central_of_odd hP' hZ le_rfl hpow hp₂ hz (by group)
    rw [this]
    exact hp₂
  have hA₁ : ∀ a : L, (a : G) ∈ A₁ → ρ a ∈ sylowCenter (unitaryCoverRoot J hJ) := by
    intro a ha
    have haP : a ∈ P' := (mem_inf.mp ha).1
    refine mem_sylowCenter.mpr ⟨by rw [← hroot]; exact ⟨a, haP, rfl⟩, fun t ht => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hrootP t ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp (mem_inf.mp ha).2) (q : G) hq)
  have hA₁' : ∀ z ∈ sylowCenter (unitaryCoverRoot J hJ), ∃ a : L, (a : G) ∈ A₁ ∧ ρ a = z := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hrootP z (mem_sylowCenter.mp hz).1
    refine ⟨p, mem_inf.mpr ⟨hp, mem_centralizer_iff.mpr fun q hq => ?_⟩, rfl⟩
    have hq' : (⟨q, hP.le hq⟩ : L) ∈ P' := hq
    have hc := (mem_sylowCenter.mp hz).2 (ρ ⟨q, hP.le hq⟩) (by rw [← hroot]; exact ⟨_, hq', rfl⟩)
    have h1 : (⟨q, hP.le hq⟩ : L) * p * (⟨q, hP.le hq⟩ : L)⁻¹ * p⁻¹ = 1 := by
      apply hinjP
      · exact mul_mem (mul_mem (mul_mem hq' hp) (inv_mem hq')) (inv_mem hp)
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
    have h2 : (⟨q, hP.le hq⟩ : L) * p = p * (⟨q, hP.le hq⟩ : L) := by
      calc (⟨q, hP.le hq⟩ : L) * p =
            (⟨q, hP.le hq⟩ : L) * p * (⟨q, hP.le hq⟩ : L)⁻¹ * p⁻¹ * (p * (⟨q, hP.le hq⟩ : L)) := by
            group
        _ = p * (⟨q, hP.le hq⟩ : L) := by rw [h1, one_mul]
    exact congrArg Subtype.val h2
  have hKA : ∀ k ∈ K₁', ∀ a : L, (a : G) ∈ A₁ → k * a = a * k := by
    intro k hk a ha
    have haP : a ∈ P' := (mem_inf.mp ha).1
    have h1 : k * a * k⁻¹ * a⁻¹ = 1 := by
      apply hinjP
      · exact mul_mem (hKP k hk a haP) (inv_mem haP)
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have := (mem_centralizer_iff.mp (hCA hk)) (ρ a) (hA₁ a ha)
        rw [← this]
        group
    calc k * a = k * a * k⁻¹ * a⁻¹ * (a * k) := by group
      _ = a * k := by rw [h1, one_mul]
  have h4 : ∃ s : Finset (unitaryCoverFixedField J), s.card = 4 := by
    have : Fintype (unitaryCoverFixedField J) := Fintype.ofFinite _
    have hc : 4 ≤ (Finset.univ : Finset (unitaryCoverFixedField J)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_unitaryCoverFixedField hfixed]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  have : CharP (unitaryCoverFixedField J) 2 := by
    have : Fintype (unitaryCoverFixedField J) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow
      (by rw [← Nat.card_eq_fintype_card, card_unitaryCoverFixedField hfixed])
  have hK₁o : Odd (Nat.card K₁) := by
    rw [show Nat.card K₁ = Nat.card K₁' from Subgroup.card_map_of_injective L.subtype_injective,
      card_comap_of_surjective' ρ hρ, hker]
    exact (u3_odd_card_torusK J hJ hf hcard hfixed).mul hZ
  have hK₁H : P ⊔ K₁ = L ⊓ normalizer (P : Set G) ⊓ centralizer (A₁ : Set G) := by
    apply le_antisymm
    · refine sup_le (le_inf (le_inf hP.le le_normalizer) ?_) ?_
      · intro x hx
        exact mem_centralizer_iff.mpr fun a ha =>
          ((mem_centralizer_iff.mp (mem_inf.mp ha).2) x hx).symm
      · rintro _ ⟨k, hk, rfl⟩
        refine mem_inf.mpr ⟨mem_inf.mpr ⟨k.2, ?_⟩, mem_centralizer_iff.mpr fun a ha => ?_⟩
        · refine mem_normalizer_iff.mpr fun p => ⟨fun hp => ?_, fun hp => ?_⟩
          · exact hKP k hk ⟨p, hP.le hp⟩ hp
          · have hpL : p ∈ L := by
              have h := L.mul_mem (L.mul_mem (L.inv_mem k.2) (hP.le hp)) k.2
              simpa [mul_assoc] using h
            have h := hKP k⁻¹ (inv_mem hk) ⟨(k : G) * p * (k : G)⁻¹, hP.le hp⟩ hp
            have e : (k⁻¹ * ⟨(k : G) * p * (k : G)⁻¹, hP.le hp⟩ * k⁻¹⁻¹ : L) = ⟨p, hpL⟩ :=
              Subtype.ext (by simp [mul_assoc])
            rw [e] at h
            exact h
        · have haL : a ∈ L := hP.le (mem_inf.mp ha).1
          exact (congrArg Subtype.val (hKA k hk ⟨a, haL⟩ ha)).symm
    · rintro x ⟨⟨hxL, hxN⟩, hxC⟩
      set x' : L := ⟨x, hxL⟩
      have hxN' : ρ x' ∈ normalizer ((unitaryCoverRoot J hJ : Subgroup _) : Set _) := by
        rw [← hroot]
        refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
        · obtain ⟨p, hp, rfl⟩ := hy
          refine ⟨x' * p * x'⁻¹, ?_, by simp⟩
          exact (mem_normalizer_iff.mp hxN (p : G)).mp hp
        · obtain ⟨p, hp, hpe⟩ := hy
          refine ⟨x'⁻¹ * p * x', ?_, ?_⟩
          · have h := (mem_normalizer_iff.mp (inv_mem hxN) (p : G)).mp hp
            rw [inv_inv] at h
            show ((x'⁻¹ * p * x' : L) : G) ∈ P
            exact h
          · rw [map_mul, map_mul, map_inv, hpe]
            group
      have hxC' : ρ x' ∈ centralizer ((sylowCenter (unitaryCoverRoot J hJ) : Subgroup _) :
          Set _) := by
        rw [mem_centralizer_iff]
        intro z hz
        obtain ⟨a, ha, rfl⟩ := hA₁' z hz
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext ((mem_centralizer_iff.mp hxC) (a : G) ha)
      obtain ⟨r, hr, t, ht, hrt⟩ :=
        u3_exists_eq_mul_of_mem_normalizer J hJ hf hcard hfixed hxN' hxC'
      obtain ⟨p, hp, rfl⟩ := hrootP r hr
      obtain ⟨k, rfl⟩ := hρ t
      have hz : (p * k)⁻¹ * x' ∈ center L := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, hrt]
        group
      have hkz : k * ((p * k)⁻¹ * x') ∈ K₁' := mul_mem ht (hZK hz)
      have hx' : x' = p * (k * ((p * k)⁻¹ * x')) := by group
      have hx : x = (p : G) * ((k * ((p * k)⁻¹ * x') : L) : G) := congrArg Subtype.val hx'
      rw [hx]
      exact mul_mem_sup hp ⟨_, hkz, rfl⟩
  set H : Subgroup G := L ⊓ normalizer (P : Set G) ⊓ centralizer (A₁ : Set G) with hHdef
  have hPH : IsSylowOf 2 P H := hP.of_le (hK₁H ▸ le_sup_left) (inf_le_left.trans inf_le_left)
  have hHN : H ≤ normalizer (P : Set G) := inf_le_left.trans inf_le_right
  obtain ⟨g, hgP, hKg⟩ := exists_conj_eq_of_sup_eq hPH hHN hKH' hK₁H hKo hK₁o
  have hgL : g ∈ L := hP.le hgP
  set g' : L := ⟨g, hgL⟩
  set r := ρ g'
  have hrR : r ∈ unitaryCoverRoot J hJ := by rw [← hroot]; exact ⟨g', hgP, rfl⟩
  set K' : Subgroup L := K.subgroupOf L
  have hKK' : K'.map L.subtype = K := by rw [subgroupOf_map_subtype, inf_eq_left.mpr hKL]
  have hZK' : center L ≤ K' := by
    intro z hz
    show (z : G) ∈ K
    rw [hKg]
    refine ⟨(z : G), ⟨z, hZK hz, rfl⟩, ?_⟩
    have hc : g' * z = z * g' := (mem_center_iff.mp hz) g'
    have hc' : g * (z : G) = (z : G) * g := congrArg Subtype.val hc
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [hc', mul_inv_cancel_right]
  have hA : K'.map ρ = (u3TorusK J hJ).map (MulAut.conj r).toMonoidHom := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : (k : G) ∈ K₁.map (MulAut.conj g).toMonoidHom := by
        rw [← hKg]
        exact hk
      obtain ⟨_, ⟨k₁, hk₁, rfl⟩, hk₁e⟩ := hk'
      have hkeq : k = g' * k₁ * g'⁻¹ := Subtype.ext (by
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hk₁e
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hk₁e.symm)
      refine ⟨ρ k₁, hk₁, ?_⟩
      rw [hkeq]
      simp [MulAut.conj_apply, r]
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨k₁, rfl⟩ := hρ a
      refine ⟨g' * k₁ * g'⁻¹, ?_, ?_⟩
      · show ((g' * k₁ * g'⁻¹ : L) : G) ∈ K
        rw [hKg]
        exact ⟨(k₁ : G), ⟨k₁, ha, rfl⟩, by simp [MulAut.conj_apply, g']⟩
      · simp [MulAut.conj_apply, r]
  have hAcomap : (K'.map ρ).comap ρ = K' := by
    rw [comap_map_eq, hker]
    exact sup_eq_left.mpr hZK'
  set J₁ := (u3SubLine J hJ).map (MulAut.conj r).toMonoidHom
  have hC : centralizer ((K'.map ρ : Subgroup _) : Set _) = J₁ ⊔ K'.map ρ := by
    rw [hA, centralizer_map_mulEquiv (MulAut.conj r), u3_centralizer_torusK J hJ hf hcard hfixed,
      Subgroup.map_sup]
  have hJA : ∀ x ∈ J₁, ∀ y ∈ K'.map ρ, x * y = y * x := by
    rw [hA]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, u3_commute_subLine_torusK J hJ hx hy]
  set eJ := u3SubLineEquiv J hJ
  have hJperf : ⁅u3SubLine J hJ, u3SubLine J hJ⁆ = u3SubLine J hJ := by
    have hp := CFSG.LinearGroups.special_linear_isPerfect
      (K := unitaryCoverFixedField J) (n := 2) le_rfl (Or.inr h4)
    have : Group.IsPerfect (u3SubLine J hJ) :=
      Group.IsPerfect.ofSurjective (f := eJ.symm.toMonoidHom) eJ.symm.surjective
    exact (Subgroup.isPerfect_iff).mp this
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ := by
    rw [← map_commutator, hJperf]
  have eJ₁ : J₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) :=
    ((u3SubLine J hJ).equivMapOfInjective (MulAut.conj r).toMonoidHom
      (MulAut.conj r).injective).symm.trans eJ
  have hJ₁Z : center J₁ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eJ₁ z ∈ center (Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := eJ₁.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) w]
    rw [u3_center_SL2_eq_bot, mem_bot] at h1
    rw [mem_bot]
    exact eJ₁.injective (h1.trans (map_one eJ₁).symm)
  obtain ⟨eF₀⟩ := nonempty_SL2_equiv_galois (unitaryCoverFixedField J) (f := f) (by omega)
    (card_unitaryCoverFixedField hfixed)
  set eF := eF₀.trans (u3SL2EquivPSL2 (GaloisField 2 f)).symm
  obtain ⟨eY⟩ := nonempty_quotCenter_commutator_equiv ρ hρ hker.le hC hJA hJ₁perf hJ₁Z
  have himg := map_commutator_centralizer_comap ρ hρ hker.le hC hJA hJ₁perf
  rw [hAcomap] at eY himg
  set Y : Subgroup L := ⁅centralizer (K' : Set L), centralizer (K' : Set L)⁆ with hYdef
  have hCL : L ⊓ centralizer (K : Set G) = (centralizer (K' : Set L)).map L.subtype := by
    have h := inf_centralizer_map_subtype (L := L) K'
    rwa [hKK'] at h
  have hX : u3X₀ L K = Y.map L.subtype := by
    show ⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆ = _
    rw [hCL, ← map_commutator]
  have hX' : ⁅u3X₀ L K, u3X₀ L K⁆ = (⁅Y, Y⁆).map L.subtype := by
    rw [hX, ← map_commutator]
  set Y' : Subgroup L := ⁅Y, Y⁆ with hY'def
  have himg' : Y'.map ρ = J₁ := by
    rw [hY'def, map_commutator, himg, hJ₁perf]
  have hcenter : ∀ {W : Subgroup L}, W.map ρ = J₁ → (center W).map W.subtype ≤ center L := by
    intro W hW
    rintro _ ⟨w, hw, rfl⟩
    rw [← hker, MonoidHom.mem_ker]
    have hwJ : ρ (w : L) ∈ J₁ := by rw [← hW]; exact ⟨w, w.2, rfl⟩
    have hc : (⟨ρ (w : L), hwJ⟩ : J₁) ∈ center J₁ := by
      rw [mem_center_iff]
      intro y
      have hy : (y : ProjectiveSpecialUnitaryMatrixGroup J) ∈ W.map ρ := by
        rw [hW]; exact y.2
      obtain ⟨v, hv, hve⟩ := hy
      apply Subtype.ext
      show (y : ProjectiveSpecialUnitaryMatrixGroup J) * ρ (w : L) = ρ (w : L) * y
      rw [← hve, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val ((mem_center_iff.mp hw) ⟨v, hv⟩)
    rw [hJ₁Z, mem_bot] at hc
    exact congrArg Subtype.val hc
  have hoddcenter : ∀ {W : Subgroup L}, W.map ρ = J₁ → Odd (Nat.card (center W)) := by
    intro W hW
    have h1 := Subgroup.card_dvd_of_le (hcenter hW)
    rw [Subgroup.card_map_of_injective W.subtype_injective] at h1
    exact hZ.of_dvd_nat h1
  have hcongr : ∀ (W : Subgroup L) (W' : Subgroup G), W' = W.map L.subtype →
      Nonempty (W' ≃* W) := by
    intro W W' hW'
    subst hW'
    exact ⟨(W.equivMapOfInjective L.subtype L.subtype_injective).symm⟩
  obtain ⟨cX⟩ := hcongr Y (u3X₀ L K) hX
  obtain ⟨cX'⟩ := hcongr Y' ⁅u3X₀ L K, u3X₀ L K⁆ hX'
  set ψ : Y' →* J₁ := (ρ.comp Y'.subtype).codRestrict J₁ (fun y => by
    rw [← himg']; exact ⟨y, y.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    intro j
    have hj : (j : ProjectiveSpecialUnitaryMatrixGroup J) ∈ Y'.map ρ := by
      rw [himg']; exact j.2
    obtain ⟨y, hy, hye⟩ := hj
    exact ⟨⟨y, hy⟩, Subtype.ext hye⟩
  have hψker : ψ.ker ≤ center Y' := by
    intro y hy
    have hy1 : ρ (y : L) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have hyZ : (y : L) ∈ center L := by rw [← hker]; exact hy1
    rw [mem_center_iff]
    intro w
    exact Subtype.ext ((mem_center_iff.mp hyZ) (w : L))
  have eY' := quotCenterEquivOfSurjective ψ hψ hψker hJ₁Z
  refine ⟨fun z hz => hZK' hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    rw [hX] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : ρ y ∈ Y'.map ρ := by rw [himg', ← himg]; exact ⟨y, hy, rfl⟩
    obtain ⟨c, hc, hce⟩ := hy'
    refine ⟨(c : G), ?_, c⁻¹ * y, ?_, ?_⟩
    · rw [hX']
      exact ⟨c, hc, rfl⟩
    · rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
    · simp
  ·
    intro a ha
    have haL : a ∈ L := hP.le (mem_inf.mp ha).1
    have hZR : ρ ⟨a, haL⟩ ∈ J₁ := by
      have hz := hA₁ ⟨a, haL⟩ ha
      have hzJ₀ := u3_center_root_le J hJ hf hcard hfixed hz
      refine ⟨ρ ⟨a, haL⟩, hzJ₀, ?_⟩
      have hcom := (mem_sylowCenter.mp hz).2 r hrR
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      rw [hcom, mul_inv_cancel_right]
    rw [← himg'] at hZR
    obtain ⟨c, hc, hce⟩ := hZR
    have hz : c⁻¹ * ⟨a, haL⟩ ∈ center L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
    have hpow : ∃ n : ℕ, (⟨a, haL⟩ : L) ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hP' ⟨⟨a, haL⟩, (mem_inf.mp ha).1⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hzo : Odd (orderOf (c⁻¹ * ⟨a, haL⟩)) :=
      hZ.of_dvd_nat (by
        have h := Subgroup.orderOf_dvd_natCard (center L) hz
        exact h)
    have hmem := mem_of_eq_mul_central_of_odd hc (mem_center_iff.mp hz) hzo hpow
      (by group)
    rw [hX']
    exact ⟨⟨a, haL⟩, hmem, rfl⟩
  ·
    rintro t ⟨htP, htK⟩
    have htL : t ∈ L := hP.le htP
    set t' : L := ⟨t, htL⟩
    have ht'P : t' ∈ P' := htP
    have htC : ρ t' ∈ centralizer ((K'.map ρ : Subgroup _) : Set _) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((mem_centralizer_iff.mp htK) (k : G) hk)
    rw [hC] at htC
    have htR : ρ t' ∈ unitaryCoverRoot J hJ := by rw [← hroot]; exact ⟨t', ht'P, rfl⟩
    have hAJ₁ : K'.map ρ ≤ normalizer (J₁ : Set _) := fun k hk =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun j hj => hJA j hj k hk)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left J₁ _ hAJ₁,
      Set.mem_mul] at htC
    obtain ⟨j, hj, k, hk, hjk⟩ := htC
    have hJK : J₁ ⊓ K'.map ρ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨x₁, hx₁, rfl⟩, hx₂⟩
      rw [hA] at hx₂
      obtain ⟨x₂, hx₂', hx₂e⟩ := hx₂
      have h12 : x₂ = x₁ := (MulAut.conj r).injective hx₂e
      have hx : x₁ ∈ u3SubLine J hJ ⊓ u3TorusK J hJ := mem_inf.mpr ⟨hx₁, h12 ▸ hx₂'⟩
      rw [u3_subLine_inf_torusK J hJ, mem_bot] at hx
      rw [hx, map_one]
      exact one_mem _
    have hKodd : Odd (Nat.card (K'.map ρ)) := by
      rw [hA, Subgroup.card_map_of_injective (MulAut.conj r).injective]
      exact u3_odd_card_torusK J hJ hf hcard hfixed
    obtain ⟨m, hm⟩ := (show IsPGroup 2 (unitaryCoverRoot J hJ) by
      rw [← hS]; exact S.isPGroup') ⟨ρ t', htR⟩
    have hm' : (ρ t') ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hk1 : k = 1 := by
      have hjkc : Commute j k := hJA j hj k hk
      have h1 : j ^ 2 ^ m * k ^ 2 ^ m = 1 := by rw [← hjkc.mul_pow, hjk, hm']
      have h2 : k ^ 2 ^ m ∈ J₁ ⊓ K'.map ρ := by
        refine mem_inf.mpr ⟨?_, pow_mem hk _⟩
        have : k ^ 2 ^ m = (j ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact inv_mem (pow_mem hj _)
      rw [hJK, mem_bot] at h2
      have hord : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2
      have hodd : Odd (orderOf k) := hKodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
      rcases i with _ | i
      · rwa [pow_zero, orderOf_eq_one_iff] at hi
      · rw [hi, pow_succ] at hodd
        exact absurd (even_iff_two_dvd.mpr (dvd_mul_left 2 _)) (Nat.not_even_iff_odd.mpr hodd)
    rw [hk1, mul_one] at hjk
    have hRJ : unitaryCoverRoot J hJ ⊓ J₁ ≤ sylowCenter (unitaryCoverRoot J hJ) := by
      have hZle : sylowCenter (unitaryCoverRoot J hJ) ≤ unitaryCoverRoot J hJ ⊓ J₁ := by
        intro z hz
        refine mem_inf.mpr ⟨(mem_sylowCenter.mp hz).1, ?_⟩
        refine ⟨z, u3_center_root_le J hJ hf hcard hfixed hz, ?_⟩
        have hcom := (mem_sylowCenter.mp hz).2 r hrR
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
        rw [hcom, mul_inv_cancel_right]
      have hZcard : Nat.card (sylowCenter (unitaryCoverRoot J hJ)) = 2 ^ f := by
        obtain ⟨-, -, hZc, -⟩ := benderBorel_sylowCenter
          (bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ) S
        rw [hS] at hZc
        exact hZc
      have hle : Nat.card (unitaryCoverRoot J hJ ⊓ J₁ : Subgroup _) ≤ 2 ^ f := by
        set W : Subgroup J₁ := (unitaryCoverRoot J hJ ⊓ J₁ : Subgroup _).subgroupOf J₁
        have hW : Nat.card W = Nat.card (unitaryCoverRoot J hJ ⊓ J₁ : Subgroup _) :=
          Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
        have hW2 : IsPGroup 2 W := by
          have h2 : IsPGroup 2 (unitaryCoverRoot J hJ) := by rw [← hS]; exact S.isPGroup'
          exact (h2.to_inf_left (K := J₁)).comap_subtype
        have hW2' : IsPGroup 2 (W.map eJ₁.toMonoidHom) := hW2.map _
        obtain ⟨k, hk⟩ := hW2'.exists_card_eq
        have hdvd := Subgroup.card_subgroup_dvd_card (W.map eJ₁.toMonoidHom)
        rw [hk, u3_card_SL2, card_unitaryCoverFixedField hfixed] at hdvd
        have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
          have he : Even ((2 ^ f) ^ 2) :=
            Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, two_ne_zero⟩
          exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity)) he odd_one
        have hcop : Nat.Coprime (2 ^ k) ((2 ^ f) ^ 2 - 1) :=
          Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
        have h5 : 2 ^ k ∣ 2 ^ f := hcop.dvd_of_dvd_mul_right hdvd
        rw [← hW, ← Subgroup.card_map_of_injective (f := eJ₁.toMonoidHom) eJ₁.injective, hk]
        exact Nat.le_of_dvd (by positivity) h5
      have heq := Subgroup.eq_of_le_of_card_ge hZle (by rw [hZcard]; exact hle)
      exact heq.ge
    have hzR : ρ t' ∈ sylowCenter (unitaryCoverRoot J hJ) :=
      hRJ (mem_inf.mpr ⟨htR, hjk ▸ hj⟩)
    obtain ⟨a, ha, hae⟩ := hA₁' _ hzR
    have haP : a ∈ P' := (mem_inf.mp ha).1
    have h1 : a⁻¹ * t' = 1 := hinjP _ (mul_mem (inv_mem haP) ht'P)
      (by rw [map_mul, map_inv, hae, inv_mul_cancel])
    have h2 : t' = a := (inv_mul_eq_one.mp h1).symm
    have h3 : t = (a : G) := congrArg Subtype.val h2
    rw [h3]
    exact ha
  ·
    rw [Nat.card_congr (Subgroup.centerCongr cX).toEquiv]
    exact hoddcenter himg
  ·
    rw [Nat.card_congr (Subgroup.centerCongr cX').toEquiv]
    exact hoddcenter himg'
  · exact ⟨((quotCenterCongr cX).trans (eY.trans eJ₁)).trans eF⟩
  · exact ⟨((quotCenterCongr cX').trans (eY'.trans eJ₁)).trans eF⟩

end CFSG.ComponentClassification.GMS78
