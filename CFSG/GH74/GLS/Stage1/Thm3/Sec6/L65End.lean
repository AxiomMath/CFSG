module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.CharacterTheory.Semidihedral.AlternatingSevenExclusion
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.GH74.GLS.IVK.Lifted.PNormalFour
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
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
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.J1.Inv
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
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

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup

theorem no_order_eight_mulAut_alt7 (φ : MulAut (alternatingGroup (Fin 7))) : orderOf φ ≠ 8 := by
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  have hbij : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := hbij.2 φ
  intro h8
  have h1 : orderOf σ = 8 := by
    have := orderOf_injective c hbij.1 σ
    rw [hσ] at this
    rw [← this, h8]
  exact CFSG.Semidihedral.AlternatingSevenExclusion.symmetric_seven_no_order_eight σ h1

theorem no_order_eight_aut_of_alt7 {A : Type} [Group A] (e : A ≃* alternatingGroup (Fin 7))
    (φ : MulAut A) : orderOf φ ≠ 8 := by
  intro h
  apply no_order_eight_mulAut_alt7 (MulAut.congr e φ)
  rw [← h]
  exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective φ)

noncomputable def centerMapHom (A : Type) [Group A] : MulAut A →* MulAut (A ⧸ center A) where
  toFun α := QuotientGroup.congr (center A) (center A) α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance _)
  map_one' := by
    ext x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem endgame {X : Type} [Group X] [Finite X] {A T : Subgroup X}
    (hA7 : Nonempty ((↥A ⧸ center ↥A) ≃* alternatingGroup (Fin 7))) (hZodd : Odd (Nat.card (center ↥A)))
    (hT : IsPGroup 2 ↥T)
    (hTA : ∀ g ∈ T, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hne : T ⊓ A ≠ ⊥)
    {C : Type} [Group C] (φ : C ≃* ↥T)
    (hC : ∀ c ∈ center C, c ≠ 1 → ∃ g : C, orderOf g = 8 ∧ g ^ 4 = c) : False := by
  obtain ⟨e⟩ := hA7
  have hDn : ∀ s ∈ T, ∀ v ∈ T ⊓ A, s * v * s⁻¹ ∈ T ⊓ A := fun s hs v hv =>
    ⟨T.mul_mem (T.mul_mem hs hv.1) (T.inv_mem hs), hTA s hs v hv.2⟩
  obtain ⟨y, hyD, hy1, hyc⟩ := IVK.Lifted.exists_central_of_normal hT inf_le_left hne hDn
  let y' : ↥T := ⟨y, hyD.1⟩
  have hy'c : y' ∈ center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hyc s s.2).symm
  have hy'1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hc : φ.symm y' ∈ center C := by
    rw [← Subgroup.map_center_eq φ.symm]
    exact Subgroup.mem_map_of_mem _ hy'c
  have hc1 : φ.symm y' ≠ 1 := fun h => hy'1 (by simpa using congrArg φ h)
  obtain ⟨g, hg8, hg4⟩ := hC _ hc hc1
  set g' : ↥T := φ g with hg'
  have hg'8 : orderOf g' = 8 := by rw [hg', MulEquiv.orderOf_eq]; exact hg8
  have hg'4 : g' ^ 4 = y' := by
    rw [hg', ← map_pow, hg4, MulEquiv.apply_symm_apply]
  have hnorm : ∀ x : T, (x : X) ∈ normalizer (A : Set X) := by
    intro x
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hTA x x.2 a ha
    · intro ha
      have := hTA (x⁻¹ : T) (x⁻¹).2 _ ha
      simpa [mul_assoc] using this
  let ρ : ↥T →* MulAut (↥A ⧸ center ↥A) :=
    (centerMapHom ↥A).comp ((A.normalizerMonoidHom).comp
      (Subgroup.inclusion (fun x hx => hnorm ⟨x, hx⟩)))
  have hρ4 : ρ g' ^ 4 = ρ y' := by rw [← map_pow, hg'4]
  have hρ8 : ρ g' ^ 8 = 1 := by
    rw [← map_pow]
    have : g' ^ 8 = 1 := by rw [← hg'8]; exact pow_orderOf_eq_one g'
    rw [this, map_one]
  have hρy : ρ y' ≠ 1 := by
    intro h1
    have hyA : y ∈ A := hyD.2
    have hcen : (QuotientGroup.mk (⟨y, hyA⟩ : ↥A) : ↥A ⧸ center ↥A) ∈ center (↥A ⧸ center ↥A) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      have h3 := congrArg (fun m : MulAut (↥A ⧸ center ↥A) => m (QuotientGroup.mk a)) h1
      simp only [MulAut.one_apply] at h3
      have h2 : (ρ y' : MulAut (↥A ⧸ center ↥A)) (QuotientGroup.mk a) =
          QuotientGroup.mk (⟨y * (a : X) * y⁻¹, hTA y hyD.1 a a.2⟩ : ↥A) := rfl
      rw [h2] at h3
      have h4 : (⟨y * (a : X) * y⁻¹, hTA y hyD.1 a a.2⟩ : ↥A) = (⟨y, hyA⟩ : ↥A) * a * (⟨y, hyA⟩ : ↥A)⁻¹ :=
        Subtype.ext rfl
      rw [h4] at h3
      have h5 : QuotientGroup.mk ((⟨y, hyA⟩ : ↥A) * a * (⟨y, hyA⟩ : ↥A)⁻¹) =
          (QuotientGroup.mk (⟨y, hyA⟩ : ↥A) : ↥A ⧸ center ↥A) * QuotientGroup.mk a *
            (QuotientGroup.mk (⟨y, hyA⟩ : ↥A))⁻¹ := by simp
      rw [h5] at h3
      calc (QuotientGroup.mk a : ↥A ⧸ center ↥A) * QuotientGroup.mk (⟨y, hyA⟩ : ↥A)
          = (QuotientGroup.mk (⟨y, hyA⟩ : ↥A) * QuotientGroup.mk a *
              (QuotientGroup.mk (⟨y, hyA⟩ : ↥A))⁻¹) * QuotientGroup.mk (⟨y, hyA⟩ : ↥A) := by rw [h3]
        _ = QuotientGroup.mk (⟨y, hyA⟩ : ↥A) * QuotientGroup.mk a := by group
    have hz : center (↥A ⧸ center ↥A) = ⊥ :=
      CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by norm_num))
    rw [hz, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
    have hodd : Odd (orderOf (⟨y, hyA⟩ : ↥A)) :=
      (hZodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hcen))
    have h2pow : ∃ n : ℕ, orderOf y = 2 ^ n := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf).1 hT ⟨y, hyD.1⟩
      exact ⟨n, by rw [← hn, Subgroup.orderOf_mk]⟩
    obtain ⟨n, hn⟩ := h2pow
    have hoy : orderOf (⟨y, hyA⟩ : ↥A) = orderOf y := Subgroup.orderOf_mk _ _
    rw [hoy, hn] at hodd
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow.mpr ⟨even_two, hn0⟩))
    rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
    exact hy1 hn
  have hord : orderOf (ρ g') = 8 := by
    refine orderOf_eq_prime_pow (p := 2) (n := 2) ?_ ?_
    · norm_num
      rw [hρ4]; exact hρy
    · norm_num; exact hρ8
  exact no_order_eight_aut_of_alt7 e _ hord

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
