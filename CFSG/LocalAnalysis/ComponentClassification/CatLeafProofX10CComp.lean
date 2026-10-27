module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CNDef
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CDiag
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpQuot
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10S8
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport
public import CFSG.GroupTheory.QuasiDihedralFusion.Structure
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S7d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Statement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAssembly
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10C

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

variable {X : Type} [Group X] [Finite X]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 X)

theorem hasNormalPComplement_of_injective {A B : Type*} [Group A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Injective f) (h : HasNormalPComplement 2 B) :
    HasNormalPComplement 2 A := by
  have h1 := QuasiDihedralFusion.hasNormalPComplement_subgroup h f.range
  have : Finite A := Finite.of_injective f hf
  exact QuasiDihedralFusion.hasNormalPComplement_of_mulEquiv
    (MonoidHom.ofInjective hf).symm h1

theorem mem_normalizer_of_map_conj_eq_self' {G : Type*} [Group G] {L : Subgroup G} {g : G}
    (h : L.map (MulAut.conj g).toMonoidHom = L) : g ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : x = y := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      have h2 := congrArg (fun w => g⁻¹ * w * g) h1
      simpa [mul_assoc] using h2.symm
    rw [hxy]
    exact hy

theorem map_mem_normalizer_of_isComponent {a : X} (ha : orderOf a = 2)
    (hL : pLayer ↥(centralizer ({a} : Set X)) 2 = ⊥) {L₀ : Subgroup (X ⧸ pPrimeCore 2 X)}
    (hL₀ : IsComponent L₀) : π a ∈ normalizer (L₀ : Set (X ⧸ pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hW, hWm⟩ := CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 L₀ hL₀
  set W := CatalogueBPrimeJoin.canonicalPrimeLift 2 L₀ with hWdef
  have hWa := conj_eq_of_pLayer_centralizer_eq_bot ha hL hW
  apply mem_normalizer_of_map_conj_eq_self'
  rw [← hWm, map_map]
  have hc : (MulAut.conj (π a)).toMonoidHom.comp π =
      MonoidHom.comp π (MulAut.conj a).toMonoidHom := by
    ext x
    simp
  rw [hc, ← map_map, hWa]

theorem sl2_or_twoA7_of_component (hN : CFTwoNilpSL2) (hK : SectionRank.IsKGroupCat X) {a z : X}
    (ha : orderOf a = 2) (hL : pLayer ↥(centralizer ({a} : Set X)) 2 = ⊥)
    (hC : HasNormalPComplement 2 ↥(centralizer ({a} : Set X))) (hz : z ∈ center X)
    (hz2 : orderOf z = 2) {L₀ : Subgroup (X ⧸ pPrimeCore 2 X)} (hL₀ : IsComponent L₀)
    (hzL : π z ∈ L₀) (h34 : ¬ Blueprint.LieModel (↥L₀ ⧸ center ↥L₀) .PSL 3 2 2)
    (h3 : 3 ∣ Nat.card L₀) :
    (∃ (K' : Type) (_ : Field K') (_ : Finite K') (r m : ℕ), r.Prime ∧ r ≠ 2 ∧ 1 ≤ m ∧
        Nat.card K' = r ^ m ∧ 5 ≤ r ^ m ∧
        Nonempty (↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* Matrix.SpecialLinearGroup (Fin 2) K')) ∨
      GH74.GLS.IsDoubleCoverOfAlt (↥L₀ ⧸ pPrimeCore 2 ↥L₀) 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hsub⟩ := hL₀
  have hO : pPrimeCore 2 ↥L₀ = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 L₀ hsub,
      pPrimeCore_quotient_pPrimeCore_eq_bot, bot_subgroupOf]
  let r₄ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* ↥L₀ :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hcat : Blueprint.Catalog (↥L₀ ⧸ center ↥L₀) := by
    have : IsSimpleGroup (↥L₀ ⧸ center ↥L₀) := hq.2.1
    refine SectionRank.catalog_of_isKGroupCat_of_surjective hK (L₀.comap π)
      ((QuotientGroup.mk' (center ↥L₀)).comp (MonoidHom.subgroupComap π L₀)) ?_
    exact (QuotientGroup.mk'_surjective _).comp
      (MonoidHom.subgroupComap_surjective π L₀ (QuotientGroup.mk'_surjective _))
  have hzc : ∀ y : X ⧸ pPrimeCore 2 X, y * π z = π z * y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 X) y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz x]
  have hz1 : π z ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := orderOf_dvd_natCard (⟨z, h1⟩ : ↥(pPrimeCore 2 X))
    rw [Subgroup.orderOf_mk, hz2] at h2
    exact Nat.not_even_iff_odd.mpr OddQuot.odd_card_pPrimeCore (even_iff_two_dvd.mpr h2)
  have hZ : ∃ w ∈ center ↥L₀, orderOf w = 2 := by
    refine ⟨⟨π z, hzL⟩, mem_center_iff.mpr fun y => Subtype.ext (hzc y), ?_⟩
    rw [Subgroup.orderOf_mk]
    refine orderOf_eq_prime ?_ hz1
    rw [← map_pow, ← hz2, pow_orderOf_eq_one, map_one]
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haN := map_mem_normalizer_of_isComponent ha hL ⟨hq, hsub⟩
  set α : MulAut ↥L₀ := L₀.normalizerMonoidHom ⟨π a, haN⟩ with hαdef
  have hαx : ∀ x : ↥L₀, ((α x : ↥L₀) : X ⧸ pPrimeCore 2 X) = π a * x * (π a)⁻¹ := fun x => rfl
  have hα2 : α * α = 1 := by
    rw [hαdef, ← map_mul]
    have h1 : (⟨π a, haN⟩ : ↥(normalizer (L₀ : Set (X ⧸ pPrimeCore 2 X)))) * ⟨π a, haN⟩ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, ha2, map_one]; rfl)
    rw [h1, map_one]
  have hCbar : HasNormalPComplement 2 ↥(centralizer ({π a} : Set (X ⧸ pPrimeCore 2 X))) := by
    rw [OddQuot.centralizer_singleton_map_eq ha2]
    exact RankThree.Coprime.hasNormalPComplement_map π hC
  have hfix : HasNormalPComplement 2 ↥(fixSub α) := by
    let ψ : ↥(fixSub α) →* ↥(centralizer ({π a} : Set (X ⧸ pPrimeCore 2 X))) :=
      { toFun := fun x => ⟨((x : ↥L₀) : X ⧸ pPrimeCore 2 X), by
          rw [mem_centralizer_singleton_iff]
          have h1 : α (x : ↥L₀) = x := x.2
          have h2 := congrArg (fun w : ↥L₀ => (w : X ⧸ pPrimeCore 2 X)) h1
          simp only [hαx] at h2
          calc ((x : ↥L₀) : X ⧸ pPrimeCore 2 X) * π a =
                (π a * x * (π a)⁻¹) * π a := by rw [h2]
            _ = π a * x := by group⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine hasNormalPComplement_of_injective ψ (fun x y hxy => ?_) hCbar
    have h1 : ((ψ x : _) : X ⧸ pPrimeCore 2 X) = ψ y := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  rcases hN ↥L₀ hq hO hcat hZ α hα2 hfix with
    ⟨K', i1, i2, r, m, hr, hr2, hm, hK', h5, ⟨e⟩⟩ | h7 | hL34 | hn3
  · exact Or.inl ⟨K', i1, i2, r, m, hr, hr2, hm, hK', h5, ⟨r₄.trans e⟩⟩
  · exact Or.inr (X10.isDoubleCoverOfAlt_seven_congr r₄.symm h7)
  · exact absurd hL34 h34
  · exact absurd h3 hn3

end CFSG.ComponentClassification.CatLeafProof.X10C
