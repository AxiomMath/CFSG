module

public import CFSG.GH74.Generic.BProg.B2.T4PGVTL2
public import CFSG.GH74.Generic.BProg.B2.PumpupTableSp4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutMain
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Inner
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Transport
import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutDiag
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutField
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.Components
public import CFSG.GH74.E2.OddRankG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Defs
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base
public import Certificates.Certificate5007
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLift
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.ComponentClassification.CatFactsSp4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.Generic.BProg.B2.PumpupTableBasic CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv
  CFSG.GH74.Generic.BProg.B2.PumpupTableL3 CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
  CFSG.GH74.Generic.BProg.B2.PumpupTableSp4
open scoped MatrixGroups

theorem Q3Cent.false_of_sl2 {N : Type} [Group N] [Finite N] {H K : Subgroup N} {t : N}
    (hs : Q3Cent H t K) {F : Type} [Field F] [Finite F] (hk : ringChar F ≠ 2)
    (e : ↥K ≃* SL(2, F)) : False := by
  obtain ⟨a, haL, b, hbL, ha2, hb2, ha1, hb1, hab⟩ := hs.two
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hk
  have hsq : ∀ x : ↥K, (x : N) * x = 1 → (x : N) ≠ 1 →
      ((e x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro x hx2 hx1
    refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (e x) ?_ ?_
    · rw [← map_pow, pow_two]
      have : x * x = 1 := Subtype.ext hx2
      rw [this, map_one]
    · intro h1
      apply hx1
      have : x = 1 := e.injective (by rw [h1, map_one])
      rw [this]; rfl
  have ea := hsq ⟨a, haL⟩ ha2 ha1
  have eb := hsq ⟨b, hbL⟩ hb2 hb1
  have : e ⟨a, haL⟩ = e ⟨b, hbL⟩ := Subtype.ext (ea.trans eb.symm)
  exact hab (congrArg Subtype.val (e.injective this))

theorem q3In_sp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) : Q3EmptyIn (fun X _ => LieModel X .PSp 2 p f) := by
  intro N _ _ H t L hs htH hH
  obtain ⟨hadm, F, _, _, hF, ⟨ψ⟩⟩ := stated_of_lieModel_psp hH
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hk : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  have hot : orderOf (⟨t, htH⟩ : ↥H) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hs.inv
  have hvu : orderOf (ψ ⟨t, htH⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hot
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd hvu
  set Φ : ↥H ≃* StatedProj (StatedSp 2 F) := ψ.trans φ with hΦ
  have hB := isCompIn_centralizer_subgroupOf htH hs.comp
  have hcomp : IsPComponent 2 ((L.subgroupOf H).subgroupOf
      (centralizer {(⟨t, htH⟩ : ↥H)})) := isPComponent_two_of_isComponent hB.2
  have hmap := isPComponent_map_subgroupOf 2 Φ hB.1 hcomp
  have hMX : (L.subgroupOf H).map Φ.toMonoidHom ≤ centralizer {Φ ⟨t, htH⟩} := by
    rw [← CFSG.ComponentClassification.CatFactsSp4.map_centralizer_singleton]
    exact Subgroup.map_mono hB.1
  rw [CFSG.ComponentClassification.CatFactsSp4.map_centralizer_singleton] at hmap
  let eM : ↥L ≃* ↥((L.subgroupOf H).map Φ.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hLH).symm.trans
      ((L.subgroupOf H).equivMapOfInjective Φ.toMonoidHom Φ.injective)
  have hΦt : Φ ⟨t, htH⟩ = φ (ψ ⟨t, htH⟩) := rfl
  rcases hφ with h | h
  · rw [← hΦt] at h
    rw [h] at hmap hMX
    obtain ⟨hE | hE, -⟩ := pComponent_centralizer_u1 hodd hMX hmap
    · exact hs.false_of_sl2 hk
        (eM.trans ((MulEquiv.subgroupCongr hE).trans (E1Equiv h2).symm))
    · exact hs.false_of_sl2 hk
        (eM.trans ((MulEquiv.subgroupCongr hE).trans (E2Equiv h2).symm))
  · rw [← hΦt] at h
    rw [h] at hmap hMX
    obtain ⟨hL, h5⟩ := pComponent_centralizer_u2 hodd hMX hmap
    exact hs.false_of_psl2 hp hp2 (lieModel_psl2_of_equiv hp hf (by omega) hF
      (eM.trans ((MulEquiv.subgroupCongr hL).trans (LEquiv F).symm)))

theorem lt_ordBC_two {q : ℕ} (hq : 3 ≤ q) : 5616 < CFSG.Open.ordBC 2 q := by
  unfold CFSG.Open.ordBC
  have hprod : ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
  rw [hprod]
  have h4 : 81 ≤ q ^ (2 * 2) := by
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h2 : 9 ≤ q ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h4' : 81 ≤ q ^ 4 := by simpa using h4
  have hX : 51840 ≤ q ^ (2 * 2) * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    calc 51840 = 81 * (8 * 80) := by norm_num
      _ ≤ q ^ (2 * 2) * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
        Nat.mul_le_mul h4 (Nat.mul_le_mul (by omega) (by omega))
  have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hgpos : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  calc 5616 < 51840 / 2 := by norm_num
    _ ≤ q ^ (2 * 2) * ((q ^ 2 - 1) * (q ^ 4 - 1)) / 2 := Nat.div_le_div_right hX
    _ ≤ q ^ (2 * 2) * ((q ^ 2 - 1) * (q ^ 4 - 1)) / Nat.gcd 2 (q - 1) :=
      Nat.div_le_div_left hg hgpos

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeafProof CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem q3Out_sp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Q3EmptyOut (fun X _ => LieModel X .PSp 2 p f) := by
  intro N _ _ H t K0 hs htH hY
  have := hs.normal
  obtain ⟨L, hL, ⟨eK⟩⟩ := hs.exists_comp_fixSub
  set α : MulAut ↥H := MulAut.conjNormal t with hαdef
  have hα : α * α = 1 := PumpupOutOrders.conjNormal_sq hs.inv
  have hout : α ∉ (MulAut.conj : ↥H →* MulAut ↥H).range :=
    PumpupOutOrders.conjNormal_not_inner hs.faithful htH
  obtain ⟨-, -, K, _, _, hK, ⟨ψ⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hY
  have hchar : ringChar K ≠ 2 := CFSG.GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hK
  have hβ2 : MulAut.congr ψ α * MulAut.congr ψ α = 1 := by rw [← map_mul, hα, map_one]
  have hα1 : α ≠ 1 := fun h => hout ⟨1, by rw [map_one, h]⟩
  have hβ1 : MulAut.congr ψ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  obtain ⟨A, σ, hAσ, hσ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 (MulAut.congr ψ α) hβ2 hβ1
  have hKc : IsComponent (L.subgroupOf (fixSub α)) := hL.2
  have hKc' := LocalCores.isComponent_map_mulEquiv (fixedSubgroupCongrEquiv ψ α) hKc
  let eL := (Subgroup.subgroupOfEquivOfLe hL.1).symm.trans
    ((L.subgroupOf (fixSub α)).equivMapOfInjective
      (fixedSubgroupCongrEquiv ψ α).toMonoidHom (fixedSubgroupCongrEquiv ψ α).injective)
  have hZL : center ↥L = ⊥ := by
    rw [← Subgroup.map_center_eq eK, hs.center_eq_bot, Subgroup.map_bot]
  by_cases hσ : σ = 1
  ·
    obtain rfl : σ = 1 := hσ
    rw [map_one, mul_one] at hAσ
    have hord : orderOf (conjAut 2 K A) = 2 := by
      rw [← hAσ]
      exact orderOf_eq_prime (by rw [pow_two]; exact hβ2) hβ1
    have hfix := congrArg CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup hAσ
    have hpsl : Psl2CQ p ↥L := Psl2CQ.of_mulEquiv eL
      (psl2CQ_of_component_equiv (MulEquiv.subgroupCongr hfix)
        (fun M hM => psl2CQ_inner_psp hp hp2 hK hf A hord hM) hKc')
    obtain ⟨j, -, hj⟩ := hpsl
    have eQ : (↥L ⧸ center ↥L) ≃* ↥K0 :=
      ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).trans eK.symm
    exact hs.false_of_psl2 hp hp2 (LieType.CurtisTits.lieModel_of_mulEquiv eQ hj)
  ·
    obtain ⟨e, he, hmodel⟩ := psp4_field_component_model hp hp2 hf hK A σ hAσ hσ2 hσ d hd hKc'
    have hmodelL : LieModel ↥L .PSp 2 p e :=
      LieType.CurtisTits.lieModel_of_mulEquiv eL.symm hmodel
    have hcL := CFSG.GH74.card_of_lieModel_PSp (n := 2) (by norm_num) hp2 hmodelL
    have hq3 : 3 ≤ p ^ e := by
      have := hp.two_le
      have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
      omega
    have hlt := lt_ordBC_two hq3
    have hcK : Nat.card ↥K0 = Nat.card ↥L := Nat.card_congr eK.toEquiv
    rw [hs.card_K, hcL] at hcK
    omega

theorem q3_sp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Q3Empty (fun X _ => LieModel X .PSp 2 p f) :=
  Q3Empty.of_in_out (q3In_sp4 hp hp2 hf) (q3Out_sp4 hp hp2 hf)

end CFSG.GH74.Generic.BProg.B2.T4.PGV
