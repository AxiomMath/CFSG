module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3J
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3P
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3R
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3T
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUCase
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.Perfect
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner82A
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerOut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCUb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILi
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUk
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUl
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4SteinU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUFour
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecLinearHigh
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecOrthFact
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSympMain
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.Sporadic.ThSchreier.Rigidity
public import Certificates.Certificate10091Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut StabU DiagU OIU
open CFSG.Assembly.LowTwoRank

theorem five_le_of_lieModel {Y : Type} [Group Y] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel Y .PSL 2 p m) : 1 ≤ m ∧ 5 ≤ p ^ m := by
  have hadm : 1 ≤ m ∧ p ^ m ≠ 3 := by
    rcases hm with ⟨-, ⟨-, hm1, -, -, h23⟩, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact ⟨hm1, fun h' => h23 (by rw [h'])⟩
    all_goals exact absurd h0 (by norm_num)
  refine ⟨hadm.1, ?_⟩
  have h3 : 3 ≤ p ^ m := by
    have h3p : 3 ≤ p := by have := hp.two_le; omega
    exact h3p.trans (Nat.le_self_pow (by omega) p)
  have hodd : (p ^ m) % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  have := hadm.2
  omega

variable {G : Type} [Group G] [Finite G]

theorem u4_inner_b {p k : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p k K) (hp2 : p ≠ 2)
    {Q : Subgroup G} {x : G} (hxN : x ∈ normalizer (Q : Set G))
    (e : ↥Q ⧸ center ↥Q ≃* StatedProj (StatedSU 4 (p ^ k) K)) {θ : unitarySU p k K 4 →* ↥Q}
    (hθ : ∀ s, piQ e (θ s) = thU p k K s) (hθ1 : θ (negOneU h) = 1)
    (hφ1 : phi hxN e ≠ 1) (hLZ : center ↥(Lay Q x) = ⊥)
    (hJφ : Jp e x ≤ OutInv.fixSub (phi hxN e))
    (hJ : IsComponent ((Jp e x).subgroupOf (OutInv.fixSub (phi hxN e))))
    {m : ℕ} (hJm : Blueprint.LieModel ↥(Jp e x) .PSL 2 p m) {A : GL (Fin 4) K}
    (hA : IsCU h A (phi hxN e)) (hφ2 : phi hxN e ^ 2 = 1) :
    m = 2 * k ∧ ∃ B : Subgroup G, B ≤ Q ⊓ centralizer {x} ∧ center ↥B = ⊥ ∧
      ∃ A : Subgroup G, A ≤ B ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8 := by
  classical
  have : Finite K := h.finite
  set J' := Jp e x with hJ'
  obtain ⟨hJs, hJna⟩ := GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hJm
  have hJZ : center ↥J' = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hJna
  let eJ : ↥J' ⧸ center ↥J' ≃* ↥J' :=
    (QuotientGroup.quotientMulEquivOfEq hJZ).trans QuotientGroup.quotientBot
  have hJm' : Blueprint.LieModel (↥J' ⧸ center ↥J') .PSL 2 p m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eJ.symm hJm
  have hX' : CFSG.Assembly.IsComponentOf J'
      (FixedCommutingProduct.fixedSubgroup (phi hxN e)) := by
    rw [← fixSub_eq_fixedSubgroup]
    exact (isComponentOf_iff_isComponent_subgroupOf hJφ).2 hJ
  obtain ⟨hm1, h5⟩ := five_le_of_lieModel h.prime hp2 hJm
  have hs : RestrictedStd.SmallSource J' := Or.inl ⟨p, m, h.prime, hp2, hm1, h5, hJm', by
    rw [hJZ, Subgroup.card_bot]
    exact odd_one⟩
  have hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 :=
    (mem_uMat h).1 hA.1
  have hψ : ∀ g, phi hxN e (QuotientGroup.mk g) = QuotientGroup.mk (conjU h hA.1 g) :=
    fun g => hA.apply h g
  have hψA : ∀ g, ((conjU h hA.1 g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := fun g => by
    rw [coe_conjU, Units.val_mul, Units.val_mul]
  have hAA : ∃ c : K, (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = c • 1 := by
    have h1 : IsCU h (A * A) 1 := by
      have := hA.mul h hA
      rwa [show phi hxN e * phi hxN e = 1 by rw [← pow_two, hφ2]] at this
    obtain ⟨c, hc⟩ := eq_smul_one_of_isCU_one h hp2 h1
    exact ⟨c, by rw [← hc, Units.val_mul]⟩
  obtain ⟨c₀, hc₀⟩ := hAA
  obtain ⟨⟨eP⟩, l, Q₀, hl0, -, hQ₀, hAQ⟩ :=
    GSThmB.Catalog7L4EU.psu4_inner_case h hp2 hφ1 hX' hs hAu hψ hψA hc₀
  have hKc := h.card_eq_sq
  have hKodd : Odd (Nat.card K) := by
    rw [hKc]
    exact ((h.prime.odd_of_ne_two hp2).pow).pow
  have hpm := GSThmB.Catalog7L4EU.eq_card_of_quotient_psl2 h.prime hp2 hJm' hKodd eP
  rw [hKc, ← pow_mul] at hpm
  have hm : m = 2 * k := by
    have := Nat.pow_right_injective h.prime.two_le hpm
    omega
  refine ⟨hm, ?_⟩
  have hJp : ⁅J', J'⁆ = J' := by
    have hJq : IsQuasisimple ↥J' :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJφ) hJ.1
    have : Group.IsPerfect ↥J' := hJq.1
    exact Subgroup.commutator_eq_self (H := J')
  have hJc : Nat.card ↥J' = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
    rw [Nat.card_congr (eJ.symm.trans eP).toEquiv,
      GSThmB.Catalog7Std.card_psl2_of_odd hKodd rfl]
  obtain ⟨hAκ, hnot, hcen, hE8⟩ :=
    u4_inner_aut h hp2 hA hl0 hQ₀ hAQ (fun y hy => hJφ hy) hJp hJc
  set κ := kappaU h hQ₀ with hκ
  have hxκ : xAut hxN (θ κ) = θ κ := by
    rw [xAut_thetaU h hxN e hθ hA κ, hAκ, map_mul, hθ1, one_mul]
  have hκ2 : θ κ * θ κ = 1 := by
    rw [← map_mul, hκ, kappaU_sq, hθ1]
  rw [← hθ κ] at hnot hcen hE8
  exact b_alternative e hLZ ((xAut_eq_iff hxN _).mp hxκ) hκ2 hnot hcen hE8

theorem u4_case (Q : Subgroup G) (x : G) (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (hQ : IsQuasisimple ↥Q) (hU : Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 p k)
    (hZ : Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ p ^ k + 1))
    (hxN : x ∈ normalizer (Q : Set G)) (hx2 : x * x = 1) (hxC : x ∉ centralizer (Q : Set G))
    (hLm : Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {x})) .PSL 2 p m) :
    m = 2 * k ∧
      ((∃ B : Subgroup G, B ≤ Q ⊓ centralizer {x} ∧ center ↥B = ⊥ ∧
          ∃ A : Subgroup G, A ≤ B ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8) ∨
        ∀ w ∈ GSThmB.layerIn (Q ⊓ centralizer {x}), orderOf w = 2 →
          ∃ X₁ X₂ : Subgroup G, X₁ ≠ X₂ ∧ X₁ ≤ Q ⊓ centralizer {w} ∧
            X₂ ≤ Q ⊓ centralizer {w} ∧ (X₁.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
            (X₂.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
            X₁ ≤ centralizer (X₂ : Set G) ∧ X₁ ⊓ X₂ = zpowers w ∧
            IsSLTwoOver (p ^ k) ↥X₁ ∧ IsSLTwoOver (p ^ k) ↥X₂) := by
  classical
  obtain ⟨K, _, h, ⟨e₀⟩⟩ := exists_unitary_of_lieModel hU hp hk
  have : Finite K := h.finite
  have hφ2 := phi_sq hxN e₀ hx2
  have hφ1 := phi_ne_one hxN e₀ hQ.1 hxC
  obtain ⟨hLs, hLna⟩ := GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hLm
  have hLZ : center ↥(Lay Q x) = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hLna
  have hJφ := Jp_le_fixSub hxN e₀
  have hJ := isComponent_Jp hxN e₀ hLna
  have huniq : ∀ R : Subgroup (StatedProj (StatedSU 4 (p ^ k) K)),
      R ≤ OutInv.fixSub (phi hxN e₀) →
      IsComponent (R.subgroupOf (OutInv.fixSub (phi hxN e₀))) → R ≤ Jp e₀ x :=
    fun R hR hRc => le_Jp_of_isComponent hxN e₀ hR hRc
  have hJm : Blueprint.LieModel ↥(Jp e₀ x) .PSL 2 p m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (equivJp e₀ hLZ) hLm
  obtain ⟨θ, hθs, hθ, hθk, hθ1⟩ := exists_thetaU h hp2 e₀ hQ hZ
  by_cases hinn : phi hxN e₀ ∈ InnU p k K h
  · obtain ⟨A, hA⟩ := (mem_InnU h).1 hinn
    obtain ⟨hm, hB⟩ := u4_inner_b h hp2 hxN e₀ hθ hθ1 hφ1 hLZ hJφ hJ hJm hA hφ2
    exact ⟨hm, Or.inl hB⟩
  · obtain ⟨hm, hrow⟩ := anti_case h hp2 hφ2 hinn hJφ hJ huniq hJm
    exact ⟨hm, Or.inr (rowOU_x_alternative h hp2 hxN e₀ hθs hθ hθk hθ1 hLZ hrow)⟩

theorem u4InvolutionCentralizerFact : U4InvolutionCentralizerFact := by
  intro G _ _ Q x p k m hp hp2 hk hQ hU hZ hxN hx2 hxC hLm
  exact u4_case Q x p k m hp hp2 hk hQ hU hZ hxN hx2 hxC hLm

theorem l4u4InvolutionCentralizerFact : L4U4InvolutionCentralizerFact :=
  l4u4InvolutionCentralizerFact_of_u4 u4InvolutionCentralizerFact

end CFSG.ComponentClassification.HarrisLit.C3
