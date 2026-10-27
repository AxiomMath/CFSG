module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCCover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentInitial.BlockSylowOrder
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCorollaryC
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL2Balance
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCClimb
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCRankGap
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCSteps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCTypes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Normal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReach39
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitBasic
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainRankTwoMaximality
public import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
@[expose] noncomputable def oddQuotConj (M : Subgroup X) :
    ↥(normalizer (M : Set X)) →* MulAut (↥M ⧸ pPrimeCore 2 ↥M) :=
  Semidihedral.Principal.CoprimeFixedPoint.quotientAction
    (LocalAnalysis.ComponentInitial.normalizerConjHom M) (pPrimeCore 2 ↥M) fun a n hn => by
      have h := Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (pPrimeCore 2 ↥M).Characteristic)
        (LocalAnalysis.ComponentInitial.normalizerConjHom M a)
      rw [← h]
      exact ⟨n, hn, rfl⟩

omit [Finite X] in
theorem oddQuotConj_mk (M : Subgroup X) (g : ↥(normalizer (M : Set X))) (x : ↥M) :
    oddQuotConj M g (x : ↥M ⧸ pPrimeCore 2 ↥M) =
      ((LocalAnalysis.ComponentInitial.normalizerConjHom M g x : ↥M) :
        ↥M ⧸ pPrimeCore 2 ↥M) := rfl

theorem fixedSubgroup_oddQuotConj {M : Subgroup X} {w : X} (hw : w ∈ normalizer (M : Set X))
    (hww : w * w = 1) :
    fixedSubgroup (oddQuotConj M ⟨w, hw⟩) =
      ((M ⊓ centralizer ({w} : Set X)).subgroupOf M).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g : ↥(normalizer (M : Set X)) := ⟨w, hw⟩ with hg
  have hgg : g * g = 1 := Subtype.ext hww
  set A := zpowers g with hA
  have hA2 : IsPGroup 2 A := fun x => ⟨1, by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp x.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      Nat.cast_ofNat, zpow_two, hgg, one_zpow, OneMemClass.coe_one]⟩
  set α : A →* MulAut ↥M := (LocalAnalysis.ComponentInitial.normalizerConjHom M).comp A.subtype
    with hα
  have hN : ∀ a : A, ∀ n ∈ pPrimeCore 2 ↥M, α a n ∈ pPrimeCore 2 ↥M := fun a n hn => by
    have h := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (pPrimeCore 2 ↥M).Characteristic)
      (LocalAnalysis.ComponentInitial.normalizerConjHom M a)
    rw [← h]
    exact ⟨n, hn, rfl⟩
  have hcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥M) :=
    Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  have key := Semidihedral.Principal.coprime_fixed_point_lifting 2 hA2 α (pPrimeCore 2 ↥M) hN hcop
  have hgen : ∀ {β : ↥(normalizer (M : Set X)) →* MulAut (↥M ⧸ pPrimeCore 2 ↥M)}
      (q : ↥M ⧸ pPrimeCore 2 ↥M), β g q = q → ∀ a : A, β a q = q := by
    intro β q hq a
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp a.2
    rw [← hn, map_zpow]
    have hfix : β g ∈ MulAction.stabilizer (MulAut (↥M ⧸ pPrimeCore 2 ↥M)) q := hq
    exact (MulAction.stabilizer _ q).zpow_mem hfix n
  have hgenX : ∀ c : ↥M, α ⟨g, mem_zpowers g⟩ c = c → ∀ a : A, α a c = c := by
    intro c hc a
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp a.2
    have ha : a = ⟨g, mem_zpowers g⟩ ^ n := Subtype.ext (by rw [← hn]; rfl)
    rw [ha, map_zpow]
    have hfix : α ⟨g, mem_zpowers g⟩ ∈ MulAction.stabilizer (MulAut ↥M) c := hc
    exact (MulAction.stabilizer _ c).zpow_mem hfix n
  ext q
  constructor
  · intro hq
    have hq' : q ∈ {q : ↥M ⧸ pPrimeCore 2 ↥M | ∀ a : A,
        Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (pPrimeCore 2 ↥M) hN a q = q} :=
      hgen (β := oddQuotConj M) q hq
    rw [key] at hq'
    obtain ⟨c, hc, rfl⟩ := hq'
    have hcw : (c : X) * w = w * c := by
      have h1 := congrArg Subtype.val (hc ⟨g, mem_zpowers g⟩)
      change w * (c : X) * w⁻¹ = c at h1
      calc (c : X) * w = w * c * w⁻¹ * w := by rw [h1]
        _ = w * c := by group
    exact ⟨c, mem_subgroupOf.mpr (mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr hcw⟩), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hcw : (c : X) * w = w * c :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_subgroupOf.mp hc)).2
    show oddQuotConj M g (c : ↥M ⧸ pPrimeCore 2 ↥M) = (c : ↥M ⧸ pPrimeCore 2 ↥M)
    rw [oddQuotConj_mk]
    congr 1
    apply Subtype.ext
    change w * (c : X) * w⁻¹ = c
    rw [← hcw]
    group

theorem exists_fixed_component_image {M T : Subgroup X} {w : X}
    (hw : w ∈ normalizer (M : Set X)) (hww : w * w = 1)
    (hTM : T ≤ M ⊓ centralizer ({w} : Set X))
    (hT : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({w} : Set X)))) :
    ∃ P : Subgroup (↥M ⧸ pPrimeCore 2 ↥M), P ≤ fixedSubgroup (oddQuotConj M ⟨w, hw⟩) ∧
      IsPComponent 2 (P.subgroupOf (fixedSubgroup (oddQuotConj M ⟨w, hw⟩))) ∧
      Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* ↥P ⧸ pPrimeCore 2 ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hφ
  have hker : ¬ 2 ∣ Nat.card φ.ker := GSThmB.OddQuot.not_two_dvd_card_ker
  set L := T.subgroupOf M with hL
  set Y := (M ⊓ centralizer ({w} : Set X)).subgroupOf M with hY
  have hLY : L ≤ Y := fun x hx => mem_subgroupOf.mpr (hTM (mem_subgroupOf.mp hx))
  have hLp : IsPComponent 2 (L.subgroupOf Y) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two).mpr hT
  have hfix := fixedSubgroup_oddQuotConj hw hww
  have hPc := GSThmB.OddQuot.isPComponent_map φ hker hLY hLp
  rw [← hfix] at hPc
  refine ⟨L.map φ, ?_, hPc, ?_⟩
  · rw [hfix]
    exact map_mono hLY
  · obtain ⟨e₁⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv φ hker L
    have hTM' : T ≤ M := hTM.trans inf_le_left
    let e : ↥T ≃* ↥L := (subgroupOfEquivOfLe hTM').symm
    exact ⟨(QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).trans e₁⟩

end CFSG.ComponentClassification.GSThmB.CorC
