module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Cent
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCOmTools
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33All
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33NonB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCTools
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Odd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Spor
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate3085Base
public import Certificates.Certificate5007

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

noncomputable abbrev projT (Q : QuadraticForm K V) : ↥(orthDerived Q) →* ProjOrthDerived Q :=
  QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))

theorem commute_of_mem_scalars {c g : V ≃ₗ[K] V} (hc : c ∈ scalars K V) : g * c = c * g := by
  obtain ⟨a, ha⟩ := mem_scalars.mp hc
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, ha, map_smul]

theorem commute_of_mem_ker_projT {c g : ↥(orthDerived Q)} (hc : projT Q c = 1) :
    g * c = c * g := by
  have hc' : (c : V ≃ₗ[K] V) ∈ scalars K V := by
    have := (QuotientGroup.eq_one_iff c).mp hc
    exact Subgroup.mem_subgroupOf.mp this
  exact Subtype.ext (commute_of_mem_scalars hc')

theorem commutatorElement_pow_left {G : Type*} [Group G] {a b : G}
    (hc : ∀ g : G, g * ⁅a, b⁆ = ⁅a, b⁆ * g) (n : ℕ) : ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n := by
  have h1 : a * b * a⁻¹ = ⁅a, b⁆ * b := by rw [commutatorElement_def]; group
  have key : ∀ n : ℕ, a ^ n * b * a⁻¹ ^ n = ⁅a, b⁆ ^ n * b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * b * a⁻¹ ^ (n + 1) = a * (a ^ n * b * a⁻¹ ^ n) * a⁻¹ := by group
        _ = a * (⁅a, b⁆ ^ n * b) * a⁻¹ := by rw [ih]
        _ = ⁅a, b⁆ ^ n * (a * b * a⁻¹) := by
          have hcn : ∀ g : G, g * ⁅a, b⁆ ^ n = ⁅a, b⁆ ^ n * g := fun g =>
            (Commute.pow_right (show Commute g ⁅a, b⁆ from hc g) n).eq
          rw [← mul_assoc, ← mul_assoc, hcn a]
          group
        _ = ⁅a, b⁆ ^ (n + 1) * b := by rw [h1, pow_succ]; group
  rw [commutatorElement_def, ← inv_pow, key n, mul_inv_cancel_right]

section Lift

variable [Finite K] [FiniteDimensional K V]

private theorem highWitt (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Nat.card ((scalars K V).subgroupOf (orthDerived Q)) ≤ 2 ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ a : ProjOrthDerived Q, orderOf a = p →
      ∃ x : orthDerived Q, (QuotientGroup.mk x = a ∧ orderOf x = p) ∧
        (∀ x' : orthDerived Q, QuotientGroup.mk x' = a → orderOf x' = p → x' = x) ∧
        Subgroup.centralizer {a} = (Subgroup.centralizer {x}).map (projT Q) := by
  obtain ⟨-, -, hZ, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  exact ⟨hZ, hlift⟩

private theorem eq_one_of_mem_ker_of_pow (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {c : ↥(orthDerived Q)} (hc : projT Q c = 1) (hcp : c ^ p = 1) : c = 1 := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hcZ : c ∈ (scalars K V).subgroupOf (orthDerived Q) := (QuotientGroup.eq_one_iff c).mp hc
  have hZ := (highWitt hQ hT).1
  have hord : orderOf (⟨c, hcZ⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣
      Nat.card ((scalars K V).subgroupOf (orthDerived Q)) := orderOf_dvd_natCard _
  have hord' : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  rw [Subgroup.orderOf_mk] at hord
  have hle : orderOf c ≤ 2 := (Nat.le_of_dvd (Nat.card_pos) hord).trans hZ
  rcases (Nat.dvd_prime hp).mp hord' with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    have := hp.two_le
    omega

theorem exists_lift (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Subgroup (ProjOrthDerived Q)} (hP : IsElemAbelian p P) :
    ∃ Pt : Subgroup ↥(orthDerived Q), IsElemAbelian p Pt ∧ Pt.map (projT Q) = P ∧
      ∀ a ∈ Pt, ∀ b ∈ Pt, projT Q a = projT Q b → a = b := by
  classical
  have hcomm : ∀ a b : ↥(orthDerived Q), projT Q a ∈ P → projT Q b ∈ P → a * b = b * a := by
    intro a b ha hb
    have hcab : projT Q ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext_iff.mp (hP.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    have hcent : ∀ g : ↥(orthDerived Q), g * ⁅a, b⁆ = ⁅a, b⁆ * g := fun g =>
      commute_of_mem_ker_projT hcab
    have hap : projT Q (a ^ p) = 1 := by rw [map_pow, hP.2 _ ha]
    have hpow : ⁅a, b⁆ ^ p = 1 := by
      rw [← commutatorElement_pow_left hcent p, commutatorElement_eq_one_iff_mul_comm]
      exact commute_of_mem_ker_projT hap |>.symm
    have h1 : ⁅a, b⁆ = 1 := eq_one_of_mem_ker_of_pow hQ hT hp hp2 hcab hpow
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  let Pt : Subgroup ↥(orthDerived Q) :=
    { carrier := {x | projT Q x ∈ P ∧ x ^ p = 1}
      one_mem' := ⟨by rw [map_one]; exact P.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul]; exact P.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hcomm a b ha.1 hb.1) p), ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨by rw [map_inv]; exact P.inv_mem ha.1, by
        rw [inv_pow, ha.2, inv_one]⟩ }
  refine ⟨Pt, ⟨⟨⟨fun a b => Subtype.ext (hcomm a b a.2.1 b.2.1)⟩⟩, fun x hx => hx.2⟩, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro a ha
      by_cases ha1 : a = 1
      · subst ha1
        exact Subgroup.one_mem _
      have hord : orderOf a = p := by
        haveI : Fact p.Prime := ⟨hp⟩
        exact orderOf_eq_prime (hP.2 a ha) ha1
      obtain ⟨x, ⟨hxa, hxo⟩, -, -⟩ := (highWitt hQ hT).2 p hp hp2 a hord
      refine ⟨x, ⟨?_, ?_⟩, hxa⟩
      · change QuotientGroup.mk x ∈ P
        rw [hxa]
        exact ha
      · rw [← hxo]
        exact pow_orderOf_eq_one x
  · intro a ha b hb hab
    have hd : projT Q (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hdp : (a * b⁻¹) ^ p = 1 := (Pt.mul_mem ha (Pt.inv_mem hb)).2
    have := eq_one_of_mem_ker_of_pow hQ hT hp hp2 hd hdp
    exact mul_inv_eq_one.mp this

end Lift

section Cent

variable [Finite K] [FiniteDimensional K V]

theorem orthDerived_le_orthogonalGroup' (Q : QuadraticForm K V) :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.commutator_le.mpr fun _ ha _ hb =>
    commutatorElement_mem_of_mem (H := TauCeti.QuadraticMap.orthogonalGroup Q) ha hb

theorem centralizer_eq_subgroupOf (y : ↥(orthDerived Q)) :
    Subgroup.centralizer {y} =
      (isometryCentralizer Q (y : V ≃ₗ[K] V)).subgroupOf (orthDerived Q) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, isometryCentralizer,
    Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨orthDerived_le_orthogonalGroup' Q g.2, congrArg Subtype.val h⟩
  · intro h
    exact Subtype.ext h.2

theorem centralizer_projT_eq (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {y : ↥(orthDerived Q)} (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    Subgroup.centralizer {projT Q y} = centralizerImage Q (y : V ≃ₗ[K] V) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hπy1 : projT Q y ≠ 1 := fun h => hy1 (eq_one_of_mem_ker_of_pow hQ hT hp hp2 h hyp)
  have hord : orderOf (projT Q y) = p :=
    orderOf_eq_prime (by rw [← map_pow, hyp, map_one]) hπy1
  obtain ⟨x, ⟨hxa, hxo⟩, huniq, hcent⟩ := (highWitt hQ hT).2 p hp hp2 _ hord
  have hyx : y = x := huniq y rfl (orderOf_eq_prime hyp hy1)
  rw [hcent, ← hyx, centralizer_eq_subgroupOf]
  rfl

end Cent

section FixedComponent

variable [Finite K] [FiniteDimensional K V] {p : ℕ} {x : V ≃ₗ[K] V}

theorem projT_injOn_supportedFixedDerived (hx : OddOrderIsometry Q p x)
    (hR : othersSpace x.toLinearMap (X - 1) ≠ ⊥) {a b : ↥(orthDerived Q)}
    (ha : (a : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x)
    (hb : (b : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x) (hab : projT Q a = projT Q b) : a = b := by
  have hd : projT Q (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hdZ := (QuotientGroup.eq_one_iff _).mp hd
  rw [Subgroup.mem_subgroupOf] at hdZ
  obtain ⟨c, hc⟩ := mem_scalars.mp hdZ
  have hdS : ((a * b⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x :=
    (supportedFixedDerived Q x).mul_mem ha ((supportedFixedDerived Q x).inv_mem hb)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  have hfix := (mem_supportedBlock.mp (supportedFixedDerived_le_supportedBlock hdS)).2 r hr
  rw [hc r] at hfix
  have hc1 : c = 1 := by
    have : (c - 1) • r = 0 := by rw [sub_smul, hfix, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hr0)
  have hone : a * b⁻¹ = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hc v, hc1, one_smul]
    rfl
  exact mul_inv_eq_one.mp hone

noncomputable def fixedComponentImageEquiv (hx : OddOrderIsometry Q p x)
    (hR : othersSpace x.toLinearMap (X - 1) ≠ ⊥) :
    ↥(fixedComponentImage Q x) ≃*
      ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) := by
  set H := (supportedFixedDerived Q x).subgroupOf (orthDerived Q)
  let φ : ↥H →* ProjOrthDerived Q := (projT Q).comp H.subtype
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (projT_injOn_supportedFixedDerived hx hR a.2 b.2 hab)
  have hrange : φ.range = fixedComponentImage Q x := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have e1 : ↥(fixedComponentImage Q x) ≃* ↥H :=
    (MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hφ).symm
  have e2 : ↥H ≃* ↥(supportedFixedDerived Q x) :=
    Subgroup.subgroupOfEquivOfLe hx.supportedFixedDerived_le_orthDerived
  have e3 := supportedFixedDerivedEquiv hx
  set O' := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)
  have e4 : ↥(commutator ↥O') ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
    (Subgroup.equivMapOfInjective _ O'.subtype O'.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator O'))
  exact e1.trans (e2.trans (e3.trans e4.symm))

theorem isQuasisimple_fixedComponentImage (hx : OddOrderIsometry Q p x)
    (hR : othersSpace x.toLinearMap (X - 1) ≠ ⊥) (hodd : Odd (Nat.card K))
    (hdim : 5 ≤ finrank K (fixedSpace x)) : CFSG.IsQuasisimple ↥(fixedComponentImage Q x) :=
  CFSG.IsQuasisimple.of_mulEquiv (fixedComponentImageEquiv hx hR)
    (CFSG.ComponentClassification.OddSelector.commutator_orthogonalGroup_quasisimple hodd _
      hx.polarBilin_fixed_nondegenerate hdim)

end FixedComponent

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
