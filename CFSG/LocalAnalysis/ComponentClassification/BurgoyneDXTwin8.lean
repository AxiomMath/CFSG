module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXTwinLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXPicture
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOSpinTwin
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXFamily
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSocle
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSub
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
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

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL)
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups

attribute [local instance] GeneralizedFitting.normal

@[expose] def p8Stated (F : Type) [Field F] :
    P8 F ≃* StatedProj (matrixDerived (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F))) :=
  MulEquiv.refl _

abbrev picR {X : Type} [Group X] {F : Type} [Field F]
    (θ : GeneralizedFitting.subgroup X ≃* P8 F) {Q₁ : QuadraticForm F (Fin (2 * 4) → F)}
    (S₁ : GL (Fin (2 * 4)) F) (ν₁ : Fˣ)
    (hS₁ : ∀ v, Q₁ (S₁.val *ᵥ v) = ν₁ * reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F) v) :
    GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q₁) :=
  (θ.trans (p8Stated F)).trans (oTransport S₁ ν₁ hS₁)

theorem congr_conj {A B : Type*} [Group A] [Group B] (Φ : A ≃* B) (z : A) :
    MulAut.congr Φ (MulAut.conj z) = MulAut.conj (Φ z) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]
  (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
  (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)

include hq in
theorem mem_twin_sup8 {F : Type} [Field F] [Finite F] (hK : ringChar F ≠ 2)
    (hK5 : 5 ≤ Nat.card F) (hd5 : 5 ≤ 2 * 4) {w : Fin (2 * 4) → F} (hw : ∀ i, w i ≠ 0)
    {a₁ a : F} (hW : OSliceW (by omega : 4 ≤ 2 * 4) w a₁ a)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F) {α : Sp8 F →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x))
    {Q₁ : QuadraticForm F (Fin (2 * 4) → F)} (S₁ : GL (Fin (2 * 4)) F) (ν₁ : Fˣ)
    (hS₁ : ∀ v, Q₁ (S₁.val *ᵥ v) = ν₁ * reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F) v)
    (S : GL (Fin (2 * 4)) F) (ν : Fˣ) (hS : ∀ v, oQ (diagGL hw) (S.val *ᵥ v) = ν * Q₁ v) :
    α (negOne8 F) ∈
      ⁅((slice (twinL hK hK5 hd5 hw hW)).comap
          (socleAction ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS)))).comap
          (liftHom K),
        ((slice (twinL hK hK5 hd5 hw hW)).comap
          (socleAction ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS)))).comap
          (liftHom K)⁆ ⊔
      ⁅((slice (twinR hK hK5 hd5 hw hW)).comap
          (socleAction ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS)))).comap
          (liftHom K),
        ((slice (twinR hK hK5 hd5 hw hW)).comap
          (socleAction ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS)))).comap
          (liftHom K)⁆ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  set Φ := ((p8Stated F).trans (oTransport S₁ ν₁ hS₁)).trans (oTransport S ν hS) with hΦ
  have hRs := range_spinMatrix_quadPlus (K := F) (n := 4) (by norm_num)
  obtain ⟨R₁, R₂, hneg, hR₁, hR₂⟩ := spin_slices_bridge h2 (by omega) hd5 hw hW
    (plusIndexEquiv 4) (quadPlus 4 F) (coe_quadPlus 4 F) hRs S₁ ν₁ hS₁ S ν hS
  have hact : ∀ g : Sp8 F, socleAction (((θ.trans (p8Stated F)).trans (oTransport S₁ ν₁ hS₁)).trans
      (oTransport S ν hS)) (liftHom K (α g)) = MulAut.conj (Φ (pi8 F g)) := by
    intro g
    have h1 : liftHom K (α g) = ((θ.symm (pi8 F g) : GeneralizedFitting.subgroup _) :
        (rhoZ K).range) := by
      rw [← coe_socleHom K hq hsimple hnab, hα]
    rw [h1, socleAction_trans', socleAction_trans', socleAction_trans', socleAction_symm,
      congr_conj, congr_conj, congr_conj]
    rfl
  have hperf : Group.IsPerfect SL(2, F) := CatalogueBGeneralLinear.specialLinear_perfect 2 F
    le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have hβ₁ : ∀ g ∈ R₁.range, ((liftHom K).comp α) g ∈ (slice (twinL hK hK5 hd5 hw hW)).comap
      (socleAction ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS))) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_comap, MonoidHom.comp_apply, hact]
    obtain ⟨x', hx'⟩ := hR₁ x
    have e : Φ (pi8 F (R₁ x)) = projH _ (oSliceH h2 (by omega) (by omega) hw hW x') := hx'
    rw [e]
    exact ⟨_, ⟨x', rfl⟩, rfl⟩
  have hβ₂ : ∀ g ∈ R₂.range, ((liftHom K).comp α) g ∈ (slice (twinR hK hK5 hd5 hw hW)).comap
      (socleAction ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS))) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_comap, MonoidHom.comp_apply, hact]
    obtain ⟨x', hx'⟩ := hR₂ x
    have e : Φ (pi8 F (R₂ x)) = projH _ (oSliceRH h2 (by omega) (by omega) hw hW x') := hx'
    rw [e]
    exact ⟨_, ⟨x', rfl⟩, rfl⟩
  have hnegmem : negOne8 F ∈ R₁.range ⊔ R₂.range := by
    have : negOne8 F = R₁ (-1) * R₂ (-1) :=
      Subtype.ext (by rw [hneg, spinGroup.coe_negOne])
    rw [this]
    exact mul_mem (mem_sup_left ⟨-1, rfl⟩) (mem_sup_right ⟨-1, rfl⟩)
  exact map_mem_sup_of_cover (liftHom K) α (fun g => rfl) (commutator_range_of_perfect hperf R₁)
    (commutator_range_of_perfect hperf R₂) hβ₁ hβ₂ hnegmem

include hq hsimple hnab in
theorem propB_of_twin_sub {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hcZ : c ∈ center (K ⧸ pPrimeCore 2 K)) (hc1 : c ≠ 1) {X' : Subgroup (rhoZ K).range}
    (hle : GeneralizedFitting.subgroup (rhoZ K).range ≤ X')
    (htX' : (rhoZ K).rangeRestrict t ∈ X') (hYX' : Y.map (rhoZ K).rangeRestrict ≤ X')
    {S₁ S₂ : Subgroup (rhoZ K).range} (hS₁F : S₁ ≤ GeneralizedFitting.subgroup (rhoZ K).range)
    (hS₂F : S₂ ≤ GeneralizedFitting.subgroup (rhoZ K).range) {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ n) (f₁ : S₁.subgroupOf X' ≃* SL(2, GaloisField p n))
    (f₂ : S₂.subgroupOf X' ≃* SL(2, GaloisField p n)) {ū' : X'} (hū' : orderOf ū' = 2)
    (hcomm' : ∀ x ∈ S₁.subgroupOf X', ∀ y ∈ S₂.subgroupOf X', x * y = y * x)
    (hū₁' : ū' ∈ S₁.subgroupOf X') (hū₂' : ū' ∈ S₂.subgroupOf X')
    (hint' : ∀ x, x ∈ S₁.subgroupOf X' → x ∈ S₂.subgroupOf X' → x = 1 ∨ x = ū')
    (hs₁' : S₁.subgroupOf X' ≤ centralizer ({ū'} : Set X'))
    (hs₁s' : ((S₁.subgroupOf X').subgroupOf (centralizer ({ū'} : Set X'))).IsSubnormal)
    (hs₂' : S₂.subgroupOf X' ≤ centralizer ({ū'} : Set X'))
    (hs₂s' : ((S₂.subgroupOf X').subgroupOf (centralizer ({ū'} : Set X'))).IsSubnormal)
    (hprop₁' : ActsProperly (⟨_, htX'⟩ : X') ((Y.map (rhoZ K).rangeRestrict).subgroupOf X')
      (S₁.subgroupOf X') ⊥)
    (hprop₂' : ActsProperly (⟨_, htX'⟩ : X') ((Y.map (rhoZ K).rangeRestrict).subgroupOf X')
      (S₂.subgroupOf X') ⊥)
    (hcT : c ∈ ⁅S₁.comap (liftHom K), S₁.comap (liftHom K)⁆ ⊔
      ⁅S₂.comap (liftHom K), S₂.comap (liftHom K)⁆) :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  have hS₁X : S₁ ≤ X' := hS₁F.trans hle
  have hS₂X : S₂ ≤ X' := hS₂F.trans hle
  let e₁ : S₁ ≃* SL(2, GaloisField p n) := (subgroupOfEquivOfLe hS₁X).symm.trans f₁
  let e₂ : S₂ ≃* SL(2, GaloisField p n) := (subgroupOfEquivOfLe hS₂X).symm.trans f₂
  have hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hcomm' ⟨a, hS₁X ha⟩ (mem_subgroupOf.mpr ha) ⟨b, hS₂X hb⟩
      (mem_subgroupOf.mpr hb))
  have hū : orderOf (ū' : (rhoZ K).range) = 2 := by rw [Subgroup.orderOf_coe]; exact hū'
  have hint : ∀ x, x ∈ S₁ → x ∈ S₂ → x = 1 ∨ x = (ū' : (rhoZ K).range) := by
    intro x hx1 hx2
    rcases hint' ⟨x, hS₁X hx1⟩ (mem_subgroupOf.mpr hx1) (mem_subgroupOf.mpr hx2) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hcent : ∀ {S' : Subgroup (rhoZ K).range} (hSX : S' ≤ X'),
      S'.subgroupOf X' ≤ centralizer ({ū'} : Set X') →
      S' ≤ centralizer ({(ū' : (rhoZ K).range)} : Set (rhoZ K).range) := by
    intro S' hSX h x hx
    have := h (mem_subgroupOf.mpr (show ((⟨x, hSX hx⟩ : X') : (rhoZ K).range) ∈ S' from hx))
    rw [mem_centralizer_singleton_iff] at this ⊢
    exact congrArg Subtype.val this
  have hrange := liftHom_range_eq K hq hsimple hnab
  exact propB_of_twin K hq (hrange ▸ hS₁F) (hrange ▸ hS₂F) hp2 h5 e₁ e₂ hcomm hū
    (mem_subgroupOf.mp hū₁') (mem_subgroupOf.mp hū₂') hint (hcent hS₁X hs₁')
    (isSubnormal_of_subgroupOf hle ū' hS₁F hs₁s') (hcent hS₂X hs₂')
    (isSubnormal_of_subgroupOf hle ū' hS₂F hs₂s')
    (actsProperly_of_subgroupOf (⟨_, htX'⟩ : X') hYX' hS₁X hprop₁')
    (actsProperly_of_subgroupOf (⟨_, htX'⟩ : X') hYX' hS₂X hprop₂') hcZ hc1 hcT

include hq hsimple hnab in
theorem propB_of_twin8 {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {p' f' : ℕ} [Fact p'.Prime] (hp2' : p' ≠ 2) {F : Type} [Field F]
    [Finite F] (hK : ringChar F ≠ 2) (hKc : Nat.card F = p' ^ f')
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F) {α : Sp8 F →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x)) (hαc : α (negOne8 F) = c)
    {X' : Subgroup (rhoZ K).range} (hle : GeneralizedFitting.subgroup (rhoZ K).range ≤ X')
    (htX' : (rhoZ K).rangeRestrict t ∈ X') (hYX' : Y.map (rhoZ K).rangeRestrict ≤ X')
    {Q₁ : QuadraticForm F (Fin (2 * 4) → F)} (S₁ : GL (Fin (2 * 4)) F) (ν₁ : Fˣ)
    (hS₁ : ∀ v, Q₁ (S₁.val *ᵥ v) = ν₁ * reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F) v)
    (hT : 5 ≤ Nat.card F ∧ TwinSliceData (Ring.two_ne_zero hK)
      (picR (subSocleEquiv hsimple hnab θ hle) S₁ ν₁ hS₁) (⟨_, htX'⟩ : X')) :
    ∃ u : K ⧸ pPrimeCore 2 K, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (K ⧸ pPrimeCore 2 K),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype = zpowers u ⊔ zpowers c ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₁ ⊥ ∧
      ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y S₂ ⊥ := by
  obtain ⟨-, -, -, hY1, hY2, -, -, -, -, -, -, -, -, hcZ, -, hc2, -⟩ := id hH
  obtain ⟨hK5, hd5, w, hw, a₁, a, hW, S, ν, hS, hker', hψ't, hcore'⟩ := hT
  have hsimple' := isSimpleGroup_sub hsimple hnab hle
  have hnab' := nab_sub hsimple hnab hle
  have hY1' : (Y.map (rhoZ K).rangeRestrict).subgroupOf X' ≠ ⊥ := by
    intro h
    apply hY1
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hYX' hy⟩ : X') ∈ (Y.map (rhoZ K).rangeRestrict).subgroupOf X' :=
      mem_subgroupOf.mpr hy
    rw [h, mem_bot] at hy'
    exact (mem_bot).mpr (congrArg Subtype.val hy')
  have hY2' : (Y.map (rhoZ K).rangeRestrict).subgroupOf X' ≤
      oddCentralizerCore (⟨_, htX'⟩ : X') := by
    intro y hy
    rw [mem_subgroupOf] at hy
    exact oddCentralizerCore_subgroupOf_le (⟨_, htX'⟩ : X') (mem_subgroupOf.mpr (hY2 hy))
  have key := odd_twin_comap hK hK5 hd5 hw hW hker' hsimple' hnab'
    ((picR (subSocleEquiv hsimple hnab θ hle) S₁ ν₁ hS₁).trans (oTransport S ν hS)) hψ't hcore'
    hY1' hY2' hKc
  obtain ⟨ū', hū', ⟨f₁⟩, ⟨f₂⟩, hcomm', hū₁', hū₂', hint', hs₁', hs₁s', hs₂', hs₂s', hprop₁',
    hprop₂'⟩ := key
  have hsoc : ∀ x' : X',
      socleAction ((picR (subSocleEquiv hsimple hnab θ hle) S₁ ν₁ hS₁).trans
        (oTransport S ν hS)) x' = socleAction ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS))
          (x' : (rhoZ K).range) := by
    intro x'
    rw [socleAction_trans', socleAction_trans', socleAction_trans', socleAction_subSocleEquiv,
      ← socleAction_trans', ← socleAction_trans', ← socleAction_trans']
  have hSF : ∀ {L : Subgroup (matrixDerived (oQ (diagGL hw)))},
      (slice L).comap (socleAction ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS))) ≤
        GeneralizedFitting.subgroup (rhoZ K).range := by
    intro L x hx
    rw [mem_socle_iff hsimple hnab ((picR θ S₁ ν₁ hS₁).trans (oTransport S ν hS))]
    exact slice_le_range hx
  have hTS : ∀ {L : Subgroup (matrixDerived (oQ (diagGL hw)))},
      (slice L).comap (socleAction ((picR (subSocleEquiv hsimple hnab θ hle) S₁ ν₁ hS₁).trans
        (oTransport S ν hS))) =
      ((slice L).comap (socleAction ((picR θ S₁ ν₁ hS₁).trans
        (oTransport S ν hS)))).subgroupOf X' := by
    intro L
    ext x'
    rw [mem_comap, mem_subgroupOf, mem_comap, hsoc]
  simp only [hTS] at f₁ f₂ hcomm' hū₁' hū₂' hint' hs₁' hs₁s' hs₂' hs₂s' hprop₁' hprop₂'
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hcT := mem_twin_sup8 K hq hsimple hnab hK hK5 hd5 hw hW θ hα S₁ ν₁ hS₁ S ν hS
  rw [hαc] at hcT
  have h5 : 5 ≤ p' ^ f' := by rw [← hKc]; exact hK5
  exact propB_of_twin_sub K hq hsimple hnab hcZ hc1 hle htX' hYX' hSF hSF hp2' h5 f₁ f₂ hū'
    hcomm' hū₁' hū₂' hint' hs₁' hs₁s' hs₂' hs₂s' hprop₁' hprop₂' hcT

end CFSG.ComponentClassification.Burgoyne.DX
