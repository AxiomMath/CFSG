module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmU43Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmM2
public import CFSG.ClassicalInvolution.Q3.TA3FrameU4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43
public import CFSG.ClassicalInvolution.Asc77.AscCX4L3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafJ1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLy
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafMcL
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafSz
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallList
public import CFSG.ClassicalInvolution.AschTight.S1916Coh
public import CFSG.ClassicalInvolution.AschTight.S1916Inv
public import CFSG.ClassicalInvolution.AschTight.S19QT68
public import CFSG.ClassicalInvolution.AschTight.S19QTInv
public import CFSG.ClassicalInvolution.AschTight.S19QTSign
public import CFSG.ClassicalInvolution.AschTight.S19TF1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LargeFrameExits
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfMain
public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Sq
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4Dat
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4
public import CFSG.ClassicalInvolution.Q3.TA3SOLRee
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinDefs
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinMap
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitCase
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.Quasithin.H13.J4Core

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.U43

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TA3 CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43
open CFSG.GH74.GLS.C3.Layer1.EndN.U43 (hud P43)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open scoped MatrixGroups

set_option linter.unusedSectionVars false

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner P43

structure Emb {Y : Type} [Group Y] (ρ : Y →* MulAut P43) : Prop where
  inj : Function.Injective ρ
  mem_iff : ∀ y : Y, ρ y ∈ Inn ↔ y ∈ genFittingFStar Y
  surj : ∀ x ∈ Inn, ∃ y : Y, ρ y = x

theorem Emb.conj {Y : Type} [Group Y] {ρ : Y →* MulAut P43} (h : Emb ρ) (d : MulAut P43) :
    Emb ((MulAut.conj d).toMonoidHom.comp ρ) := by
  have hN := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal P43
  refine ⟨(MulAut.conj d).injective.comp h.inj, fun y => ?_, fun x hx => ?_⟩
  · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [← h.mem_iff]
    constructor
    · intro hy
      have := hN.conj_mem _ hy d⁻¹
      simpa [mul_assoc] using this
    · intro hy
      exact hN.conj_mem _ hy d
  · obtain ⟨y, hy⟩ := h.surj _ (hN.conj_mem x hx d⁻¹)
    refine ⟨y, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hy]
    group

theorem exists_emb {Y : Type} [Group Y] [Finite Y]
    (hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥)
    (e : ↥(genFittingFStar Y) ≃* P43) : ∃ ρ : Y →* MulAut P43, Emb ρ := by
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  set ρ : Y →* MulAut P43 :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥(genFittingFStar Y))
    with hρ
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : y ∈ Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h2 : (ρ y) (e ⟨m, hm⟩) = e ⟨m, hm⟩ := by rw [hy]; rfl
      have h3 : e (MulAut.conjNormal y ⟨m, hm⟩) = e ⟨m, hm⟩ := by
        have h5 : (ρ y) (e ⟨m, hm⟩) = e (MulAut.conjNormal y (e.symm (e ⟨m, hm⟩))) := rfl
        rw [h5, e.symm_apply_apply] at h2
        exact h2
      have h4 := congrArg Subtype.val (e.injective h3)
      simp only [MulAut.conjNormal_apply] at h4
      calc m * y = (y * m * y⁻¹) * y := by rw [h4]
        _ = y * m := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact h1
  have hval : ∀ (y : Y) (hy : y ∈ genFittingFStar Y), ρ y = MulAut.conj (e ⟨y, hy⟩) := by
    intro y hy
    ext z
    show e (MulAut.conjNormal y (e.symm z)) = e ⟨y, hy⟩ * z * (e ⟨y, hy⟩)⁻¹
    have hz : z = e (e.symm z) := (e.apply_symm_apply z).symm
    conv_rhs => rw [hz]
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (by simp [MulAut.conjNormal_apply]))
  refine ⟨ρ, hinj, fun y => ⟨fun hy => ?_, fun hy => ⟨e ⟨y, hy⟩, (hval y hy).symm⟩⟩,
    fun x hx => ?_⟩
  · obtain ⟨p, hp⟩ := hy
    have h1 : ρ ((e.symm p : ↥(genFittingFStar Y)) : Y) = ρ y := by
      rw [hval _ (e.symm p).2, Subtype.coe_eta, e.apply_symm_apply]
      exact hp
    rw [← hinj h1]
    exact (e.symm p).2
  · obtain ⟨p, rfl⟩ := hx
    exact ⟨(e.symm p : Y), by rw [hval _ (e.symm p).2, Subtype.coe_eta, e.apply_symm_apply]⟩

theorem Emb.mem_of_odd {Y : Type} [Group Y] [Finite Y] {ρ : Y →* MulAut P43} (h : Emb ρ) {y : Y}
    (hy : Odd (orderOf y)) : y ∈ genFittingFStar Y := by
  rw [← h.mem_iff]
  set z : Outer P43 := QuotientGroup.mk' (Inn) (ρ y) with hz
  have h1 : orderOf z ∣ orderOf y := by
    rw [hz]
    exact orderOf_map_dvd ((QuotientGroup.mk' (Inn)).comp ρ) y
  have h2 : orderOf z ∣ 2 ^ 3 := by
    have := orderOf_dvd_natCard z
    rw [card_outer_P43] at this
    simpa using this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hodd : Odd (orderOf z) := Odd.of_dvd_nat hy h1
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk'] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
  rw [hk0, pow_zero, orderOf_eq_one_iff, hz, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hk'
  exact hk'

theorem map_conjSub {Y : Type} [Group Y] (ρ : Y →* MulAut P43) (c : Y) (J : Subgroup Y) :
    (conjSub c J).map ρ = (J.map ρ).map (MulAut.conj (ρ c)).toMonoidHom := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem oddCore_eq_bot_of_mulEquiv {H : Type*} [Group H] [Finite H] (e : H ≃* SL(2, ZMod 3)) :
    classicalInvolutionOddCore H = ⊥ := by
  have hSL : classicalInvolutionOddCore SL(2, ZMod 3) = ⊥ :=
    CFSG.ClassicalInvolution.Asc77.CX.CX4.L4.oddCore_sl2_eq_bot_odd (by decide)
  refine le_bot_iff.mp ?_
  unfold classicalInvolutionOddCore
  refine sSup_le fun N hN => ?_
  have h1 : N.map e.toMonoidHom ≤ classicalInvolutionOddCore SL(2, ZMod 3) :=
    le_sSup ⟨hN.1.map e.toMonoidHom e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact hN.2⟩
  rw [hSL, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h1
  rw [h1]


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_pair_core (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) :
    ∃ p q : Y, IsQ8Pair p q ∧ p ^ 2 = t ∧
      tightCore R = Subgroup.closure ({p, q} : Set Y) := by
  set S' : Subgroup Y := (S : Subgroup R).map R.subtype with hS'
  have hSyl := h.core.datum.sylow_core
  obtain ⟨eq8⟩ := h.core.q8
  have hcardS : Nat.card S' = 8 := by
    rw [hS', Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr eq8.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ : CFSG.ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup S' :=
    ⟨3, le_rfl, ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).symm.trans eq8⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_q8Pair hQ
  have hKS : tightCore R ≤ S' := (hSyl.2.2 (tightCore R) le_rfl hK2 hSyl.1).le
  have hSK : S' ≤ tightCore R := hSyl.1
  have hpK : p ∈ tightCore R := hSK hp
  have hqK : q ∈ tightCore R := hSK hq
  have hz := uniqueInv_core h
  have hp2 : p ^ 2 = t := by
    have h4 : p ^ 2 * p ^ 2 = 1 := by rw [← pow_add]; exact hpq.1
    rcases hz.unique _ ((tightCore R).pow_mem hpK 2) h4 with h1 | h1
    · exact absurd h1 hpq.2.2.2
    · exact h1
  refine ⟨p, q, hpq, hp2, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hpK
    · exact hqK
  · rw [card_closure_pair hpq, ← hcardS]
    exact Subgroup.card_le_of_le hKS


theorem oddCoreIn_eq_bot {ρ : Y →* MulAut P43} (hρ : Emb ρ) (ht : ρ t = tz) :
    Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  set O := Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) with hO
  have hOodd : Odd (Nat.card O) := Balance.odd_card_oddCoreIn _
  have hOC : O ≤ Subgroup.centralizer ({t} : Set Y) := Balance.oddCoreIn_le _
  have hle : O.map ρ ≤ centT := by
    rintro _ ⟨o, ho, rfl⟩
    have hoL : o ∈ genFittingFStar Y :=
      hρ.mem_of_odd (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O ho))
    have hot : o * t = t * o := Subgroup.mem_centralizer_singleton_iff.mp (hOC ho)
    refine (mem_centT_iff _).2 ⟨(hρ.mem_iff o).2 hoL, ?_⟩
    rw [← ht, ← map_mul, ← map_mul, hot]
  have hnorm : ∀ c ∈ centT, ∀ m ∈ O.map ρ, c * m * c⁻¹ ∈ O.map ρ := by
    rintro c hc _ ⟨o, ho, rfl⟩
    obtain ⟨hcin, hct⟩ := (mem_centT_iff c).1 hc
    obtain ⟨y, rfl⟩ := hρ.surj c hcin
    have hyt : y ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hρ.inj
      rw [map_mul, map_mul, ht]
      exact hct
    exact ⟨y * o * y⁻¹, Balance.conj_mem_oddCoreIn hyt ho, by simp⟩
  have hodd : Odd (Nat.card (O.map ρ)) := by
    rw [Subgroup.card_map_of_injective hρ.inj]
    exact hOodd
  have := eq_bot_of_odd hle hnorm hodd
  exact (Subgroup.map_eq_bot_iff_of_injective O hρ.inj).mp this

theorem false_of_viol (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R))
    {ρ : Y →* MulAut P43} (hρ : Emb ρ) (ht : ρ t = tz) {c : MulAut P43} (hc : c ∈ centT)
    (hv : Viol ((tightCore R).map ρ) c) : False := by
  obtain ⟨hcin, hct⟩ := (mem_centT_iff c).1 hc
  obtain ⟨y, rfl⟩ := hρ.surj c hcin
  have hy : y ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hρ.inj
    rw [map_mul, map_mul, ht]
    exact hct
  set K := tightCore R with hK
  have hmem : ∀ w : Y, ρ w ∈ K.map ρ ↔ w ∈ K := fun w => Subgroup.mem_map_iff_mem hρ.inj
  have hconj : ∀ w : Y, ρ y * ρ w * (ρ y)⁻¹ = ρ (y * w * y⁻¹) := fun w => by
    rw [map_mul, map_mul, map_inv]
  obtain ⟨⟨_, ⟨k, hk, rfl⟩, hk'⟩, h2⟩ := hv
  have hne : conjSub y K ≠ K := by
    intro heq
    apply hk'
    rw [hconj, hmem, ← heq]
    exact conj_mem_conjSub hk
  rcases h2 with ⟨_, ⟨k₁, hk₁, rfl⟩, _, ⟨k₂, hk₂, rfl⟩, hnc⟩ | ⟨_, ⟨k₂, hk₂, rfl⟩, hin, hsq⟩
  · refine false_of_omega4_comm h hK2 hy hne hk₁ (conj_mem_conjSub hk₂) fun hc' => hnc ?_
    rw [hconj, ← map_mul, ← map_mul, hc']
  · rw [hconj, hmem] at hin
    have hsq' : (y * k₂ * y⁻¹) * (y * k₂ * y⁻¹) ≠ 1 := by
      intro h1
      apply hsq
      rw [hconj, ← map_mul, h1, map_one]
    refine false_of_omega4_inf h hK2 hy hne fun heq => hsq' ?_
    have hmemI : y * k₂ * y⁻¹ ∈ K ⊓ conjSub y K := ⟨hin, conj_mem_conjSub hk₂⟩
    rw [heq] at hmemI
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmemI
    rw [← hm, ← zpow_add, ← two_mul, zpow_mul]
    have ht2 : t ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      exact (uniqueInv_core h).sq
    rw [ht2, one_zpow]

theorem longFundSetE3_of_quat1 (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R))
    {ρ : Y →* MulAut P43} (hρ : Emb ρ) (ht : ρ t = tz) (hK : (tightCore R).map ρ = quat1) :
    LongFundSetE3 R t := by
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  set K := tightCore R with hKdef
  have hKL : K ≤ genFittingFStar Y := by
    intro k hk
    rw [← hρ.mem_iff]
    exact quat1_le_inner (hK ▸ Subgroup.mem_map_of_mem ρ hk)
  have hall : ∀ y : Y, y ∈ genFittingFStar Y := by
    have hgen : (⨆ g : Y, conjSub g K) = ⊤ := h.core.gen
    have hle : (⨆ g : Y, conjSub g K) ≤ genFittingFStar Y := by
      refine iSup_le fun g => ?_
      rintro _ ⟨k, hk, rfl⟩
      exact hTn.conj_mem k (hKL hk) g
    rw [hgen] at hle
    exact fun y => hle (Subgroup.mem_top y)
  have hinner : ∀ y : Y, ρ y ∈ Inn := fun y => (hρ.mem_iff y).2 (hall y)
  have hperm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      (conjSub c K).map ρ = quat1 ∨ (conjSub c K).map ρ = quat2 := by
    intro c hc
    have hcT : ρ c ∈ centT := by
      refine (mem_centT_iff _).2 ⟨hinner c, ?_⟩
      rw [← ht, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc]
    rw [map_conjSub, hK]
    exact perm_quat1 hcT
  obtain ⟨g, hg, hne, -, -⟩ := exists_twin h
  set K' := conjSub g K with hK'def
  have hK'2 : K'.map ρ = quat2 := by
    rcases hperm g hg with h1 | h1
    · exfalso
      apply hne
      apply Subgroup.map_injective hρ.inj
      rw [h1, hK]
    · exact h1
  have hK'tw : K' ∈ twins R := conj_mem_twins h (core_mem_twins h) hg
  have hV : ∀ J ∈ twins R, J = K ∨ J = K' := by
    intro J hJ
    obtain ⟨c, hc, rfl⟩ := exists_conj_of_mem_twins h hJ
    rcases hperm c hc with h1 | h1
    · left
      apply Subgroup.map_injective hρ.inj
      rw [h1, hK]
    · right
      apply Subgroup.map_injective hρ.inj
      rw [h1, hK'2]
  have hcent : ∀ (J : Subgroup Y) (y : Y), y ∈ Subgroup.centralizer (J : Set Y) ↔
      ∀ w ∈ J.map ρ, ρ y * w = w * ρ y := by
    intro J y
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · rintro hy _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul, hy w hw]
    · intro hy w hw
      apply hρ.inj
      rw [map_mul, map_mul]
      exact (hy (ρ w) (Subgroup.mem_map_of_mem ρ hw)).symm
  have hrange : (Subgroup.centralizer (K' : Set Y)).map ρ = psiHom.range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine (mem_range_psiHom_iff _).1 ⟨hinner y, ?_⟩
      rw [← hK'2]
      exact (hcent K' y).1 hy
    · intro hx
      obtain ⟨hxin, hxc⟩ := (mem_range_psiHom_iff x).2 hx
      obtain ⟨y, rfl⟩ := hρ.surj x hxin
      refine ⟨y, (hcent K' y).2 ?_, rfl⟩
      rw [hK'2]
      exact hxc
  let e : ↥(Subgroup.centralizer (K' : Set Y)) ≃* SL(2, ZMod 3) :=
    ((Subgroup.equivMapOfInjective _ ρ hρ.inj).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective psiHom_injective).symm
  have hsl : Nonempty (↥(Subgroup.centralizer (K' : Set Y)) ⧸
      classicalInvolutionOddCore ↥(Subgroup.centralizer (K' : Set Y)) ≃* SL(2, ZMod 3)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (oddCore_eq_bot_of_mulEquiv e)).trans
      (QuotientGroup.quotientBot.trans e)⟩
  have hcomm : Commutes (Subgroup.centralizer (K' : Set Y))
      (Subgroup.centralizer ((K : Subgroup Y) : Set Y)) := by
    intro x hx y hy
    have hx' : ρ x ∈ Inn ∧ ∀ w ∈ quat2, ρ x * w = w * ρ x :=
      ⟨hinner x, by rw [← hK'2]; exact (hcent K' x).1 hx⟩
    have hy' : ρ y ∈ Inn ∧ ∀ w ∈ quat1, ρ y * w = w * ρ y :=
      ⟨hinner y, by rw [← hK]; exact (hcent K y).1 hy⟩
    apply hρ.inj
    rw [map_mul, map_mul]
    exact (commute_of_cent hy' hx').symm
  exact longFundSetE3_of_two_twins h hK2 hK'tw hne hV hsl hcomm

theorem longFundSetE3_of_emb (h : PerpHypS n Y R S t) {ρ : Y →* MulAut P43} (hρ : Emb ρ)
    (ht : ρ t = tz) : LongFundSetE3 R t := by
  have hK2 : IsPGroup 2 ↥(tightCore R) :=
    isPGroup_core_of_oddCore_centralizer h (oddCoreIn_eq_bot hρ ht)
  obtain ⟨p, q, hpq, hp2, hK⟩ := exists_pair_core h hK2
  have hpq' : IsQ8Pair (ρ p) (ρ q) := hpq.map ρ hρ.inj
  have hp2' : ρ p ^ 2 = tz := by rw [← map_pow, hp2, ht]
  have hmap : (tightCore R).map ρ = Subgroup.closure ({ρ p, ρ q} : Set (MulAut P43)) := by
    rw [hK, MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton]
  rcases q8_dichotomy hpq' hp2' with ⟨c, hc, hv⟩ | ⟨d, hdt, hd⟩
  · rw [← hmap] at hv
    exact (false_of_viol h hK2 hρ ht hc hv).elim
  · refine longFundSetE3_of_quat1 h hK2 (hρ.conj d) ?_ ?_
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, ht, hdt, mul_inv_cancel_right]
    · rw [← Subgroup.map_map, hmap, hd]

theorem longFundSetE3_u43 (h : PerpHypS n Y R S t)
    (hF : CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSU 4 3 1) : LongFundSetE3 R t := by
  haveI := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psu hF
  have hu : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  have htL : t ∈ genFittingFStar Y := M2.twin_mem_of_noQ8Outer h hC
    (Q5U4.noQ8Outer_statedPSU hu (by norm_num) |> fun hO => noQ8Outer_of_mulEquiv e hO)
  obtain ⟨eP⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.exists_mulEquiv_P43 hF
  obtain ⟨ρ, hρ⟩ := exists_emb hC eP
  have hti : ρ t ∈ Inn := (hρ.mem_iff t).2 htL
  have hto : orderOf (ρ t) = 2 := by
    rw [orderOf_injective ρ hρ.inj]
    exact h.core.datum.order
  obtain ⟨d, hd⟩ := exists_conj_tz hti hto
  refine longFundSetE3_of_emb h (hρ.conj d) ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact hd

theorem leaf_u43 {n : ℕ} : TwinLeafS n (fun F _ => CFSG.Blueprint.LieModel F .PSU 4 3 1) :=
  fun _ _ _ _ _ _ h _ hF => longFundSetE3_u43 h hF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.U43
