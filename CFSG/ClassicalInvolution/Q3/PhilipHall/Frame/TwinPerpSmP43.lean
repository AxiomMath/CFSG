module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmP43Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
public import CFSG.ClassicalInvolution.Q3.TL3Ident
public import CFSG.ClassicalInvolution.Q3.TL3Lift
public import Certificates.Certificate397501
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerpCentral
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallM2
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916Coh
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S1916Inv
public import CFSG.ClassicalInvolution.AschTight.S19QT68
public import CFSG.ClassicalInvolution.AschTight.S19QTInv
public import CFSG.ClassicalInvolution.AschTight.S19QTSign
public import CFSG.ClassicalInvolution.AschTight.S19TF1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LargeFrameExits
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Sq
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.TA3SOLCore
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreRank
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4TwistTw
public import CFSG.ClassicalInvolution.SmallCases.A7T22Setup
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Lift
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.Foundations
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.RestSetup
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.P43

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Check Certificates.P43Twin
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

open scoped MatrixGroups

set_option linter.unusedSectionVars false

local notation "P45" => Equiv.Perm (Fin 45)

section SL2


theorem sl2_of_card {Y : Type} [Group Y] [Finite Y] {J K : Subgroup Y} (hJ : Nat.card J = 24)
    (hKJ : K ≤ J) (eK : Nonempty (↥K ≃* QuaternionGroup 2)) {x r : Y} (hx : x ∈ J) (hr : r ∈ J)
    (hx3 : x ^ 3 = 1) (hxr : orderOf (x * r * x⁻¹ * r⁻¹) = 4) :
    Nonempty (↥J ⧸ classicalInvolutionOddCore ↥J ≃* SL(2, ZMod 3)) := by
  obtain ⟨eK⟩ := eK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥J :=
    CFSG.GH74.KGroups.isSolvable_of_two_primes (by rw [hJ]; decide +kernel)
  have hKcard : Nat.card ↥(K.subgroupOf J) = 2 ^ (Nat.card ↥J).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv, Nat.card_congr eK.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card, hJ]
    decide +kernel
  let P : Sylow 2 ↥J := Sylow.ofCard (K.subgroupOf J) hKcard
  let φ : ↥J ≃* ↥(⊤ : Subgroup ↥J) := Subgroup.topEquiv.symm
  let T : Sylow 2 ↥(⊤ : Subgroup ↥J) := P.mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hT : Nonempty ((T : Subgroup ↥(⊤ : Subgroup ↥J)) ≃* QuaternionGroup 2) := by
    have hTc : (T : Subgroup ↥(⊤ : Subgroup ↥J)) = (P : Subgroup ↥J).map φ.toMonoidHom :=
      Sylow.coe_mapSurjective φ.surjective P
    have hPc : (P : Subgroup ↥J) = K.subgroupOf J := Sylow.coe_ofCard _ _
    exact ⟨(MulEquiv.subgroupCongr hTc).trans ((MulEquiv.subgroupMap φ (P : Subgroup ↥J)).symm.trans
      ((MulEquiv.subgroupCongr hPc).trans ((Subgroup.subgroupOfEquivOfLe hKJ).trans eK)))⟩
  have hnot : ¬ IsPGroup 2 (↥J ⧸ oddCore ↥J) := by
    intro hP
    have hxo : (⟨x, hx⟩ : ↥J) ∈ oddCore ↥J :=
      mem_oddCore_of_isPGroup_quotient hP (k := 1) (Subtype.ext (by simpa using hx3))
    have hwo : (⟨x, hx⟩ : ↥J) * ⟨r, hr⟩ * (⟨x, hx⟩ : ↥J)⁻¹ * (⟨r, hr⟩ : ↥J)⁻¹ ∈ oddCore ↥J := by
      have h1 : (⟨r, hr⟩ : ↥J) * (⟨x, hx⟩ : ↥J)⁻¹ * (⟨r, hr⟩ : ↥J)⁻¹ ∈ oddCore ↥J :=
        (inferInstance : (oddCore ↥J).Normal).conj_mem _ ((oddCore ↥J).inv_mem hxo) ⟨r, hr⟩
      have h2 := (oddCore ↥J).mul_mem hxo h1
      have e : (⟨x, hx⟩ : ↥J) * ⟨r, hr⟩ * (⟨x, hx⟩ : ↥J)⁻¹ * (⟨r, hr⟩ : ↥J)⁻¹ =
          (⟨x, hx⟩ : ↥J) * ((⟨r, hr⟩ : ↥J) * (⟨x, hx⟩ : ↥J)⁻¹ * (⟨r, hr⟩ : ↥J)⁻¹) := by
        simp only [mul_assoc]
      rw [e]
      exact h2
    have hodd := (CFSG.ComponentClassification.OddCore.odd_card ↥J).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard (oddCore ↥J) hwo)
    have h4 : orderOf
        ((⟨x, hx⟩ : ↥J) * ⟨r, hr⟩ * (⟨x, hx⟩ : ↥J)⁻¹ * (⟨r, hr⟩ : ↥J)⁻¹) = 4 := by
      rw [← Subgroup.orderOf_coe]
      simpa using hxr
    rw [h4] at hodd
    exact absurd hodd (by decide)
  exact nonempty_mulEquiv_sl2Three_of_normal_odd_index (⊤ : Subgroup ↥J)
    (by rw [Subgroup.index_top]; decide) T hT hnot

end SL2


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

section Core

theorem core_eq_sylow (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) :
    tightCore R = (S : Subgroup R).map R.subtype :=
  h.core.datum.sylow_core.2.2 _ le_rfl hK2 h.core.datum.sylow_core.1

theorem core_q8 (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) :
    Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := h.core.q8
  exact ⟨(MulEquiv.subgroupCongr (core_eq_sylow h hK2)).trans
    ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e)⟩

theorem core_shape (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) :
    ∃ a b : Y, a * a = t ∧ b * b = t ∧ b * a = t * a * b ∧
      ∀ y, y ∈ tightCore R ↔ y ∈ q8List t a b := by
  obtain ⟨e⟩ := h.core.q8
  have hd := h.core.datum
  have hKS := core_eq_sylow h hK2
  let ι : (S : Subgroup R) →* Y := R.subtype.comp (S : Subgroup R).subtype
  have hιinj : Function.Injective ι :=
    R.subtype_injective.comp (S : Subgroup R).subtype_injective
  have hιK : ∀ s, ι s ∈ tightCore R := fun s => by
    rw [hKS]
    exact Subgroup.mem_map_of_mem _ s.2
  obtain ⟨i, hi⟩ : ∃ i : (S : Subgroup R), i = e.symm (QuaternionGroup.a 1) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : (S : Subgroup R), j = e.symm (QuaternionGroup.xa 0) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : (S : Subgroup R), z = e.symm (QuaternionGroup.a 2) := ⟨_, rfl⟩
  have hii : i * i = z := by
    rw [hi, hz, ← map_mul]
    congr 1
  have hjj : j * j = z := by
    rw [hj, hz, ← map_mul]
    congr 1
  have hji : j * i = z * i * j := by
    rw [hj, hi, hz, ← map_mul, ← map_mul, ← map_mul]
    congr 1
  have hzt : t = ι z := by
    obtain ⟨s, hs, hst⟩ := hd.mem
    have ht2 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [hd.order, pow_two] at this
    have ht1 : t ≠ 1 := fun h' => by
      have := hd.order
      rw [h', orderOf_one] at this
      omega
    set s' : (S : Subgroup R) := ⟨s, hs⟩ with hs'
    have hts : ι s' = t := hst
    have hs2 : s' * s' = 1 := by
      apply hιinj
      rw [map_mul, hts, ht2, map_one]
    have hs1 : s' ≠ 1 := fun h' => ht1 (by rw [← hts, h', map_one])
    have hw := TA3.q8_eq_of_sq_eq_one (w := e s') (by rw [← map_mul, hs2, map_one])
      (fun h' => hs1 (e.injective (by rw [h', map_one])))
    have : s' = z := by
      rw [hz, ← hw, MulEquiv.symm_apply_apply]
    rw [← hts, this]
  refine ⟨ι i, ι j, by rw [← map_mul, hii, ← hzt], by rw [← map_mul, hjj, ← hzt], ?_,
    fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [hzt]
    simp only [← map_mul]
    exact congrArg ι hji
  · rw [hKS] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    set s : (S : Subgroup R) := ⟨r, hr⟩ with hs
    have hrs : R.subtype r = ι s := rfl
    rw [hrs]
    have hsw : s = e.symm (e s) := (MulEquiv.symm_apply_apply e s).symm
    rcases TA3.q8_cases (e s) with h' | h' | h' | h' | h' | h' | h' | h'
    · have : s = 1 := by rw [hsw, h', ← QuaternionGroup.one_def, map_one]
      rw [this, map_one]
      simp [q8List]
    · have : s = i := by rw [hsw, h', hi]
      rw [this]
      simp [q8List]
    · have : s = z := by rw [hsw, h', hz]
      rw [this, ← hzt]
      simp [q8List]
    · have : s = z * i := by
        rw [hsw, h', hz, hi, ← map_mul]
        congr 1
      rw [this, map_mul, ← hzt]
      simp [q8List]
    · have : s = j := by rw [hsw, h', hj]
      rw [this]
      simp [q8List]
    · have : s = j * i := by
        rw [hsw, h', hj, hi, ← map_mul]
        congr 1
      rw [this, map_mul]
      simp [q8List]
    · have : s = j * z := by
        rw [hsw, h', hj, hz, ← map_mul]
        congr 1
      rw [this, map_mul, ← hzt]
      simp [q8List]
    · have : s = j * (z * i) := by
        rw [hsw, h', hj, hz, hi, ← map_mul, ← map_mul]
        congr 1
      rw [this, map_mul, map_mul, ← hzt]
      simp [q8List]
  · have ha : ι i ∈ tightCore R := hιK i
    have hb : ι j ∈ tightCore R := hιK j
    have ht : t ∈ tightCore R := hzt ▸ hιK z
    simp only [q8List, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ha
    · exact ht
    · exact mul_mem ht ha
    · exact hb
    · exact mul_mem hb ha
    · exact mul_mem hb ht
    · exact mul_mem hb (mul_mem ht ha)

theorem core_ident (h : PerpHypS n Y R S t) {f : Y →* P45} (hf : Function.Injective f)
    {Lst : List P45} (hL : ∀ m, m ∈ Lst ↔ ∃ y, f y = m) (hloc : localChk Lst (f t) = true) :
    IsPGroup 2 ↥(tightCore R) ∧ f t = tA ∧
      ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
        (∀ y, y ∈ conjSub c (tightCore R) ↔ f y ∈ Q1) ∨
          (∀ y, y ∈ conjSub c (tightCore R) ↔ f y ∈ Q2) := by
  simp only [localChk, Bool.and_eq_true] at hloc
  obtain ⟨hodd, hpair⟩ := hloc
  have hno : NoOddNormalAt t := noOddNormalAt_of_noOddB hf hL hodd
  have hO : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    oddCoreImg_eq_bot hno le_rfl Subgroup.le_normalizer
  have hK2 : IsPGroup 2 ↥(tightCore R) := isPGroup_core_of_oddCore_centralizer h hO
  obtain ⟨a, b, haa, hbb, hba, hK⟩ := core_shape h hK2
  have hrep : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      pairOK (f t) (f (c * a * c⁻¹)) (f (c * b * c⁻¹)) = true ∧
        ∀ y, y ∈ conjSub c (tightCore R) ↔
          f y ∈ q8B (f t) (f (c * a * c⁻¹)) (f (c * b * c⁻¹)) := by
    intro c hc
    have hct : c * t * c⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      rw [hc]
      group
    refine ⟨pairOK_of_pairChk hf hL hpair ?_ ?_ ?_, fun y => ?_⟩
    · calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
        _ = t := by rw [haa, hct]
    · calc c * b * c⁻¹ * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
        _ = t := by rw [hbb, hct]
    · calc c * b * c⁻¹ * (c * a * c⁻¹) = c * (b * a) * c⁻¹ := by group
        _ = c * (t * a * b) * c⁻¹ := by rw [hba]
        _ = (c * t * c⁻¹) * (c * a * c⁻¹) * (c * b * c⁻¹) := by group
        _ = t * (c * a * c⁻¹) * (c * b * c⁻¹) := by rw [hct]
    · rw [mem_conjSub_iff, hK, ← mem_map_conj_iff, q8List_conj hct, mem_q8List_iff hf]
  have h1 := (hrep 1 (Subgroup.one_mem _)).1
  simp only [pairOK, Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨hK2, h1.1, fun c hc => ?_⟩
  obtain ⟨hok, hmem⟩ := hrep c hc
  simp only [pairOK, Bool.and_eq_true, Bool.or_eq_true] at hok
  rcases hok.2 with hQ | hQ
  · exact Or.inl fun y => (hmem y).trans (mem_iff_of_setEqB hQ _)
  · exact Or.inr fun y => (hmem y).trans (mem_iff_of_setEqB hQ _)

end Core

section Main


theorem final_of_reps (h : PerpHypS n Y R S t) {f : Y →* P45} (hf : Function.Injective f)
    (hL : ∀ m, m ∈ elemsT QP45 ↔ ∃ y, f y = m) (hK2 : IsPGroup 2 ↥(tightCore R)) {g : Y}
    (hg : g ∈ Subgroup.centralizer ({t} : Set Y))
    (hne : conjSub g (tightCore R) ≠ tightCore R)
    (hK'Ω : conjSub g (tightCore R) ∈ CoreAssembly.conjClass (tightCore R))
    (hz' : IsUniqueInvolution (conjSub g (tightCore R)) t) {Qa Qb : List P45}
    (hQa : ∀ q ∈ Qa, q ∈ elemsT QP45) (hQb : ∀ q ∈ Qb, q ∈ elemsT QP45)
    (hKa : ∀ y, y ∈ tightCore R ↔ f y ∈ Qa) (hKb : ∀ y, y ∈ conjSub g (tightCore R) ↔ f y ∈ Qb)
    (hV : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      (∀ y, y ∈ conjSub c (tightCore R) ↔ f y ∈ Qa) ∨
        (∀ y, y ∈ conjSub c (tightCore R) ↔ f y ∈ Qb))
    (h24 : (centQ (elemsT QP45) Qb).length = 24) {x r : P45} (hx : x ∈ centQ (elemsT QP45) Qb)
    (hr : r ∈ centQ (elemsT QP45) Qb) (hx3 : x ^ 3 = 1) (hxr : orderOf (x * r * x⁻¹ * r⁻¹) = 4)
    (hcomm : ∀ u ∈ centQ (elemsT QP45) Qb, ∀ v ∈ centQ (elemsT QP45) Qa, u * v = v * u) :
    LongFundSetE3 R t := by
  have hK'tw : conjSub g (tightCore R) ∈ twins R := ⟨hK'Ω, t, uniqueInv_core h, hz'⟩
  have hcK' := mem_centralizer_iff_centQ hf hL hKb hQb
  have hcK := mem_centralizer_iff_centQ hf hL hKa hQa
  refine longFundSetE3_of_two_twins h hK2 hK'tw hne ?_ ?_ ?_
  · intro J hJ
    obtain ⟨c, hc, rfl⟩ := exists_conj_of_mem_twins h hJ
    rcases hV c hc with h1 | h1
    · exact Or.inl (Subgroup.ext fun y => (h1 y).trans (hKa y).symm)
    · exact Or.inr (Subgroup.ext fun y => (h1 y).trans (hKb y).symm)
  · obtain ⟨x', rfl⟩ := (hL x).1 (mem_of_mem_centQ hx)
    obtain ⟨r', rfl⟩ := (hL r).1 (mem_of_mem_centQ hr)
    have hcard : Nat.card ↥(Subgroup.centralizer (conjSub g (tightCore R) : Set Y)) = 24 := by
      rw [card_centralizer_eq hf hL (nodup_elemsT QP45 QP45_ok) hKb hQb, h24]
    have hKle : tightCore R ≤ Subgroup.centralizer (conjSub g (tightCore R) : Set Y) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((twin_facts h hK2 hg hne).1 k hk y hy).symm
    refine sl2_of_card hcard hKle (core_q8 h hK2) ((hcK' x').2 hx) ((hcK' r').2 hr)
      (hf (by rw [map_pow, hx3, map_one])) ?_
    rw [← orderOf_injective f hf]
    simpa only [map_mul, map_inv] using hxr
  · intro u hu v hv
    exact hf (by rw [map_mul, map_mul]; exact hcomm _ ((hcK' u).1 hu) _ ((hcK v).1 hv))

theorem leaf_of_L0 (h : PerpHypS n Y R S t) {f : Y →* P45} (hf : Function.Injective f)
    (hL : ∀ m, m ∈ elemsT QP45 ↔ ∃ y, f y = m) (hloc : localChk (elemsT QP45) (f t) = true)
    (hsig : sigmaChk (elemsT QP45) = true) : LongFundSetE3 R t := by
  obtain ⟨hK2, -, hrep⟩ := core_ident h hf hL hloc
  obtain ⟨hQ, h24a, h24b, hx1, ha2, hx2, ha1, hx13, hx23, ho1, ho2, hcomm⟩ := sigma_parts hsig
  have hQ1 : ∀ q ∈ Q1, q ∈ elemsT QP45 := fun q hq => hQ q (List.mem_append_left _ hq)
  have hQ2 : ∀ q ∈ Q2, q ∈ elemsT QP45 := fun q hq => hQ q (List.mem_append_right _ hq)
  obtain ⟨g, hg, hne, hK'Ω, hz'⟩ := exists_twin h
  have hK := hrep 1 (Subgroup.one_mem _)
  rw [conjSub_one] at hK
  have hK' := hrep g hg
  rcases hK with hKa | hKa <;> rcases hK' with hKb | hKb
  · exact absurd (Subgroup.ext fun y => (hKb y).trans (hKa y).symm) hne
  · exact final_of_reps h hf hL hK2 hg hne hK'Ω hz' hQ1 hQ2 hKa hKb hrep h24b hx2 ha1 hx23 ho2
      (fun u hu v hv => (hcomm v hv u hu).symm)
  · exact final_of_reps h hf hL hK2 hg hne hK'Ω hz' hQ2 hQ1 hKa hKb (fun c hc => (hrep c hc).symm)
      h24a hx1 ha2 hx13 ho1 hcomm
  · exact absurd (Subgroup.ext fun y => (hKb y).trans (hKa y).symm) hne

theorem false_of_A (h : PerpHypS n Y R S t) {f : Y →* P45} (hf : Function.Injective f)
    (hL : ∀ m, m ∈ elemsT QA45 ↔ ∃ y, f y = m)
    (hN : ∀ y, y ∈ genFittingFStar Y ↔ f y ∈ QP45.originalSubgroup)
    (hloc : localChk (elemsT QA45) (f t) = true) (hsig : sigmaChk (elemsT QP45) = true)
    (hcard : Nat.card Y = 51840) : False := by
  obtain ⟨-, -, hrep⟩ := core_ident h hf hL hloc
  have hQ := (sigma_parts hsig).1
  have hKN : tightCore R ≤ genFittingFStar Y := by
    intro y hy
    have hy' : y ∈ conjSub 1 (tightCore R) := by rwa [conjSub_one]
    rw [hN, ← mem_elemsT QP45 QP45_ok]
    rcases hrep 1 (Subgroup.one_mem _) with h1 | h1
    · exact hQ _ (List.mem_append_left _ ((h1 y).1 hy'))
    · exact hQ _ (List.mem_append_right _ ((h1 y).1 hy'))
  have hNtop : genFittingFStar Y = ⊤ := by
    have hNn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
    rw [eq_top_iff, ← h.core.gen]
    refine iSup_le fun g => ?_
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 := hNn.conj_mem _ (hKN hx) g
    simpa [mul_assoc] using h1
  have hle : f.range ≤ QP45.originalSubgroup := by
    rintro _ ⟨y, rfl⟩
    exact (hN y).1 (hNtop ▸ Subgroup.mem_top y)
  have h1 := Subgroup.card_le_of_le hle
  rw [card_L0, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hcard] at h1
  omega

theorem leaf_psp43 {n : ℕ} : TwinLeafS n fun F _ => CFSG.Blueprint.LieModel F .PSp 2 3 1 := by
  intro Y _ _ R S t h _ hF
  haveI := h.core.simple
  haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  obtain ⟨hcovL, hlocL, hcovA, hlocA, hsig⟩ := check_parts Certificates.certificate397501
  obtain ⟨f₀, hf₀, hA, hN₀, hP⟩ := model_embedding h.core.nonab hF
  rcases range_cases hf₀ hA hP with ⟨-, hL⟩ | ⟨hcard, hL⟩
  · obtain ⟨f, hf, hL', -, hrep⟩ := normalize hf₀ hL hN₀ hcovL h.core.datum.order
    exact leaf_of_L0 h hf hL' (hlocL _ hrep) hsig
  · obtain ⟨f, hf, hL', hN, hrep⟩ := normalize hf₀ hL hN₀ hcovA h.core.datum.order
    exact (false_of_A h hf hL' hN (hlocA _ hrep) hsig hcard).elim

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.P43
