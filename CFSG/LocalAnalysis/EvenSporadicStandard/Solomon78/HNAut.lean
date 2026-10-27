module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.AutModelRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.Sporadic.HNOddCore.FusB
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.Sporadic.HNOddCore.ThreeInvol
public import CFSG.Sporadic.HNOddCore.Fusion
public import CFSG.Sporadic.HNSchreier.FullAut
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public noncomputable section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNOddCore
  CFSG.Sporadic.SmallOddCore CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 100000 in
theorem swap01_comm_sig2 : Equiv.swap (0 : Fin 12) 1 * sig2 = sig2 * Equiv.swap 0 1 := by
  unfold sig2
  decide

theorem swap01_comm_sig4 : Equiv.swap (0 : Fin 12) 1 * sig4 = sig4 * Equiv.swap 0 1 := by
  unfold sig4
  ext i
  fin_cases i <;> rfl

theorem sig2_comm_sig4 : sig2 * sig4 = sig4 * sig2 := by
  unfold sig2 sig4
  ext i
  fin_cases i <;> rfl

section HN

abbrev hnP : Subgroup RH := jR.range

theorem hn_autModel : AutModel hnP (⊤ : Subgroup RH) where
  le := le_top
  conj_mem := fun x _ p hp => range_jR_normal.conj_mem p hp x
  surj := by
    intro α
    let e : JH ≃* hnP := MonoidHom.ofInjective jR_injective
    let α' : MulAut JH := (e.trans α).trans e.symm
    obtain ⟨r, hr⟩ := conjR_surjective α'
    refine ⟨r, mem_top r, fun p => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g : JH, e g = p := e.surjective p
    have h1 : ((α (e g) : hnP) : RH) = jR (α' g) := by
      have : e (α' g) = α (e g) := by
        show e (e.symm (α (e g))) = α (e g)
        exact e.apply_symm_apply _
      rw [← this]
      rfl
    rw [h1]
    apply Subtype.ext
    have h2 := congrArg (fun φ : MulAut JH => (φ g : GL (Fin hnsData.d) (ZMod 5))) hr
    simp only [conjR_apply] at h2
    have h3 : ((e g : hnP) : RH) = jR g := rfl
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h3, jR_val, jR_val, ← h2]
  inj := by
    intro x _ hx
    apply Subtype.ext
    refine eq_one_of_centralizes x.2 fun g hg => ?_
    have h := hx (jR ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩
    have := congrArg Subtype.val h
    simpa [jR_val] using this

theorem thetaR_t1V_eq : thetaR t1V = Equiv.swap 0 1 := thetaR_cR

theorem thetaR_t2V_eq : thetaR t2V = sig2 := (thetaR_jR t2H.2).trans thetaJ_t2H

theorem thetaR_t4V_eq : thetaR t4V = sig4 := (thetaR_jR t4H.2).trans thetaJ_t4H

theorem comm_of_thetaR {x y : RV} (h : thetaR x * thetaR y = thetaR y * thetaR x) :
    (x : RH) * y = y * x := by
  have h1 : x * y = y * x := thetaR.injective (by rw [map_mul, map_mul]; exact h)
  have h2 := congrArg Subtype.val h1
  rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h2

theorem cR_comm_t2 : cR * jR t2J = jR t2J * cR := by
  exact comm_of_thetaR (x := t1V) (y := t2V) (by
    rw [thetaR_t1V_eq, thetaR_t2V_eq]
    exact swap01_comm_sig2)

theorem cR_comm_t4 : cR * jR t4J = jR t4J * cR := by
  exact comm_of_thetaR (x := t1V) (y := t4V) (by
    rw [thetaR_t1V_eq, thetaR_t4V_eq]
    exact swap01_comm_sig4)

theorem t2_comm_t4 : jR t2J * jR t4J = jR t4J * jR t2J := by
  exact comm_of_thetaR (x := t2V) (y := t4V) (by
    rw [thetaR_t2V_eq, thetaR_t4V_eq]
    exact sig2_comm_sig4)

theorem jR_t2J_sq : (jR t2J) ^ 2 = 1 := by rw [← map_pow, t2J_sq, map_one]

theorem jR_t4J_sq : (jR t4J) ^ 2 = 1 := by rw [← map_pow, t4J_sq', map_one]

theorem jR_t2J_ne_one : jR t2J ≠ 1 := fun h =>
  t2J_ne_one (jR_injective (h.trans (map_one jR).symm))

theorem jR_t4J_ne_one : jR t4J ≠ 1 := fun h =>
  t4J_ne_one (jR_injective (h.trans (map_one jR).symm))

theorem hn_cover_P : ∀ u ∈ hnP, orderOf u = 2 →
    ∃ r ∈ [jR t2J, jR t4J], ∃ c ∈ hnP, u = c * r * c⁻¹ := by
  intro u hu hu2
  have hu_sq : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  obtain ⟨g, rfl⟩ := hu
  rcases involution_cover_R hu_sq hu1 with h | h | h
  · exact absurd h (not_isConj_c_jR g)
  · obtain ⟨g', hg'⟩ := exists_J_conj jR_t2J_sq jR_t2J_ne_one h
    exact ⟨jR t2J, by simp, jR g', ⟨g', rfl⟩, hg'.symm⟩
  · obtain ⟨g', hg'⟩ := exists_J_conj jR_t4J_sq jR_t4J_ne_one h
    exact ⟨jR t4J, by simp, jR g', ⟨g', rfl⟩, hg'.symm⟩

theorem hn_cover_R : ∀ w ∈ (⊤ : Subgroup RH), orderOf w = 2 →
    ∃ r ∈ [cR, jR t2J, jR t4J], ∃ c ∈ (⊤ : Subgroup RH), w = c * r * c⁻¹ := by
  intro w _ hw2
  have hw_sq : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  rcases involution_cover_R hw_sq hw1 with h | h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact ⟨cR, by simp, c, mem_top c, hc.symm⟩
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact ⟨jR t2J, by simp, c, mem_top c, hc.symm⟩
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact ⟨jR t4J, by simp, c, mem_top c, hc.symm⟩

theorem hn_fuse : ∀ r ∈ [jR t2J, jR t4J], ∀ c ∈ (⊤ : Subgroup RH),
    ∃ g ∈ hnP, c * r * c⁻¹ = g * r * g⁻¹ := by
  intro r hr c _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain ⟨g, hg⟩ := exists_J_conj jR_t2J_sq jR_t2J_ne_one (isConj_iff.2 ⟨c, rfl⟩)
    exact ⟨jR g, ⟨g, rfl⟩, hg.symm⟩
  · obtain ⟨g, hg⟩ := exists_J_conj jR_t4J_sq jR_t4J_ne_one (isConj_iff.2 ⟨c, rfl⟩)
    exact ⟨jR g, ⟨g, rfl⟩, hg.symm⟩

theorem hn_wit : ∀ r ∈ [jR t2J, jR t4J], ∀ r' ∈ [cR, jR t2J, jR t4J],
    ∃ h ∈ hnP, (h * r * h⁻¹) * r' = r' * (h * r * h⁻¹) := by
  intro r hr r' hr'
  refine ⟨1, one_mem _, ?_⟩
  simp only [inv_one, one_mul, mul_one]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl | rfl
  · exact cR_comm_t2.symm
  · rfl
  · exact t2_comm_t4
  · exact cR_comm_t4.symm
  · exact t2_comm_t4.symm
  · rfl

theorem hn_umovesCond_P : UMovesCond ↥hnP :=
  AutModel.umovesCond hn_autModel fun u hu hu2 w hw hww =>
    exists_commuting_conj_of_cover (P := hnP) (R := ⊤) [jR t2J, jR t4J] [cR, jR t2J, jR t4J]
      hn_cover_P hn_cover_R hn_fuse hn_wit le_top u hu hu2 w hw hww

abbrev hnC (w : RH) : Subgroup JH := CFSG.Sporadic.HNOddCore.CJ w

theorem mem_hnC (w : RH) (y : JH) : y ∈ hnC w ↔ jR y * w = w * jR y :=
  CFSG.Sporadic.HNOddCore.mem_CJ

theorem hn_outer_equiv (w : RH) (hwP : w ∉ hnP) (hww : w * w = 1) :
    Nonempty (hnC w ≃* Equiv.Perm (Fin 10)) := by
  have hw1 : w ≠ 1 := fun h => hwP (h ▸ one_mem _)
  have hw2 : w ^ 2 = 1 := by rw [pow_two]; exact hww
  obtain ⟨g, hg⟩ := fuse_t1R w hw2 hw1 hwP
  obtain ⟨e1⟩ := sub_centralizer_conj_equiv jR g t1R (hnC w) (hnC t1R)
    (fun j => by rw [mem_hnC, hg]) (fun j => mem_hnC t1R j)
  obtain ⟨e2⟩ := ctuc_hn_three_involution_centralizers_exact.2.2.1
  exact ⟨e1.trans e2⟩

theorem hn_card_hnC (w : RH) (hwP : w ∉ hnP) (hww : w * w = 1) :
    Nat.card (hnC w) = 3628800 := by
  obtain ⟨e⟩ := hn_outer_equiv w hwP hww
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem hn_card_centralizer_ge (a : JH) (ha : orderOf (jR a) = 2) :
    3686400 ≤ Nat.card (centralizer ({a} : Set JH)) := by
  have ha2 : a ^ 2 = 1 := by
    apply jR_injective
    rw [map_pow, map_one, ← ha]
    exact pow_orderOf_eq_one _
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ha
    exact absurd ha (by norm_num)
  obtain ⟨r, hr, c, ⟨g, rfl⟩, hc⟩ := hn_cover_P (jR a) ⟨a, rfl⟩ ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have key : ∀ t : JH, jR a = jR g * jR t * (jR g)⁻¹ → IsConj t a := by
    intro t h
    refine isConj_iff.2 ⟨g, jR_injective ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact h.symm
  rcases hr with rfl | rfl
  · have h := card_centralizer_of_isConj (key t2J hc)
    rw [card_CJ_t2] at h
    omega
  · have h := card_centralizer_of_isConj (key t4J hc)
    rw [card_CJ_t4] at h
    omega

theorem hn_outerLe : ∀ a ∈ hnP, orderOf a = 2 → ∀ w ∈ (⊤ : Subgroup RH), w ∉ hnP → w * w = 1 →
    ¬ ∀ y ∈ hnP, y * a = a * y → y * w = w * y := by
  intro a ha ha2 w _ hwP hww hall
  obtain ⟨a', rfl⟩ := ha
  have hle : centralizer ({a'} : Set JH) ≤ hnC w := by
    intro y hy
    rw [mem_hnC]
    refine hall (jR y) ⟨y, rfl⟩ ?_
    have := mem_centralizer_singleton_iff.1 hy
    rw [← map_mul, ← map_mul]
    exact congrArg jR this
  have h1 := Subgroup.card_le_of_le hle
  rw [hn_card_hnC w hwP hww] at h1
  have h2 := hn_card_centralizer_ge a' ha2
  omega

theorem hn_outerCentre (w : RH) (hwP : w ∉ hnP) (hww : w * w = 1) (z : RH) (hz : z ∈ hnP)
    (hz2 : orderOf z = 2) (hall : ∀ y ∈ hnP, y * w = w * y → y * z = z * y)
    (hzw : z * w = w * z) : False := by
  obtain ⟨z', rfl⟩ := hz
  obtain ⟨e⟩ := hn_outer_equiv w hwP hww
  have hz'mem : z' ∈ hnC w := (mem_hnC w z').2 hzw
  have hcomm : ∀ y : Equiv.Perm (Fin 10), e ⟨z', hz'mem⟩ * y = y * e ⟨z', hz'mem⟩ := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hxz : (⟨z', hz'mem⟩ : hnC w) * x = x * ⟨z', hz'mem⟩ := by
      apply Subtype.ext
      show z' * (x : JH) = (x : JH) * z'
      have hx := (mem_hnC w x).1 x.2
      have := hall (jR x) ⟨x, rfl⟩ hx
      apply jR_injective
      rw [map_mul, map_mul]
      exact this.symm
    have := congrArg e hxz
    rwa [map_mul, map_mul] at this
  have h1 := CFSG.perm_eq_one_of_forall_commute (by simp) hcomm
  have h2 : (⟨z', hz'mem⟩ : hnC w) = 1 := e.injective (h1.trans (map_one e).symm)
  have h3 : z' = 1 := congrArg Subtype.val h2
  rw [h3, map_one, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem hn_index : ∀ x ∈ (⊤ : Subgroup RH), x ∉ hnP → ∀ y ∈ (⊤ : Subgroup RH), y ∉ hnP →
    x⁻¹ * y ∈ hnP := by
  intro x _ hx y _ hy
  rcases exists_jR_or x with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact absurd ⟨g, rfl⟩ hx
  rcases exists_jR_or y with ⟨g', rfl⟩ | ⟨g', rfl⟩
  · exact absurd ⟨g', rfl⟩ hy
  refine ⟨conjC (g⁻¹ * g'), ?_⟩
  rw [← cR_conj_jR (g⁻¹ * g'), cR_inv, mul_inv_rev, cR_inv, map_mul, map_inv]
  group

theorem hn_autRowData (hci : CenterInvolutions JH) : AutRowData hnP (⊤ : Subgroup RH) where
  model := hn_autModel
  index := hn_index
  centerInv := CenterInvolutions.subgroup (MonoidHom.ofInjective jR_injective).symm hci
  outerLe := hn_outerLe

theorem hn_autCenterCond_P (hci : CenterInvolutions JH) : AutCenterCond ↥hnP :=
  AutCenterCondExc.toCond ((hn_autRowData hci).autCenterCondExc
    fun _ w _ hwP _ hww z hz hz2 hzw hall => (hn_outerCentre w hwP hww z hz hz2 hall hzw).elim)

theorem hn_equiv_P {Y : Type} [Group Y] (h : IsSporadic Y .HN) : Nonempty (Y ≃* ↥hnP) := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.HN := e
  exact ⟨(e'.trans hnEquivJ).trans (MonoidHom.ofInjective jR_injective)⟩

theorem hn_autCenterCond (hci : CenterInvolutions JH) {Y : Type}
    [Group Y] (h : IsSporadic Y .HN) : AutCenterCond Y := by
  obtain ⟨e⟩ := hn_equiv_P h
  exact @AutCenterCond.of_mulEquiv ↥hnP Y _ _ e.symm (hn_autCenterCond_P hci)

theorem hn_umovesCond {Y : Type} [Group Y] (h : IsSporadic Y .HN) : UMovesCond Y := by
  obtain ⟨e⟩ := hn_equiv_P h
  exact @UMovesCond.of_mulEquiv ↥hnP Y _ _ e.symm hn_umovesCond_P

end HN

end CFSG.EvenSporadicStandard.Solomon78
