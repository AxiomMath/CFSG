module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLift
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldCoverBLift
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (F4Work SwapComponentData oddCoreLift HasBLift)

section Generic

variable {H : Type} [Group H] [Finite H]

theorem swapLift_decomposition_of_cover {t : H} (ht : t * t = 1)
    (hC : ∀ c ∈ oddCore H, c * t = t * c → c ∈ center H)
    {Kb Db : Subgroup (H ⧸ oddCore H)}
    (h : SwapComponentData (QuotientGroup.mk' (oddCore H) t) Kb Db)
    (hOut : Group.IsSolvable (Outer Kb)) :
    (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom ≤ centralizer (oddCoreLift Kb : Set H) ∧
      oddCoreLift Kb ⊓ (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom ≤ oddCore H ∧
      oddCoreLift Kb ⊔ (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom =
        perfectCore (⊤ : Subgroup H) ∧
      ⁅oddCoreLift Kb, oddCoreLift Kb⁆ = oddCoreLift Kb := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set τ := π t with hτ
  set Kh := oddCoreLift Kb with hKh
  have hO := F4Pilot.oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  have hKp : ⁅Kb, Kb⁆ = Kb := isPerfect_iff.mp h.isComponent.1.1
  have hKτp : ⁅Kb.map (MulAut.conj τ).toMonoidHom, Kb.map (MulAut.conj τ).toMonoidHom⁆ =
      Kb.map (MulAut.conj τ).toMonoidHom := by
    rw [← map_commutator, hKp]
  obtain ⟨hBsup, hBK⟩ := F4Pilot.hasBLift_sup_conj_of_le_center ht hKp h.commute hC
  have hKt : Kh.map (MulAut.conj t).toMonoidHom =
      oddCoreLift (Kb.map (MulAut.conj τ).toMonoidHom) :=
    F4Pilot.map_conj_oddCoreLift Kb t
  have hKhp : ⁅Kh, Kh⁆ = Kh := F4Pilot.commutator_oddCoreLift Kb
  have hKhtp : ⁅Kh.map (MulAut.conj t).toMonoidHom, Kh.map (MulAut.conj t).toMonoidHom⁆ =
      Kh.map (MulAut.conj t).toMonoidHom := by
    rw [← map_commutator, hKhp]
  have hπK : Kh.map π = Kb := F4Pilot.map_oddCoreLift hKp
  have hπKt : (Kh.map (MulAut.conj t).toMonoidHom).map π =
      Kb.map (MulAut.conj τ).toMonoidHom := by
    rw [hKt]
    exact F4Pilot.map_oddCoreLift hKτp
  have hOK : oddCore H ≤ centralizer (Kh : Set H) := le_centralizer_iff.1 hBK
  have hcomm : ⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    apply CFSG.LocalCores.perfect_double_commutator (isPerfect_iff.mpr hKhp)
    have h1 : ⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆ ≤ oddCore H := by
      have h2 : (⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆).map π = ⊥ := by
        rw [map_commutator, hπK, hπKt]
        exact h.commute
      have h3 := (Subgroup.map_eq_bot_iff _).1 h2
      rwa [hπ, QuotientGroup.ker_mk'] at h3
    exact commutator_eq_bot_iff_le_centralizer.2 (h1.trans hOK)
  have hdisj : Kh ⊓ Kh.map (MulAut.conj t).toMonoidHom ≤ oddCore H := by
    rintro x ⟨hx, hxt⟩
    have h1 : π x ∈ Kb ⊓ Kb.map (MulAut.conj τ).toMonoidHom :=
      ⟨hπK ▸ mem_map_of_mem π hx, hπKt ▸ mem_map_of_mem π hxt⟩
    rw [h.inf_eq_bot hO, mem_bot] at h1
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hle : Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom ≤ perfectCore (⊤ : Subgroup H) :=
    sup_le (CFSG.Quasithin.le_perfectCore_of_perfect le_top hKhp)
      (CFSG.Quasithin.le_perfectCore_of_perfect le_top hKhtp)
  have hsup : Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom = perfectCore (⊤ : Subgroup H) := by
    refine le_antisymm hle ?_
    have hPp := CFSG.Quasithin.perfectCore_perfect (⊤ : Subgroup H)
    have hPmap : (perfectCore (⊤ : Subgroup H)).map π ≤
        Kb ⊔ Kb.map (MulAut.conj τ).toMonoidHom := by
      rw [CFSG.Quasithin.map_perfectCore, map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
      exact h.perfectCore_top_le hO hOut
    have hPO : perfectCore (⊤ : Subgroup H) ≤ centralizer (oddCore H : Set H) :=
      (F4Pilot.le_oddCoreLift_of_perfect hPp hPmap).trans hBsup
    refine F4Pilot.perfect_le_of_forall_exists_commute hPp hle fun a ha => ?_
    have hπa : π a ∈ (Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom).map π := by
      rw [Subgroup.map_sup, hπK, hπKt]
      exact hPmap (mem_map_of_mem π ha)
    obtain ⟨m, hm, hma⟩ := hπa
    refine ⟨m, hm, m⁻¹ * a, by group, fun b hb => ?_⟩
    have hz : m⁻¹ * a ∈ oddCore H := by
      have h2 : π (m⁻¹ * a) = 1 := by rw [map_mul, map_inv, hma, inv_mul_cancel]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact mem_centralizer_iff.1 (hPO hb) _ hz
  exact ⟨le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm), hdisj, hsup, hKhp⟩

end Generic

section Root


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

omit
  [Finite G] in
theorem neighbourCore_high_eq_perfectCore_rootTorusG (e : L ≃* adjointGroup .E6 K) :
    neighbourCore e .high = perfectCore (centralizer (rootTorusG e : Set G)) := by
  rw [neighbourCore_high]
  rfl

theorem exists_swapDecomposition_high {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .E6 K) (hk : RootSwapKind e t) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Odd (Nat.card (Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom : Subgroup G)) ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e .high ∧ ⁅Kc, Kc⁆ = Kc ∧
      ∀ s ∈ centralizer (rootTorusG e : Set G), Odd (orderOf s) →
        s ∈ normalizer (Kc : Set G) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  set X : Subgroup G := rootTorusG e with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := rootLeviG e with hDdef
  obtain ⟨htX, Kb, hKb, hDK, hne, hcomm, ⟨eK⟩⟩ := hk
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hTodd : Odd (Nat.card ((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (highTorusLine_le_adjointGroup (Or.inl rfl))).toEquiv]
    exact odd_card_highTorusLine hw.one_le hw.card_eq
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_E6_of_centralizer_eq_sup hw.standard.standard htC
    hw.orderOf_eq hw.inf_eq hf hw.card_eq e (centralizer_highTorusLine_eq (Or.inl rfl) hq)
    highTorusLine_subgroupOf_le_centralizer_perpLevi highTorusLine_subgroupOf_le_centralizer_self
    hTodd (X := X) rfl htX (D := D) rfl
  have hDH : D ≤ H :=
    F4Pilot.map_map_symm_le_centralizer e highTorusLine_subgroupOf_le_centralizer_perpLevi
  have hDL : D ≤ L := map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hτD : π t' ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData (π t') Kb Db :=
    ⟨by rw [← map_mul, ht't', map_one], hKb, hne, hcomm, hDK, hτD, hsyl⟩
  have hO := F4Pilot.oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  have hC := mem_center_of_mem_oddCore_of_commute_rootTorusG hw hf e htX
  have hZ : center Kb = ⊥ := hdata.center_eq_bot hO
  let eKD : Kb ≃* Db :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eK
  let eD' : a5Levi K ≃* D.subgroupOf H := (a5LeviMapEquiv e).trans (subgroupOfEquivOfLe hDH).symm
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv eD' isQuasisimple_open_a5Levi
  have hD'Z : center (D.subgroupOf H) = ⊥ := F4Pilot.center_eq_bot_congr eD' center_a5Levi_eq_bot
  let eDb : D.subgroupOf H ≃* Db :=
    F4Pilot.mapMkEquivOfInfEqBot (oddCore H) (D.subgroupOf H) (F4Pilot.inf_oddCore_eq_bot hD'q hD'Z)
  let eKC : Kb ≃* a5Levi K := eKD.trans (eDb.symm.trans eD'.symm)
  have hOut := (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eKC).2.2
    (isSolvable_outer_a5Levi (K := K))
  obtain ⟨hcH, hdH, hsH, hpH⟩ := swapLift_decomposition_of_cover ht't' hC hdata hOut
  set Kh := oddCoreLift Kb with hKhdef
  have hKct : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      (Kh.map (MulAut.conj t').toMonoidHom).map H.subtype :=
    (F4Pilot.map_subtype_map_conj Kh t').symm
  have hc1 : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((Kh.map H.subtype : Subgroup G) : Set G) := by
    rw [hKct]
    exact F4Pilot.map_le_centralizer_map H.subtype hcH
  have hd1 : Odd (Nat.card (Kh.map H.subtype ⊓ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom :
      Subgroup G)) := by
    rw [hKct, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective,
      card_map_of_injective H.subtype_injective]
    exact (CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := H)).of_dvd_nat
      (card_dvd_of_le hdH)
  have he1 : Kh.map H.subtype ⊔ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      neighbourCore e .high := by
    rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype, neighbourCore_high_eq_perfectCore_rootTorusG]
  refine ⟨Kh.map H.subtype, hc1, hd1, he1, by rw [← map_commutator, hpH], fun s hs hso => ?_⟩
  obtain ⟨σ, hσ⟩ := hdata.exists_sign
  set s' : H := ⟨s, hs⟩ with hs'def
  have hs'o : Odd (orderOf s') := by rw [← Subgroup.orderOf_coe]; exact hso
  have h2 : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have hσ1 : σ (π s') = 1 := by
    obtain ⟨k, hk⟩ := hs'o
    have h1 : σ (π s') ^ (2 * k + 1) = 1 := by
      rw [← map_pow, ← map_pow, ← hk, pow_orderOf_eq_one, map_one, map_one]
    rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h1
    exact h1
  have hKs := F4Pilot.mem_normalizer_oddCoreLift Kb (hσ _ hσ1)
  rw [mem_normalizer_iff_map_conj_eq] at hKs ⊢
  calc (Kh.map H.subtype).map (MulAut.conj s).toMonoidHom =
      (Kh.map (MulAut.conj s').toMonoidHom).map H.subtype :=
        (F4Pilot.map_subtype_map_conj Kh s').symm
    _ = Kh.map H.subtype := congrArg (Subgroup.map H.subtype) hKs

end Root

end CFSG.SeitzReduction.E6Pilot
