module

public import CFSG.GH74.GLS.C3.Layer1.Th2Pump
public import CFSG.GH74.GLS.C3.Layer1.St1RigMain
public import CFSG.GH74.GLS.C3.Layer1.St1Conj
public import CFSG.GH74.GLS.C3.Layer1.Th2A7
public import CFSG.GH74.GLS.IVK.Proofs2.LocalUnbalancing
import CFSG.Adapters.GeneralizedFitting
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.PumpTerm

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

theorem comp_le_centralizer_of_ne {H : Type} [Group H] [Finite H] {A B : Subgroup H}
    (hA : CFSG.IsComponent A) (hB : CFSG.IsComponent B) (hne : A ≠ B) :
    A ≤ Subgroup.centralizer (B : Set H) := by
  have hA' : CFSG.GorensteinWalter.IsComponentOf A ⊤ :=
    (CFSG.Adapters.isComponentOf_top_iff A).1 ((CFSG.isComponent_iff_open A).1 hA)
  have hB' : CFSG.GorensteinWalter.IsComponentOf B ⊤ :=
    (CFSG.Adapters.isComponentOf_top_iff B).1 ((CFSG.isComponent_iff_open B).1 hB)
  have := CFSG.GorensteinWalter.component_commute_of_ne hA' hB' hne
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_klein_cover {M Λ : Subgroup G} (hΛM : Λ ≤ M)
    (hcover : ∀ k ∈ M, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 M, k = l * o)
    (V : Subgroup (kBar M)) (hVsq : ∀ v ∈ V, v * v = 1) (hV4 : 4 ∣ Nat.card ↥V) :
    ∃ E : Subgroup G, E ≤ Λ ∧ (∀ e ∈ E, e * e = 1) ∧ 4 ∣ Nat.card ↥E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set YM : Subgroup ↥M := pPrimeCore 2 ↥M with hYM
  set Y : Subgroup G := pPrimeCoreOf 2 M with hY
  let ρ : ↥Λ →* kBar M := (QuotientGroup.mk' YM).comp (Subgroup.inclusion hΛM)
  have hρ : ∀ l : ↥Λ, ρ l = (QuotientGroup.mk (⟨(l : G), hΛM l.2⟩ : ↥M) : kBar M) := fun l => rfl
  have hρsurj : Function.Surjective ρ := by
    intro w
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨l, hl, o, ho, hk⟩ := hcover (k : G) k.2
    obtain ⟨o', ho', rfl⟩ := ho
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hρ]
    have h1 : (k : ↥M) = ⟨l, hΛM hl⟩ * o' := by
      apply Subtype.ext
      simpa using hk
    rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o').2 ho', mul_one]
  have hρker : ∀ l : ↥Λ, ρ l = 1 ↔ (l : G) ∈ Y := by
    intro l
    rw [hρ, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem M.subtype_injective).symm
  have hYcop : Nat.Coprime 2 (Nat.card ↥Y) := by
    have h1 : Nat.card ↥Y = Nat.card ↥YM := Subgroup.card_map_of_injective M.subtype_injective
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := ↥M)
  set EΛ : Subgroup ↥Λ := V.comap ρ with hEΛ
  set E : Subgroup G := EΛ.map Λ.subtype with hE
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨P, hPE, hPp, hPcard, -⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.exists_normalized_sylow_two E ⊥ hbot bot_le
  have hEΛ_le : E ≤ Λ := Subgroup.map_subtype_le _
  have h4E : 2 ^ 2 ∣ Nat.card ↥E := by
    have h1 : Nat.card ↥E = Nat.card ↥EΛ := Subgroup.card_map_of_injective Λ.subtype_injective
    have h2 : EΛ.map ρ = V := Subgroup.map_comap_eq_self_of_surjective hρsurj V
    have h3 : Nat.card ↥(EΛ.map ρ) ∣ Nat.card ↥EΛ := Subgroup.card_map_dvd EΛ ρ
    rw [h2] at h3
    rw [h1]
    exact (by norm_num : 2 ^ 2 ∣ 4).trans (hV4.trans h3)
  have hm2 : 2 ≤ (Nat.card ↥E).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h4E
  refine ⟨P, hPE.trans hEΛ_le, ?_, ?_⟩
  · intro e he
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 (hPE he)
    have hk2 : ρ (l * l) = 1 := by
      rw [map_mul]
      exact hVsq _ hl
    have hkk : (((l * l : ↥Λ) : ↥Λ) : G) ∈ Y := (hρker _).1 hk2
    exact CFSG.GH74.GLS.IVK.Proofs2.eq_one_of_mem_of_coprime hYcop hPp (by simpa using hkk)
      (P.mul_mem he he)
  · rw [← hPcard]
    exact (by norm_num : (4 : ℕ) = 2 ^ 2) ▸ pow_dvd_pow 2 hm2

end Lift

section Rank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem center_eq_bot_of_centerlessBar {K : Subgroup G} (h : CenterlessBar K) :
    center (kBar K) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  exact h a fun b => (Subgroup.mem_center_iff.1 ha b).symm

theorem eq_one_of_mem_of_cSec {M : Subgroup G} (hMcen : CenterlessBar M) {t : G} (htM : t ∈ M)
    (ht : t ∈ centralizerSection M (pPrimeCoreOf 2 M)) (ht2 : orderOf t = 2) : t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : t ∈ pPrimeCoreOf 2 M := mem_pPrimeCoreOf_of_commutators hMcen htM ht.2.2
  have hxp : IsPGroup 2 ↥(zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht2]; norm_num)
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCoreOf 2 M)) :=
    Nat.coprime_two_left.mpr (TwoThin.card_pPrimeCoreOf_odd M)
  exact IVK.Proofs2.eq_one_of_mem_of_coprime hcop hxp h3 (Subgroup.mem_zpowers t)

theorem false_of_commuting_cover (hr4 : pRank 2 G = 4) {u' : G} (hu'o : orderOf u' = 2)
    {K'' M Λ : Subgroup G}
    (hK'' : IsPCompIn 2 (centralizer ({u'} : Set G)) K'') (hcen'' : CenterlessBar K'')
    (hMq : CFSG.IsQuasisimple (kBar M)) (hMcen : CenterlessBar M)
    (hΛM : Λ ≤ M) (hΛY : Λ ≤ centralizer ({u'} : Set G))
    (hcover : ∀ k ∈ M, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 M, k = l * o)
    (hu'M : u' ∈ centralizerSection M (pPrimeCoreOf 2 M))
    (hcomm : ∀ e ∈ Λ, e ∈ centralizerSection K'' (pPrimeCoreOf 2 K'')) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu'sq : u' * u' = 1 := by
    have := pow_orderOf_eq_one u'
    rwa [hu'o, sq] at this
  have hu'1 : u' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu'o
    omega
  obtain ⟨V, hVel, hV4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hMq
      (by rw [center_eq_bot_of_centerlessBar hMcen, Subgroup.card_bot]; exact odd_one))
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := (GH74.Uniqueness.SU.SU1.isElemAbelian_iff.1 hVel).2 v hv
    rwa [sq] at this
  obtain ⟨E, hEΛ, hEsq, hE4⟩ := exists_lift_klein_cover hΛM hcover V hVsq (by rw [hV4])
  have hu'E : u' ∉ E := fun h =>
    hu'1 (eq_one_of_mem_of_cSec hMcen (hΛM (hEΛ h)) hu'M hu'o)
  have hEC : E ≤ centralizer ({u'} : Set G) := hEΛ.trans hΛY
  obtain ⟨hcommB, hBsq, hBcard⟩ := C3.Layer1.P47.zpowers_sup_facts hu'sq hu'1 hEC hEsq hu'E
  set B : Subgroup G := zpowers u' ⊔ E with hB
  have hBea : CFSG.IsElementaryAbelian 2 ↥B := IVK.Proofs2.isElementaryAbelian_two_of_mul_self B hBsq
  have hu'sec : u' ∈ centralizerSection K'' (pPrimeCoreOf 2 K'') :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun k hk => (mem_centralizer_singleton_iff.1 (hK''.1 hk)).symm) (TwoThin.pPrimeCoreOf_le K'')
  have hBsec : B ≤ centralizerSection K'' (pPrimeCoreOf 2 K'') :=
    sup_le ((Subgroup.zpowers_le).2 hu'sec) (fun e he => hcomm e (hEΛ he))
  have hq'' : CFSG.IsQuasisimple (kBar K'') := TwoThin.isQuasisimple_hat hK''
  obtain ⟨V'', hV''el, hV''4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq''
      (by rw [center_eq_bot_of_centerlessBar hcen'', Subgroup.card_bot]; exact odd_one))
  have hV''sq : ∀ v ∈ V'', v * v = 1 := fun v hv => by
    have := (GH74.Uniqueness.SU.SU1.isElemAbelian_iff.1 hV''el).2 v hv
    rwa [sq] at this
  obtain ⟨m, Q, hm2, hQsq, hQcard⟩ := IVK.Proofs2.exists_big_elemAbelian K'' B hBea hBsec V''
    hV''sq (by rw [hV''4]) hcen''
  have hQea : CFSG.IsElementaryAbelian 2 ↥Q := IVK.Proofs2.isElementaryAbelian_two_of_mul_self Q hQsq
  have hBpg : IsPGroup 2 ↥B := CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  obtain ⟨j, hj⟩ := hBpg.exists_card_eq
  have hE4' : 4 ≤ Nat.card ↥E := Nat.le_of_dvd Nat.card_pos hE4
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have hlt' : j < 3 := not_le.mp hlt
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrank := le_pRank_group_of_elem hQea (k := j + m) (by rw [hQcard, hj, pow_add])
  omega

end Rank
section Core

open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

theorem normal_of_A7_pumpup {u : G} {K Q : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({u} : Set G)) K)
    (hA7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ : IsSylowOf 2 Q (CxK u K)) (hQ4 : Nat.card ↥Q = 4) :
    ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 K
  have hP8 : Nat.card ↥P = 8 := CFSG.GH74.GLS.Th2.card_sylow_A7 hP hA7
  refine CFSG.GH74.GLS.normal_of_card_sylow_cSec_lt (Q := Q) hK hP.le hP.isPGroup ?_ ?_
  · simpa [CxK] using hQ
  · omega

theorem false_of_commuting_cover_smallQ {u' : G} (hu'o : orderOf u' = 2)
    {K'' M Λ Q : Subgroup G}
    (hK'' : IsPCompIn 2 (centralizer ({u'} : Set G)) K'')
    (hQ : IsSylowOf 2 Q (CxK u' K'')) (hQ4 : Nat.card ↥Q = 4)
    (hMq : CFSG.IsQuasisimple (kBar M)) (hMcen : CenterlessBar M)
    (hΛM : Λ ≤ M) (hΛY : Λ ≤ centralizer ({u'} : Set G))
    (hcover : ∀ k ∈ M, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 M, k = l * o)
    (hu'M : u' ∈ centralizerSection M (pPrimeCoreOf 2 M))
    (hcomm : ∀ e ∈ Λ, e ∈ centralizerSection K'' (pPrimeCoreOf 2 K'')) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu'sq : u' * u' = 1 := by
    have := pow_orderOf_eq_one u'
    rwa [hu'o, sq] at this
  have hu'1 : u' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu'o
    omega
  obtain ⟨V, hVel, hV4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hMq
      (by rw [center_eq_bot_of_centerlessBar hMcen, Subgroup.card_bot]; exact odd_one))
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := (GH74.Uniqueness.SU.SU1.isElemAbelian_iff.1 hVel).2 v hv
    rwa [sq] at this
  obtain ⟨E, hEΛ, hEsq, hE4⟩ := exists_lift_klein_cover hΛM hcover V hVsq (by rw [hV4])
  have hu'E : u' ∉ E := fun h =>
    hu'1 (eq_one_of_mem_of_cSec hMcen (hΛM (hEΛ h)) hu'M hu'o)
  have hEC : E ≤ centralizer ({u'} : Set G) := hEΛ.trans hΛY
  obtain ⟨hcommB, hBsq, hBcard⟩ := C3.Layer1.P47.zpowers_sup_facts hu'sq hu'1 hEC hEsq hu'E
  set B : Subgroup G := zpowers u' ⊔ E with hB
  have hBea : CFSG.IsElementaryAbelian 2 ↥B := IVK.Proofs2.isElementaryAbelian_two_of_mul_self B hBsq
  have hB2 : IsPGroup 2 ↥B := CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  have hu'sec : u' ∈ centralizerSection K'' (pPrimeCoreOf 2 K'') :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun k hk => (mem_centralizer_singleton_iff.1 (hK''.1 hk)).symm) (TwoThin.pPrimeCoreOf_le K'')
  have hBsec : B ≤ centralizerSection K'' (pPrimeCoreOf 2 K'') :=
    sup_le ((Subgroup.zpowers_le).2 hu'sec) (fun e he => hcomm e (hEΛ he))
  have hBcen : B ≤ centralizer ({u'} : Set G) := by
    refine sup_le ((Subgroup.zpowers_le).2 ?_) (hEΛ.trans hΛY)
    exact Subgroup.mem_centralizer_singleton_iff.2 (by rfl)
  have hBcx : B ≤ CxK u' K'' := fun b hb => ⟨hBcen hb, hBsec hb⟩
  obtain ⟨g, -, hgQ⟩ := Th2.exists_cj_le_of_isSylowOf hQ hBcx hB2
  have hcardB : 8 ≤ Nat.card ↥B := by
    rw [hBcard]
    have : 4 ≤ Nat.card ↥E := Nat.le_of_dvd Nat.card_pos hE4
    omega
  have hcard_cj : Nat.card ↥(cj g B) = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcard_le : Nat.card ↥B ≤ Nat.card ↥Q := by
    rw [← hcard_cj]
    exact Subgroup.card_le_of_le hgQ
  omega

private theorem bar_pumpup_eq_core {u : G} {M : Subgroup G}
    {u' : G} {M' K'' : Subgroup G}
    (hlt : PumpUpLT 2 u M u' M')
    (hK''c : IsPCompIn 2 (centralizer ({u'} : Set G)) K'')
    (hN : ∀ a ∈ centralizer ({u'} : Set G), a ∈ normalizer (K'' : Set G))
    (hfalse : ∀ (Λ : Subgroup G), Λ ≤ M → Λ ≤ centralizer ({u'} : Set G) →
      (∀ k ∈ M, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 M, k = l * o) →
      (∀ e ∈ Λ, e ∈ centralizerSection K'' (pPrimeCoreOf 2 K'')) → False) :
    bar u' M' = bar u' K'' := by
  by_contra hne
  have huY : u ∈ centralizer ({u'} : Set G) := TwoThin.mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ, hM'c, ⟨L, hL, himg, hcases⟩, -⟩ := step_core hlt huY
  have hSc : CFSG.IsComponent (bar u' K'') := isComponent_bar hK''c
  have huN : u ∈ normalizer (K'' : Set G) := hN u huY
  have hSstab : conjSub (sbar u huY) (bar u' K'') = bar u' K'' :=
    map_conj_bar_of_normalizes huY huN
  have hū2 : orderOf (sbar u huY) = 2 := orderOf_sbar hlt.1.1 huY
  have hūinv : (sbar u huY)⁻¹ = sbar u huY := inv_eq_self_of_orderOf_eq_two hū2
  have hSstab' : conjSub (sbar u huY)⁻¹ (bar u' K'') = bar u' K'' := by
    rw [hūinv]; exact hSstab
  have hLS : L ≠ bar u' K'' := by
    intro hLS
    apply hne
    rcases himg with h | h
    · exact h.trans hLS
    · exact h.trans (by rw [hLS, hSstab'])
  have hL'c : CFSG.IsComponent (conjSub (sbar u huY)⁻¹ L) := isComponent_conjSub hL _
  have hL'S : conjSub (sbar u huY)⁻¹ L ≠ bar u' K'' := by
    intro h
    apply hLS
    have := congrArg (conjSub (sbar u huY)) h
    rwa [conjSub_conjSub_inv, hSstab] at this
  have hLC : L ≤ Subgroup.centralizer ((bar u' K'' : Subgroup _) : Set _) :=
    comp_le_centralizer_of_ne hL hSc hLS
  have hL'C : conjSub (sbar u huY)⁻¹ L ≤ Subgroup.centralizer ((bar u' K'' : Subgroup _) : Set _) :=
    comp_le_centralizer_of_ne hL'c hSc hL'S
  have hΛC : bar u' Λ ≤ Subgroup.centralizer ((bar u' K'' : Subgroup _) : Set _) := by
    rcases hcases with ⟨-, hΛL⟩ | ⟨-, hAB, hAD⟩
    · exact hΛL.trans hLC
    · intro w hw
      obtain ⟨b, rfl⟩ := hAD hw
      rw [swapDiag_apply]
      exact Subgroup.mul_mem _ (hLC b.2) (hL'C (conj_mem_conjSub b.2))
  have hΛM : Λ ≤ M := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({u'} : Set G) := hΛ.le.trans inf_le_right
  refine hfalse Λ hΛM hΛY hΛ.cover (fun l hl => ?_)
  have hlY : l ∈ centralizer ({u'} : Set G) := hΛY hl
  have hmem : sbar l hlY ∈ bar u' Λ :=
    ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hcl : l ∈ CxK u' K'' := by
    refine mem_CxK_of_centralizes hK''c hlY (fun w hw => ?_)
    have := Subgroup.mem_centralizer_iff.1 (hΛC hmem) w hw
    rw [← this]
    group
  exact (Subgroup.mem_inf.1 hcl).2

theorem bar_pumpup_eq (hr4 : pRank 2 G = 4) {x u : G} {K M : Subgroup G}
    (hKcen : CenterlessBar K) (hterm : IsTwoTerminal x K) (e : kBar M ≃* kBar K)
    {u' : G} (hux' : u' ∈ centralizer ({x} : Set G))
    (hu'K : u' ∈ centralizerSection K (pPrimeCoreOf 2 K))
    {M' : Subgroup G} (hlt : PumpUpLT 2 u M u' M') :
    ∃ K'' : Subgroup G, PumpUpLT 2 x K u' K'' ∧ bar u' M' = bar u' K'' := by
  classical
  have hxo : orderOf x = 2 := hterm.1.1
  have hu'o : orderOf u' = 2 := hlt.2.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hterm.1.2.2
  have hR : 3 ≤ pRank 2 ↥(centralizer ({u'} : Set G)) := by
    simpa [oBound] using hlt.2.1.2.1
  obtain ⟨K'', hltK⟩ := TwoThin.exists_pumpup_of_involution hxo hu'o hKc hux' hu'K hterm.1 hR
  obtain ⟨hxK'', ⟨e''⟩⟩ := hterm.2.1 u' K'' hltK
  have hK''c : IsPCompIn 2 (centralizer ({u'} : Set G)) K'' := hltK.2.1.2.2
  have hcen'' : CenterlessBar K'' := centerlessBar_of_equiv hKcen e''
  have hq'' : CFSG.IsQuasisimple (kBar K'') := TwoThin.isQuasisimple_hat hK''c
  have hN : ∀ a ∈ centralizer ({u'} : Set G), a ∈ normalizer (K'' : Set G) := fun a ha =>
    C3.Layer1.PumpGen.mem_normalizer_of_centerless hr4 ⟨hu'o, hK''c⟩ hq''
      (center_eq_bot_of_centerlessBar hcen'') ha
  refine ⟨K'', hltK, bar_pumpup_eq_core hlt hK''c hN ?_⟩
  intro Λ hΛM hΛY hcover hcomm
  exact false_of_commuting_cover hr4 hu'o hK''c hcen''
    (TwoThin.isQuasisimple_hat hlt.1.2.2) (centerlessBar_of_equiv hKcen e)
    hΛM hΛY hcover hlt.2.2.2.1 hcomm

theorem bar_pumpup_eq_smallQ {x u : G} {K M Q : Subgroup G}
    (hterm : IsTwoTerminal x K) (e7 : kBar K ≃* alternatingGroup (Fin 7))
    (hQ : IsSylowOf 2 Q (CxK x K)) (hQ4 : Nat.card ↥Q = 4)
    (huQ : u ∈ Q) (hltM : PumpUpLT 2 x K u M)
    {u' : G} (hu'Q : u' ∈ Q) {M' : Subgroup G} (hlt : PumpUpLT 2 u M u' M') :
    ∃ K'' : Subgroup G, PumpUpLT 2 x K u' K'' ∧ bar u' M' = bar u' K'' := by
  classical
  have hxo : orderOf x = 2 := hterm.1.1
  have hu'o : orderOf u' = 2 := hlt.2.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hterm.1.2.2
  have hR : 3 ≤ pRank 2 ↥(centralizer ({u'} : Set G)) := by
    simpa [oBound] using hlt.2.1.2.1
  have hu'x : u' ∈ centralizer ({x} : Set G) := (hQ.le hu'Q).1
  have hu'K : u' ∈ centralizerSection K (pPrimeCoreOf 2 K) := (hQ.le hu'Q).2
  obtain ⟨K'', hltK⟩ := TwoThin.exists_pumpup_of_involution hxo hu'o hKc hu'x hu'K hterm.1 hR
  obtain ⟨hxK'', ⟨e''⟩⟩ := hterm.2.1 u' K'' hltK
  have hK''c : IsPCompIn 2 (centralizer ({u'} : Set G)) K'' := hltK.2.1.2.2
  have hcenK : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hcen'' : CenterlessBar K'' := centerlessBar_of_equiv hcenK e''
  have hQcomm : IsMulCommutative ↥Q :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hQ4]; norm_num)
  have hu'Qcomm : ∀ q ∈ Q, u' * q = q * u' := fun q hq =>
    congrArg Subtype.val (hQcomm.is_comm.comm ⟨u', hu'Q⟩ ⟨q, hq⟩)
  have hQK'' : IsSylowOf 2 Q (CxK u' K'') := hterm.2.2 Q hQ u' K'' hltK hu'Q hu'Qcomm
  have hK''norm : ∀ c ∈ centralizer ({u'} : Set G), ∀ k ∈ K'', c * k * c⁻¹ ∈ K'' :=
    normal_of_A7_pumpup hK''c ⟨e''.trans e7⟩ hQK'' hQ4
  have hN : ∀ a ∈ centralizer ({u'} : Set G), a ∈ normalizer (K'' : Set G) := fun a ha =>
    CFSG.GH74.GLS.Th2Tstar.mem_normalizer_of_conj_mem (hK''norm a ha)
      (hK''norm a⁻¹ ((centralizer ({u'} : Set G)).inv_mem ha))
  obtain ⟨-, ⟨eM⟩⟩ := hterm.2.1 u M hltM
  have hMcen : CenterlessBar M := centerlessBar_of_equiv hcenK eM
  refine ⟨K'', hltK, bar_pumpup_eq_core hlt hK''c hN ?_⟩
  intro Λ hΛM hΛY hcover hcomm
  exact false_of_commuting_cover_smallQ hu'o hK''c hQK'' hQ4
    (TwoThin.isQuasisimple_hat hlt.1.2.2) hMcen hΛM hΛY hcover hlt.2.2.2.1 hcomm

end Core

section Main

open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.Stage1.Thm3.Sec4

variable {G : Type} [Group G] [Finite G]

theorem CxK_eq_of_bar_eq {t : G} {K₁ K₂ : Subgroup G}
    (h₁ : IsPCompIn 2 (centralizer ({t} : Set G)) K₁) (h₂ : IsPCompIn 2 (centralizer ({t} : Set G)) K₂)
    (h : bar t K₁ = bar t K₂) : CxK t K₁ = CxK t K₂ := by
  ext q
  constructor
  · intro hq
    have hqY : q ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.1 hq).1
    refine mem_CxK_of_centralizes h₂ hqY (fun w hw => ?_)
    rw [← h] at hw
    exact centralizes_of_mem_CxK h₁ hqY hq w hw
  · intro hq
    have hqY : q ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.1 hq).1
    refine mem_CxK_of_centralizes h₁ hqY (fun w hw => ?_)
    rw [h] at hw
    exact centralizes_of_mem_CxK h₂ hqY hq w hw

omit [Finite G] in
theorem CxK_cmap' (c x : G) (K : Subgroup G) :
    CxK (c * x * c⁻¹) (cmap c K) = cmap c (CxK x K) := by
  ext z
  rw [mem_cmap]
  unfold CxK
  rw [Subgroup.mem_inf, Subgroup.mem_inf, pPrimeCoreOf_cmap]
  have h1 : z ∈ centralizer ({c * x * c⁻¹} : Set G) ↔ c⁻¹ * z * c ∈ centralizer ({x} : Set G) := by
    rw [← mem_cmap, ← Stage1.Thm2.Recip.map_centralizer_singleton_conj x c]
  have h2 : z ∈ centralizerSection (cmap c K) (cmap c (pPrimeCoreOf 2 K)) ↔
      c⁻¹ * z * c ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
    have := mem_centralizerSection_cmap_iff (c := c) (z := c⁻¹ * z * c) (K := K)
      (M := pPrimeCoreOf 2 K)
    rwa [show c * (c⁻¹ * z * c) * c⁻¹ = z by group] at this
  rw [h1, h2]

theorem b_thm2_pump_terminal_of (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) :
    B_thm2_pump_terminal := by
  intro G _ _ hG x y K T S h hrk2 u hu huc hu2 M hltM hMN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  obtain ⟨hcenK, -⟩ := h.centerless_and_shape hG hL34 h102
  have hterm : IsTwoTerminal x K := h.v2ss.isV2Triple.2.1
  obtain ⟨-, ⟨e⟩, hQ⟩ := h.pumpup_data hu huc hltM
  have hQxK : IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) := h.sylow_Q
  have core : ∀ {u' : G} {M' : Subgroup G}, u' ∈ T ⊓ CxK x K → PumpUpLT 2 u M u' M' →
      ∃ K'' : Subgroup G, PumpUpLT 2 x K u' K'' ∧ bar u' M' = bar u' K'' := by
    intro u' M' hu'Q hlt'
    exact bar_pumpup_eq hr4 hcenK hterm e hu'Q.2.1 hu'Q.2.2 hlt'
  have hfix : ∀ {u' : G} {M' : Subgroup G}, PumpUpLT 2 u M u' M' → ∀ {g : G}, g ∈ CxK u M →
      PumpUpLT 2 u M (g * u' * g⁻¹) (cmap g M') := by
    intro u' M' hlt' g hgC
    have hgY : g ∈ centralizer ({u} : Set G) := (Subgroup.mem_inf.1 hgC).1
    have hgN : g ∈ normalizer (M : Set G) := (Subgroup.mem_inf.1 hgC).2.1
    have hgu : g * u * g⁻¹ = u := conj_fix_of_mem_centralizer hgY
    have hgM : cmap g M = M := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    have := pumpUpLT_cmap hlt' g
    rwa [hgu, hgM] at this
  have hMcen : CenterlessBar M := centerlessBar_of_equiv hcenK e
  refine ⟨hltM.2.1, ?_, ?_⟩
  ·
    intro u' M' hlt'
    have hu'C : u' ∈ CxK u M := mem_CxK_of_pumpUpLT hlt'
    have hu'o : orderOf u' = 2 := hlt'.2.1.1
    have hW : IsPGroup 2 ↥(zpowers u') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu'o]; norm_num)
    obtain ⟨g, hgC, hg⟩ := Th2.exists_cj_le_of_isSylowOf hQ (Subgroup.zpowers_le.2 hu'C) hW
    have hgY : g ∈ centralizer ({u} : Set G) := (Subgroup.mem_inf.1 hgC).1
    have hgu : g * u * g⁻¹ = u := conj_fix_of_mem_centralizer hgY
    have hu''Q : g * u' * g⁻¹ ∈ T ⊓ CxK x K :=
      hg ⟨u', Subgroup.mem_zpowers u', by simp [MulAut.conj_apply]⟩
    have hlt'' := hfix hlt' hgC
    obtain ⟨K'', hltK, hbar⟩ := core hu''Q hlt''
    have hM''c : IsPCompIn 2 (centralizer ({g * u' * g⁻¹} : Set G)) (cmap g M') := hlt''.2.1.2.2
    have hK''c : IsPCompIn 2 (centralizer ({g * u' * g⁻¹} : Set G)) K'' := hltK.2.1.2.2
    obtain ⟨hxK'', ⟨e''⟩⟩ := hterm.2.1 (g * u' * g⁻¹) K'' hltK
    obtain ⟨e1⟩ := kBar_equiv_bar hM''c
    obtain ⟨e2⟩ := kBar_equiv_bar hK''c
    let eM'' : kBar (cmap g M') ≃* kBar M :=
      e1.trans ((MulEquiv.subgroupCongr hbar).trans (e2.symm.trans (e''.trans e.symm)))
    have hcenM'' : CenterlessBar (cmap g M') := centerlessBar_of_equiv hMcen eM''
    have huN'' : u ∈ normalizer ((cmap g M' : Subgroup G) : Set G) :=
      C3.Layer1.PumpGen.mem_normalizer_of_centerless hr4 ⟨hlt''.2.1.1, hM''c⟩
        (TwoThin.isQuasisimple_hat hM''c) (center_eq_bot_of_centerlessBar hcenM'')
        (TwoThin.mem_centralizer_symm hlt''.2.2.1)
    refine ⟨?_, ⟨(nonempty_quot_cmap g M').some.symm.trans eM''⟩⟩
    have := (mem_normalizer_cmap_iff (c := g) (y := u) (K := M')).1 (by rw [hgu]; exact huN'')
    exact this
  ·
    intro Q' hQ' u' M' hlt' hu'Q' hu'c
    obtain ⟨g, hgC, hg⟩ := Th2.exists_cj_le_of_isSylowOf hQ hQ'.le hQ'.isPGroup
    have hcard : Nat.card ↥(T ⊓ CxK x K) ≤ Nat.card ↥(cmap g Q') := by
      rw [hQ.card_eq, Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ'.card_eq]
      exact le_rfl
    have hgQ : cmap g Q' = T ⊓ CxK x K := Subgroup.eq_of_le_of_card_ge (hg : cmap g Q' ≤ _) hcard
    have hlt'' := hfix hlt' hgC
    have hu''Q : g * u' * g⁻¹ ∈ T ⊓ CxK x K := by
      rw [← hgQ]
      exact ⟨u', hu'Q', by simp [MulAut.conj_apply]⟩
    have hu''c : ∀ q ∈ T ⊓ CxK x K, (g * u' * g⁻¹) * q = q * (g * u' * g⁻¹) := by
      intro q hq
      rw [← hgQ] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := hu'c q' hq'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * u' * g⁻¹ * (g * q' * g⁻¹) = g * (u' * q') * g⁻¹ := by group
        _ = g * (q' * u') * g⁻¹ := by rw [this]
        _ = g * q' * g⁻¹ * (g * u' * g⁻¹) := by group
    obtain ⟨K'', hltK, hbar⟩ := core hu''Q hlt''
    have hS := hterm.2.2 (T ⊓ CxK x K) hQxK (g * u' * g⁻¹) K'' hltK hu''Q hu''c
    have hCx : CxK (g * u' * g⁻¹) (cmap g M') = CxK (g * u' * g⁻¹) K'' :=
      CxK_eq_of_bar_eq hlt''.2.1.2.2 hltK.2.1.2.2 hbar
    have hS2 : IsSylowOf 2 (T ⊓ CxK x K) (CxK (g * u' * g⁻¹) (cmap g M')) := by
      rw [hCx]; exact hS
    have hS' := isSylowOf_cmap hS2 g⁻¹
    have e1 : cmap g⁻¹ (T ⊓ CxK x K) = Q' := by rw [← hgQ, cmap_inv_cancel]
    have e2 : cmap g⁻¹ (CxK (g * u' * g⁻¹) (cmap g M')) = CxK u' M' := by
      rw [CxK_cmap', cmap_inv_cancel]
    rw [e1, e2] at hS'
    exact hS'

end Main


section SmallQ

open CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1.Bk
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage1.Thm3.Sec4

variable {G : Type} [Group G] [Finite G]

theorem isTwoTerminal_of_A7_smallQ {x u : G} {K M Q : Subgroup G}
    (hterm : IsTwoTerminal x K) (e7 : kBar K ≃* alternatingGroup (Fin 7))
    (hQ : IsSylowOf 2 Q (CxK x K)) (hQ4 : Nat.card ↥Q = 4)
    (huQ : u ∈ Q) (hltM : PumpUpLT 2 x K u M) :
    IsTwoTerminal u M := by
  classical
  have hQcomm : IsMulCommutative ↥Q :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hQ4]; norm_num)
  have huQcomm : ∀ q ∈ Q, u * q = q * u := fun q hq =>
    congrArg Subtype.val (hQcomm.is_comm.comm ⟨u, huQ⟩ ⟨q, hq⟩)
  have hQM : IsSylowOf 2 Q (CxK u M) := hterm.2.2 Q hQ u M hltM huQ huQcomm
  have core : ∀ {u' : G} {M' : Subgroup G}, u' ∈ Q → PumpUpLT 2 u M u' M' →
      ∃ K'' : Subgroup G, PumpUpLT 2 x K u' K'' ∧ bar u' M' = bar u' K'' := by
    intro u' M' hu'Q hlt'
    exact bar_pumpup_eq_smallQ hterm e7 hQ hQ4 huQ hltM hu'Q hlt'
  have hfix : ∀ {u' : G} {M' : Subgroup G}, PumpUpLT 2 u M u' M' → ∀ {g : G}, g ∈ CxK u M →
      PumpUpLT 2 u M (g * u' * g⁻¹) (cmap g M') := by
    intro u' M' hlt' g hgC
    have hgY : g ∈ centralizer ({u} : Set G) := (Subgroup.mem_inf.1 hgC).1
    have hgN : g ∈ normalizer (M : Set G) := (Subgroup.mem_inf.1 hgC).2.1
    have hgu : g * u * g⁻¹ = u := conj_fix_of_mem_centralizer hgY
    have hgM : cmap g M = M := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    have := pumpUpLT_cmap hlt' g
    rwa [hgu, hgM] at this
  obtain ⟨-, ⟨eM⟩⟩ := hterm.2.1 u M hltM
  have hcenK : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hMcen : CenterlessBar M := centerlessBar_of_equiv hcenK eM
  refine ⟨hltM.2.1, ?_, ?_⟩
  ·
    intro u' M' hlt'
    have hu'C : u' ∈ CxK u M := mem_CxK_of_pumpUpLT hlt'
    have hu'o : orderOf u' = 2 := hlt'.2.1.1
    have hW : IsPGroup 2 ↥(zpowers u') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu'o]; norm_num)
    obtain ⟨g, hgC, hg⟩ := Th2.exists_cj_le_of_isSylowOf hQM (Subgroup.zpowers_le.2 hu'C) hW
    have hgY : g ∈ centralizer ({u} : Set G) := (Subgroup.mem_inf.1 hgC).1
    have hgu : g * u * g⁻¹ = u := conj_fix_of_mem_centralizer hgY
    have hu''Q : g * u' * g⁻¹ ∈ Q :=
      hg ⟨u', Subgroup.mem_zpowers u', by simp [MulAut.conj_apply]⟩
    have hlt'' := hfix hlt' hgC
    obtain ⟨K'', hltK, hbar⟩ := core hu''Q hlt''
    have hM''c : IsPCompIn 2 (centralizer ({g * u' * g⁻¹} : Set G)) (cmap g M') := hlt''.2.1.2.2
    have hK''c : IsPCompIn 2 (centralizer ({g * u' * g⁻¹} : Set G)) K'' := hltK.2.1.2.2
    obtain ⟨hxK'', ⟨e''⟩⟩ := hterm.2.1 (g * u' * g⁻¹) K'' hltK
    obtain ⟨e1⟩ := kBar_equiv_bar hM''c
    obtain ⟨e2⟩ := kBar_equiv_bar hK''c
    let eM'' : kBar (cmap g M') ≃* kBar M :=
      e1.trans ((MulEquiv.subgroupCongr hbar).trans (e2.symm.trans (e''.trans eM.symm)))
    have hM''cen : CenterlessBar (cmap g M') := centerlessBar_of_equiv hMcen eM''
    have hA7M'' : Nonempty (kBar (cmap g M') ≃* alternatingGroup (Fin 7)) :=
      ⟨eM''.trans (eM.trans e7)⟩
    have hu''Qcomm : ∀ q ∈ Q, (g * u' * g⁻¹) * q = q * (g * u' * g⁻¹) := fun q hq =>
      congrArg Subtype.val (hQcomm.is_comm.comm ⟨g * u' * g⁻¹, hu''Q⟩ ⟨q, hq⟩)
    have hQK'' : IsSylowOf 2 Q (CxK (g * u' * g⁻¹) K'') :=
      hterm.2.2 Q hQ (g * u' * g⁻¹) K'' hltK hu''Q hu''Qcomm
    have hCx : CxK (g * u' * g⁻¹) (cmap g M') = CxK (g * u' * g⁻¹) K'' :=
      CxK_eq_of_bar_eq hM''c hK''c hbar
    have hQM'' : IsSylowOf 2 Q (CxK (g * u' * g⁻¹) (cmap g M')) := by
      rw [hCx]
      exact hQK''
    have hM''norm : ∀ c ∈ centralizer ({g * u' * g⁻¹} : Set G), ∀ k ∈ cmap g M',
        c * k * c⁻¹ ∈ cmap g M' :=
      normal_of_A7_pumpup hM''c hA7M'' hQM'' hQ4
    have huCv : u ∈ centralizer ({g * u' * g⁻¹} : Set G) :=
      TwoThin.mem_centralizer_symm hlt''.2.2.1
    have huN'' : u ∈ normalizer ((cmap g M' : Subgroup G) : Set G) :=
      CFSG.GH74.GLS.Th2Tstar.mem_normalizer_of_conj_mem (hM''norm u huCv)
        (hM''norm u⁻¹ ((centralizer ({g * u' * g⁻¹} : Set G)).inv_mem huCv))
    refine ⟨?_, ⟨(nonempty_quot_cmap g M').some.symm.trans eM''⟩⟩
    have := (mem_normalizer_cmap_iff (c := g) (y := u) (K := M')).1 (by rw [hgu]; exact huN'')
    exact this
  ·
    intro Q' hQ' u' M' hlt' hu'Q' hu'c
    obtain ⟨g, hgC, hg⟩ := Th2.exists_cj_le_of_isSylowOf hQM hQ'.le hQ'.isPGroup
    have hcard : Nat.card ↥Q ≤ Nat.card ↥(cmap g Q') := by
      rw [hQM.card_eq, Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ'.card_eq]
      exact le_rfl
    have hgQ : cmap g Q' = Q := Subgroup.eq_of_le_of_card_ge (hg : cmap g Q' ≤ Q) hcard
    have hlt'' := hfix hlt' hgC
    have hu''Q : g * u' * g⁻¹ ∈ Q := by
      rw [← hgQ]
      exact ⟨u', hu'Q', by simp [MulAut.conj_apply]⟩
    have hu''c : ∀ q ∈ Q, (g * u' * g⁻¹) * q = q * (g * u' * g⁻¹) := by
      intro q hq
      rw [← hgQ] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := hu'c q' hq'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * u' * g⁻¹ * (g * q' * g⁻¹) = g * (u' * q') * g⁻¹ := by group
        _ = g * (q' * u') * g⁻¹ := by rw [this]
        _ = g * q' * g⁻¹ * (g * u' * g⁻¹) := by group
    obtain ⟨K'', hltK, hbar⟩ := core hu''Q hlt''
    have hS := hterm.2.2 Q hQ (g * u' * g⁻¹) K'' hltK hu''Q hu''c
    have hCx : CxK (g * u' * g⁻¹) (cmap g M') = CxK (g * u' * g⁻¹) K'' :=
      CxK_eq_of_bar_eq hlt''.2.1.2.2 hltK.2.1.2.2 hbar
    have hS2 : IsSylowOf 2 Q (CxK (g * u' * g⁻¹) (cmap g M')) := by
      rw [hCx]
      exact hS
    have hS' := isSylowOf_cmap hS2 g⁻¹
    have e1 : cmap g⁻¹ Q = Q' := by rw [← hgQ, cmap_inv_cancel]
    have e2 : cmap g⁻¹ (CxK (g * u' * g⁻¹) (cmap g M')) = CxK u' M' := by
      rw [CxK_cmap', cmap_inv_cancel]
    rw [e1, e2] at hS'
    exact hS'

theorem exists_pumpup_of_A7_card_Q_four {x y : G} {K T S : Subgroup G}
    (h : Th2Std x y K T S) (e7 : kBar K ≃* alternatingGroup (Fin 7))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4)
    {u : G} (huQ : u ∈ T ⊓ CxK x K) (huc : ∀ t ∈ T, u * t = t * u)
    (hu2 : orderOf u = 2) :
    ∃ M : Subgroup G, PumpUpLT 2 x K u M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQcomm : IsMulCommutative ↥(T ⊓ CxK x K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hQ4]; norm_num)
  have hxQ : x ∈ T ⊓ CxK x K := ⟨h.x_mem_T, h.x_mem_CxK⟩
  have hxu : x * u = u * x := congrArg Subtype.val (hQcomm.is_comm.comm ⟨x, hxQ⟩ ⟨u, huQ⟩)
  have hPshape : RankTwoShape (T ⊓ K) := rankTwoShape_sylow_A7 h.sylow_P ⟨e7⟩
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hPshape
  have hcen : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hPQ := h.commDisj hcen
  have hUleC : U ≤ centralizer ({u} : Set G) := by
    intro p hp
    exact mem_centralizer_singleton_iff.2 (huc p (hU.1 hp).1).symm
  have huC : u ∈ centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (by rfl)
  have hdisj : U ⊓ zpowers u = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rw [Subgroup.mem_bot]
    have hzP : z ∈ T ⊓ K := hU.1 hz.1
    have hzQ : z ∈ T ⊓ CxK x K := (Subgroup.zpowers_le.2 huQ) hz.2
    have hzbot : z ∈ (⊥ : Subgroup G) := by
      rw [← hPQ.inf]
      exact ⟨hzP, hzQ⟩
    exact Subgroup.mem_bot.1 hzbot
  have hcommU : ∀ a ∈ U, ∀ b ∈ zpowers u, a * b = b * a := by
    intro a ha b hb
    have hbQ : b ∈ T ⊓ CxK x K := (Subgroup.zpowers_le.2 huQ) hb
    exact hPQ.comm a (hU.1 ha) b hbQ
  have hcd : CommDisj U (zpowers u) := ⟨hcommU, hdisj⟩
  have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers u) :=
    isElementaryAbelian_zpowers_of_orderOf_two hu2
  have hVea : CFSG.IsElementaryAbelian 2 ↥(U ⊔ zpowers u) :=
    hcd.isElementaryAbelian_sup' hU.2.1 hzel le_rfl le_rfl
  have hVrank : pRank 2 ↥(U ⊔ zpowers u) = 3 := by
    rw [hcd.pRank_sup hU.2.1 hzel le_rfl le_rfl, pRank_of_isFourSub hU,
      pRank_zpowers_of_orderOf_two hu2]
  have hVC : U ⊔ zpowers u ≤ centralizer ({u} : Set G) := sup_le hUleC (Subgroup.zpowers_le.2 huC)
  have hR : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := by
    rw [← hVrank]
    exact C3.Layer1.Back.pRank_mono' hVC
  have hKil : IsILo 2 x K := h.v2ss.isV2Triple.2.1.1
  exact TwoThin.exists_pumpup_of_involution h.orderOf_x hu2 h.comp huQ.2.1 huQ.2.2 hKil hR

theorem isSylow_T_of_A7_card_Q_four {x y : G} {K T S : Subgroup G}
    (h : Th2Std x y K T S) (e7 : kBar K ≃* alternatingGroup (Fin 7))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4)
    {u : G} (hu : u ∈ T ⊓ CxK x K) (huc : ∀ t ∈ T, u * t = t * u)
    (hu2 : orderOf u = 2) :
    IsSylowOf 2 T (centralizer ({u} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hux : u = x
  · subst hux
    simpa using h.setup.sylowT
  have hQ := h.sylow_Q
  have hterm : IsTwoTerminal x K := h.v2ss.isV2Triple.2.1
  have hQcomm : IsMulCommutative ↥(T ⊓ CxK x K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hQ4]; norm_num)
  have hxQ : x ∈ T ⊓ CxK x K := ⟨h.x_mem_T, h.x_mem_CxK⟩
  have hxu : x * u = u * x := congrArg Subtype.val (hQcomm.is_comm.comm ⟨x, hxQ⟩ ⟨u, hu⟩)
  have huQcomm : ∀ q ∈ T ⊓ CxK x K, u * q = q * u := fun q hq =>
    congrArg Subtype.val (hQcomm.is_comm.comm ⟨u, hu⟩ ⟨q, hq⟩)
  obtain ⟨M, hltM⟩ := exists_pumpup_of_A7_card_Q_four h e7 hQ4 hu huc hu2
  have htermM : IsTwoTerminal u M := isTwoTerminal_of_A7_smallQ hterm e7 hQ hQ4 hu hltM
  obtain ⟨hxM, ⟨eMK⟩⟩ := hterm.2.1 u M hltM
  have hMcomp : IsPCompIn 2 (centralizer ({u} : Set G)) M := hltM.2.1.2.2
  have hA7M : Nonempty (kBar M ≃* alternatingGroup (Fin 7)) := ⟨eMK.trans e7⟩
  have hQM : IsSylowOf 2 (T ⊓ CxK x K) (CxK u M) :=
    hterm.2.2 (T ⊓ CxK x K) hQ u M hltM hu huQcomm
  have hMnorm : ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ M, c * k * c⁻¹ ∈ M :=
    normal_of_A7_pumpup hMcomp hA7M hQM hQ4
  obtain ⟨y', hy'M, hlu⟩ := CFSG.GH74.GLS.exists_locally_unbalancing_of_a7
    (x := u) (K := M) ⟨hu2, hMcomp⟩ hA7M
  have hxQ' : x ∈ T ⊓ CxK x K := ⟨h.x_mem_T, h.x_mem_CxK⟩
  have hxu' : x * u = u * x := hxu
  have hdisj : zpowers x ⊓ zpowers u = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rw [Subgroup.mem_bot]
    rcases CFSG.GH74.GLS.mem_zpowers_two h.orderOf_x hz.1 with h0 | h0
    · exact h0
    · rcases CFSG.GH74.GLS.mem_zpowers_two hu2 hz.2 with h1 | h1
      · exact h1
      · exact absurd (h0.symm.trans h1) (Ne.symm hux)
  have hcd : CommDisj (zpowers x) (zpowers u) := by
    refine ⟨fun a ha b hb => ?_, hdisj⟩
    rcases CFSG.GH74.GLS.mem_zpowers_two h.orderOf_x ha with rfl | rfl
    · simp
    · rcases CFSG.GH74.GLS.mem_zpowers_two hu2 hb with rfl | rfl
      · simp
      · exact hxu'
  have hzelx : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    isElementaryAbelian_zpowers_of_orderOf_two h.orderOf_x
  have hzelu : CFSG.IsElementaryAbelian 2 ↥(zpowers u) :=
    isElementaryAbelian_zpowers_of_orderOf_two hu2
  have hVrank : pRank 2 ↥(zpowers x ⊔ zpowers u) = 2 := by
    rw [hcd.pRank_sup hzelx hzelu le_rfl le_rfl,
      pRank_zpowers_of_orderOf_two h.orderOf_x, pRank_zpowers_of_orderOf_two hu2]
  have hVQ : zpowers x ⊔ zpowers u ≤ T ⊓ CxK x K :=
    sup_le (Subgroup.zpowers_le.2 hxQ') (Subgroup.zpowers_le.2 hu)
  have hrankC : 2 ≤ pRank 2 ↥(CxK u M) := by
    have hmono : pRank 2 ↥(zpowers x ⊔ zpowers u) ≤ pRank 2 ↥(CxK u M) :=
      C3.Layer1.Back.pRank_mono' (hVQ.trans hQM.le)
    omega
  have hcardM : Nat.card (kBar M) = 2520 := by
    rw [Nat.card_congr eMK.toEquiv, Nat.card_congr e7.toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hnoL34 : ¬ IsL34Quotient (kBar M) := fun hl =>
    CFSG.GH74.GLS.Th2Tstar.not_isL34Quotient_of_card_lt
      (by rw [hcardM]; norm_num) hl
  have hV2 : IsV2Triple u y' M :=
    ⟨hlu, htermM, Or.inl hrankC, fun hl => (hnoL34 hl).elim⟩
  have hv := h.v2ss.1
  have hM1 : V2Max1 u y' M := ⟨hV2, fun x' y'' K'' h'' hsucc =>
    hv.1.1.1.2 x' y'' K'' h'' (U2Succ_congr_right eMK hsucc)⟩
  have hrk : pRank 2 ↥(CxK x K) = pRank 2 ↥(CxK u M) := by
    rw [← pRank_eq_of_isSylowOf hQ, ← pRank_eq_of_isSylowOf hQM]
  have hcard : twoPartCard (CxK x K) = twoPartCard (CxK u M) := by
    rw [twoPartCard_eq_card_of_isSylowOf hQ, twoPartCard_eq_card_of_isSylowOf hQM]
  have hM2 : V2Max2 u y' M := ⟨hM1, fun x' y'' K'' h'' => hrk ▸ hv.1.1.2 x' y'' K'' h''⟩
  have hM3 : V2Max3 u y' M := ⟨hM2, fun x' y'' K'' h'' => hcard ▸ hv.1.2 x' y'' K'' h''⟩
  have hmax := hv.2 u y' M hM3
  have hN : NxK u M = centralizer ({u} : Set G) := by
    refine le_antisymm inf_le_left (le_inf le_rfl fun c hc => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hMnorm c hc k, fun hk => ?_⟩
    have := hMnorm c⁻¹ (Subgroup.inv_mem _ hc) _ hk
    simpa [mul_assoc] using this
  rw [hN] at hmax
  have hT0 := h.setup.sylowT0
  have h1 : twoPartCard (NxK x K) ≤ Nat.card ↥T := by
    rw [twoPartCard_eq_card_of_isSylowOf hT0]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hTC : T ≤ centralizer ({u} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 (huc t ht).symm
  refine isSylowOf_of_card hTC ?_
  have hle : Nat.card ↥T ≤ twoPartCard (centralizer ({u} : Set G)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h.T_pGroup
    have hdvd : Nat.card ↥T ∣ Nat.card ↥(centralizer ({u} : Set G)) :=
      Subgroup.card_dvd_of_le hTC
    have hne : Nat.card ↥(centralizer ({u} : Set G)) ≠ 0 := Nat.card_pos.ne'
    rw [hn] at hdvd ⊢
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 hdvd
    exact Nat.pow_le_pow_right (by norm_num) this
  exact le_antisymm hle (hmax.trans h1)

end SmallQ

end CFSG.GH74.GLS.Th2.PumpTerm
