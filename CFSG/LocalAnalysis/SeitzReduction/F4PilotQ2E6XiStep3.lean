module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6UniqueMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartnerS

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Transport

variable {G : Type} [Group G]

@[expose] noncomputable def quotCenterEquivOfEqBot {H : Type*} [Group H] (hZ : center H = ⊥) :
    H ⧸ center H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem quotCenterEquivOfEqBot_symm_apply {H : Type*} [Group H] (hZ : center H = ⊥) (h : H) :
    (quotCenterEquivOfEqBot hZ).symm h = QuotientGroup.mk h := by
  rw [MulEquiv.symm_apply_eq]
  rfl

@[expose] noncomputable def quotTransport {N M : Subgroup G} {X : Type*} [Group X] (hZN : center N = ⊥)
    (hZM : center M = ⊥) (eN : N ⧸ center N ≃* X) (eM : M ⧸ center M ≃* X) (φ : MulAut X) :
    N ≃* M :=
  (quotCenterEquivOfEqBot hZN).symm.trans
    (eN.trans (φ.trans (eM.symm.trans (quotCenterEquivOfEqBot hZM))))

theorem eM_mk_quotTransport {N M : Subgroup G} {X : Type*} [Group X] (hZN : center N = ⊥)
    (hZM : center M = ⊥) (eN : N ⧸ center N ≃* X) (eM : M ⧸ center M ≃* X) (φ : MulAut X)
    (n : N) :
    eM (QuotientGroup.mk (quotTransport hZN hZM eN eM φ n)) = φ (eN (QuotientGroup.mk n)) := by
  have h1 : quotTransport hZN hZM eN eM φ n =
      quotCenterEquivOfEqBot hZM (eM.symm (φ (eN ((quotCenterEquivOfEqBot hZN).symm n)))) := rfl
  rw [h1, ← quotCenterEquivOfEqBot_symm_apply hZM, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply, quotCenterEquivOfEqBot_symm_apply hZN]

theorem quotTransport_conj {N M : Subgroup G} {X : Type*} [Group X] (hZN : center N = ⊥)
    (hZM : center M = ⊥) (eN : N ⧸ center N ≃* X) (eM : M ⧸ center M ≃* X) {φ : MulAut X}
    {s t : G} (hsN : s ∈ normalizer (N : Set G)) (htM : t ∈ normalizer (M : Set G))
    (hφ : φ * normalizerQuotMulAut eN ⟨s, hsN⟩ * φ⁻¹ = normalizerQuotMulAut eM ⟨t, htM⟩)
    (n : N) :
    quotTransport hZN hZM eN eM φ (N.normalizerMonoidHom ⟨s, hsN⟩ n) =
      M.normalizerMonoidHom ⟨t, htM⟩ (quotTransport hZN hZM eN eM φ n) := by
  set β := quotTransport hZN hZM eN eM φ with hβ
  have hφ' : ∀ x, φ (normalizerQuotMulAut eN ⟨s, hsN⟩ x) =
      normalizerQuotMulAut eM ⟨t, htM⟩ (φ x) := by
    intro x
    rw [← hφ]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have key : eM (QuotientGroup.mk (β (N.normalizerMonoidHom ⟨s, hsN⟩ n))) =
      eM (QuotientGroup.mk (M.normalizerMonoidHom ⟨t, htM⟩ (β n))) := by
    rw [hβ, eM_mk_quotTransport]
    have h1 := normalizerQuotMulAut_apply eN ⟨s, hsN⟩ n
    have h2 := normalizerQuotMulAut_apply eM ⟨t, htM⟩ (β n)
    simp only [QuotientGroup.mk'_apply] at h1 h2
    rw [← h1, hφ', ← h2, hβ, eM_mk_quotTransport]
  have key' := eM.injective key
  have hinj : Function.Injective (QuotientGroup.mk : M → M ⧸ center M) := by
    intro a b hab
    have := congrArg (quotCenterEquivOfEqBot hZM) hab
    rwa [← quotCenterEquivOfEqBot_symm_apply hZM, ← quotCenterEquivOfEqBot_symm_apply hZM,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  exact hinj key'

theorem quotTransport_mem_centralizer_iff {N M : Subgroup G} {X : Type*} [Group X]
    (hZN : center N = ⊥) (hZM : center M = ⊥) (eN : N ⧸ center N ≃* X)
    (eM : M ⧸ center M ≃* X) {φ : MulAut X} {s t : G} (hsN : s ∈ normalizer (N : Set G))
    (htM : t ∈ normalizer (M : Set G))
    (hφ : φ * normalizerQuotMulAut eN ⟨s, hsN⟩ * φ⁻¹ = normalizerQuotMulAut eM ⟨t, htM⟩)
    (n : N) :
    (n : G) ∈ centralizer ({s} : Set G) ↔
      (quotTransport hZN hZM eN eM φ n : G) ∈ centralizer ({t} : Set G) := by
  set β := quotTransport hZN hZM eN eM φ with hβ
  have hc := quotTransport_conj hZN hZM eN eM hsN htM hφ n
  rw [← hβ] at hc
  have e1 : ∀ (H : Subgroup G) (a : G) (ha : a ∈ normalizer (H : Set G)) (h : H),
      ((h : G) ∈ centralizer ({a} : Set G) ↔ H.normalizerMonoidHom ⟨a, ha⟩ h = h) := by
    intro H a ha h
    rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    constructor
    · intro h1
      rw [← h1, mul_inv_cancel_right]
    · intro h1
      calc (h : G) * a = a * h * a⁻¹ * a := by rw [h1]
        _ = a * h := by group
  rw [e1 N s hsN n, e1 M t htM (β n), ← hc]
  exact β.injective.eq_iff.symm

end Transport

section Dichotomy


variable {G : Type} [Group G] [Finite G]

theorem exists_perfect_transport_core {L : Subgroup G} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K)
    (X₀ : Subgroup (adjointGroup .F4 K)) {t : G} {N M : Subgroup G} (hLN : L ≤ N)
    (hML : M ⊓ centralizer ({t} : Set G) = L) (hLt : L ≤ centralizer ({t} : Set G))
    (hEN : centralizerPerfectCore (subgroupToG e X₀) ≤ N) (β : N ≃* M)
    (hβ : ∀ n : N, (n : G) ∈ centralizer ({t} : Set G) →
      (β n : G) ∈ centralizer ({t} : Set G)) :
    ∃ (m : ℕ) (P : Subgroup G), m < 2 ∧ ⁅P, P⁆ = P ∧
      Nat.card P = Nat.card (centralizerPerfectCore (subgroupToG e X₀)) ∧ P ≤ M ∧
      ∀ p ∈ P, ∀ z ∈ X₀, p * ((e.symm ((graphAutF4 K ^ m) z) : L) : G) =
        ((e.symm ((graphAutF4 K ^ m) z) : L) : G) * p := by
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (adjointGroup .F4 K) := inferInstance
  have hLM : L ≤ M := by
    intro l hl
    rw [← hML] at hl
    exact hl.1
  have hmem : ∀ l : L, ((β ⟨l, hLN l.2⟩ : M) : G) ∈ L := by
    intro l
    have h1 : ((β ⟨l, hLN l.2⟩ : M) : G) ∈ M ⊓ centralizer ({t} : Set G) :=
      ⟨(β _).2, hβ _ (hLt l.2)⟩
    rwa [hML] at h1
  set f : L →* G := M.subtype.comp (β.toMonoidHom.comp (Subgroup.inclusion hLN)) with hfdef
  have hf : ∀ l : L, f l = ((β ⟨l, hLN l.2⟩ : M) : G) := fun l => rfl
  set βL : L →* L := f.codRestrict L (fun l => (hf l).symm ▸ hmem l) with hβLdef
  have hβL : ∀ l : L, ((βL l : L) : G) = ((β ⟨l, hLN l.2⟩ : M) : G) := fun l => rfl
  have hβLinj : Function.Injective βL := by
    intro a b hab
    have h1 : ((βL a : L) : G) = ((βL b : L) : G) := congrArg Subtype.val hab
    rw [hβL, hβL] at h1
    have h2 := β.injective (Subtype.ext h1)
    have h3 : (a : G) = b := Subtype.mk.inj h2
    exact Subtype.ext h3
  set θh : adjointGroup .F4 K →* adjointGroup .F4 K :=
    e.toMonoidHom.comp (βL.comp e.symm.toMonoidHom) with hθhdef
  have hθinj : Function.Injective θh := by
    intro a b hab
    exact e.symm.injective (hβLinj (e.injective hab))
  set θ : MulAut (adjointGroup .F4 K) :=
    MulEquiv.ofBijective θh ⟨hθinj, Finite.injective_iff_surjective.mp hθinj⟩ with hθdef
  have hθ : ∀ y, ((e.symm (θ y) : L) : G) = ((β ⟨(e.symm y : G), hLN (e.symm y).2⟩ : M) : G) := by
    intro y
    have h1 : θ y = e (βL (e.symm y)) := rfl
    rw [h1, MulEquiv.symm_apply_apply, hβL]
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form le_rfl K hK'
  obtain ⟨⟨x₁, m⟩, hxm, -⟩ := hnf θ
  set x : adjointGroup .F4 K := x₁ with hxdef
  have hθx : ∀ y, θ y = x * (graphAutF4 K ^ (m : ℕ)) y * x⁻¹ := by
    intro y
    rw [hxm]
    rfl
  set n : G := ((e.symm x : L) : G) with hndef
  have hnM : n ∈ M := hLM (e.symm x).2
  have hβz : ∀ y, ((β ⟨(e.symm y : G), hLN (e.symm y).2⟩ : M) : G) =
      n * ((e.symm ((graphAutF4 K ^ (m : ℕ)) y) : L) : G) * n⁻¹ := by
    intro y
    rw [← hθ, hθx, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
  have : Group.IsPerfect (centralizerPerfectCore (subgroupToG e X₀)) :=
    Subgroup.isPerfect_iff.2 (commutator_centralizerPerfectCore _)
  set γ : centralizerPerfectCore (subgroupToG e X₀) →* G :=
    (MulAut.conj n⁻¹).toMonoidHom.comp (M.subtype.comp (β.toMonoidHom.comp
      (Subgroup.inclusion hEN))) with hγdef
  have hγ : ∀ p : centralizerPerfectCore (subgroupToG e X₀),
      γ p = n⁻¹ * ((β ⟨p, hEN p.2⟩ : M) : G) * n := by
    intro p
    change n⁻¹ * _ * n⁻¹⁻¹ = _
    rw [inv_inv]
    rfl
  have hγinj : Function.Injective γ := by
    intro a b hab
    rw [hγ, hγ] at hab
    have h1 : ((β ⟨a, hEN a.2⟩ : M) : G) = ((β ⟨b, hEN b.2⟩ : M) : G) := by
      simpa using hab
    have h2 := β.injective (Subtype.ext h1)
    have h3 : (a : G) = b := Subtype.mk.inj h2
    exact Subtype.ext h3
  refine ⟨m, γ.range, by have := m.2; omega, commutator_monoidHom_range_eq_of_isPerfect γ, ?_, ?_,
    ?_⟩
  · exact (Nat.card_congr (MonoidHom.ofInjective hγinj).toEquiv).symm
  · rintro _ ⟨p, rfl⟩
    rw [hγ]
    exact mul_mem (mul_mem (inv_mem hnM) (β _).2) hnM
  · rintro _ ⟨p, rfl⟩ z hz
    rw [hγ]
    have hzX : ((e.symm z : L) : G) ∈ subgroupToG e X₀ := ⟨e.symm z, ⟨z, hz, rfl⟩, rfl⟩
    have hpz : (p : G) * ((e.symm z : L) : G) = ((e.symm z : L) : G) * p :=
      ((mem_centralizer_iff.1 (centralizerPerfectCore_le_centralizer _ p.2)) _ hzX).symm
    have hN : (⟨p, hEN p.2⟩ : N) * ⟨(e.symm z : G), hLN (e.symm z).2⟩ =
        ⟨(e.symm z : G), hLN (e.symm z).2⟩ * ⟨p, hEN p.2⟩ := Subtype.ext hpz
    have hM := congrArg (fun q : N => ((β q : M) : G)) hN
    simp only [map_mul, Subgroup.coe_mul] at hM
    rw [hβz] at hM
    set b : G := ((β ⟨p, hEN p.2⟩ : M) : G)
    set w : G := ((e.symm ((graphAutF4 K ^ (m : ℕ)) z) : L) : G)
    calc n⁻¹ * b * n * w = n⁻¹ * (b * (n * w * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * w * n⁻¹) * b) * n := by rw [hM]
      _ = w * (n⁻¹ * b * n) := by group

end Dichotomy

section Step3


@[expose] def TwoE6CoreNotDvdInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ¬ Nat.card (centralizerPerfectCore (subgroupToG e X₀)) ∣
        Nat.card (centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))

theorem twoE6CoreCardInput_of_notDvd (h : TwoE6CoreNotDvdInput) : TwoE6CoreCardInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' φ hφ g htM hML
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have htC := hw.mem_centralizer
  obtain ⟨hZ0, e₆₀, -⟩ := exists_mulEquiv_twoE6Span_of_family hK e X₀ htC hφ
  set e₆ : twoE6Span e X₀ ⧸ center (twoE6Span e X₀) ≃* adjointGroup TwistTag.E6.tag K := e₆₀
    with he₆def
  have hG₀ := commutator_twoE6Span e X₀
  have htN := mem_normalizer_twoE6Span e X₀ htC
  have hZodd : Odd (Nat.card (center (twoE6Span e X₀))) := by
    rw [hZ0, Subgroup.card_bot]
    exact odd_one
  rcases inf_centralizer_eq_or_xi_E6_quot_27 hw.standard hw.card_eq e htC hw.orderOf_eq hw.inf_eq
      hG₀ hZodd hw.card_eq e₆ htN with ⟨-, η, hη, φ₀, hφ₀⟩ | ⟨η, hη, hx, φ₀, hφ₀⟩
  swap
  · exact (false_of_le_of_conj_xi_E6 (le_twoE6Span e X₀) hw.center_eq_bot hw.card_eq e
      hw.card_eq e₆ htC htN hη hx hφ₀).elim
  set M := CFSG.conjugate (twoE6Span e X₀) g with hMdef
  have hLM : L ≤ M := fun x hx => by
    rw [← hML] at hx
    exact hx.1
  have hMp := E6Pilot.commutator_conjugate_eq hG₀ g
  have hZMc : Nat.card (center M) = 1 := by
    rw [hMdef, E6Pilot.card_center_conjugate, hZ0, Subgroup.card_bot]
  have hZM : center M = ⊥ := Subgroup.eq_bot_of_card_eq _ hZMc
  have hZModd : Odd (Nat.card (center M)) := by
    rw [hZMc]
    exact odd_one
  set eM := (E6Pilot.coverConjugateQuotientCenterEquiv (twoE6Span e X₀) g).symm.trans e₆
    with heMdef
  rcases inf_centralizer_eq_or_xi_E6_quot_27 hw.standard hw.card_eq e htC hw.orderOf_eq hw.inf_eq
      hMp hZModd hw.card_eq eM htM with ⟨-, η', hη', φ₁, hφ₁⟩ | ⟨η', hη', hx', φ₁, hφ₁⟩
  swap
  · exact (false_of_le_of_conj_xi_E6 hLM hw.center_eq_bot hw.card_eq e hw.card_eq eM htC htM hη'
      hx' hφ₁).elim
  have hηη' : η' = η := MulEquiv.ext fun x => Subtype.ext ((hη' x).trans (hη x).symm)
  rw [hηη'] at hφ₁
  set ψ := φ₁⁻¹ * φ₀ with hψdef
  have hψ : ψ * normalizerQuotMulAut e₆ ⟨t, htN⟩ * ψ⁻¹ = normalizerQuotMulAut eM ⟨t, htM⟩ := by
    calc ψ * normalizerQuotMulAut e₆ ⟨t, htN⟩ * ψ⁻¹ =
        φ₁⁻¹ * (φ₀ * normalizerQuotMulAut e₆ ⟨t, htN⟩ * φ₀⁻¹) * φ₁ := by
          rw [hψdef]
          group
      _ = φ₁⁻¹ * (φ₁ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ₁⁻¹) * φ₁ := by rw [hφ₀, hφ₁]
      _ = normalizerQuotMulAut eM ⟨t, htM⟩ := by group
  set β := quotTransport hZ0 hZM e₆ eM ψ with hβdef
  have hβ : ∀ n : twoE6Span e X₀, (n : G) ∈ centralizer ({t} : Set G) →
      (β n : G) ∈ centralizer ({t} : Set G) := fun n hn =>
    (quotTransport_mem_centralizer_iff hZ0 hZM e₆ eM htN htM hψ n).1 hn
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  obtain ⟨m, P, hm, hPp, hPc, hPM, hPX⟩ := exists_perfect_transport_core hK e X₀
    (le_twoE6Span e X₀) hML hLt (centralizerPerfectCore_le_twoE6Span e X₀) β hβ
  interval_cases m
  ·
    have hPC : P ≤ M ⊓ centralizer (subgroupToG e X₀ : Set G) := by
      refine le_inf hPM fun p hp => ?_
      rw [mem_centralizer_iff]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have h1 := hPX p hp z hz
      rw [pow_zero, MulAut.one_apply] at h1
      exact h1.symm
    rw [← hPc]
    exact Subgroup.card_le_of_le (CFSG.Quasithin.le_perfectCore_of_perfect hPC hPp)
  ·
    exfalso
    have hPY : P ≤ centralizer (subgroupToG (e.trans (graphAutF4 K).symm) X₀ : Set G) := by
      intro p hp
      rw [mem_centralizer_iff]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have h1 := hPX p hp z hz
      rw [pow_one] at h1
      have h2 : ((((e.trans (graphAutF4 K).symm).symm.toMonoidHom z) : L) : G) =
          ((e.symm (graphAutF4 K z) : L) : G) := by
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
      simp only [Subgroup.coe_subtype]
      rw [h2]
      exact h1.symm
    have hle := le_centralizerPerfectCore hPp hPY
    refine h G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' ?_
    rw [← hPc]
    exact Subgroup.card_dvd_of_le hle

theorem twoE6ConjugateInput_of_notDvd (h : TwoE6CoreNotDvdInput) : TwoE6ConjugateInput :=
  twoE6ConjugateInput_of_coreCard (twoE6CoreCardInput_of_notDvd h)

end Step3

end CFSG.SeitzReduction.F4Pilot
