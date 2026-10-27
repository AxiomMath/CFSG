module

public import CFSG.LargeExtraspecial.S8A5J
public import CFSG.LargeExtraspecial.S8CorBA5Statement
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
import CFSG.Adapters.WholeGroupLayer
public import CFSG.LargeExtraspecial.S8A5F
public import CFSG.LargeExtraspecial.S8Lin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Transfer

variable {Y X : Type*} [Group Y] [Group X]

theorem corBA5_map (e : Y ≃* X) {t : Y}
    (hA : ∀ R N : Subgroup Y, N ≤ R → R ≤ normalClosure ({t} : Set Y) →
      R ≤ centralizer ({t} : Set Y) → (∀ c : Y, c * t = t * c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
      ⁅R, R⁆ = R → ∀ (_ : (N.subgroupOf R).Normal), t ∈ N →
      IsSimpleGroup (↥R ⧸ N.subgroupOf R) → Nat.card (↥R ⧸ N.subgroupOf R) = 60 →
      IsExtraspecialPGroup 2 N → Nat.card N < 2 ^ 9) :
    ∀ R N : Subgroup X, N ≤ R → R ≤ normalClosure ({e t} : Set X) →
      R ≤ centralizer ({e t} : Set X) →
      (∀ c : X, c * e t = e t * c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
      ⁅R, R⁆ = R → ∀ (_ : (N.subgroupOf R).Normal), e t ∈ N →
      IsSimpleGroup (↥R ⧸ N.subgroupOf R) → Nat.card (↥R ⧸ N.subgroupOf R) = 60 →
      IsExtraspecialPGroup 2 N → Nat.card N < 2 ^ 9 := by
  intro R N hNR hRU hRt hRn hRp hNn htN hs h60 hext
  set R' : Subgroup Y := R.map (e.symm : X →* Y) with hR'
  set N' : Subgroup Y := N.map (e.symm : X →* Y) with hN'
  set eR : R' ≃* R := (e.symm.subgroupMap R).symm with heR
  have he : (N'.subgroupOf R').map eR.toMonoidHom = N.subgroupOf R := by
    ext x
    rw [mem_map_equiv, mem_subgroupOf, mem_subgroupOf]
    change e.symm (x : X) ∈ N.map e.symm.toMonoidHom ↔ (x : X) ∈ N
    rw [mem_map_equiv, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have hcomap : N'.subgroupOf R' = (N.subgroupOf R).comap eR.toMonoidHom := by
    rw [← he, comap_map_eq_self_of_injective eR.injective]
  have hN'n : (N'.subgroupOf R').Normal := by
    rw [hcomap]
    exact hNn.comap _
  set eQ : (↥R' ⧸ N'.subgroupOf R') ≃* (↥R ⧸ N.subgroupOf R) :=
    QuotientGroup.congr (N'.subgroupOf R') (N.subgroupOf R) eR he with heQ
  have hs' : IsSimpleGroup (↥R' ⧸ N'.subgroupOf R') := eQ.isSimpleGroup
  have hUmap : (normalClosure ({t} : Set Y)).map (e : Y →* X) =
      normalClosure ({e t} : Set X) := by
    rw [map_normalClosure _ _ e.surjective, Set.image_singleton, MonoidHom.coe_ofClass]
  have hR'U : R' ≤ normalClosure ({t} : Set Y) := by
    rintro _ ⟨r, hr, rfl⟩
    have h := hRU hr
    rw [← hUmap] at h
    obtain ⟨u, hu, rfl⟩ := h
    simpa using hu
  have hR't : R' ≤ centralizer ({t} : Set Y) := by
    rintro _ ⟨r, hr, rfl⟩
    have hrc := mem_centralizer_singleton_iff.mp (hRt hr)
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    simpa using hrc
  have hR'n : ∀ c : Y, c * t = t * c → ∀ r ∈ R', c * r * c⁻¹ ∈ R' := by
    rintro c hc _ ⟨r, hr, rfl⟩
    have hc' : e c * e t = e t * e c := by rw [← map_mul, hc, map_mul]
    refine ⟨e c * r * (e c)⁻¹, hRn (e c) hc' r hr, ?_⟩
    simp
  have hR'p : ⁅R', R'⁆ = R' := by rw [hR', ← map_commutator, hRp]
  have htN' : t ∈ N' := ⟨e t, htN, by simp⟩
  have h60' : Nat.card (↥R' ⧸ N'.subgroupOf R') = 60 := (Nat.card_congr eQ.toEquiv).trans h60
  have hext' : IsExtraspecialPGroup 2 N' :=
    CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv (e.symm.subgroupMap N) hext
  have := hA R' N' (map_mono hNR) hR'U hR't hR'n hR'p hN'n htN' hs' h60' hext'
  rwa [hN', card_map_of_injective e.symm.injective] at this

end Transfer

theorem corB_trichotomy_A5 (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hA5 : CorBListA5Facts) {X : Type u} [Group X] [Finite X] {t : X} (ht : orderOf t = 2)
    (h1p : IsPGroup 2 (closure (conjCent t)))
    (h1c : ⁅⁅closure (conjCent t), closure (conjCent t)⁆, closure (conjCent t)⁆ = ⊥)
    (h2 : ∀ τ : X, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ)) :
    (∃ K : Subgroup X, K.Normal ∧ Odd (Nat.card K) ∧ normalClosure {t} = K ⊔ zpowers t) ∨
    (∀ x ∈ normalClosure ({t} : Set X), ∀ y ∈ normalClosure ({t} : Set X),
      x * y = y * x ∧ x * x = 1) ∨
    (IsSimpleGroup (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X))) ∧
      (∃ k, derivedSeries X k ≤
        normalClosure ({t} : Set X) ⊔ centralizer (normalClosure ({t} : Set X) : Set X)) ∧
      ∀ R N : Subgroup X, N ≤ R → R ≤ normalClosure ({t} : Set X) →
        R ≤ centralizer ({t} : Set X) → (∀ c : X, c * t = t * c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
        ⁅R, R⁆ = R → ∀ (_ : (N.subgroupOf R).Normal), t ∈ N →
        IsSimpleGroup (↥R ⧸ N.subgroupOf R) → Nat.card (↥R ⧸ N.subgroupOf R) = 60 →
        IsExtraspecialPGroup 2 N → Nat.card N < 2 ^ 9) := by
  set e : Shrink.{0} X ≃* X := Shrink.mulEquiv with he
  set t' : Shrink.{0} X := e.symm t with ht'
  have het : e t' = t := e.apply_symm_apply t
  have hW : (closure (conjCent t')).map (e : Shrink.{0} X →* X) = closure (conjCent t) := by
    rw [map_closure_conjCent, het]
  have ho' : orderOf t' = 2 := by rw [ht', MulEquiv.orderOf_eq]; exact ht
  have h1p' : IsPGroup 2 (closure (conjCent t')) := by
    have := h1p.comap_of_injective (e : Shrink.{0} X →* X) e.injective
    rwa [← hW, comap_map_eq_self_of_injective e.injective] at this
  have h1c' : ⁅⁅closure (conjCent t'), closure (conjCent t')⁆, closure (conjCent t')⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective (f := (e : Shrink.{0} X →* X)) _ e.injective).mp
    rw [map_commutator, map_commutator, hW]
    exact h1c
  have h2' : ∀ τ, τ * t' = t' * τ → IsConj t' τ → τ ≠ t' → IsConj t' (t' * τ) := by
    intro τ hτ hc hne
    have h := h2 (e τ) (by rw [← het, ← map_mul, hτ, map_mul])
      (by rw [← het]; exact (e : Shrink.{0} X →* X).map_isConj hc)
      (fun h => hne (e.injective (h.trans het.symm)))
    have := (e.symm : X →* Shrink.{0} X).map_isConj h
    rwa [MonoidHom.coe_ofClass, map_mul, e.symm_apply_apply] at this
  have hU : (normalClosure ({t'} : Set (Shrink.{0} X))).map (e : Shrink.{0} X →* X) =
      normalClosure ({t} : Set X) := by
    rw [map_normalClosure _ _ e.surjective, Set.image_singleton, MonoidHom.coe_ofClass, het]
  rcases hCorB (Shrink.{0} X) t' ho' h1p' h1c' h2' with ⟨K', hK'U, hK'n, hK'odd, hUK'⟩ | hab |
    hlist
  ·
    left
    have ht't' : t' * t' = 1 := by rw [← pow_two, ← ho']; exact pow_orderOf_eq_one t'
    have ht'1 : t' ≠ 1 := fun h => by
      rw [h, orderOf_one] at ho'
      exact absurd ho' (by norm_num)
    have hK'N := normal_of_sup_zpowers normalClosure_normal hK'U hK'n hK'odd ht't' ht'1 hUK'
    refine ⟨K'.map (e : Shrink.{0} X →* X), hK'N.map _ e.surjective, ?_, ?_⟩
    · rw [card_map_of_injective e.injective]
      exact hK'odd
    · rw [← hU, hUK', Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.coe_ofClass, het]
  ·
    right; left
    rw [← hU]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨hxy, hxx⟩ := hab x hx y hy
    exact ⟨by rw [← map_mul, ← map_mul, hxy], by rw [← map_mul, hxx, map_one]⟩
  ·
    right; right
    obtain ⟨hsimp, hder, -⟩ := hFacts (Shrink.{0} X) _ normalClosure_normal hlist
    have hE := corBA5_map e (hA5 (Shrink.{0} X) t' ho' h1p' h1c' h2' hlist)
    rw [het] at hE
    refine ⟨?_, ?_, hE⟩
    · rw [← hU]
      exact isSimpleGroup_quotient_center_map e _
    · rw [← hU]
      exact exists_derivedSeries_le_map e
        (hder (commutator_normalClosure_eq_of_isConj_mul ho' h2' hsimp))

section Perfect

variable {X : Type*} [Group X]

theorem odd_orderOf_of_mem_center_normalClosure [Finite X] {t : X}
    (hO2 : ∀ P : Subgroup X, CFSG.Open.IsSubnormal P ⊤ → IsPGroup 2 P → P = ⊥) :
    ∀ z ∈ center ↥(normalClosure ({t} : Set X)), Odd (orderOf z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := normalClosure ({t} : Set X) with hU
  have hUn : U.Normal := normalClosure_normal
  intro z hz
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have h0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  set w := z ^ (orderOf z / 2) with hw
  have hwo : orderOf w = 2 := orderOf_pow_orderOf_div h0 (even_iff_two_dvd.mp hev)
  have hwc : w ∈ center ↥U := pow_mem hz _
  have hwX : orderOf (w : X) = 2 := by rw [Subgroup.orderOf_coe, hwo]
  have hsub : CFSG.Open.IsSubnormal (zpowers (w : X)) ⊤ := by
    refine CFSG.Open.IsSubnormal.step (zpowers_le.mpr w.2) ⟨fun n hn u => ?_⟩
      (CFSG.Open.IsSubnormal.step le_top ⟨fun n hn x => ?_⟩ (CFSG.Open.IsSubnormal.refl ⊤))
    · rw [mem_subgroupOf] at hn ⊢
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
      have hwu : (u : X) * w = w * u := congrArg Subtype.val ((mem_center_iff.mp hwc u))
      change (u : X) * n * (u : X)⁻¹ ∈ zpowers (w : X)
      rw [← hk, (Commute.zpow_right hwu k).eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers _) k
    · rw [mem_subgroupOf] at hn ⊢
      exact hUn.conj_mem _ hn _
  have h2 : IsPGroup 2 (zpowers (w : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwX, pow_one])
  have hbot := hO2 _ hsub h2
  have : (w : X) ∈ zpowers (w : X) := mem_zpowers _
  rw [hbot, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hwX
  exact absurd hwX (by norm_num)

theorem le_normalClosure_of_perfect [Finite X] {t : X} (htt : t * t = 1) (ht1 : t ≠ 1)
    (hO2 : ∀ P : Subgroup X, CFSG.Open.IsSubnormal P ⊤ → IsPGroup 2 P → P = ⊥)
    (hO3 : Nat.card (timmesfeldOddCore X) ∣ 3)
    (hE : CFSG.Open.IsQuasisimple (timmesfeldLayer X))
    (hF : timmesfeldFStar X = timmesfeldOddCore X ⊔ timmesfeldLayer X)
    (hB : centralizer (timmesfeldFStar X : Set X) ≤ timmesfeldFStar X)
    (hsimpU : IsSimpleGroup
      (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X))))
    (hder : ∃ k, derivedSeries X k ≤
      normalClosure ({t} : Set X) ⊔ centralizer (normalClosure ({t} : Set X) : Set X))
    {R : Subgroup X} (hR : ⁅R, R⁆ = R) : R ≤ normalClosure ({t} : Set X) := by
  set U := normalClosure ({t} : Set X) with hU
  have hUn : U.Normal := normalClosure_normal
  have hperf := commutator_eq_top_normalClosure htt (odd_orderOf_of_mem_center_normalClosure hO2)
    hsimpU
  have hUE := normalClosure_eq_layer ht1 hperf hsimpU hE
  have hCC := commutator_commutator_centralizer_eq_bot hO3 hF hB
  rw [← hUE] at hCC
  obtain ⟨k, hk⟩ := hder
  set C := centralizer (U : Set X) with hC
  have hXU : derivedSeries X (k + 2) ≤ U := by
    have h1 : derivedSeries X (k + 1) ≤ U ⊔ ⁅C, C⁆ := by
      rw [derivedSeries_succ]
      exact (commutator_mono hk hk).trans commutator_sup_le_sup_commutator
    rw [derivedSeries_succ]
    refine (commutator_mono h1 h1).trans (commutator_sup_le_sup_commutator.trans ?_)
    rw [hCC, sup_bot_eq]
  have hRd : ∀ j, R ≤ derivedSeries X j := by
    intro j
    induction j with
    | zero => exact le_top
    | succ j ih =>
      rw [derivedSeries_succ]
      exact hR.symm.le.trans (commutator_mono ih ih)
  exact (hRd (k + 2)).trans hXU

end Perfect

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem corB_hyps_Mbar {t : S.O} (htM : t ∈ S.Mbar)
    (h1p : IsPGroup 2 (closure (conjCentM S t)))
    (h1c : ⁅⁅closure (conjCentM S t), closure (conjCentM S t)⁆, closure (conjCentM S t)⁆ = ⊥)
    (h2 : ∀ τ ∈ conjCentM S t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t) :
    IsPGroup 2 (closure (conjCent (⟨t, htM⟩ : S.Mbar))) ∧
      ⁅⁅closure (conjCent (⟨t, htM⟩ : S.Mbar)), closure (conjCent (⟨t, htM⟩ : S.Mbar))⁆,
        closure (conjCent (⟨t, htM⟩ : S.Mbar))⁆ = ⊥ ∧
      ∀ τ : S.Mbar, τ * ⟨t, htM⟩ = ⟨t, htM⟩ * τ → IsConj ⟨t, htM⟩ τ → τ ≠ ⟨t, htM⟩ →
        IsConj (⟨t, htM⟩ : S.Mbar) (⟨t, htM⟩ * τ) := by
  set tX : S.Mbar := ⟨t, htM⟩ with htX
  have himage : S.Mbar.subtype '' conjCent tX = conjCentM S t := by
    ext τ
    constructor
    · rintro ⟨τ', ⟨hc, hconj⟩, rfl⟩
      obtain ⟨c, hc'⟩ := isConj_iff.mp hconj
      exact ⟨τ'.2, congrArg Subtype.val hc, c, c.2, by rw [← hc']; rfl⟩
    · rintro ⟨hτM, hτt, x, hxM, hxτ⟩
      exact ⟨⟨τ, hτM⟩, ⟨Subtype.ext hτt, isConj_iff.mpr ⟨⟨x, hxM⟩, Subtype.ext hxτ.symm⟩⟩, rfl⟩
  have hmapW : (closure (conjCent tX)).map S.Mbar.subtype = closure (conjCentM S t) := by
    rw [MonoidHom.map_closure, himage]
  refine ⟨?_, ?_, ?_⟩
  · have := h1p.comap_of_injective S.Mbar.subtype S.Mbar.subtype_injective
    rwa [← hmapW, comap_map_eq_self_of_injective S.Mbar.subtype_injective] at this
  · apply (map_eq_bot_iff_of_injective _ S.Mbar.subtype_injective).mp
    rw [map_commutator, map_commutator, hmapW]
    exact h1c
  · intro τ hτt hconj hne
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hmem : (τ : S.O) ∈ conjCentM S t :=
      ⟨τ.2, congrArg Subtype.val hτt, c, c.2, by rw [← hc]; rfl⟩
    obtain ⟨y, hyM, hy⟩ := h2 τ hmem fun h => hne (Subtype.ext h)
    refine isConj_iff.mpr ⟨⟨y, hyM⟩ * c, Subtype.ext ?_⟩
    have hc' : (c : S.O) * t * (c : S.O)⁻¹ = τ := congrArg Subtype.val hc
    calc ((⟨y, hyM⟩ * c : S.Mbar) : S.O) * t * ((⟨y, hyM⟩ * c : S.Mbar) : S.O)⁻¹ =
        y * ((c : S.O) * t * (c : S.O)⁻¹) * y⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_mk]; group
      _ = (τ : S.O) * t := by rw [hc', hy]
      _ = t * τ := (congrArg Subtype.val hτt)

theorem RbarX_RmodN (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    RbarX haQ t (RmodN S g t) = Rbar S g t := by
  refine le_antisymm (RbarX_le_Rbar haQ t _) fun x hx => mem_RbarX.mpr ⟨hx, ?_⟩
  rw [← range_resV haQ t]
  exact ⟨_, rfl⟩

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem false_of_list_A5 (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {tX : S.Mbar}
    (htX : (tX : S.O) = t)
    (hsimpU : IsSimpleGroup
      (↥(normalClosure ({tX} : Set S.Mbar)) ⧸ center ↥(normalClosure ({tX} : Set S.Mbar))))
    (hder : ∃ k, derivedSeries S.Mbar k ≤ normalClosure ({tX} : Set S.Mbar) ⊔
      centralizer (normalClosure ({tX} : Set S.Mbar) : Set S.Mbar))
    (hA : ∀ R N : Subgroup S.Mbar, N ≤ R → R ≤ normalClosure ({tX} : Set S.Mbar) →
      R ≤ centralizer ({tX} : Set S.Mbar) →
      (∀ c : S.Mbar, c * tX = tX * c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
      ⁅R, R⁆ = R → ∀ (_ : (N.subgroupOf R).Normal), tX ∈ N →
      IsSimpleGroup (↥R ⧸ N.subgroupOf R) → Nat.card (↥R ⧸ N.subgroupOf R) = 60 →
      IsExtraspecialPGroup 2 N → Nat.card N < 2 ^ 9) : False := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htXX : tX * tX = 1 := Subtype.ext (by rw [Subgroup.coe_mul, htX, htt]; rfl)
  have htX1 : tX ≠ 1 := fun h => ht1 (by rw [← htX, h]; rfl)
  have hd := eight_le_finrank_WV hCE hNo hΩ D hm2 hmin hA7
  have hw := D.finrank_WV
  obtain ⟨hO3, hEq, hF⟩ := S5.timmesfeld_5_5 hCE hIrr H hNo C (S45Q.hyp45Q H C) (by omega)
  have hB : centralizer (timmesfeldFStar S.Mbar : Set S.Mbar) ≤ timmesfeldFStar S.Mbar :=
    CFSG.Adapters.centralizer_timmesfeldFStar_le _
  have hmin' : ∀ U : Submodule (ZMod 2) (Vt S g t), finrank (ZMod 2) U = 2 →
      ∃ u ∈ U, D.Q u ≠ 0 := fun U hU => by
    by_contra hcon
    push Not at hcon
    have := hmin U hcon
    omega
  have h4 : finrank (ZMod 2) (Vt S g t) = 4 := by rw [D.hdim, hm2]
  obtain ⟨hs, -⟩ : IsSimpleGroup (RmodN S g t) ∧ ¬ ∀ x y : RmodN S g t, x * y = y * x := by
    rw [D.hX]
    exact isSimpleGroup_omegaGroup_minus_four D.hQ h4 hmin'
  have h60 : Nat.card (RmodN S g t) = 60 := by
    rw [D.hX]
    exact card_omegaGroup_minus_four D.hQ h4 hmin'
  have hNn := normal_NbarX haQ (t := t) (RmodN S g t)
  have hRX := RbarX_RmodN haQ t
  have hmemR : ∀ r : S.Mbar, r ∈ (RbarX haQ t (RmodN S g t)).subgroupOf S.Mbar ↔
      (r : S.O) ∈ Rbar S g t := fun r => by rw [mem_subgroupOf, hRX]
  have hRp : ⁅(RbarX haQ t (RmodN S g t)).subgroupOf S.Mbar,
      (RbarX haQ t (RmodN S g t)).subgroupOf S.Mbar⁆ =
      (RbarX haQ t (RmodN S g t)).subgroupOf S.Mbar := by
    apply Subgroup.map_injective S.Mbar.subtype_injective
    rw [Subgroup.map_commutator, subgroupOf_map_subtype, hRX, inf_eq_left.mpr Rbar_le_Mbar,
      commutator_Rbar_eq_A5 hNo hΩ D hm2 hmin hA7]
  have hNR : NbarM S g t ≤ (RbarX haQ t (RmodN S g t)).subgroupOf S.Mbar := fun n hn =>
    Nbar_le_RbarX haQ (RmodN S g t) hn
  have hRU := le_normalClosure_of_perfect htXX htX1 eq_bot_of_isSubnormal_top_Mbar hO3 hEq hF hB
    hsimpU hder hRp
  have hRt : (RbarX haQ t (RmodN S g t)).subgroupOf S.Mbar ≤ centralizer ({tX} : Set S.Mbar) :=
    fun r hr => mem_centralizer_singleton_iff.mpr (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, htX]
      exact commute_of_mem_Rbar haQ ((hmemR r).mp hr)))
  have hRn : ∀ c : S.Mbar, c * tX = tX * c →
      ∀ r ∈ (RbarX haQ t (RmodN S g t)).subgroupOf S.Mbar,
        c * r * c⁻¹ ∈ (RbarX haQ t (RmodN S g t)).subgroupOf S.Mbar := by
    intro c hc r hr
    rw [hmemR] at hr ⊢
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp c.2
    have hkt : S.ρ k * t = t * S.ρ k := by
      rw [hk, ← htX]
      exact congrArg Subtype.val hc
    have := conj_mem_Rbar hkt hr
    rw [hk] at this
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  have htN : tX ∈ NbarM S g t := by
    show (tX : S.O) ∈ Nbar S g t
    rw [htX]
    exact self_mem_Nbar H ht
  have hs' := (quotEquivX haQ t (le_refl (RmodN S g t))).isSimpleGroup
  have h60' := (Nat.card_congr (quotEquivX haQ t (le_refl (RmodN S g t))).toEquiv).trans h60
  have hNM : Nbar S g t ≤ S.Mbar := fun x hx => Rbar_le_Mbar (Nbar_le_Rbar hx)
  have hext : IsExtraspecialPGroup 2 (NbarM S g t) :=
    CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hNM).symm (timmesfeld_8_5 hNo hΩ D hA7)
  have hlt := hA _ _ hNR hRU hRt hRn hRp hNn htN hs' h60' hext
  have hcard : Nat.card (NbarM S g t) = 2 ^ (2 * S.width - 4 * D.m + 1) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv).trans D.card_Nbar
  have hle : 2 ^ 9 ≤ 2 ^ (2 * S.width - 4 * D.m + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hcard] at hlt
  exact absurd hlt (not_lt.mpr hle)

theorem false_of_allBad_A5 (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hA5 : CorBListA5Facts) (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
    (hall : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ ≠ t →
      ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    False := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have hflag : ∀ τ ∈ conjCentM S t, (∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∧
      ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
    intro τ hτ
    refine ⟨step1_fix_Vt_A5 hCE hNo hΩ D hm2 hmin hA7 τ hτ, fun w hw => ?_⟩
    obtain ⟨-, hτt, x, hxM, rfl⟩ := hτ
    by_cases hxt : x * t * x⁻¹ = t
    · have hw' : w ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [(commSpace_t_eq H C ht ht1 hVQ).2]
        exact hw
      rw [hxt, mem_fixSpace.mp hw', sub_self]
      exact zero_mem _
    · exact hall x hxM hτt hxt w hw
  have hW : closure (conjCentM S t) ≤ flagGroup S (Vt S g t) (Wt S g t) :=
    (closure_le _).mpr fun τ hτ => mem_flagGroup_of_fix (hflag τ hτ).1 (hflag τ hτ).2
  have h2 : ∀ τ ∈ conjCentM S t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t := by
    intro τ hτ hne
    have hbad := (hflag τ hτ).2
    obtain ⟨-, hτt, x, hxM, hxτ⟩ := hτ
    obtain ⟨n, hnN, hnτ⟩ :=
      exists_Nbar_conj_eq_mul_of_bad hCE hNo hΩ D hm2 hmin hA7 hxM hxτ hτt hne hbad
    exact ⟨n, Rbar_le_Mbar (Nbar_le_Rbar hnN), hnτ⟩
  obtain ⟨h1p', h1c', h2'⟩ := corB_hyps_Mbar htM (isPGroup_of_le_flagGroup hW)
    (commutator_commutator_eq_bot_of_le_flagGroup (Vt_le_Wt H ht1) hW) h2
  set tX : S.Mbar := ⟨t, htM⟩ with htXdef
  have htXX : tX * tX = 1 := Subtype.ext htt
  have htX1 : tX ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have htXo : orderOf tX = 2 := orderOf_eq_prime (by rw [pow_two]; exact htXX) htX1
  rcases corB_trichotomy_A5 hCorB hFacts hA5 htXo h1p' h1c' h2' with ⟨K, hKN, hKodd, hUK⟩ |
    hab | ⟨hsimpU, hder, hE⟩
  ·
    have hd := eight_le_finrank_WV hCE hNo hΩ D hm2 hmin hA7
    have hw := D.finrank_WV
    obtain ⟨hO3, -, -⟩ := S5.timmesfeld_5_5 hCE hIrr H hNo C (S45Q.hyp45Q H C) (by omega)
    apply hA7
    refine le_antisymm (inf_le_right.trans
      (Nbar_le_zpowers_of_oddCore H ht ht1 D.isPGroup_Nbar hO3 hKN hKodd hUK)) ?_
    rw [zpowers_le]
    exact ⟨ht, self_mem_Nbar H ht⟩
  ·
    have hU2 : IsPGroup 2 (normalClosure ({tX} : Set S.Mbar)) := fun u =>
      ⟨1, Subtype.ext (by
        rw [SubmonoidClass.coe_pow, Subgroup.coe_one, pow_one, pow_two]
        exact (hab u u.2 u u.2).2)⟩
    have hsub : IsSubnormal (normalClosure ({tX} : Set S.Mbar)) ⊤ :=
      IsSubnormal.step le_top ⟨fun n hn x => by
        rw [mem_subgroupOf] at hn ⊢
        exact normalClosure_normal.conj_mem _ hn _⟩ (IsSubnormal.refl ⊤)
    have hbot := eq_bot_of_isSubnormal_top_Mbar _ hsub hU2
    have : tX ∈ normalClosure ({tX} : Set S.Mbar) := subset_normalClosure (Set.mem_singleton _)
    rw [hbot, Subgroup.mem_bot] at this
    exact htX1 this
  ·
    exact false_of_list_A5 hCE hIrr hNo hΩ D hm2 hmin hA7 rfl hsimpU hder hE

theorem timmesfeld83A5Good_of_corB (hA5 : CorBListA5Facts) : Timmesfeld83A5Good.{u} := by
  intro G _ _ S g hCorB hFacts hCE hIrr H hNo C t ht ht1 hVQ hΩ D hm2 hmin hA7 _
  by_contra hall
  push Not at hall
  exact false_of_allBad_A5 hCorB hFacts hA5 hCE hIrr hNo hΩ D hm2 hmin hA7 hall

end CFSG.LargeExtraspecial.S8
