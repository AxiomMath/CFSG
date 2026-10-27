module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

namespace E8Layer6

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh CFSG.Open TauCeti
open CFSG.LieType.Steinberg.TwistedE6 CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem dvd_cube_add_one_of_orderOf_six {p : ℕ} [hp : Fact p.Prime] {N : ℕ}
    (h : orderOf ((N : ZMod p)) = 6) : p ∣ N ^ 3 + 1 := by
  have h6 : (N : ZMod p) ^ 6 = 1 := by
    have := pow_orderOf_eq_one (N : ZMod p)
    rw [h] at this
    exact this
  have h3 : (N : ZMod p) ^ 3 ≠ 1 := by
    intro h3
    have hd : orderOf (N : ZMod p) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [h] at hd
    norm_num at hd
  have hmul : ((N : ZMod p) ^ 3 - 1) * ((N : ZMod p) ^ 3 + 1) = 0 := by
    have e : ((N : ZMod p) ^ 3 - 1) * ((N : ZMod p) ^ 3 + 1) = (N : ZMod p) ^ 6 - 1 := by
      ring
    rw [e, h6, sub_self]
  rcases mul_eq_zero.1 hmul with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) h3
  · have h2 : ((N ^ 3 + 1 : ℕ) : ZMod p) = 0 := by
      push_cast
      exact h1
    exact (ZMod.natCast_eq_zero_iff _ _).1 h2

theorem exists_orderOf_statedSU3 {K : Type} [Field K] [Finite K] {c f : ℕ} [Fact c.Prime]
    [CharP K c] {p : ℕ} [Fact p.Prime] (hK : Nat.card K = (c ^ f) ^ 2)
    (hdvd : p ∣ (c ^ f) ^ 3 + 1) :
    ∃ a : ↥(StatedSU 3 (c ^ f) K), orderOf a = p := by
  refine exists_prime_orderOf_dvd_card' p ?_
  rw [CFSG.SectionRank.OddCover.card_statedSU_three hK]
  exact Dvd.dvd.mul_left hdvd _

section Main


theorem exists_orderOf_statedSU3' {K : Type} [Field K] [Finite K] {N c f : ℕ} [Fact c.Prime]
    [CharP K c] {p : ℕ} [Fact p.Prime] (hN : N = c ^ f) (hK : Nat.card K = N ^ 2)
    (hdvd : p ∣ N ^ 3 + 1) : ∃ a : ↥(StatedSU 3 N K), orderOf a = p := by
  subst hN
  exact exists_orderOf_statedSU3 hK hdvd

@[expose] def TwE8SCLayer : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid),
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (θ : K →+* K),
      Nat.card K = q.card ^ 2 ∧ CharP K q.p ∧ (∀ c, θ c = c ^ q.card) ∧
      ∃ (P S : Subgroup (Cat ⟨.E8 q, hv⟩)) (Ψ : ↥(fixedGroup K θ) →* ↥P),
        Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center ↥(fixedGroup K θ) ∧
        Nonempty (↥S ≃* ↥(StatedSU 3 q.card K)) ∧
        (∀ l ∈ P, ∀ s ∈ S, l * s = s * l) ∧ (∀ x ∈ S, x ∈ P → x ^ 3 = 1)

theorem e8E6LayerInput6_of_twE8SCLayer (hL : TwE8SCLayer) :
    CFSG.LieType.SeitzGeneration.ExcHigh.E8E6LayerInput6 := by
  intro q hv p hp h7 _hpq hord
  haveI : Fact p.Prime := ⟨hp⟩
  unfold TwE8SCLayer at hL
  obtain ⟨K, hKf, hKfin, θ, hKcard, hCh, hθq, P, S, Ψ, hΨsurj, hΨker, ⟨e⟩, hcomm, hdisj⟩ :=
    hL q hv
  have hcardpow : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hq2 : 2 ≤ q.card := by
    rw [hcardpow]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow (by have := q.exponent_pos; omega) _)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    nlinarith [hq2]
  have hθ2 : ∀ c, θ (θ c) = c := fun c => by
    rw [hθq, hθq]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hKcard c
  have hsc := fixedGroup_isQuasisimple_of_four_le_card θ hθ2 hK4
  have hMM : ⁅(⊤ : Subgroup ↥(fixedGroup K θ)), (⊤ : Subgroup ↥(fixedGroup K θ))⁆ = ⊤ :=
    Group.isPerfect_def.1 hsc.1
  have hisoS : Function.Surjective (CFSG.LieType.Simplicity.twistedIsogeny θ hθ2 hK4) :=
    CFSG.LieType.Simplicity.twistedIsogeny_surjective θ hθ2 hK4
  have hisoK : (CFSG.LieType.Simplicity.twistedIsogeny θ hθ2 hK4).ker =
      Subgroup.center ↥(fixedGroup K θ) :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.ker_twistedIsogeny_eq_center hθ2 hK4
  have hZD : Subgroup.center ↥⁅twistedFixedGroup TwistTag.E6 K θ,
      twistedFixedGroup TwistTag.E6 K θ⁆ = ⊥ := by
    rw [E8Layer.center_eq_map_of_perfect hisoS hisoK.le hMM, ← hisoK]
    refine eq_bot_iff.2 ?_
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.mem_bot]
    exact MonoidHom.mem_ker.1 hg
  have hfDsurj : Function.Surjective ((QuotientGroup.mk' (Subgroup.center
      ↥⁅twistedFixedGroup TwistTag.E6 K θ, twistedFixedGroup TwistTag.E6 K θ⁆)).comp
      (CFSG.LieType.Simplicity.twistedIsogeny θ hθ2 hK4)) :=
    (QuotientGroup.mk'_surjective _).comp hisoS
  have hfDker : ((QuotientGroup.mk' (Subgroup.center
      ↥⁅twistedFixedGroup TwistTag.E6 K θ, twistedFixedGroup TwistTag.E6 K θ⁆)).comp
      (CFSG.LieType.Simplicity.twistedIsogeny θ hθ2 hK4)).ker =
      Subgroup.center ↥(fixedGroup K θ) := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZD, Subgroup.mem_bot, ← hisoK, MonoidHom.mem_ker]
  have hΨ' : Ψ.ker ≤ ((QuotientGroup.mk' (Subgroup.center
      ↥⁅twistedFixedGroup TwistTag.E6 K θ, twistedFixedGroup TwistTag.E6 K θ⁆)).comp
      (CFSG.LieType.Simplicity.twistedIsogeny θ hθ2 hK4)).ker :=
    hΨker.trans hfDker.ge
  let F : ↥P →* CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K θ) :=
    (QuotientGroup.lift Ψ.ker _ hΨ').comp
      (QuotientGroup.quotientKerEquivOfSurjective Ψ hΨsurj).symm.toMonoidHom
  have hF : ∀ g, F (Ψ g) = (QuotientGroup.mk' (Subgroup.center
      ↥⁅twistedFixedGroup TwistTag.E6 K θ, twistedFixedGroup TwistTag.E6 K θ⁆)).comp
      (CFSG.LieType.Simplicity.twistedIsogeny θ hθ2 hK4) g := by
    intro g
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective Ψ hΨsurj).symm (Ψ g) =
        (g : ↥(fixedGroup K θ) ⧸ Ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift Ψ.ker _ hΨ' ((QuotientGroup.quotientKerEquivOfSurjective Ψ hΨsurj).symm
      (Ψ g)) = _
    rw [h1]
    rfl
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨g, rfl⟩ := hfDsurj y
    exact ⟨Ψ g, hF g⟩
  have hFker : F.ker = Subgroup.center ↥P := by
    ext x
    rw [MonoidHom.mem_ker, E8Layer.center_eq_map_of_perfect hΨsurj hΨker hMM]
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := hΨsurj x
      rw [hF] at hx
      have hg : g ∈ ((QuotientGroup.mk' (Subgroup.center
          ↥⁅twistedFixedGroup TwistTag.E6 K θ, twistedFixedGroup TwistTag.E6 K θ⁆)).comp
          (CFSG.LieType.Simplicity.twistedIsogeny θ hθ2 hK4)).ker :=
        MonoidHom.mem_ker.2 hx
      rw [hfDker] at hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      rw [hF]
      have hg' : g ∈ ((QuotientGroup.mk' (Subgroup.center
          ↥⁅twistedFixedGroup TwistTag.E6 K θ, twistedFixedGroup TwistTag.E6 K θ⁆)).comp
          (CFSG.LieType.Simplicity.twistedIsogeny θ hθ2 hK4)).ker := by
        rw [hfDker]
        exact hg
      exact MonoidHom.mem_ker.1 hg'
  have hcenP : Nat.card (Subgroup.center ↥P) ∣ 3 := by
    have h1 := E8Layer.card_center_dvd_of_perfect hΨsurj hΨker hMM
    have h2 := (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
      (θ := θ) (q := q.card) hKcard hθq).1
    exact dvd_trans h1 (by rw [h2]; exact Nat.gcd_dvd_left 3 _)
  obtain ⟨bq⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q
    (LieTypeIndex.valid_twistedE6 q) K hKcard θ hθq
  let π : ↥P →* Cat ⟨.twistedE6 q, LieTypeIndex.valid_twistedE6 q⟩ := bq.toMonoidHom.comp F
  have hπker : π.ker = Subgroup.center ↥P := by
    ext x
    rw [MonoidHom.mem_ker, ← hFker, MonoidHom.mem_ker]
    exact map_eq_one_iff bq.toMonoidHom bq.injective
  have hπsurj : Function.Surjective π := bq.surjective.comp hFsurj
  have hπcard : Nat.card π.ker ∣ 3 := by
    rw [hπker]
    exact hcenP
  have hπcen : ∀ z : ↥P, π z = 1 → z ∈ Subgroup.center ↥P := fun z hz => by
    have hz' : z ∈ π.ker := MonoidHom.mem_ker.2 hz
    rw [hπker] at hz'
    exact hz'
  have hPcomm : ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ = ⊤ := by
    have h1 : Subgroup.map Ψ (⊤ : Subgroup ↥(fixedGroup K θ)) = ⊤ :=
      Subgroup.map_top_of_surjective Ψ hΨsurj
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥(fixedGroup K θ)) ⊤ Ψ
    rw [hMM, h1] at h2
    exact h2.symm
  have hDsimple : IsSimpleGroup (CFSG.Blueprint.DerivedCentralQuotient
      (twistedFixedGroup TwistTag.E6 K θ)) := by
    have hCEM : CFSG.Blueprint.ChevalleyExceptionalModel
        (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K θ))
        .twistedE6 q.p q.exponent := by
      refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
      refine ⟨K, hKf, hKfin, ?_, θ, ?_, ⟨MulEquiv.refl _⟩⟩
      · rw [hKcard, hcardpow]
        rfl
      · intro c
        rw [hθq, hcardpow]
    exact (CFSG.LieType.Simplicity.fam_2e6_simplicity _ q.p q.exponent hCEM).2
  have hPsimple : IsSimpleGroup (↥P ⧸ Subgroup.center ↥P) := by
    have eqv : ↥P ⧸ Subgroup.center ↥P ≃* CFSG.Blueprint.DerivedCentralQuotient
        (twistedFixedGroup TwistTag.E6 K θ) :=
      (QuotientGroup.quotientMulEquivOfEq hFker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective F hFsurj)
    haveI := hDsimple
    exact eqv.isSimpleGroup
  have hPquasi : CFSG.Open.IsQuasisimple ↥P := ⟨hPcomm, hPsimple⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hdvdN : p ∣ q.card ^ 3 + 1 := dvd_cube_add_one_of_orderOf_six hord
  obtain ⟨a', ha'⟩ := exists_orderOf_statedSU3' (K := K) (N := q.card) (c := q.p)
    (f := q.exponent) (p := p) hcardpow hKcard hdvdN
  obtain ⟨a, ha⟩ : ∃ a : ↥S, orderOf (a : Cat ⟨.E8 q, hv⟩) = p := by
    refine ⟨e.symm a', ?_⟩
    rw [Subgroup.orderOf_coe]
    exact (orderOf_injective e.symm.toMonoidHom e.symm.injective a').trans ha'
  refine ⟨P, Subgroup.zpowers (a : Cat ⟨.E8 q, hv⟩), π, hπsurj, hπcard, hπcen, hPquasi,
    E8Layer.isElemAbelian_zpowers' ha, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, ha]
  · have hc : ∀ l ∈ P, (a : Cat ⟨.E8 q, hv⟩) * l = l * (a : Cat ⟨.E8 q, hv⟩) :=
      fun l hl => (hcomm l hl a a.2).symm
    intro l hl x hx
    exact E8Layer.commute_zpowers_of hc x hx l hl
  · have hxP : (a : Cat ⟨.E8 q, hv⟩) ∉ P := fun h => by
      have h3 := hdisj a a.2 h
      have hd := orderOf_dvd_of_pow_eq_one h3
      rw [ha] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    exact E8Layer.disjoint_zpowers_of_not_mem ha hxP

end Main

end E8Layer6
end CFSG.LieType.SeitzGeneration.ExcHigh
end
