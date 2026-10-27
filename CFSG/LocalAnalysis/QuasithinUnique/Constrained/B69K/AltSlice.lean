module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltMClause
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltSliceData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.SectionOffK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Main
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Nat
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.Coordinator
open scoped commutatorElement

namespace B69K

open CFSG.Quasithin.B69

theorem center_eq_bot_of_alt {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L) {m : ℕ}
    (hm : 8 ≤ m) (hAlt : IsAlt m (L ⧸ Subgroup.center L)) (hodd : Odd (Nat.card ↥(Subgroup.center L))) :
    Subgroup.center L = ⊥ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨e⟩ := hAlt
  haveI : Group.IsPerfect L := ⟨hL.1⟩
  let η : L →* alternatingGroup (Fin (m' + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' (Subgroup.center L) x) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega : 6 ≤ m') η hηs
    (hker ▸ le_rfl) (hker ▸ hodd)
  rw [hker] at h1
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem coreMod_equiv_altHeart {n : ℕ} (hn : Odd n) :
    ∃ Φ : ↥(G6.coreMod n) ≃* Multiplicative (altHeart n),
      ∀ (σ : Equiv.Perm (Fin n)) (x : ↥(G6.coreMod n)),
        Multiplicative.toAdd (Φ (G6.coreAct n σ x)) = altAct σ (Multiplicative.toAdd (Φ x)) := by
  have hinj : Function.Injective (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.coreHeart n) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h := (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.coreHeart_eq_one_iff hn.pos x).1 hx
    rw [B69.natKer_inf_eq_bot hn, Subgroup.mem_bot] at h
    exact h
  refine ⟨MulEquiv.ofBijective _ ⟨hinj,
    CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.coreHeart_surjective n⟩, fun σ x => ?_⟩
  exact CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.toAdd_coreHeart_permAct σ x

section Glue

variable {S : Type} [CommGroup S] [Finite S] {G Lt : Subgroup (MulAut S)} {hLG : Lt ≤ G} {m : ℕ}

theorem realizesVia_of_mulEquiv {E : FFModel} (hE : E.ker = ⊥) {V : Type*} [CommGroup V]
    {H : Subgroup (MulAut V)} (π : E.Gam →* ↥H) (hπs : Function.Surjective π)
    (Φ : V ≃* ↥E.sec) (hΦ : ∀ γ v, (Φ ((π γ : MulAut V) v) : E.Amb) = E.act γ (Φ v)) :
    E.RealizesVia H ⊤ ⊥ π := by
  have hsec : ∀ γ, ∀ m ∈ E.sec, E.act γ m ∈ E.sec := fun γ m hm => by
    obtain ⟨v, hv⟩ := Φ.surjective ⟨m, hm⟩
    rw [← show (Φ v : E.Amb) = m from congrArg Subtype.val hv, ← hΦ]
    exact (Φ _).2
  have hact1 : ∀ γ, E.act γ 1 = 1 := fun γ => by
    have h := hΦ γ 1
    simp only [map_one, OneMemClass.coe_one] at h
    exact h.symm
  have hkeq : ∀ x : ↥E.sec, x ∈ E.ker.subgroupOf E.sec ↔ x = 1 := fun x => by
    rw [Subgroup.mem_subgroupOf, hE, Subgroup.mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  let β : ↥(⊤ : Subgroup V) →* ↥E.sec ⧸ E.ker.subgroupOf E.sec :=
    (QuotientGroup.mk' _).comp (Φ.toMonoidHom.comp (⊤ : Subgroup V).subtype)
  refine ⟨hπs, bot_le, by rw [hE]; exact bot_le, fun _ _ _ => Subgroup.mem_top _,
    fun h z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one], hsec,
    fun γ m hm => by rw [hE, Subgroup.mem_bot] at hm ⊢; rw [hm, hact1], β, fun q => ?_,
    fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, rfl⟩ := Φ.surjective x
    exact ⟨⟨v, Subgroup.mem_top v⟩, rfl⟩
  · show (QuotientGroup.mk (Φ u) : ↥E.sec ⧸ E.ker.subgroupOf E.sec) = 1 ↔ (u : V) ∈ ⊥
    rw [QuotientGroup.eq_one_iff, hkeq, Subgroup.mem_bot, MulEquiv.map_eq_one_iff]
  · have h1 : Φ u = m := by
      have h := (QuotientGroup.eq (s := E.ker.subgroupOf E.sec) (a := Φ u) (b := m)).1 hum
      rw [hkeq, inv_mul_eq_one] at h
      exact h
    show (QuotientGroup.mk (Φ ((π γ : MulAut V) u)) : ↥E.sec ⧸ E.ker.subgroupOf E.sec) =
      QuotientGroup.mk ⟨E.act γ m, hm⟩
    congr 1
    apply Subtype.ext
    rw [hΦ, h1]

theorem realizesVia_symDn_of_data (D : AltNatData G Lt hLG m) (hodd : Odd m)
    (hsurj : Function.Surjective D.θ) :
    ∃ πG : Equiv.Perm (Fin m) →* ↥G, Function.Injective πG ∧ (∀ σ, D.θ (πG σ) = σ) ∧
      (FFModel.symDn m).RealizesVia G ⊤ ⊥ πG := by
  obtain ⟨Φ1, hΦ1⟩ := coreMod_equiv_altHeart hodd
  let θe : ↥G ≃* Equiv.Perm (Fin m) := MulEquiv.ofBijective D.θ ⟨D.inj, hsurj⟩
  let πG : Equiv.Perm (Fin m) →* ↥G := θe.symm.toMonoidHom
  have hθπ : ∀ σ, D.θ (πG σ) = σ := fun σ => θe.apply_symm_apply σ
  let e' : S ≃* ↥(G6.coreMod m) := D.π.trans Φ1.symm
  have he' : ∀ (g : ↥G) (s : S),
      e' ((g : MulAut S) s) = G6.coreAct m (D.θ g) (e' s) := by
    intro g s
    apply Φ1.injective
    apply Multiplicative.toAdd.injective
    rw [hΦ1]
    simp only [e', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact D.equiv g s
  have hker : (Subgroup.zpowers (G6.allOnes m) ⊓ G6.coreMod m).subgroupOf (G6.coreMod m) = ⊥ :=
    B69.natKer_inf_eq_bot hodd
  have hkb : (FFModel.symDn m).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : (⟨x, hx.2⟩ : ↥(G6.coreMod m)) ∈
        (Subgroup.zpowers (G6.allOnes m) ⊓ G6.coreMod m).subgroupOf (G6.coreMod m) := hx
    rw [hker, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  refine ⟨πG, θe.symm.injective, hθπ, ?_⟩
  refine realizesVia_of_mulEquiv hkb πG θe.symm.surjective e' fun (γ : Equiv.Perm (Fin m)) v => ?_
  have h2 := he' (πG γ) v
  rw [hθπ] at h2
  exact congrArg Subtype.val h2

theorem zpowers_offender {Y : Subgroup (MulAut S)} {b : MulAut S} (hbY : b ∈ Y)
    (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1)
    (hcard : Nat.card S = 2 * Nat.card (fixV (Subgroup.zpowers b))) :
    IsFFStarOffender Y (Subgroup.zpowers b) ∧
      Nat.card (Subgroup.zpowers b) * Nat.card (fixV (Subgroup.zpowers b)) = Nat.card S := by
  have hord : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have hcz : Nat.card (Subgroup.zpowers b) = 2 := by rw [Nat.card_zpowers, hord]
  refine ⟨⟨Subgroup.zpowers_le.2 hbY, ?_, ?_, ?_⟩, by rw [hcz, hcard]⟩
  · intro h
    apply hb1
    have h1 := Subgroup.mem_zpowers b
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  · refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.refl b).zpow_zpow i j |>.eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb2, one_zpow]
  · intro B' hB'
    have hdvd : Nat.card B' ∣ 2 := hcz ▸ Subgroup.card_dvd_of_le hB'
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · have h0 : B' = ⊥ := Subgroup.eq_bot_of_card_eq B' h1
      subst h0
      rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, hcz, hcard]
      omega
    · have h3 : B' = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge hB' (by rw [hcz, h2])
      rw [h3]

end Glue

theorem asAltSlice_of (hGF2 : GF2EightFive) : AsAltSlice := by
  intro V _ _ hV X T M A L hH W hW j hj hAlt
  obtain ⟨k, hk2, hk4⟩ : ∃ k : ℕ, 2 ^ j = 2 * k ∧ 4 ≤ k := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine ⟨2 ^ i, by ring, ?_⟩
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hk2] at hAlt
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hm9 : 9 ≤ 2 * k + 1 := by omega
  obtain ⟨-, hmp, hO2, -, -, hA, hL, hLA⟩ := id hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAZs : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_alt hLq (by omega) hAlt (odd_card_center_comp hO2 hL)
  obtain ⟨ℓ, hℓs, hcent, hLbq, hIrr, hFstar, hLbn, hℓa⟩ := sectionFittingDataK hV hH hW
  have hℓi : Function.Injective ℓ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : x ∈ Subgroup.center ↥L := hcent (MonoidHom.mem_ker.2 hx)
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  have hLiso : Nonempty (↥(autSec L W (W ⊓ fixV L)) ≃* alternatingGroup (Fin (2 * k + 1))) := by
    obtain ⟨e⟩ := hAlt
    let eL : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
      (QuotientGroup.quotientBot (G := ↥L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact ⟨(MulEquiv.ofBijective ℓ ⟨hℓi, hℓs⟩).symm.trans (eL.trans e)⟩
  have hLG : autSec L W (W ⊓ fixV L) ≤ autSec (L ⊔ A) W (W ⊓ fixV L) := autSec_mono le_sup_left W _
  obtain ⟨B, hBA, hBo⟩ := sectionOffenderK hV hH hW
  obtain ⟨D⟩ := natural_data_of_gf2 hGF2 hS2 hFstar.symm hLG hm9 hLiso ⟨B, hBo⟩ hIrr
  have hq : qOf (wtLA A L W) = ((1 : ℚ) : WithTop ℚ) :=
    qOf_eq_one_of_offender D hm9 hodd hS2 ⟨B, hBo⟩
  have hnonstrong := section_nonstrongK hV hH hW hq
  obtain ⟨hsup, hfaithA⟩ := eq_sup_fixV_of_sec hV hA hLq hLA hW hnonstrong
  obtain ⟨hinv, hcomm, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  obtain ⟨Φ1, hΦ1⟩ := coreMod_equiv_altHeart hodd
  let actW : ↥L →* MulAut ↥W := (resHom W).comp (Subgroup.inclusion hLW)
  let e : Sec W (W ⊓ fixV L) ≃* ↥(G6.coreMod (2 * k + 1)) := D.π.trans Φ1.symm
  let ρ : ↥L →* Equiv.Perm (Fin (2 * k + 1)) := D.θ.comp ((Subgroup.inclusion hLG).comp ℓ)
  have hperf : Group.IsPerfect ↥(autSec L W (W ⊓ fixV L)) := hLbq.1
  have hU0 : (W ⊓ fixV L).subgroupOf W = ⊥ := by
    refine fixed_eq_bot_of_natural (W := ↥W) (fun w => Subtype.ext (hV w)) actW
      (U := (W ⊓ fixV L).subgroupOf W) ?_ hodd (by omega) ρ ?_ ?_ ?_ e ?_ ?_
    · intro γ u hu
      have hu' : (u : V) ∈ W ⊓ fixV L := hu
      exact Subtype.ext (hu'.2 _ γ.2)
    · intro γ
      exact theta_mem_alt D hperf (ℓ γ)
    · intro σ hσ
      obtain ⟨x, hx⟩ := D.alt_le hσ
      obtain ⟨γ, rfl⟩ := hℓs x
      exact ⟨γ, hx⟩
    · exact D.inj.comp ((Subgroup.inclusion_injective hLG).comp hℓi)
    · intro γ w
      have h1 : (QuotientGroup.mk (actW γ w) : Sec W (W ⊓ fixV L)) =
          ((ℓ γ : ↥(autSec L W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L)))
            (QuotientGroup.mk w) := by
        rw [hℓa hLW hLZ γ]
        rfl
      apply Φ1.injective
      apply Multiplicative.toAdd.injective
      show _ = Multiplicative.toAdd (Φ1 (G6.coreAct (2 * k + 1) (D.θ (Subgroup.inclusion hLG (ℓ γ)))
        (Φ1.symm (D.π (QuotientGroup.mk w)))))
      rw [hΦ1]
      simp only [e, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [h1]
      exact D.equiv (Subgroup.inclusion hLG (ℓ γ)) (QuotientGroup.mk w)
    · rw [eq_top_iff]
      intro w _
      have hw : (w : V) ∈ commSub W L := by rw [hcomm]; exact w.2
      have hle : commSub W L ≤
          (Subgroup.closure {x : ↥W | ∃ γ w', x = actW γ w' * w'⁻¹}).map W.subtype := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨x, hx, v, hv, rfl⟩
        exact ⟨actW ⟨x, hx⟩ ⟨v, hv⟩ * ⟨v, hv⟩⁻¹,
          Subgroup.subset_closure ⟨⟨x, hx⟩, ⟨v, hv⟩, rfl⟩, rfl⟩
      obtain ⟨y, hy, hyw⟩ := hle hw
      have : y = w := Subtype.ext hyw
      rw [← this]
      exact hy
  have hU' : W ⊓ fixV L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥W) ∈ (W ⊓ fixV L).subgroupOf W := hx
    rw [hU0, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  have hnt : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  have hge := sec_card_le_of_offender hA.1 hLq hAn hW hAW hnt
  have hAprod : Nat.card (autSec A W (W ⊓ fixV L)) *
      Nat.card (fixV (autSec A W (W ⊓ fixV L))) = Nat.card (Sec W (W ⊓ fixV L)) :=
    le_antisymm hnonstrong hge
  have hBoff : IsFFStarOffender (autSec A W (W ⊓ fixV L)) B :=
    ⟨hBA, hBo.2.1, hBo.2.2.1, hBo.2.2.2⟩
  have hr1 : rAV B = 1 := rAV_eq_one_of_one_le_qOf hS2 (hq ▸ le_rfl) hBo
  have hBprod : Nat.card (Sec W (W ⊓ fixV L)) = Nat.card B * Nat.card (fixV B) :=
    (rAV_eq_one_iff hS2 hBo.isA2).1 hr1
  have hBeq : B = autSec A W (W ⊓ fixV L) :=
    lift_offender hA hU' hAWs hAZs hsup hfaithA hBoff (hBprod.symm.trans hAprod.symm)
  have hBG : B ≤ autSec (L ⊔ A) W (W ⊓ fixV L) := hBA.trans (autSec_mono le_sup_right W _)
  obtain ⟨b, hbB, hsw⟩ := exists_swap_of_offender D hm9 hodd hBG hBo.2.2.1 hBo.2.1 hBprod.le
  have hbG : b ∈ autSec (L ⊔ A) W (W ⊓ fixV L) := hBG hbB
  obtain ⟨hb2, -, hb1, hcb⟩ := swap_properties D hm9 hodd hbG hsw
  have hbA : b ∈ autSec A W (W ⊓ fixV L) := hBeq ▸ hbB
  obtain ⟨hB₁o, hB₁p⟩ := zpowers_offender (Y := autSec A W (W ⊓ fixV L)) hbA hb2 hb1 hcb
  have hB₁eq : Subgroup.zpowers b = autSec A W (W ⊓ fixV L) :=
    lift_offender hA hU' hAWs hAZs hsup hfaithA hB₁o (hB₁p.trans hAprod.symm)
  have hsurj : Function.Surjective D.θ :=
    MonoidHom.range_eq_top.1 (range_eq_top_of_swap D hbG hsw)
  obtain ⟨πG, hπGi, hθπ, hπG⟩ := realizesVia_symDn_of_data D hodd hsurj
  have hπθ : ∀ g : ↥(autSec (L ⊔ A) W (W ⊓ fixV L)), πG (D.θ g) = g :=
    fun g => D.inj (hθπ _)
  have hLeq : autSec L W (W ⊓ fixV L) =
      (alternatingGroup (Fin (2 * k + 1))).map
        ((autSec (L ⊔ A) W (W ⊓ fixV L)).subtype.comp πG) := by
    ext x
    constructor
    · intro hx
      refine ⟨D.θ ⟨x, hLG hx⟩, theta_mem_alt D hperf ⟨x, hx⟩, ?_⟩
      show ((πG (D.θ ⟨x, hLG hx⟩) : ↥(autSec (L ⊔ A) W (W ⊓ fixV L))) : MulAut _) = x
      rw [hπθ]
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨y, hy⟩ := D.alt_le hσ
      have hy' : πG σ = Subgroup.inclusion hLG y := by
        rw [← hy]
        exact hπθ _
      have h3 : ((autSec (L ⊔ A) W (W ⊓ fixV L)).subtype.comp πG) σ =
          (y : MulAut (Sec W (W ⊓ fixV L))) := by
        show ((πG σ : ↥(autSec (L ⊔ A) W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L))) = _
        rw [hy']
        rfl
      rw [h3]
      exact y.2
  have hAeq : autSec A W (W ⊓ fixV L) =
      (Subgroup.zpowers (D.θ ⟨b, hbG⟩)).map
        ((autSec (L ⊔ A) W (W ⊓ fixV L)).subtype.comp πG) := by
    rw [← hB₁eq, MonoidHom.map_zpowers]
    congr 1
    show b = ((πG (D.θ ⟨b, hbG⟩) : ↥(autSec (L ⊔ A) W (W ⊓ fixV L))) : MulAut _)
    rw [hπθ]
  obtain ⟨π', hπ'i, hπ's, hπ'r, hLeq', i, j', hij, hAeq'⟩ :=
    alt_data_general (m := 2 * k + 1) hV hO2 hA hL hLA hU' hW hLZ hAZs hsup
      (J := autSec (L ⊔ A) W (W ⊓ fixV L)) rfl πG hπGi hπG hLeq hsw hAeq
  obtain ⟨hcV, hAcQ, -⟩ := commV_eq_of_sup hV hA hLq hLA hW hsup
  have hAc : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X → L ≠ L' → ⁅L', A⁆ = ⊥ :=
    fun L' hL' hne => commutator_eq_bot_of_natural hV hA hL hW hcV hAcQ hL' hne
  obtain ⟨ρ', hρ'⟩ := mStructure_general hmp hO2 hL hA.1.1 hAc hodd (by omega) π' hπ'i hπ's hLeq'
  refine ⟨k, by omega, π'.comp (MulAut.conj ρ').toMonoidHom,
    hπ's.comp (MulAut.conj ρ').surjective, symDn_realizesVia_conj hπ'r ρ', ?_,
    ⟨ρ'⁻¹ i, ρ'⁻¹ j', ?_, ?_⟩, hρ'⟩
  · show L = (alternatingGroup (Fin (2 * k + 1))).map
      ((L ⊔ A).subtype.comp (π'.comp (MulAut.conj ρ').toMonoidHom))
    rw [← MonoidHom.comp_assoc, ← Subgroup.map_map, alt_map_conj]
    exact hLeq'
  · exact fun h => hij ((ρ'⁻¹).injective h)
  · show A = (Subgroup.zpowers (Equiv.swap (ρ'⁻¹ i) (ρ'⁻¹ j'))).map
      ((L ⊔ A).subtype.comp (π'.comp (MulAut.conj ρ').toMonoidHom))
    have hsw' : (MulAut.conj ρ').toMonoidHom (Equiv.swap (ρ'⁻¹ i) (ρ'⁻¹ j')) =
        Equiv.swap i j' := by
      show ρ' * Equiv.swap (ρ'⁻¹ i) (ρ'⁻¹ j') * ρ'⁻¹ = _
      rw [← Equiv.swap_apply_apply]
      simp
    have h : (Subgroup.zpowers (Equiv.swap (ρ'⁻¹ i) (ρ'⁻¹ j'))).map
        ((L ⊔ A).subtype.comp (π'.comp (MulAut.conj ρ').toMonoidHom)) =
        (Subgroup.zpowers (Equiv.swap i j')).map ((L ⊔ A).subtype.comp π') := by
      rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      simp only [MonoidHom.comp_apply, hsw']
    exact hAeq'.trans h.symm

end B69K

end CFSG.Quasithin
