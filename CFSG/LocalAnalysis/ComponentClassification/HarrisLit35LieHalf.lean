module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieCyc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieCover
public import CFSG.GH74.Generic.GKFUnitary

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Blueprint.Multiplier
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem odd_exceptionalOrders_psu_four {p k : ℕ} (hp2 : p ≠ 2) :
    Odd ((exceptionalOrders .PSU 4 p k).1 * (exceptionalOrders .PSU 4 p k).2) := by
  have h : Odd (exceptionalOrders .PSU 4 p k).1 ∧ Odd (exceptionalOrders .PSU 4 p k).2 := by
    unfold exceptionalOrders
    split <;> simp_all
    all_goals decide
  exact h.1.mul h.2

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem tilde_isPerfect (h : Config G p w v L K) :
    Group.IsPerfect ↥((L.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))) := by
  have hLp : Group.IsPerfect ↥L := h.compL.2.2.1
  let g : ↥L →* ↥((L.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))) :=
    { toFun := fun x => ⟨QuotientGroup.mk (⟨x, h.L_le x.2⟩ : ↥K), ⟨⟨x, h.L_le x.2⟩, x.2, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hg : Function.Surjective g := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  exact Group.IsPerfect.ofSurjective (f := g) hg

theorem wbar_mem_tilde (h : Config G p w v L K) :
    h.wbar ∈ (L.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
  ⟨⟨w, h.w_mem_K⟩, h.w_mem_L, rfl⟩

theorem wbar_ne_one (h : Config G p w v L K) : h.wbar ≠ 1 := by
  intro h1
  have h2 := h.orderOf_wbar
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem hat_lieModel_of_lin (h : Config G p w v L K) {τ : StatedLieTag} {n k : ℕ}
    (hτ : τ = .PSL ∨ τ = .PSU)
    (hmS : Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) τ n p k) :
    ∃ f : ℕ, Blueprint.LieModel (↥(hatOf K L) ⧸ center ↥(hatOf K L)) .PSL 2 p f := by
  have hq := h.quasisimple_quot
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have hsq : quotAut h.tau * quotAut h.tau = 1 := by
    ext y
    exact h.quotAut_tau_sq y
  have hadm := N36.admissible_of_lieModel' hmS
  set F := fixedSubgroup (quotAut h.tau) with hFdef
  have hc : IsTwoComponentIn (hatOf K L) F := h.isTwoComponentIn_hat h.compLK
  have hpc := (isTwoComponentIn_iff hc.1).mp hc
  have hqL : IsQuasisimple ↥((hatOf K L).subgroupOf F) :=
    fixedTwoComponentsQuasisimple_lin h.ne_two hτ hadm hmS (quotAut h.tau) hsq
      h.quotAut_tau_ne_one _ hpc
  have hqL' : IsQuasisimple ↥(hatOf K L) :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hc.1) hqL
  obtain ⟨e⟩ := h.nonempty_centralQuot_of_quasisimple hqL' (hatHom h.L_le)
    (hatHom_surjective h.L_le)
  obtain ⟨f, hf, hs5, hLsl⟩ := h.slTwo
  obtain ⟨-, -, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hf hs5 hLsl
  exact ⟨f, GSThmB.OddQuot.lieModel_of_equiv e hQm⟩

theorem center_two_of_cover (h : Config G p w v L K) {g m : ℕ} (hm : Odd m) (hg2 : Even g)
    (hg4 : g ∣ 4)
    (hM : Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) = g * m)
    (hne : ordProj[2] (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) ≠
      ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)))) :
    Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧ g = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hzdvd : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ∣
      Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) := by
    rw [Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).toEquiv]
    exact Center47.card_center_dvd_card_griessHopfMultiplier h.quasisimple_quot
  have hev := h.even_card_center
  rw [hM] at hzdvd hne
  obtain ⟨a, ha⟩ := (N36.center_isPGroup (G := ↥K ⧸ pPrimeCore 2 ↥K)
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)).exists_card_eq
  rw [ha] at hzdvd hne hev ⊢
  have ha1 : a ≠ 0 := by
    rintro rfl
    exact absurd hev (by decide)
  have hdg : 2 ^ a ∣ g :=
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)).dvd_of_dvd_mul_right hzdvd
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd hg4) (by norm_num)
  have hfac : (g * m).factorization 2 = g.factorization 2 := factorization_two_mul_odd hg0 hm
  rw [hfac, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hne
  have hle : 2 ^ a ≤ 4 := Nat.le_of_dvd (by norm_num) (hdg.trans hg4)
  have ha2 : a ≤ 2 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hc
    omega
  have hf2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have hf4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  have hg : g = 2 ∨ g = 4 := by
    have hgle : g ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
    obtain ⟨c, hc⟩ := hg2
    interval_cases g <;> omega
  have ha12 : a = 1 ∨ a = 2 := by omega
  rcases hg with rfl | rfl
  · rw [hf2] at hne
    rcases ha12 with rfl | rfl
    · exact absurd rfl hne
    · exact absurd hdg (by decide)
  · rw [hf4] at hne
    rcases ha12 with rfl | rfl
    · exact ⟨by norm_num, rfl⟩
    · exact absurd rfl hne

theorem false_of_psl4 (hGA : TBLit.GriessMultipliersAllModels) (h : Config G p w v L K) {k : ℕ}
    (hm : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL 4 p k)
    (hne : ordProj[2] (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) ≠
      ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hq := h.quasisimple_quot
  have hmS : Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))
      .PSL 4 p k := GSThmB.OddQuot.lieModel_of_equiv eZ hm
  have hodd : Odd (p ^ k) := (h.prime.odd_of_ne_two h.ne_two).pow
  have hMcard : Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) =
      Nat.gcd 4 (p ^ k - 1) * 1 := by
    rw [mul_one, Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
    exact GH74.Generic.S1.card_hopfMultiplier_psl_four hGA h.ne_two
      (GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm)
  have hgev : Even (Nat.gcd 4 (p ^ k - 1)) := by
    obtain ⟨c, hc⟩ := hodd
    exact even_iff_two_dvd.mpr (Nat.dvd_gcd (by norm_num) ⟨c, by omega⟩)
  obtain ⟨hZ2, hg4⟩ := h.center_two_of_cover odd_one hgev (Nat.gcd_dvd_left _ _) hMcard hne
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := N36.statedClassicalModel_of_lieModel' (.inl rfl) hmS
  have hFodd : Odd (Nat.card F) := hF ▸ hodd
  obtain ⟨π, hπ, hcomp⟩ := GH74.Generic.psl4_cover_of_griess hGA hq
    (N36.center_isPGroup (pPrimeCore_quotient_pPrimeCore_eq_bot 2)) F hFodd e
  have hN : ∀ g : ↥(StatedSL 4 F), g ∈ (StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F) ↔
      π g ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    intro g
    constructor
    · intro hg
      have h1 : (QuotientGroup.mk g : StatedProj (StatedSL 4 F)) = 1 :=
        (QuotientGroup.eq_one_iff g).mpr hg
      rw [← hcomp g, map_eq_one_iff e e.injective] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro hg
      have h1 : (QuotientGroup.mk (π g) : (↥K ⧸ pPrimeCore 2 ↥K) ⧸
          center (↥K ⧸ pPrimeCore 2 ↥K)) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
      have h2 := congrArg e h1
      rw [hcomp g, map_one] at h2
      exact (QuotientGroup.eq_one_iff g).mp h2
  have hNc := LieType.Universal.Spin.statedScalars_subgroupOf_le_center (StatedSL 4 F)
  have hN4 : Nat.card ↥((StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F)) = 4 := by
    rw [← map_center_eq_statedScalars 4 F,
      Subgroup.card_map_of_injective (specialLinearGroupEquivStatedSL 4 F).injective,
      OrderReductions.LinearOrders.card_specialLinear_center F 4 (by norm_num), hF]
    exact hg4
  refine false_of_cyclicCover π hπ hN hNc hN4 (fun x hx y hy => eq_of_mem_statedScalars hx hy)
    hZ2 h.tilde_isPerfect h.wbar_mem_center h.wbar_mem_tilde h.wbar_ne_one fun P hP hPm => ?_
  obtain ⟨f, hLm⟩ := h.hat_lieModel_of_lin (Or.inl rfl) hmS
  exact not_four_dvd_card_center_of_map hGA π hN hNc h.prime h.ne_two hLm P hP hPm

theorem false_of_psu4 (hGA : TBLit.GriessMultipliersAllModels) (h : Config G p w v L K) {k : ℕ}
    (hm : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSU 4 p k)
    (hne : ordProj[2] (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) ≠
      ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hq := h.quasisimple_quot
  have hmS : Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))
      .PSU 4 p k := GSThmB.OddQuot.lieModel_of_equiv eZ hm
  have hodd : Odd (p ^ k) := (h.prime.odd_of_ne_two h.ne_two).pow
  have hk : 1 ≤ k := (N36.admissible_of_lieModel' hm).2.1
  have hMcard : Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) =
      Nat.gcd 4 (p ^ k + 1) *
        ((exceptionalOrders .PSU 4 p k).1 * (exceptionalOrders .PSU 4 p k).2) := by
    rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      GH74.Generic.card_hopfMultiplier_of_griess hGA
        (GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm)]
    have hgen : genericOrders .PSU 4 p k = (Nat.gcd 4 (p ^ k + 1), 1) := rfl
    rw [hgen]
    simp
  have hgev : Even (Nat.gcd 4 (p ^ k + 1)) := by
    obtain ⟨c, hc⟩ := hodd
    exact even_iff_two_dvd.mpr (Nat.dvd_gcd (by norm_num) ⟨c + 1, by omega⟩)
  obtain ⟨hZ2, hg4⟩ := h.center_two_of_cover (odd_exceptionalOrders_psu_four h.ne_two) hgev
    (Nat.gcd_dvd_left _ _) hMcard hne
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := N36.statedClassicalModel_of_lieModel' (.inr rfl) hmS
  obtain ⟨π, hπ, hcomp⟩ := GH74.Generic.psu4_cover_of_griess hGA hq
    (N36.center_isPGroup (pPrimeCore_quotient_pPrimeCore_eq_bot 2)) F (p ^ k) hF hodd e
  have hN : ∀ g : ↥(StatedSU 4 (p ^ k) F),
      g ∈ (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (p ^ k) F) ↔
        π g ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    intro g
    constructor
    · intro hg
      have h1 : (QuotientGroup.mk g : StatedProj (StatedSU 4 (p ^ k) F)) = 1 :=
        (QuotientGroup.eq_one_iff g).mpr hg
      rw [← hcomp g, map_eq_one_iff e e.injective] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro hg
      have h1 : (QuotientGroup.mk (π g) : (↥K ⧸ pPrimeCore 2 ↥K) ⧸
          center (↥K ⧸ pPrimeCore 2 ↥K)) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
      have h2 := congrArg e h1
      rw [hcomp g, map_one] at h2
      exact (QuotientGroup.eq_one_iff g).mp h2
  have hNc := LieType.Universal.Spin.statedScalars_subgroupOf_le_center (StatedSU 4 (p ^ k) F)
  have hN4 : Nat.card ↥((StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (p ^ k) F)) = 4 := by
    rw [GH74.Generic.S1.card_scalars_statedSU_four h.prime hk hF]
    exact hg4
  refine false_of_cyclicCover π hπ hN hNc hN4 (fun x hx y hy => eq_of_mem_statedScalars hx hy)
    hZ2 h.tilde_isPerfect h.wbar_mem_center h.wbar_mem_tilde h.wbar_ne_one fun P hP hPm => ?_
  obtain ⟨f, hLm⟩ := h.hat_lieModel_of_lin (Or.inr rfl) hmS
  exact not_four_dvd_card_center_of_map hGA π hN hNc h.prime h.ne_two hLm P hP hPm

end Config

end CFSG.ComponentClassification.HarrisLit.L35

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.Assembly.LowTwoRank

@[expose] def Harris81Lemma35IdentEvenSporFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (w v : G) (L K : Subgroup G),
    L35.Config G p w v L K → ¬ N36.IsAlt (↥K ⧸ Open.fusionZStar ↥K) →
    ((∃ (t : StatedLieTag) (n f : ℕ), Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n 2 f) ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .M12 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .J2 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .HS) →
    L35.Concl p v L K

theorem harris81Lemma35IdentFourCoverFact_of_evenSpor (hGA : TBLit.GriessMultipliersAllModels)
    (hE : Harris81Lemma35IdentEvenSporFact) : Harris81Lemma35IdentFourCoverFact := by
  intro G _ _ p w v L K h halt hcase
  rcases hcase with ⟨k, hm, hne, -⟩ | hrest
  · rcases hm with hm | hm
    · exact (h.false_of_psl4 hGA hm hne).elim
    · exact (h.false_of_psu4 hGA hm hne).elim
  · exact hE G p w v L K h halt hrest

end CFSG.ComponentClassification.HarrisLit
