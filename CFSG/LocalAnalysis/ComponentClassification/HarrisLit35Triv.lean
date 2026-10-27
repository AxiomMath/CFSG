module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltId
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltSmall

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem nonempty_centralQuot_of_surjective (h : Config G p w v L K) {B : Type} [Group B]
    [Finite B] [Nontrivial B] (f : ↥L →* B) (hf : Function.Surjective f)
    (hO : pPrimeCore 2 B = ⊥) :
    Nonempty ((↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L) ≃* B ⧸ center B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hs5, hLsl⟩ := h.slTwo
  obtain ⟨hQq, -, -, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hk hs5 hLsl
  have hOker : pPrimeCore 2 ↥L ≤ f.ker := by
    have hn : ((pPrimeCore 2 ↥L).map f).Normal :=
      (inferInstance : (pPrimeCore 2 ↥L).Normal).map f hf
    have hle : (pPrimeCore 2 ↥L).map f ≤ pPrimeCore 2 B := by
      refine le_pPrimeCore_of_normal_coprime hn ?_
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) pPrimeCore_coprime_card
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
    exact hle
  set ψ : ↥L ⧸ pPrimeCore 2 ↥L →* B := QuotientGroup.lift _ f hOker with hψdef
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hQo : Open.IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    (AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQq)
  have hker : ψ.ker ≤ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rcases Quasisimple.normal_le_center_or_eq_top hQo ψ.ker with hc | ht
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne B
      obtain ⟨x, rfl⟩ := hψ a
      obtain ⟨y, rfl⟩ := hψ b
      have hx : x ∈ ψ.ker := ht ▸ mem_top x
      have hy : y ∈ ψ.ker := ht ▸ mem_top y
      rw [MonoidHom.mem_ker] at hx hy
      exact hab (by rw [hx, hy])
  exact LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hQq ψ hψ hker

theorem isComponent_hat (h : Config G p w v L K)
    (hO : pPrimeCore 2 ↥(fixedPoints (quotAut h.tau)) = ⊥) :
    IsComponent ((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) ∧
      ∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧
        Blueprint.LieModel (↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) ⧸
          center ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau)))) .PSL 2 p k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := h.isTwoComponentIn_hat h.compLK
  have hp := (isTwoComponentIn_iff hc.1).mp hc
  have hcomp : IsComponent ((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) :=
    (isTwoComponent_iff_isComponent hO _).mp ((isTwoComponent_iff_isPComponent _).mpr hp)
  refine ⟨hcomp, ?_⟩
  have hOB := pPrimeCore_eq_bot_of_isSubnormal hO hcomp.2
  have : Nontrivial ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) :=
    LocalCores.isQuasisimple_nontrivial hcomp.1
  let f : ↥L →* ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) :=
    (subgroupOfEquivOfLe hc.1).symm.toMonoidHom.comp (hatHom h.L_le)
  have hf : Function.Surjective f :=
    (subgroupOfEquivOfLe hc.1).symm.surjective.comp (hatHom_surjective h.L_le)
  obtain ⟨e⟩ := h.nonempty_centralQuot_of_surjective f hf hOB
  obtain ⟨k, hk, hs5, hLsl⟩ := h.slTwo
  obtain ⟨-, -, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hk hs5 hLsl
  exact ⟨k, hk, hs5, GSThmB.OddQuot.lieModel_of_equiv e hQm⟩

theorem quotAut_tau_ne_one (h : Config G p w v L K) : quotAut h.tau ≠ 1 := by
  intro hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hs5, hLsl⟩ := h.slTwo
  obtain ⟨hQq, hQZ, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hk hs5 hLsl
  have hq := h.quasisimple_quot
  have hS : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have hc := h.isTwoComponentIn_hat h.compLK
  have hfix : fixedPoints (quotAut h.tau) = ⊤ := by
    rw [hσ]
    ext y
    simp only [mem_fixedPoints, MulAut.one_apply, mem_top]
  rw [hfix] at hc
  have htop : hatOf K L = ⊤ := by
    have hsub : (hatOf K L).IsSubnormal := by
      have h1 := hc.2.1.map (f := (⊤ : Subgroup _).subtype) fun y => ⟨⟨y, mem_top y⟩, rfl⟩
      rwa [subgroupOf_map_subtype, inf_top_eq] at h1
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hS hsub with hb | ht
    · exfalso
      apply not_odd_card_of_isTwoQuasisimple hc.2.2
      rw [hb, card_bot]
      exact odd_one
    · exact ht
  have hOS : pPrimeCore 2 ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (pPrimeCore 2 _) with hb | ht
    · exact hb
    · exfalso
      apply not_odd_card_of_isTwoQuasisimple hc.2.2
      have hcop := pPrimeCore_coprime_card (p := 2)
        (G := (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))
      rw [ht, card_top] at hcop
      rw [htop, card_top]
      exact Nat.coprime_two_left.mp hcop
  let fS : ↥L →* (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) :=
    (hatOf K L).subtype.comp (hatHom h.L_le)
  have hfS : Function.Surjective fS := by
    intro y
    obtain ⟨x, hx⟩ := hatHom_surjective h.L_le ⟨y, htop ▸ mem_top y⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  obtain ⟨e1⟩ := h.nonempty_centralQuot_of_surjective fS hfS hOS
  have hZS := CatLeaf.center_eq_bot_of_simple hq.2.2
  let e2 : ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) ⧸
      center ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) ≃*
      (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) :=
    (QuotientGroup.quotientMulEquivOfEq hZS).trans QuotientGroup.quotientBot
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  obtain ⟨eL⟩ := nonempty_fusionZStar_quotient_equiv ↥L
  let eKL : ↥K ⧸ Open.fusionZStar ↥K ≃* ↥L ⧸ Open.fusionZStar ↥L :=
    eZ.trans (e2.symm.trans (e1.symm.trans eL.symm))
  have hlieL : Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) .PSL 2 p k :=
    GSThmB.OddQuot.lieModel_of_equiv eL.symm hQm
  have hlieK : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL 2 p k :=
    GSThmB.OddQuot.lieModel_of_equiv eKL.symm hlieL
  have hoK : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card))
  have hoL : Odd (Nat.card ↥(pPrimeCore 2 ↥L)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card))
  have hZK : Nat.card ↥(Open.fusionZStar ↥K) =
      Nat.card ↥(pPrimeCore 2 ↥K) * Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) := by
    have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥K)).ker := by
      rw [QuotientGroup.ker_mk']
      exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
    rw [card_fusionZStar_of_surjective _ (QuotientGroup.mk'_surjective _) hker,
      QuotientGroup.ker_mk',
      fusionZStar_eq_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)]
  have hZL : Nat.card ↥(Open.fusionZStar ↥L) = Nat.card ↥(pPrimeCore 2 ↥L) * 2 := by
    have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥L)).ker := by
      rw [QuotientGroup.ker_mk']
      exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
    rw [card_fusionZStar_of_surjective _ (QuotientGroup.mk'_surjective _) hker,
      QuotientGroup.ker_mk',
      fusionZStar_eq_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2), hQZ]
  have hML : ordProj[2] (Nat.card ↥(Open.fusionZStar ↥L)) =
      ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥L ⧸ Open.fusionZStar ↥L))) := by
    rcases h.mTypeL with ⟨-, -, -, hcond⟩ | ⟨-, ⟨e3⟩⟩
    · exact hcond 1 k one_pos hk (Or.inl hlieL)
    · exfalso
      have h24 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) = 24 := by
        rw [Nat.card_congr e3.toEquiv]
        exact card_specialLinearGroup_two_zmod_three
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (center (↥L ⧸ pPrimeCore 2 ↥L))
      rw [h24, hQZ] at hmul
      have h2q := RestrictedStd.Spor.two_mul_ordA_one (q := p ^ k)
        (h.prime.eq_two_or_odd'.resolve_left h.ne_two).pow
      rw [← GSThmB.card_of_lieModel_psl_two h.ne_two hQm] at h2q
      have h120 : 120 ≤ p ^ k * ((p ^ k) ^ 2 - 1) :=
        calc (120 : ℕ) = 5 * (5 ^ 2 - 1) := by norm_num
          _ ≤ p ^ k * ((p ^ k) ^ 2 - 1) := RestrictedStd.Spor.cubic_mono hs5
      generalize p ^ k * ((p ^ k) ^ 2 - 1) = N at h2q h120
      omega
  have hfL : (Nat.card ↥(Open.fusionZStar ↥L)).factorization 2 = 1 := by
    rw [hZL, mul_comm, factorization_two_mul_odd two_ne_zero hoL]
    exact Nat.Prime.factorization_self Nat.prime_two
  have hMK : Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) =
      Nat.card (Open.griessHopfMultiplier (↥L ⧸ Open.fusionZStar ↥L)) :=
    Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eKL).toEquiv
  have hfM : (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K))).factorization 2 =
      1 := by
    have h1 := hML
    rw [hfL, ← hMK] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hM0 : Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) ≠ 0 := by
    intro h0
    rw [h0, Nat.factorization_zero, Finsupp.zero_apply] at hfM
    exact absurd hfM (by norm_num)
  have hz0 : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ≠ 0 := Nat.card_pos.ne'
  have hzdvd : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ∣
      Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)) := by
    rw [Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).toEquiv]
    exact Center47.card_center_dvd_card_griessHopfMultiplier hq
  have hle : (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))).factorization 2 ≤ 1 := by
    rw [← hfM]
    exact (Nat.factorization_le_iff_dvd hz0 hM0).mpr hzdvd 2
  have hge : 0 < (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hz0
      (even_iff_two_dvd.mp h.even_card_center)
  apply h.not_mType
  refine Or.inl ⟨h.compK.2.2, ⟨.PSL, 2, k, hlieK⟩, ?_, fun n r _ _ _ => ?_⟩
  · rw [hZK]
    exact h.even_card_center.mul_left _
  · rw [hZK, mul_comm (Nat.card ↥(pPrimeCore 2 ↥K)), factorization_two_mul_odd hz0 hoK, hfM]
    congr 1
    omega

end Config

end CFSG.ComponentClassification.HarrisLit.L35
