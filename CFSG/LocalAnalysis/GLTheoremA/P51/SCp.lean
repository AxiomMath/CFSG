module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.LocalAnalysis.GLTheoremA.Lemma48
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P51

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem dvd_card_pQuot {p : ℕ} (hp : p.Prime) {X H : Subgroup G}
    (hH : GLAPComponent p X H) : p ∣ Nat.card (PQuot p H) := by
  by_contra hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (PQuot p H) := isQuasisimple_nontrivial
    (isQuasisimple_pQuot_of_glaPComponent hp hH)
  have hKc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥H)) := CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card ↥H = Nat.card (PQuot p H) * Nat.card (GLAPPrimeCore p ↥H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcop : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥H)) := by
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hcard]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd) hKc
  have htop : (⊤ : Subgroup ↥H) ≤ GLAPPrimeCore p ↥H := le_sSup ⟨inferInstance, hcop⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : PQuot p H)
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx ((QuotientGroup.eq_one_iff h).2 (htop (Subgroup.mem_top h)))

private theorem not_le_centModSubgroup_of_maximal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X H B : Subgroup G} (hH : GLAPComponent p X H) (hB : IsElemAbelian p B)
    (hBH : B ≤ Subgroup.normalizer (H : Set G))
    (hmax : ∀ E : Subgroup G, IsElemAbelian p E → B ≤ E → E ≤ H ⊔ B → E = B) :
    ¬ B ≤ centModSubgroup p H := by
  intro hC
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let π : ↥H →* PQuot p H := QuotientGroup.mk' (GLAPPrimeCore p ↥H)
  have hKc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥H)) := CFSG.pPrimeCore_coprime_card
  obtain ⟨yb, hyord, hycen⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      (isQuasisimple_pQuot_of_glaPComponent hp hH) hp hp2 (dvd_card_pQuot hp hH)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hpy : π y ^ p = 1 := by
    have h := pow_orderOf_eq_one (π y)
    have hyord' : orderOf (π y) = p := hyord
    rwa [hyord'] at h
  have hBO : B ≤ Subgroup.normalizer (GLAPPrimeCoreOf p H : Set G) :=
    hBH.trans (normalizer_le_normalizer_glaPPrimeCoreOf p H)
  have hcoset : ∀ a ∈ B, (y : G)⁻¹ * (a * y * a⁻¹) ∈ GLAPPrimeCoreOf p H := by
    intro a ha
    have h1 := (hC ha).2 (y : G)⁻¹ (H.inv_mem y.2)
    have h2 : (y : G)⁻¹ * (a * y * a⁻¹) = ⁅(y : G)⁻¹, a⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact h1
  obtain ⟨n, hnO, hnC⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.exists_fixed_mem_coset hp
      (isPGroup_of_isElemAbelian hB) hBO (not_dvd_card_glaPPrimeCoreOf hp H) hcoset
  obtain ⟨n', hn'K, rfl⟩ := hnO
  set u : ↥H := y * n' with hu
  have huC : (u : G) ∈ Subgroup.centralizer (B : Set G) := hnC
  have hπu : π u = π y := by
    rw [hu, map_mul]
    have : π n' = 1 := (QuotientGroup.eq_one_iff n').2 hn'K
    rw [this, mul_one]
  obtain ⟨a, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos u).ne' p hp.ne_one
  set v : ↥H := u ^ m with hv
  have hπv : π v = π y ^ m := by rw [hv, map_pow, hπu]
  have hvK : v ^ p ∈ GLAPPrimeCore p ↥H := by
    have : π (v ^ p) = 1 := by
      rw [map_pow, hπv, ← pow_mul, mul_comm, pow_mul, hpy, one_pow]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hpow : (v ^ p) ^ (p ^ a) = 1 := by
    have h1 : u ^ (p ^ a * m) = 1 := hkm ▸ pow_orderOf_eq_one u
    calc (v ^ p) ^ (p ^ a) = (u ^ (p ^ a * m)) ^ p := by
          rw [hv, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [h1, one_pow]
  have hv1 : v ^ p = 1 := by
    have h1 : orderOf (v ^ p) ∣ p ^ a := orderOf_dvd_of_pow_eq_one hpow
    have h2 : orderOf (v ^ p) ∣ Nat.card (GLAPPrimeCore p ↥H) :=
      Subgroup.orderOf_dvd_natCard _ hvK
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left a hKc)] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hvG : (v : G) ^ p = 1 := by
    have := congrArg Subtype.val hv1
    simpa using this
  have hvC : (v : G) ∈ Subgroup.centralizer (B : Set G) := by
    rw [hv, Subgroup.coe_pow]
    exact Subgroup.pow_mem _ huC m
  have hBv : B ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hvC) b hb
  have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers (v : G)) :=
    isElemAbelian_sup_zpowers hB hBv hvG
  have hEle : B ⊔ Subgroup.zpowers (v : G) ≤ H ⊔ B :=
    sup_le le_sup_right (by rw [Subgroup.zpowers_le]; exact Subgroup.mem_sup_left v.2)
  have hEB := hmax _ hE le_sup_left hEle
  have hvB : (v : G) ∈ B := by
    have : (v : G) ∈ B ⊔ Subgroup.zpowers (v : G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [hEB] at this
  have hπvc : π v ∈ Subgroup.center (PQuot p H) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : ⁅(l : G), (v : G)⁆ ∈ GLAPPrimeCoreOf p H := (hC hvB).2 l l.2
    have h2 : ⁅l, v⁆ ∈ GLAPPrimeCore p ↥H := by
      obtain ⟨c, hc, hcG⟩ := h1
      have : c = ⁅l, v⁆ := Subtype.ext hcG
      rwa [this] at hc
    have h3 : π ⁅l, v⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h2
    rw [map_commutatorElement] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  apply hycen
  rw [hπv] at hπvc
  obtain ⟨s, t, hst⟩ := Nat.Coprime.isCoprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have : π y = (π y ^ m) ^ t := by
    have e : (1 : ℤ) = (p : ℤ) * s + (m : ℤ) * t := by linarith [hst]
    calc π y = π y ^ (1 : ℤ) := (zpow_one _).symm
      _ = π y ^ ((p : ℤ) * s + (m : ℤ) * t) := by rw [← e]
      _ = (π y ^ m) ^ t := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hpy, one_zpow, one_mul]
  have hfin : π y ∈ Subgroup.center (PQuot p H) := by
    rw [this]
    exact Subgroup.zpow_mem _ hπvc t
  exact hfin

theorem le_commutator_of_maximal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X H B : Subgroup G}
    (hH : GLAPComponent p X H) (hB : IsElemAbelian p B)
    (hBH : B ≤ Subgroup.normalizer (H : Set G))
    (hmax : ∀ E : Subgroup G, IsElemAbelian p E → B ≤ E → E ≤ H ⊔ B → E = B) :
    H ≤ (⁅H, B⁆ : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup G := ⁅H, B⁆ with hN
  have hNH : N ≤ H := by
    rw [hN, Subgroup.commutator_le]
    intro h hh b hb
    rw [commutatorElement_def]
    have : b * h⁻¹ * b⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 (hBH hb) h⁻¹).1 (H.inv_mem hh)
    simpa [mul_assoc] using H.mul_mem hh this
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => CFSG.HardMathSupport.Solomon.Coordinator.Generation228.tools_conj_comm_X
      (D := B) hc y hy, fun hy => ?_⟩
    have := CFSG.HardMathSupport.Solomon.Coordinator.Generation228.tools_conj_comm_X
      (D := B) (H.inv_mem hc) _ hy
    simpa [mul_assoc] using this
  have key : H ≤ N ⊔ GLAPPrimeCoreOf p H := by
    by_contra hnot
    have hQ := isQuasisimple_pQuot_of_glaPComponent hp hH
    let π : ↥H →* PQuot p H := QuotientGroup.mk' (GLAPPrimeCore p ↥H)
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hnormN : (N.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hHN
    have hnormNbar : ((N.subgroupOf H).map π).Normal := hnormN.map π hπs
    have hne : (N.subgroupOf H).map π ≠ ⊤ := by
      intro htop
      apply hnot
      intro h hh
      have hmem : π ⟨h, hh⟩ ∈ (N.subgroupOf H).map π := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnπ⟩ := hmem
      have hq : (n⁻¹ * ⟨h, hh⟩ : ↥H) ∈ GLAPPrimeCore p ↥H := by
        rw [← QuotientGroup.eq]
        exact hnπ
      have hnN : (n : G) ∈ N := hn
      have hqO : ((n⁻¹ * ⟨h, hh⟩ : ↥H) : G) ∈ GLAPPrimeCoreOf p H := ⟨_, hq, rfl⟩
      have : h = (n : G) * ((n⁻¹ * ⟨h, hh⟩ : ↥H) : G) := by simp
      rw [this]
      exact Subgroup.mul_mem_sup hnN hqO
    have hcent := le_center_of_normal_of_isQuasisimple hQ hnormNbar hne
    have hZ : ∀ x : ↥H, (x : G) ∈ N → π x ∈ Subgroup.center (PQuot p H) := fun x hx =>
      hcent (Subgroup.mem_map_of_mem π (show x ∈ N.subgroupOf H from hx))
    refine not_le_centModSubgroup_of_maximal hp hp2 hH hB hBH hmax (fun b hb => ?_)
    have hbn : b ∈ Subgroup.normalizer (H : Set G) := hBH hb
    let cb : ↥H →* ↥H := ((MulAut.conj b).toMonoidHom.comp H.subtype).codRestrict H
      (fun l => (Subgroup.mem_normalizer_iff.1 hbn l).1 l.2)
    have hcb : ∀ l : ↥H, ((cb l : ↥H) : G) = b * l * b⁻¹ := fun l => rfl
    have hz : ∀ l : ↥H, π (l⁻¹ * cb l) ∈ Subgroup.center (PQuot p H) := by
      intro l
      apply hZ
      have : (((l⁻¹ * cb l : ↥H)) : G) = ⁅(l : G)⁻¹, b⁆ := by
        simp [hcb, commutatorElement_def, mul_assoc]
      rw [this]
      exact Subgroup.commutator_mem_commutator (H.inv_mem l.2) hb
    let T : Subgroup ↥H := MonoidHom.eqLocus (π.comp cb) π
    have hcomm : ∀ l₁ l₂ : ↥H, ⁅l₁, l₂⁆ ∈ T := by
      intro l₁ l₂
      show π (cb ⁅l₁, l₂⁆) = π ⁅l₁, l₂⁆
      have e : ∀ l : ↥H, π (cb l) = π l * π (l⁻¹ * cb l) := by
        intro l
        rw [map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      rw [map_commutatorElement, map_commutatorElement, map_commutatorElement, e l₁, e l₂,
        commutatorElement_mul_center_left (hz l₁), commutatorElement_mul_center_right (hz l₂)]
    have hT : T = ⊤ := by
      have hperf : commutator ↥H = ⊤ :=
        (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hH)).commutator_eq_top
      rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
      intro l₁ _ l₂ _
      exact hcomm l₁ l₂
    refine ⟨hbn, fun l hl => ?_⟩
    have hmem : (⟨l, hl⟩ : ↥H)⁻¹ ∈ T := hT ▸ Subgroup.mem_top _
    have hmem' : π (cb (⟨l, hl⟩ : ↥H)⁻¹) = π (⟨l, hl⟩ : ↥H)⁻¹ := hmem
    have hq : ((⟨l, hl⟩ : ↥H)⁻¹)⁻¹ * cb (⟨l, hl⟩ : ↥H)⁻¹ ∈ GLAPPrimeCore p ↥H := by
      rw [← QuotientGroup.eq]
      exact hmem'.symm
    refine ⟨_, hq, ?_⟩
    simp [hcb, commutatorElement_def, mul_assoc]
  exact CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup hp hH
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp H))
    ((Subgroup.map_subtype_le _).trans hHN) key

end CFSG.LocalAnalysis.GLTheoremA.P51
