module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem leafDSBZSJ [DSLeaf LeafSylowS] [DSLeaf LeafZiStructure] [DSLeaf LeafFaithfulA5] [DSLeaf LeafRankBounds] : LeafDSBZSJ := by
  intro G _ _ L1 L2 S h hq hq8 hcen
  have hpr : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hSP, hS2, -⟩, hQS⟩ := sylow_s h
  obtain ⟨hcard, A, B, -, ⟨eA⟩, -⟩ := hq8
  set P : Subgroup G := L1 ⊔ bigB L1 L2 S
  set Q : Subgroup G := pCoreOf 2 P
  have hCT : P ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := F1.parabolic_charTwo h
  have hPN1 : P ≤ Subgroup.normalizer (L1 : Set G) := F1.parabolic_le_normalizer h
  have hL1P : L1 ≤ P := le_sup_left
  have hQnorm : P ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hQP : Q ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hO1norm : P ≤ Subgroup.normalizer ((pCoreOf 2 L1 : Subgroup G) : Set G) :=
    hPN1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1)
  have hO1P : pCoreOf 2 L1 ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans hL1P) hO1norm
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L1)
  have hO1nt : Nontrivial ↥(pCoreOf 2 L1) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have hO1ne : pCoreOf 2 L1 ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hO1nt
  have hSne : S ≠ ⊥ := fun h0 => hO1ne (eq_bot_iff.mpr ((hO1P.trans hQS).trans h0.le))
  have hSnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  have hZnt : Nontrivial ↥(Subgroup.center ↥S) := hS2.center_nontrivial
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥S) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hS2.to_subgroup (Subgroup.center ↥S))
    have h1 := Finite.one_lt_card_iff_nontrivial.mpr hZnt
    rw [hn] at h1 ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at h1
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥S)) 2 hdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  obtain ⟨z, hzS, hzc, hz1, hz2⟩ :
      ∃ z : G, z ∈ S ∧ (∀ s ∈ S, s * z = z * s) ∧ z ≠ 1 ∧ z ^ 2 = 1 := by
    refine ⟨((x : ↥S) : G), (x : ↥S).2, fun s hs => ?_, fun h1 => hx1 ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp x.2 ⟨s, hs⟩
      simpa using congrArg (fun y : ↥S => (y : G)) this
    · apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    · have h2 : x ^ 2 = 1 := by
        have h := pow_orderOf_eq_one x
        rwa [hx] at h
      simpa using congrArg (fun y : ↥(Subgroup.center ↥S) => ((y : ↥S) : G)) h2
  have hzCS : z ∈ centerOf S := ⟨hzS, Subgroup.mem_centralizer_iff.mpr hzc⟩
  have hzL2 : ∀ l ∈ L2, l * z = z * l := fun l hl => Subgroup.mem_centralizer_iff.mp (hcen hzCS) l hl
  have hzQC : ∀ q ∈ Q, q * z = z * q := fun q hq => hzc q (hQS hq)
  have hzQ : z ∈ Q := hCT ⟨hSP hzS, Subgroup.mem_centralizer_iff.mpr hzQC⟩
  have hconj_z : ∀ g : G, Commute g z → ∀ x ∈ Subgroup.zpowers z, g * x * g⁻¹ ∈ Subgroup.zpowers z := by
    intro g hgc x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [(hgc.zpow_right n).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) n
  have hNz : ∀ g : G, Commute g z →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro g hgc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj_z g hgc x
    · intro hx
      have := hconj_z g⁻¹ hgc.inv_left _ hx
      simpa [mul_assoc] using this
  have hL1z : ∃ l ∈ L1, l * z ≠ z * l := by
    by_contra hcon
    push Not at hcon
    have hXp : IsPGroup 2 (Subgroup.zpowers z) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
      norm_num
    have hXle : Subgroup.zpowers z ≤ L1 ⊔ L2 ⊔ S :=
      Subgroup.zpowers_le.mpr ((show S ≤ L1 ⊔ L2 ⊔ S from le_sup_right) hzS)
    have h1 : L1 ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
      fun l hl => hNz l (hcon l hl)
    have h2 : L2 ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
      fun l hl => hNz l (hzL2 l hl)
    have h3 : S ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
      fun s hs => hNz s (hzc s hs)
    have hX := coreFree h.hyp hXp hXle h1 h2 h3
    have hzmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [hX, Subgroup.mem_bot] at hzmem
    exact hz1 hzmem
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup G,
      F = Subgroup.closure {x : G | ∃ p ∈ P, x = p * z * p⁻¹} := ⟨_, rfl⟩
  have hYΩ : ∀ p ∈ P, p * z * p⁻¹ ∈ Q ∧ (∀ q ∈ Q, q * (p * z * p⁻¹) = p * z * p⁻¹ * q) ∧
      (p * z * p⁻¹) ^ 2 = 1 := by
    intro p hp
    have hmem : p * z * p⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQnorm hp) z).mp hzQ
    refine ⟨hmem, fun q hq => ?_, ?_⟩
    · have hq' : p⁻¹ * q * p⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hQnorm (P.inv_mem hp)) q).mp hq
      rw [inv_inv] at hq'
      have hc : p⁻¹ * q * p * z = z * (p⁻¹ * q * p) := hzQC _ hq'
      calc q * (p * z * p⁻¹) = p * (p⁻¹ * q * p * z) * p⁻¹ := by group
        _ = p * (z * (p⁻¹ * q * p)) * p⁻¹ := by rw [hc]
        _ = p * z * p⁻¹ * q := by group
    · calc (p * z * p⁻¹) ^ 2 = p * z ^ 2 * p⁻¹ := by simp only [pow_two, mul_assoc, inv_mul_cancel_left]
        _ = 1 := by rw [hz2]; group
  have hFΩ : ∀ x ∈ F, x ∈ Q ∧ (∀ q ∈ Q, q * x = x * q) ∧ x ^ 2 = 1 := by
    intro x hx
    rw [hFdef] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      exact hYΩ p hp
    | one => exact ⟨Q.one_mem, fun q _ => by simp, by simp⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨Q.mul_mem ihx.1 ihy.1, fun q hq => ?_, ?_⟩
      · exact Commute.mul_right (show Commute q x from ihx.2.1 q hq)
          (show Commute q y from ihy.2.1 q hq)
      · have hyx : y * x = x * y := ihx.2.1 y ihy.1
        calc (x * y) ^ 2 = x * (y * x) * y := by simp only [pow_two, mul_assoc]
          _ = x * (x * y) * y := by rw [hyx]
          _ = x ^ 2 * y ^ 2 := by simp only [pow_two, mul_assoc]
          _ = 1 := by rw [ihx.2.2, ihy.2.2, mul_one]
    | inv x _ ihx =>
      refine ⟨Q.inv_mem ihx.1, fun q hq => ?_, ?_⟩
      · exact Commute.inv_right (show Commute q x from ihx.2.1 q hq)
      · rw [inv_pow, ihx.2.2, inv_one]
  have hFQ : F ≤ Q := fun x hx => (hFΩ x hx).1
  have hzF : z ∈ F := by
    rw [hFdef]
    exact Subgroup.subset_closure ⟨1, P.one_mem, by simp⟩
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x :=
    fun x hx y hy => ((hFΩ x hx).2.1 y (hFQ hy)).symm
  have hFelem : ∀ x ∈ F, x ^ 2 = 1 := fun x hx => (hFΩ x hx).2.2
  have hFab : IsElemAbelian 2 F :=
    ⟨⟨⟨fun a b => Subtype.ext (hFcomm a a.2 b b.2)⟩⟩, hFelem⟩
  have hconjF : ∀ g ∈ P, ∀ x ∈ F, g * x * g⁻¹ ∈ F := by
    intro g hg x hx
    rw [hFdef] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨g * p, P.mul_mem hg hp, by group⟩
    | one => simpa using Subgroup.one_mem _
    | mul x y _ _ ihx ihy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ihx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ihx
  have hPF : P ≤ Subgroup.normalizer (F : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjF g hg x, fun hx => ?_⟩
    have := hconjF g⁻¹ (P.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hPbot : P ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  have hFP : F ≤ P := hFQ.trans hQP
  have hcoreF : ∀ q ∈ pCoreOf 2 P, ∀ e ∈ F, ⁅q, e⁆ ∈ (⊥ : Subgroup G) := by
    intro q hq e he
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hFΩ e he).2.1 q hq
  have hnt : ∃ l ∈ L1, ∃ e ∈ F, ⁅l, e⁆ ∉ (⊥ : Subgroup G) := by
    obtain ⟨l, hl, hlz⟩ := hL1z
    refine ⟨l, hl, z, hzF, fun h0 => hlz ?_⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h0
    exact h0
  have hcardF : Nat.card F ≤ 16 := (rank_bounds (G := G)).2 F hFab
  have hsecF : IsElemSec (⊥ : Subgroup G) F := by
    refine ⟨bot_le, ?_, fun e he => ?_⟩
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hFcomm x hx y hy
    · rw [Subgroup.mem_bot]
      exact hFelem e he
  have hcardrel : (⊥ : Subgroup G).relIndex F ≤ 16 := by
    rw [Subgroup.relIndex_bot_left]
    exact hcardF
  have hA5 : A5Chief P L1 F ⊥ :=
    faithful_a5 hL1P hPN1 hFP hPF hPbot hsecF hcardrel hq hcoreF hnt
  have hFcard : Nat.card F = 16 := by
    have := hA5.card
    rwa [Subgroup.relIndex_bot_left] at this
  have hXN : P ≤ Subgroup.normalizer ((F ⊓ pCoreOf 2 L1 : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have e1 := Subgroup.mem_normalizer_iff.mp (hPF hg) x
    have e2 := Subgroup.mem_normalizer_iff.mp (hO1norm hg) x
    simp only [Subgroup.mem_inf]
    exact and_congr e1 e2
  rcases hA5.irred (F ⊓ pCoreOf 2 L1) bot_le inf_le_left hXN with hX | hX
  ·
    have hdvd2 : 2 ∣ Nat.card ↥(pCoreOf 2 L1) := by
      rw [hcard]
      norm_num
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(pCoreOf 2 L1)) 2 hdvd2
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hc
      norm_num at hc
    have hc2 : c ^ 2 = 1 := by
      have h := pow_orderOf_eq_one c
      rwa [hc] at h
    obtain ⟨c', hc'⟩ : ∃ c' : G, c' = (c : G) := ⟨_, rfl⟩
    have hc'O : c' ∈ pCoreOf 2 L1 := hc' ▸ c.2
    have hc'Q : c' ∈ Q := hO1P hc'O
    have hc'1 : c' ≠ 1 := by
      intro h0
      apply hc1
      apply Subtype.ext
      rw [hc'] at h0
      simpa using h0
    have hc'2 : c' ^ 2 = 1 := by
      rw [hc']
      simpa using congrArg (fun y : ↥(pCoreOf 2 L1) => (y : G)) hc2
    have hcF : ∀ x ∈ F, c' * x = x * c' := fun x hx => (hFΩ x hx).2.1 c' hc'Q
    obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = Subgroup.closure ((F : Set G) ∪ {c'}) := ⟨_, rfl⟩
    have hEform : ∀ x ∈ E, ∃ f ∈ F, ∃ n : ℤ, x = f * c' ^ n := by
      intro x hx
      rw [hEdef] at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact ⟨x, hx, 0, by simp⟩
        · rw [Set.mem_singleton_iff] at hx
          exact ⟨1, F.one_mem, 1, by simp [hx]⟩
      | one => exact ⟨1, F.one_mem, 0, by simp⟩
      | mul x y _ _ ihx ihy =>
        obtain ⟨f, hf, n, rfl⟩ := ihx
        obtain ⟨g, hg, m, rfl⟩ := ihy
        refine ⟨f * g, F.mul_mem hf hg, n + m, ?_⟩
        have hcg : Commute (c' ^ n) g := Commute.zpow_left (show Commute c' g from hcF g hg) n
        calc f * c' ^ n * (g * c' ^ m) = f * (c' ^ n * g) * c' ^ m := by group
          _ = f * (g * c' ^ n) * c' ^ m := by rw [hcg.eq]
          _ = f * g * (c' ^ n * c' ^ m) := by group
          _ = f * g * c' ^ (n + m) := by rw [zpow_add]
      | inv x _ ihx =>
        obtain ⟨f, hf, n, rfl⟩ := ihx
        refine ⟨f⁻¹, F.inv_mem hf, -n, ?_⟩
        have hcf : Commute (c' ^ n) f := Commute.zpow_left (show Commute c' f from hcF f hf) n
        calc (f * c' ^ n)⁻¹ = (c' ^ n)⁻¹ * f⁻¹ := by group
          _ = f⁻¹ * (c' ^ n)⁻¹ := (hcf.inv_left.inv_right).eq
          _ = f⁻¹ * c' ^ (-n) := by rw [zpow_neg]
    have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx y hy
      obtain ⟨f, hf, n, rfl⟩ := hEform x hx
      obtain ⟨g, hg, m, rfl⟩ := hEform y hy
      have hfg : Commute f g := hFcomm f hf g hg
      have hcg : Commute (c' ^ n) g := Commute.zpow_left (show Commute c' g from hcF g hg) n
      have hfcm : Commute f (c' ^ m) := Commute.zpow_right (show Commute f c' from (hcF f hf).symm) m
      have hcc : Commute (c' ^ n) (c' ^ m) := ((Commute.refl c').zpow_left n).zpow_right m
      have h1 : Commute (f * c' ^ n) g := Commute.mul_left hfg hcg
      have h2 : Commute (f * c' ^ n) (c' ^ m) := Commute.mul_left hfcm hcc
      exact Commute.mul_right h1 h2
    have hcz : ∀ n : ℤ, (c' ^ n) ^ 2 = 1 := by
      intro n
      calc (c' ^ n) ^ 2 = (c' ^ (2 : ℤ)) ^ n := by
            rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
            norm_num
        _ = 1 := by
            rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hc'2, one_zpow]
    have hEab : IsElemAbelian 2 E := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩, ?_⟩
      intro x hx
      obtain ⟨f, hf, n, rfl⟩ := hEform x hx
      have hcn : Commute f (c' ^ n) := Commute.zpow_right (show Commute f c' from (hcF f hf).symm) n
      rw [hcn.mul_pow, hFelem f hf, hcz n, one_mul]
    have hFE : F ≤ E := by
      rw [hEdef]
      intro x hx
      exact Subgroup.subset_closure (Or.inl hx)
    have hc'E : c' ∈ E := by
      rw [hEdef]
      exact Subgroup.subset_closure (Or.inr rfl)
    have hc'F : c' ∉ F := by
      intro hcF'
      have hmem : c' ∈ F ⊓ pCoreOf 2 L1 := Subgroup.mem_inf.mpr ⟨hcF', hc'O⟩
      rw [hX, Subgroup.mem_bot] at hmem
      exact hc'1 hmem
    have hrel : F.relIndex E ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hc'F (h1 hc'E)
    have hmul := Subgroup.relIndex_mul_card (H := F) (K := E)
    rw [inf_eq_left.mpr hFE, hFcard] at hmul
    have hEle := (rank_bounds (G := G)).2 E hEab
    have hpos : 0 < Nat.card ↥E := Nat.card_pos
    have h2 : 2 ≤ F.relIndex E := by omega
    omega
  ·
    exfalso
    have hrelO : F.relIndex (pCoreOf 2 L1) = 2 := by
      have hm := Subgroup.relIndex_mul_card (H := F) (K := pCoreOf 2 L1)
      rw [hX, hFcard, hcard] at hm
      omega
    have hF'cen : ∀ n ∈ F.subgroupOf (pCoreOf 2 L1), ∀ g : ↥(pCoreOf 2 L1), g * n = n * g := by
      intro n hn g
      apply Subtype.ext
      have hnF : (n : G) ∈ F := Subgroup.mem_subgroupOf.mp hn
      exact (hFΩ (n : G) hnF).2.1 (g : G) (hO1P g.2)
    haveI hF'N : (F.subgroupOf (pCoreOf 2 L1)).Normal :=
      ⟨fun n hn g => by
        rw [hF'cen n hn g, mul_inv_cancel_right]
        exact hn⟩
    have hF'Z : F.subgroupOf (pCoreOf 2 L1) ≤ Subgroup.center ↥(pCoreOf 2 L1) :=
      fun n hn => Subgroup.mem_center_iff.mpr (fun g => hF'cen n hn g)
    haveI hcyc : IsCyclic (↥(pCoreOf 2 L1) ⧸ F.subgroupOf (pCoreOf 2 L1)) :=
      isCyclic_of_prime_card (p := 2) hrelO
    have hHcomm : IsMulCommutative ↥(pCoreOf 2 L1) :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (F.subgroupOf (pCoreOf 2 L1)))
        (by rw [QuotientGroup.ker_mk']; exact hF'Z)
    have hq8comm : ∀ a b : QuaternionGroup 2, a * b = b * a := by
      intro a b
      have hAab : (eA.symm a * eA.symm b : ↥A) = eA.symm b * eA.symm a := by
        apply Subtype.ext
        exact hHcomm.is_comm.comm ((eA.symm a : ↥A) : ↥(pCoreOf 2 L1))
          ((eA.symm b : ↥A) : ↥(pCoreOf 2 L1))
      have := congrArg eA hAab
      simpa using this
    have hbad := hq8comm (QuaternionGroup.a 1) (QuaternionGroup.xa 0)
    revert hbad
    decide

end CFSG.GH74.QTGen4.DSGen4
