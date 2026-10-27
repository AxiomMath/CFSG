module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64H
public import CFSG.GH74.GLS.C3.Layer1.Th2P64E
public import CFSG.GH74.GLS.C3.Layer1.Th2PumpTerm
public import CFSG.GH74.GLS.C3.Layer1.Th2P64D

public section

open Equiv Equiv.Perm Subgroup CFSG
open CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs CFSG.ABGLocalTools CFSG.GH74.GLS.IVK
open scoped commutatorElement

namespace CFSG.GH74.GLS.Th2.Obs

variable {G : Type} [Group G] [Finite G]

theorem Obstr52.not_mem_J {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hb2 : orderOf b = 2) : b ∉ J := by
  intro hbJ
  exact h.ne_one (PumpTerm.eq_one_of_mem_of_cSec h.centerlessBar hbJ (mem_CxK_self' h.comp.1).2 hb2)

theorem Obstr52.eq_of_actOn_eq_one {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hb2 : orderOf b = 2) (hN2 : twoPartCard (CxK b J) = 2)
    {e₇ : kBar J ≃* alternatingGroup (Fin 7)} {W : Subgroup G}
    (hWb : W ≤ centralizer ({b} : Set G)) (hW2 : IsPGroup 2 ↥W)
    (hWN : W ≤ normalizer (J : Set G)) {g : G} (hg : g ∈ W)
    (hψ : actOn e₇ hWN ⟨g, hg⟩ = 1) : g = 1 ∨ g = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgC : g ∈ CxK b J := ⟨hWb hg, (actOn_eq_one_iff e₇ hWN hg).1 hψ⟩
  by_cases hg1 : g = 1
  · exact Or.inl hg1
  · right
    have hle : Nat.card (zpowers g) ≤ 2 := by
      have := Th2.L627.card_le_twoPartCard (A := zpowers g) (X := CxK b J)
        (hW2.to_le (zpowers_le.2 hg)) (zpowers_le.2 hgC)
      rwa [hN2] at this
    rw [Nat.card_zpowers] at hle
    have hpos : 0 < orderOf g := orderOf_pos g
    have h1 : orderOf g ≠ 1 := fun h1 => hg1 (orderOf_eq_one_iff.1 h1)
    exact eq_of_mem_CxK_of_orderOf_two h.comp hb2 hN2 hgC (by omega)

theorem Obstr52.card_ker_actOn {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hN2 : twoPartCard (CxK b J) = 2)
    {e₇ : kBar J ≃* alternatingGroup (Fin 7)} {W : Subgroup G}
    (hWb : W ≤ centralizer ({b} : Set G)) (hW2 : IsPGroup 2 ↥W) (hbW : b ∈ W)
    (hWN : W ≤ normalizer (J : Set G)) : Nat.card (actOn e₇ hWN).ker = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := actOn e₇ hWN with hφ
  have hbk : (⟨b, hbW⟩ : ↥W) ∈ φ.ker := by
    show φ ⟨b, hbW⟩ = 1
    exact (actOn_eq_one_iff e₇ hWN hbW).2 (mem_CxK_self' h.comp.1).2
  have hle : Nat.card φ.ker ≤ 2 := by
    have hk2 : IsPGroup 2 ↥(φ.ker.map W.subtype) := (hW2.to_subgroup φ.ker).map W.subtype
    have hkle : φ.ker.map W.subtype ≤ CxK b J := by
      rintro g ⟨⟨g', hg'⟩, hgk, rfl⟩
      exact ⟨hWb hg', (actOn_eq_one_iff e₇ hWN hg').1 hgk⟩
    have := Th2.L627.card_le_twoPartCard hk2 hkle
    rw [hN2, Subgroup.card_map_of_injective W.subtype_injective] at this
    exact this
  have hge : 2 ≤ Nat.card φ.ker := by
    have hb1 : (⟨b, hbW⟩ : ↥W) ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
    have : φ.ker ≠ ⊥ := fun hbot => hb1 (by simpa [hbot] using hbk)
    have := (Subgroup.one_lt_card_iff_ne_bot φ.ker).2 this
    omega
  omega


theorem eight_dvd_card_centralizer_alt {s : Perm (Fin 7)} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    8 ∣ Nat.card ↥(centralizer ({s} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) := by
  have hsq : s ^ 2 = 1 := by rw [sq]; exact hs2
  rcases A7.involution_cycleType s hsq hs1 with h | h | h
  · rw [A7.card_centralizer_A7_two h hsq hs1]; norm_num
  · rw [A7.card_centralizer_A7_two_two h hsq hs1]; norm_num
  · rw [A7.card_centralizer_A7_two_two_two h hsq hs1]; norm_num

theorem Obstr52.V_split {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (e₇ : kBar J ≃* alternatingGroup (Fin 7)) (hN2 : twoPartCard (CxK b J) = 2)
    (hB16 : Nat.card ↥B = 16)
    {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxb : x ≠ b) (hxcomm : x * b = b * x)
    (hBx : B ≤ centralizer ({x} : Set G))
    {V : Subgroup G} (hV : IsSylowOf 2 V (centralizer ({x, b} : Set G))) (hBV : B ≤ V)
    (hVN : V ≤ normalizer (J : Set G)) :
    ∃ (t₀ : G) (ht₀B : t₀ ∈ B), t₀ * t₀ = 1 ∧ (actOn e₇ hVN ⟨t₀, hBV ht₀B⟩).IsSwap ∧
      (∀ z ∈ zpowers t₀ ⊔ zpowers b, ∀ v ∈ V, z * v = v * z) ∧ Nat.card ↥(V ⊓ J) = 8 ∧
      (∀ v ∈ V, ∃ p ∈ V ⊓ J, ∃ z ∈ zpowers t₀ ⊔ zpowers b, v = p * z) ∧
      (∀ (z : G) (hzV : z ∈ V), z ∈ zpowers t₀ ⊔ zpowers b →
        actOn e₇ hVN ⟨z, hzV⟩ = 1 ∨ actOn e₇ hVN ⟨z, hzV⟩ = actOn e₇ hVN ⟨t₀, hBV ht₀B⟩) ∧
      (∀ (g : G) (hg : g ∈ V), actOn e₇ hVN ⟨g, hg⟩ = 1 → g = 1 ∨ g = b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  set D := centralizer ({x, b} : Set G) with hD
  have hDb : D ≤ centralizer ({b} : Set G) := Subgroup.centralizer_le (by simp)
  have hDx : D ≤ centralizer ({x} : Set G) := Subgroup.centralizer_le (by simp)
  have hDN : D ≤ normalizer (J : Set G) := hDb.trans (h.centralizer_le_normalizer hG4 hB)
  have hxD : x ∈ D := by
    rw [hD, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | rfl
    · rfl
    · exact hxcomm.symm
  have hbD : b ∈ D := by
    rw [hD, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | rfl
    · exact hxcomm
    · rfl
  have hBD : B ≤ D := by
    intro β hβ
    rw [hD, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | rfl
    · exact (mem_centralizer_singleton_iff.1 (hBx hβ)).symm
    · exact hBc _ h.mem β hβ
  have hVD : V ≤ D := hV.le
  have hV2 : IsPGroup 2 ↥V := hV.isPGroup
  have hVb : V ≤ centralizer ({b} : Set G) := hVD.trans hDb
  have hVx : V ≤ centralizer ({x} : Set G) := hVD.trans hDx
  have hbV : b ∈ V := hBV h.mem
  have hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7)) := ⟨e₇⟩
  have hV32 : Nat.card ↥V = 32 := by
    have hle := h.card_le_32 hG4 hB hA hN2 hVb hV2
    have hdvd := h.thirtyTwo_dvd_card hG4 hB hA hN2 hx2 hx1 hxb hxcomm hBx
    have h5 : 5 ≤ (Nat.card D).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by simpa using hdvd)
    have hge : 32 ≤ Nat.card ↥V := by
      rw [hV.card_eq]
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (Nat.card D).factorization 2 := Nat.pow_le_pow_right (by norm_num) h5
    omega
  set ψ := actOn e₇ hVN with hψ
  have hkerV : Nat.card ψ.ker = 2 := h.card_ker_actOn hN2 hVb hV2 hbV hVN
  have hrangeV : Nat.card ψ.range = 16 := by
    have := Subgroup.card_ker_mul_card_range ψ
    rw [hkerV, hV32] at this
    omega
  have hbJ : b ∉ J := h.not_mem_J hb2
  have hker : ∀ (g : G) (hg : g ∈ V), ψ ⟨g, hg⟩ = 1 → g = 1 ∨ g = b := fun g hg hψ1 =>
    h.eq_of_actOn_eq_one hb2 hN2 hVb hV2 hVN hg hψ1
  obtain ⟨F, t, hF, ht, hdis, hrange⟩ := h.exists_image_B hG4 hB e₇ hBV hVN
  set φB := actOn e₇ (hBV.trans hVN) with hφB
  have hBb : B ≤ centralizer ({b} : Set G) := hBV.trans hVb
  have hkerB : Nat.card φB.ker = 2 :=
    h.card_ker_actOn hN2 hBb (CFSG.IsElementaryAbelian.isPGroup 2 ↥B) h.mem (hBV.trans hVN)
  have hMcard : Nat.card ↥(F ⊔ zpowers t) = 8 := by
    have := Subgroup.card_ker_mul_card_range φB
    rw [hkerB, hB16, hrange] at this
    omega
  have hMY : F ⊔ zpowers t ≤ ψ.range := by
    rw [← hrange]
    rintro _ ⟨⟨β, hβ⟩, rfl⟩
    exact ⟨⟨β, hBV hβ⟩, rfl⟩
  have htcomm : ∀ (v : G) (hv : v ∈ V), ψ ⟨v, hv⟩ * t = t * ψ ⟨v, hv⟩ := fun v hv =>
    forall_comm_swap_of_card hF ht hdis hMY (by rw [hrangeV, hMcard]) _ ⟨⟨v, hv⟩, rfl⟩
  have hsign_t : Equiv.Perm.sign t = -1 := by
    obtain ⟨a₁, a₂, hne, rfl⟩ := ht
    exact Equiv.Perm.sign_swap hne
  have ht1 : t ≠ 1 := ht.isCycle.ne_one
  have htr : t ∈ F ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  rw [← hrange] at htr
  obtain ⟨⟨t₀, ht₀B⟩, ht₀⟩ := htr
  have ht₀V : t₀ ∈ V := hBV ht₀B
  have ht₀ψ : ψ ⟨t₀, ht₀V⟩ = t := ht₀
  have ht₀sq : t₀ * t₀ = 1 := hBsq t₀ ht₀B
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    apply ht1
    rw [← ht₀ψ]
    have : (⟨t₀, ht₀V⟩ : ↥V) = 1 := Subtype.ext h1
    rw [this, map_one]
  have ht₀o : orderOf t₀ = 2 := orderOf_eq_prime (by rw [sq]; exact ht₀sq) ht₀1
  have hbψ : ψ ⟨b, hbV⟩ = 1 := (actOn_eq_one_iff e₇ hVN hbV).2 (mem_CxK_self' h.comp.1).2
  have hψJ : ∀ (g : G) (hg : g ∈ V ⊓ J),
      ψ ⟨g, hg.1⟩ = ((e₇ (QuotientGroup.mk (⟨g, hg.2⟩ : ↥J))) : Perm (Fin 7)) := fun g hg =>
    (actOn_apply e₇ hVN hg.1).trans (a7Act_of_mem e₇ hg.2)
  have hψeven : ∀ (g : G) (hg : g ∈ V ⊓ J), ψ ⟨g, hg.1⟩ ∈ alternatingGroup (Fin 7) := fun g hg => by
    rw [hψJ g hg]; exact (e₇ _).2
  have hψinj : ∀ (g : G) (hg : g ∈ V ⊓ J), ψ ⟨g, hg.1⟩ = 1 → g = 1 := by
    intro g hg hg1
    rcases hker g hg.1 hg1 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hg.2) hbJ
  have ht₀p : ∀ p ∈ V ⊓ J, t₀ * p = p * t₀ := by
    intro p hp
    set c : G := t₀ * p * t₀⁻¹ * p⁻¹ with hc
    have hcV : c ∈ V := V.mul_mem (V.mul_mem (V.mul_mem ht₀V hp.1) (V.inv_mem ht₀V)) (V.inv_mem hp.1)
    have hcJ : c ∈ J := by
      have h1 : t₀ * p * t₀⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hVN ht₀V) p).1 hp.2
      exact J.mul_mem h1 (J.inv_mem hp.2)
    have hψc : ψ ⟨c, hcV⟩ = 1 := by
      have : (⟨c, hcV⟩ : ↥V) = ⟨t₀, ht₀V⟩ * ⟨p, hp.1⟩ * ⟨t₀, ht₀V⟩⁻¹ * ⟨p, hp.1⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, ht₀ψ]
      have h2 := htcomm p hp.1
      rw [← h2]
      group
    have hc1 : c = 1 := hψinj c ⟨hcV, hcJ⟩ hψc
    exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact hc1)
  have hbt₀ : t₀ * b = b * t₀ := hBc t₀ ht₀B b h.mem
  have hcZ : ∀ u ∈ zpowers t₀, ∀ w ∈ zpowers b, u * w = w * u := by
    intro u hu w hw
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_zpow (show Commute t₀ b from hbt₀) m n).eq
  set Z₀ : Subgroup G := zpowers t₀ ⊔ zpowers b with hZ₀
  have hZ₀V : Z₀ ≤ V := sup_le (zpowers_le.2 ht₀V) (zpowers_le.2 hbV)
  have hZP : ∀ z ∈ Z₀, ∀ p ∈ V ⊓ J, z * p = p * z := by
    intro z hz p hp
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_commute hcZ hz
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
    have h1 : t₀ ^ m * p = p * t₀ ^ m :=
      (Commute.zpow_left (show Commute t₀ p from ht₀p p hp) m).eq
    have h2 : b ^ n * p = p * b ^ n :=
      (Commute.zpow_left (show Commute b p from (mem_centralizer_singleton_iff.1 (hVb hp.1)).symm) n).eq
    calc t₀ ^ m * b ^ n * p = t₀ ^ m * (b ^ n * p) := by rw [mul_assoc]
      _ = t₀ ^ m * (p * b ^ n) := by rw [h2]
      _ = (t₀ ^ m * p) * b ^ n := by rw [mul_assoc]
      _ = (p * t₀ ^ m) * b ^ n := by rw [h1]
      _ = p * (t₀ ^ m * b ^ n) := by rw [mul_assoc]
  have hcommk : ∀ k ∈ zpowers t₀, ∀ m ∈ Z₀, m * k = k * m := by
    intro k hk m hm
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_commute hcZ hm
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hk
    have h1 : t₀ ^ i * t₀ ^ l = t₀ ^ l * t₀ ^ i := (Commute.zpow_zpow_self t₀ i l).eq
    have h2 : w * t₀ ^ l = t₀ ^ l * w := (hcZ _ hk w hw).symm
    calc t₀ ^ i * w * t₀ ^ l = t₀ ^ i * (w * t₀ ^ l) := by rw [mul_assoc]
      _ = t₀ ^ i * (t₀ ^ l * w) := by rw [h2]
      _ = (t₀ ^ i * t₀ ^ l) * w := by rw [mul_assoc]
      _ = (t₀ ^ l * t₀ ^ i) * w := by rw [h1]
      _ = t₀ ^ l * (t₀ ^ i * w) := by rw [mul_assoc]
  have hZ₀card : Nat.card ↥Z₀ = 4 := by
    have hkd : zpowers t₀ ⊓ zpowers b = ⊥ := by
      refine eq_bot_iff.2 fun z hz => ?_
      rw [Subgroup.mem_bot]
      rcases mem_zpowers_two ht₀o hz.1 with h0 | h0
      · exact h0
      · exfalso
        rw [h0] at hz
        rcases mem_zpowers_two hb2 hz.2 with h1 | h1
        · exact ht₀1 h1
        · apply ht1
          rw [← ht₀ψ]
          have : (⟨t₀, ht₀V⟩ : ↥V) = ⟨b, hbV⟩ := Subtype.ext h1
          rw [this]
          exact hbψ
    have hcard := card_mul_card_inf_eq (M := Z₀) (K := zpowers t₀) (D := zpowers b)
      le_sup_left le_sup_right (fun m hm k hk => by
        rw [show m * k * m⁻¹ = k by rw [hcommk k hk m hm, mul_inv_cancel_right]]
        exact hk) (fun m hm => exists_mul_of_mem_sup_of_commute hcZ hm)
    rw [hkd, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, ht₀o, hb2] at hcard
    omega
  have hψz : ∀ (z : G) (hzV : z ∈ V), z ∈ Z₀ → ψ ⟨z, hzV⟩ = 1 ∨ ψ ⟨z, hzV⟩ = t := by
    intro z hzV hz
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_commute hcZ hz
    have hu' : u ∈ V := hZ₀V (mem_sup_left hu)
    have hw' : w ∈ V := hZ₀V (mem_sup_right hw)
    have hmul : (⟨u * w, hzV⟩ : ↥V) = ⟨u, hu'⟩ * ⟨w, hw'⟩ := rfl
    have hψw : ψ ⟨w, hw'⟩ = 1 := by
      rcases mem_zpowers_two hb2 hw with h0 | h0
      · have : (⟨w, hw'⟩ : ↥V) = 1 := Subtype.ext h0
        rw [this, map_one]
      · have : (⟨w, hw'⟩ : ↥V) = ⟨b, hbV⟩ := Subtype.ext h0
        rw [this]; exact hbψ
    rw [hmul, map_mul, hψw, mul_one]
    rcases mem_zpowers_two ht₀o hu with h0 | h0
    · left
      have : (⟨u, hu'⟩ : ↥V) = 1 := Subtype.ext h0
      rw [this, map_one]
    · right
      have : (⟨u, hu'⟩ : ↥V) = ⟨t₀, ht₀V⟩ := Subtype.ext h0
      rw [this]; exact ht₀ψ
  have hPZ : (V ⊓ J) ⊓ Z₀ = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rw [Subgroup.mem_bot]
    obtain ⟨hzP, hzZ⟩ := hz
    rcases hψz z hzP.1 hzZ with h1 | h1
    · exact hψinj z hzP h1
    · exfalso
      have := hψeven z hzP
      rw [h1, Equiv.Perm.mem_alternatingGroup, hsign_t] at this
      exact absurd this (by decide)
  have hZP' : ∀ a ∈ V ⊓ J, ∀ z ∈ Z₀, a * z = z * a := fun a ha z hz => (hZP z hz a ha).symm
  set M₂ : Subgroup G := (V ⊓ J) ⊔ Z₀ with hM₂
  have hM₂V : M₂ ≤ V := sup_le inf_le_left hZ₀V
  have hM₂card : Nat.card ↥M₂ * 1 = Nat.card ↥(V ⊓ J) * 4 := by
    have hcard := card_mul_card_inf_eq (M := M₂) (K := V ⊓ J) (D := Z₀) le_sup_left le_sup_right
      (fun m hm k hk => by
        obtain ⟨p, hp, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute hZP' hm
        have hzk : z * k = k * z := hZP z hz k hk
        have : p * z * k * (p * z)⁻¹ = p * k * p⁻¹ := by
          calc p * z * k * (p * z)⁻¹ = p * (z * k) * z⁻¹ * p⁻¹ := by group
            _ = p * (k * z) * z⁻¹ * p⁻¹ := by rw [hzk]
            _ = p * k * p⁻¹ := by group
        rw [this]
        exact (V ⊓ J).mul_mem ((V ⊓ J).mul_mem hp hk) ((V ⊓ J).inv_mem hp))
      (fun m hm => exists_mul_of_mem_sup_of_commute hZP' hm)
    rw [hPZ, Subgroup.card_bot, hZ₀card] at hcard
    exact hcard
  set J₁ : Subgroup G := J ⊓ centralizer ({x} : Set G) with hJ₁
  have hJ₁D : J₁ ≤ D := by
    intro j hj
    rw [hD, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | rfl
    · exact (mem_centralizer_singleton_iff.1 hj.2).symm
    · exact (mem_centralizer_singleton_iff.1 (h.comp.1 hj.1)).symm
  have hDJ₁ : D ≤ normalizer (J₁ : Set G) := fun d hd =>
    C3.Layer1.U1a.mem_normalizer_of_norm (M := D) (L := J₁) (fun m hm k hk =>
      ⟨(Subgroup.mem_normalizer_iff.1 (hDN hm) k).1 hk.1,
        (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem (hDx hm) hk.2)
          ((centralizer ({x} : Set G)).inv_mem (hDx hm))⟩) hd
  have hVJ₁ : IsSylowOf 2 (V ⊓ J₁) J₁ := hV.inf_of_le_normalizer hJ₁D hDJ₁
  have hVJ : V ⊓ J₁ = V ⊓ J := by
    ext g
    constructor
    · rintro ⟨hgV, hgJ, -⟩
      exact ⟨hgV, hgJ⟩
    · rintro ⟨hgV, hgJ⟩
      exact ⟨hgV, hgJ, hVx hgV⟩
  have hxN : x ∈ normalizer (J : Set G) := hDN hxD
  set s : Perm (Fin 7) := a7Act J e₇ ⟨x, hxN⟩ with hs
  have hs2 : s * s = 1 := by
    rw [hs, ← map_mul]
    have : (⟨x, hxN⟩ * ⟨x, hxN⟩ : ↥(normalizer (J : Set G))) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    have h3 := (barAct_eq_one_iff _).1 ((a7Act_eq_one_iff e₇ _).1 h1)
    exact hxb (eq_of_mem_CxK_of_orderOf_two h.comp hb2 hN2 ⟨hDb hxD, h3⟩ hxo)
  let ψ₁ : ↥J₁ →* Perm (Fin 7) := (a7Act J e₇).comp (Subgroup.inclusion
    (fun j hj => Subgroup.le_normalizer hj.1 : J₁ ≤ normalizer (J : Set G)))
  have hlift : centralizer ({s} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ≤ ψ₁.range := by
    rintro y₀ ⟨hy₀c, hy₀A⟩
    have hy₀s : y₀ * s = s * y₀ := mem_centralizer_singleton_iff.1 hy₀c
    obtain ⟨y', hy'J, hy'x, hy'ψ⟩ := exists_J_lift e₇ hxN hx2 hx1 hy₀A hy₀s
    exact ⟨⟨y', hy'J, mem_centralizer_singleton_iff.2 hy'x.symm⟩, hy'ψ⟩
  have h8J₁ : 8 ∣ Nat.card J₁ := by
    have h1 : Nat.card ↥(centralizer ({s} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) ∣
        Nat.card ψ₁.range := Subgroup.card_dvd_of_le hlift
    exact (eight_dvd_card_centralizer_alt hs2 hs1).trans (h1.trans (Subgroup.card_range_dvd ψ₁))
  have hP₁ge : 8 ≤ Nat.card ↥(V ⊓ J) := by
    rw [← hVJ, hVJ₁.card_eq]
    have h5 : 3 ≤ (Nat.card J₁).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by simpa using h8J₁)
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h5
  have hM₂le : Nat.card ↥M₂ ≤ 32 := hV32 ▸ Subgroup.card_le_of_le hM₂V
  have hP₁card : Nat.card ↥(V ⊓ J) = 8 := by omega
  have hM₂V' : M₂ = V :=
    Subgroup.eq_of_le_of_card_ge hM₂V (by rw [hV32]; omega)
  have ht₀V' : ∀ v ∈ V, t₀ * v = v * t₀ := by
    intro v hv
    have hv' : v ∈ M₂ := hM₂V' ▸ hv
    obtain ⟨p, hp, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute hZP' hv'
    have h1 : t₀ * p = p * t₀ := ht₀p p hp
    have h2 : t₀ * z = z * t₀ := (hcommk t₀ (mem_zpowers t₀) z hz).symm
    calc t₀ * (p * z) = (t₀ * p) * z := by rw [mul_assoc]
      _ = (p * t₀) * z := by rw [h1]
      _ = p * (t₀ * z) := by rw [mul_assoc]
      _ = p * (z * t₀) := by rw [h2]
      _ = p * z * t₀ := by rw [mul_assoc]
  refine ⟨t₀, ht₀B, ht₀sq, ?_, ?_, hP₁card, ?_, fun z hzV hz => ?_, hker⟩
  · show (ψ ⟨t₀, ht₀V⟩).IsSwap
    rw [ht₀ψ]
    exact ht
  · intro z hz v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_commute hcZ hz
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    have h1 : t₀ ^ i * v = v * t₀ ^ i := (Commute.zpow_left (show Commute t₀ v from ht₀V' v hv) i).eq
    have h2 : b ^ j * v = v * b ^ j :=
      (Commute.zpow_left (show Commute b v from (mem_centralizer_singleton_iff.1 (hVb hv)).symm) j).eq
    calc t₀ ^ i * b ^ j * v = t₀ ^ i * (b ^ j * v) := by rw [mul_assoc]
      _ = t₀ ^ i * (v * b ^ j) := by rw [h2]
      _ = (t₀ ^ i * v) * b ^ j := by rw [mul_assoc]
      _ = (v * t₀ ^ i) * b ^ j := by rw [h1]
      _ = v * (t₀ ^ i * b ^ j) := by rw [mul_assoc]
  · intro v hv
    have hv' : v ∈ M₂ := hM₂V' ▸ hv
    obtain ⟨p, hp, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute hZP' hv'
    exact ⟨p, hp, z, hz, rfl⟩
  · rcases hψz z hzV hz with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans ht₀ψ.symm)

theorem commutator_mul_right_comm {H : Type*} [Group H] {a w z : H} (hzw : z * w = w * z) :
    ⁅a * z, w⁆ = ⁅a, w⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * z * w * (z⁻¹ * a⁻¹) * w⁻¹ = a * (z * w) * z⁻¹ * a⁻¹ * w⁻¹ := by group
    _ = a * (w * z) * z⁻¹ * a⁻¹ * w⁻¹ := by rw [hzw]
    _ = a * w * a⁻¹ * w⁻¹ := by group

theorem commutator_mul_left_comm {H : Type*} [Group H] {w a z : H} (hzw : z * w = w * z) :
    ⁅w, a * z⁆ = ⁅w, a⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  have h1 : z * w⁻¹ = w⁻¹ * z := (Commute.inv_right (show Commute z w from hzw)).eq
  calc w * (a * z) * w⁻¹ * (z⁻¹ * a⁻¹) = w * a * (z * w⁻¹) * z⁻¹ * a⁻¹ := by group
    _ = w * a * (w⁻¹ * z) * z⁻¹ * a⁻¹ := by rw [h1]
    _ = w * a * w⁻¹ * a⁻¹ := by group

theorem Obstr52.exists_swap_of_bad {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (e₇ : kBar J ≃* alternatingGroup (Fin 7)) (hN2 : twoPartCard (CxK b J) = 2)
    (hB16 : Nat.card ↥B = 16)
    {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxb : x ≠ b) (hxcomm : x * b = b * x)
    (hBx : B ≤ centralizer ({x} : Set G))
    {V : Subgroup G} (hV : IsSylowOf 2 V (centralizer ({x, b} : Set G))) (hBV : B ≤ V)
    (hVN : V ≤ normalizer (J : Set G))
    {C₀ : Subgroup G} (hC₀ : ∀ v ∈ V, ∀ c ∈ C₀, v * c * v⁻¹ ∈ C₀) (hbC : b ∉ C₀)
    {E₁ : Subgroup G} (hE₁ : E₁ ≤ B ⊓ C₀) (hE₁4 : 4 ≤ Nat.card ↥E₁)
    (hbad : ∃ u ∈ V, ∃ v ∈ V, ⁅u, v⁆ ∉ C₀) :
    ∃ (e : G) (heE : e ∈ E₁), (actOn e₇ hVN ⟨e, hBV (hE₁ heE).1⟩).IsSwap := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  obtain ⟨t₀, ht₀B, ht₀sq, ht₀swap, hZc, hP₁card, hdec, hψz, hker⟩ :=
    h.V_split hG4 hB e₇ hN2 hB16 hx2 hx1 hxb hxcomm hBx hV hBV hVN
  set ψ := actOn e₇ hVN with hψ
  have hV2 : IsPGroup 2 ↥V := hV.isPGroup
  have hbV : b ∈ V := hBV h.mem
  have hbJ : b ∉ J := h.not_mem_J hb2
  have hZ₀V : zpowers t₀ ⊔ zpowers b ≤ V := sup_le (zpowers_le.2 (hBV ht₀B)) (zpowers_le.2 hbV)
  have hψinj : ∀ (g : G) (hg : g ∈ V ⊓ J), ψ ⟨g, hg.1⟩ = 1 → g = 1 := by
    intro g hg hg1
    rcases hker g hg.1 hg1 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hg.2) hbJ
  set tt := ψ ⟨t₀, hBV ht₀B⟩ with htt
  set P₁ : Subgroup G := V ⊓ J with hP₁
  have hP₁V : P₁ ≤ V := inf_le_left
  have hP₁N : ∀ v ∈ V, ∀ p ∈ P₁, v * p * v⁻¹ ∈ P₁ := fun v hv p hp =>
    ⟨V.mul_mem (V.mul_mem hv hp.1) (V.inv_mem hv), (Subgroup.mem_normalizer_iff.1 (hVN hv) p).1 hp.2⟩
  obtain ⟨u, huV, v, hvV, hnot⟩ := hbad
  obtain ⟨p, hp, z, hz, rfl⟩ := hdec u huV
  obtain ⟨p', hp', z', hz', rfl⟩ := hdec v hvV
  have hcomm : ⁅p * z, p' * z'⁆ = ⁅p, p'⁆ := by
    have hzp' : z * p' = p' * z := hZc z hz p' hp'.1
    have hzz' : z * z' = z' * z := hZc z hz z' (hZ₀V hz')
    have hz'p : z' * p = p * z' := hZc z' hz' p hp.1
    have hzw : z * (p' * z') = (p' * z') * z := by
      calc z * (p' * z') = (z * p') * z' := by rw [mul_assoc]
        _ = (p' * z) * z' := by rw [hzp']
        _ = p' * (z * z') := by rw [mul_assoc]
        _ = p' * (z' * z) := by rw [hzz']
        _ = (p' * z') * z := by rw [mul_assoc]
    rw [commutator_mul_right_comm hzw, commutator_mul_left_comm hz'p]
  have hcP : ⁅p, p'⁆ ∈ P₁ := by
    rw [commutatorElement_def]
    exact P₁.mul_mem (P₁.mul_mem (P₁.mul_mem hp hp') (P₁.inv_mem hp)) (P₁.inv_mem hp')
  set cc : ↥P₁ := ⟨⁅p, p'⁆, hcP⟩ with hcc
  have hcZ : cc ∈ center ↥P₁ :=
    commutator_mem_center_of_card_eight hP₁card (⟨p, hp⟩ : ↥P₁) ⟨p', hp'⟩
  have hc_notC : ⁅p, p'⁆ ∉ C₀ := by rw [← hcomm]; exact hnot
  have hcc1 : cc ≠ 1 := by
    intro h1
    apply hc_notC
    have : ⁅p, p'⁆ = 1 := congrArg Subtype.val h1
    rw [this]; exact C₀.one_mem
  have hnonab : (⟨p, hp⟩ : ↥P₁) * ⟨p', hp'⟩ ≠ ⟨p', hp'⟩ * ⟨p, hp⟩ := fun hab => hc_notC (by
    have h2 : p * p' = p' * p := congrArg Subtype.val hab
    rw [commutatorElement_eq_one_iff_mul_comm.2 h2]
    exact C₀.one_mem)
  have hcen2 : Nat.card (center ↥P₁) = 2 := card_center_eq_two_of_card_eight hP₁card hnonab
  have hcenEq : ∀ g ∈ center ↥P₁, g = 1 ∨ g = cc := by
    intro g hg
    have hord : orderOf cc = 2 := by
      have hdvd : orderOf cc ∣ Nat.card (center ↥P₁) := Subgroup.orderOf_dvd_natCard (center ↥P₁) hcZ
      rw [hcen2] at hdvd
      have : orderOf cc ≠ 1 := fun h1 => hcc1 (orderOf_eq_one_iff.1 h1)
      exact ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left this
    have hz' : zpowers cc = center ↥P₁ := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hcZ)
      rw [Nat.card_zpowers, hord, hcen2]
    rw [← hz'] at hg
    exact mem_zpowers_two hord hg
  have hNP : ∀ n ∈ P₁, n ∈ C₀ → n = 1 := by
    intro n hnP hnC
    by_contra hn1
    have hP₁2 : IsPGroup 2 ↥P₁ := hV2.to_le hP₁V
    have : Group.IsNilpotent ↥P₁ := IsPGroup.isNilpotent hP₁2
    let A : Subgroup ↥P₁ := C₀.subgroupOf P₁
    have hAn : A.Normal := ⟨fun q hq g => by
      rw [Subgroup.mem_subgroupOf] at hq ⊢
      exact hC₀ (g : G) g.2.1 (q : G) hq⟩
    have hA0 : A ≠ ⊥ := by
      intro hbot
      have : (⟨n, hnP⟩ : ↥P₁) ∈ A := Subgroup.mem_subgroupOf.2 hnC
      rw [hbot, Subgroup.mem_bot] at this
      exact hn1 (congrArg Subtype.val this)
    obtain ⟨⟨g, hgA, hgZ⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hA0)
    rcases hcenEq g hgZ with h0 | h0
    · exact hg1 (Subtype.ext h0)
    · rw [h0] at hgA
      exact hc_notC (Subgroup.mem_subgroupOf.1 hgA)
  have hNcomm : ∀ n ∈ V, n ∈ C₀ → ∀ q ∈ P₁, n * q = q * n := by
    intro n hnV hnC q hq
    have hdP : n * q * n⁻¹ * q⁻¹ ∈ P₁ :=
      P₁.mul_mem (hP₁N n hnV q hq) (P₁.inv_mem hq)
    have hdC : n * q * n⁻¹ * q⁻¹ ∈ C₀ := by
      have : n * q * n⁻¹ * q⁻¹ = n * (q * n⁻¹ * q⁻¹) := by group
      rw [this]
      exact C₀.mul_mem hnC (hC₀ q hq.1 n⁻¹ (C₀.inv_mem hnC))
    have h1 := hNP _ hdP hdC
    exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h1)
  set ζ : Perm (Fin 7) := ψ ⟨⁅p, p'⁆, hcP.1⟩ with hζ
  set T : Finset (Perm (Fin 7)) := {1, ζ, tt, ζ * tt} with hT
  have hψE : ∀ (e : G) (heE : e ∈ E₁), ψ ⟨e, hBV (hE₁ heE).1⟩ ∈ T := by
    intro e heE
    have heV : e ∈ V := hBV (hE₁ heE).1
    have heC : e ∈ C₀ := (hE₁ heE).2
    obtain ⟨p₀, hp₀, z₀, hz₀, hez⟩ := hdec e heV
    have hz₀V : z₀ ∈ V := hZ₀V hz₀
    have hp₀c : (⟨p₀, hp₀⟩ : ↥P₁) ∈ center ↥P₁ := by
      rw [Subgroup.mem_center_iff]
      intro q
      have h1 : e * (q : G) = (q : G) * e := hNcomm e heV heC q q.2
      have h2 : z₀ * (q : G) = (q : G) * z₀ := hZc z₀ hz₀ q q.2.1
      apply Subtype.ext
      show (q : G) * p₀ = p₀ * (q : G)
      rw [hez] at h1
      have h3 : (q : G) * p₀ * z₀ = p₀ * (q : G) * z₀ := by
        calc (q : G) * p₀ * z₀ = (q : G) * (p₀ * z₀) := by rw [mul_assoc]
          _ = (p₀ * z₀) * (q : G) := h1.symm
          _ = p₀ * (z₀ * (q : G)) := by rw [mul_assoc]
          _ = p₀ * ((q : G) * z₀) := by rw [h2]
          _ = p₀ * (q : G) * z₀ := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hmul : (⟨e, heV⟩ : ↥V) = ⟨p₀, hp₀.1⟩ * ⟨z₀, hz₀V⟩ := Subtype.ext hez
    rw [show (⟨e, hBV (hE₁ heE).1⟩ : ↥V) = ⟨e, heV⟩ from rfl, hmul, map_mul]
    have hpz : ψ ⟨p₀, hp₀.1⟩ = 1 ∨ ψ ⟨p₀, hp₀.1⟩ = ζ := by
      rcases hcenEq _ hp₀c with h0 | h0
      · left
        have h00 : p₀ = 1 := congrArg Subtype.val h0
        have : (⟨p₀, hp₀.1⟩ : ↥V) = 1 := Subtype.ext h00
        rw [this, map_one]
      · right
        have h00 : p₀ = ⁅p, p'⁆ := congrArg Subtype.val h0
        have : (⟨p₀, hp₀.1⟩ : ↥V) = ⟨⁅p, p'⁆, hcP.1⟩ := Subtype.ext h00
        rw [this]
    rcases hpz with h1 | h1 <;> rcases hψz z₀ hz₀V hz₀ with h2 | h2 <;>
      simp [hT, h1, h2]
  let f : ↥E₁ → Perm (Fin 7) := fun e => ψ ⟨e.1, hBV (hE₁ e.2).1⟩
  have hfinj : Function.Injective f := by
    intro e e' hee
    have heV : (e : G) ∈ V := hBV (hE₁ e.2).1
    have he'V : (e' : G) ∈ V := hBV (hE₁ e'.2).1
    have hmem : (e : G)⁻¹ * e' ∈ V := V.mul_mem (V.inv_mem heV) he'V
    have h1 : ψ ⟨(e : G)⁻¹ * e', hmem⟩ = 1 := by
      have : (⟨(e : G)⁻¹ * e', hmem⟩ : ↥V) = ⟨e, heV⟩⁻¹ * ⟨e', he'V⟩ := rfl
      rw [this, map_mul, map_inv]
      have hee' : ψ ⟨e, heV⟩ = ψ ⟨e', he'V⟩ := hee
      rw [hee', inv_mul_cancel]
    have hE₁mem : (e : G)⁻¹ * e' ∈ E₁ := E₁.mul_mem (E₁.inv_mem e.2) e'.2
    rcases hker _ hmem h1 with h0 | h0
    · apply Subtype.ext
      have : (e : G) = e' := by
        calc (e : G) = e * ((e : G)⁻¹ * e') := by rw [h0]; simp
          _ = e' := by group
      exact this
    · exact absurd ((hE₁ hE₁mem).2) (h0 ▸ hbC)
  have hrange_sub : Set.range f ⊆ (T : Set (Perm (Fin 7))) := by
    rintro _ ⟨e, rfl⟩
    exact hψE e.1 e.2
  have hcardT : (T : Set (Perm (Fin 7))).ncard ≤ 4 := by
    rw [Set.ncard_coe_finset]
    exact Finset.card_le_four
  have hcardR : 4 ≤ (Set.range f).ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hfinj]
    exact hE₁4
  have hEq : Set.range f = (T : Set (Perm (Fin 7))) :=
    Set.eq_of_subset_of_ncard_le hrange_sub (hcardT.trans hcardR) (Finset.finite_toSet T)
  have httT : tt ∈ (T : Set (Perm (Fin 7))) := by simp [hT]
  rw [← hEq] at httT
  obtain ⟨e, he⟩ := httT
  exact ⟨e.1, e.2, by
    show (ψ ⟨e.1, hBV (hE₁ e.2).1⟩).IsSwap
    have : ψ ⟨e.1, hBV (hE₁ e.2).1⟩ = tt := he
    rw [this]
    exact ht₀swap⟩

end CFSG.GH74.GLS.Th2.Obs
