module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.RankThree.PerfectCover Subgroup

section Rank3

variable {G : Type} [Group G] [Finite G]

theorem u6_pRank_bdd (H : Subgroup G) :
    BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨E, -, -, hE⟩
  have h1 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
  omega
theorem u6_le_pRank {H E : Subgroup G} {k : ℕ} (hEH : E ≤ H) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ k) : k ≤ CFSG.Open.pRank 3 H := by
  unfold CFSG.Open.pRank
  exact le_csSup (u6_pRank_bdd H) ⟨E, hEH, hE, hc⟩
theorem u6_pRank_le {G' : Type} [Group G'] [Finite G'] {P : Subgroup G} {Q : Subgroup G'}
    (h : ∀ k : ℕ, (∃ E : Subgroup G, E ≤ P ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k) →
      ∃ F : Subgroup G', F ≤ Q ∧ CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 3 ^ k) :
    CFSG.Open.pRank 3 P ≤ CFSG.Open.pRank 3 Q := by
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, hE, hEel, hc⟩
  obtain ⟨F, hF, hFel, hFc⟩ := h k ⟨E, hE, hEel, hc⟩
  exact le_csSup (u6_pRank_bdd Q) ⟨F, hF, hFel, hFc⟩
theorem u6_pRank_center {K : Type} [Group K] [Finite K]
    (h3 : 3 ∣ Nat.card (center K)) (h9 : ¬ 9 ∣ Nat.card (center K)) :
    CFSG.Open.pRank 3 (center K) = 1 := by
  apply le_antisymm
  · unfold CFSG.Open.pRank
    refine csSup_le' ?_
    rintro k ⟨E, hE, -, hc⟩
    have hd : 3 ^ k ∣ Nat.card (center K) := by
      rw [← hc]; exact Subgroup.card_dvd_of_le hE
    by_contra hk
    have h2 : 3 ^ 2 ∣ Nat.card (center K) := (pow_dvd_pow 3 (by omega)).trans hd
    exact h9 (by norm_num at h2; exact h2)
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center K) 3 h3
    have hzK : orderOf (z : K) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
    have hel : CFSG.Open.IsElemAbelian 3 (zpowers (z : K)) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_mem_zpowers hx).trans (dvd_of_eq hzK))
    have := u6_le_pRank (k := 1) (zpowers_le.2 z.2) hel (by rw [Nat.card_zpowers, hzK]; norm_num)
    omega
end Rank3

section Transfer

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

theorem u6_card_comap (h : A →* B) (hs : Function.Surjective h) (E : Subgroup B) :
    Nat.card (E.comap h) = Nat.card E * Nat.card h.ker := by
  have h1 := Subgroup.card_mul_index (E.comap h)
  have h2 := Subgroup.card_mul_index E
  have h3 := card_eq_card_mul_card_ker h hs
  rw [Subgroup.index_comap_of_surjective E hs] at h1
  have hi : 0 < E.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hi
  rw [h1, h3, ← h2]
  ring
theorem u6_inf_bot_of_three {S N : Subgroup A} {k : ℕ} (hS : Nat.card S = 3 ^ k)
    (hN : ¬ 3 ∣ Nat.card N) : S ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.1 hx
  have h1 : orderOf x ∣ 3 ^ k := by
    have := orderOf_dvd_natCard (⟨x, hxS⟩ : S)
    rw [Subgroup.orderOf_mk, hS] at this
    exact this
  have h2 : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    rw [Subgroup.orderOf_mk] at this
    exact this
  have hcop : Nat.Coprime (3 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN)
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h3)
theorem u6_hinj {h : A →* B} {F : Subgroup A} (hFN : F ⊓ h.ker = ⊥) :
    ∀ x ∈ F, ∀ y ∈ F, h x = h y → x = y := by
  intro x hx y hy hxy
  have hmem : x⁻¹ * y ∈ F ⊓ h.ker := by
    refine Subgroup.mem_inf.2 ⟨F.mul_mem (F.inv_mem hx) hy, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  rw [hFN, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.1 hmem
theorem u6_isElemAbelian_of_hinj {h : A →* B} {F : Subgroup A} (hFN : F ⊓ h.ker = ⊥)
    {E : Subgroup B} (hE : CFSG.Open.IsElemAbelian 3 E) (hFE : ∀ x ∈ F, h x ∈ E) :
    CFSG.Open.IsElemAbelian 3 F := by
  have hinj := u6_hinj hFN
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hinj _ (F.mul_mem a.2 b.2) _ (F.mul_mem b.2 a.2)
    rw [map_mul, map_mul]
    have key := congrArg Subtype.val
      (hE.1.is_comm.comm (⟨h a, hFE a a.2⟩ : E) ⟨h b, hFE b b.2⟩)
    exact key
  · apply hinj _ (F.pow_mem hx 3) 1 F.one_mem
    rw [map_pow, map_one]
    exact hE.2 _ (hFE x hx)
theorem u6_pRank_source_le (h : A →* B) (hs : Function.Surjective h)
    (hN : ¬ 3 ∣ Nat.card h.ker) :
    CFSG.Open.pRank 3 (⊤ : Subgroup B) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup A) := by
  refine u6_pRank_le ?_
  rintro k ⟨E, -, hE, hc⟩
  have hTc : Nat.card (E.comap h) = 3 ^ k * Nat.card h.ker := by
    rw [u6_card_comap h hs E, hc]
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ k ∣ Nat.card (E.comap h) from ⟨_, hTc⟩)
  have hFc : Nat.card (K'.map (E.comap h).subtype) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hK']
  have hFN : K'.map (E.comap h).subtype ⊓ h.ker = ⊥ :=
    u6_inf_bot_of_three hFc hN
  have hFE : ∀ x ∈ K'.map (E.comap h).subtype, h x ∈ E := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_comap.1 t.2
  exact ⟨K'.map (E.comap h).subtype, le_top, u6_isElemAbelian_of_hinj hFN hE hFE, hFc⟩
theorem u6_pRank_target_le (h : A →* B) (hN : ¬ 3 ∣ Nat.card h.ker) :
    CFSG.Open.pRank 3 (⊤ : Subgroup A) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup B) := by
  refine u6_pRank_le ?_
  rintro k ⟨S, -, hS, hc⟩
  have hFN : S ⊓ h.ker = ⊥ := u6_inf_bot_of_three hc hN
  have hinj : Function.Injective (h.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : (a : A) ∈ S ⊓ h.ker :=
      Subgroup.mem_inf.2 ⟨a.2, by simpa using ha⟩
    rw [hFN, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hrange : (h.comp S.subtype).range = S.map h := by
    ext x
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  refine ⟨(h.comp S.subtype).range, le_top, ?_, ?_⟩
  · rw [hrange]
    exact CFSG.SectionRank.isElemAbelian_map hS h
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hc
end Transfer

section Cover

variable {X : Type} [Group X] [Finite X]

theorem u6_card_mul_ker [Group.IsPerfect X] {E : Type} [Group E] [Group.IsPerfect E]
    (q : E →* X) (hq : Function.Surjective q) (hkc : q.ker = center E) :
    Nat.card (center E) * Nat.card (hopfLift q hq hkc.le).ker = Nat.card (hopfMultiplier X) := by
  have h1 : Nat.card (HopfCover X) = Nat.card X * Nat.card (hopfMultiplier X) :=
    card_eq_card_mul_card_ker (hopfCoverMap X) hopfCoverMap_surjective
  have h2 : Nat.card (HopfCover X) = Nat.card E * Nat.card (hopfLift q hq hkc.le).ker :=
    card_eq_card_mul_card_ker (hopfLift q hq hkc.le) (hopfLift_surjective q hq hkc.le)
  have h3 : Nat.card E = Nat.card X * Nat.card (center E) := by
    rw [← hkc]; exact card_eq_card_mul_card_ker q hq
  have hXpos : 0 < Nat.card X := by
    have := Nat.card_pos (α := X); exact this
  apply Nat.eq_of_mul_eq_mul_left hXpos
  rw [← h1, h2, h3]
  ring
theorem u6_three_not_dvd_ker [Group.IsPerfect X] {E : Type} [Group E] [Group.IsPerfect E]
    (q : E →* X) (hq : Function.Surjective q) (hkc : q.ker = center E) {m : ℕ}
    (hM : Nat.card (hopfMultiplier X) = 3 * m) (hm : ¬ 3 ∣ m) (h3 : 3 ∣ Nat.card (center E)) :
    ¬ 3 ∣ Nat.card (hopfLift q hq hkc.le).ker := by
  intro hd
  have key := u6_card_mul_ker q hq hkc
  rw [hM] at key
  have h9 : 3 * 3 ∣ 3 * m := by
    rw [← key]; exact mul_dvd_mul h3 hd
  exact hm (by omega)
theorem u6_pRank_le_of_covers [Group.IsPerfect X] [Finite X]
    {L K : Type} [Group L] [Group K] [Finite L] [Finite K]
    [Group.IsPerfect L] [Group.IsPerfect K]
    (qL : L →* X) (hqL : Function.Surjective qL) (hkL : qL.ker = center L)
    (qK : K →* X) (hqK : Function.Surjective qK) (hkK : qK.ker = center K)
    {m : ℕ} (hM : Nat.card (hopfMultiplier X) = 3 * m) (hm : ¬ 3 ∣ m)
    (h3L : 3 ∣ Nat.card (center L)) (h3K : 3 ∣ Nat.card (center K)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  haveI : Finite (HopfCover X) := finite_hopfCover (inferInstance : Group.IsPerfect X)
  have hL := u6_pRank_source_le (hopfLift qL hqL hkL.le) (hopfLift_surjective qL hqL hkL.le)
    (u6_three_not_dvd_ker qL hqL hkL hM hm h3L)
  have hK := u6_pRank_target_le (hopfLift qK hqK hkK.le)
    (u6_three_not_dvd_ker qK hqK hkK hM hm h3K)
  exact hL.trans hK
end Cover

end CFSG.LocalAnalysis.GLTheoremA