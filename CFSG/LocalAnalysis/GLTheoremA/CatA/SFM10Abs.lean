module

public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM10

open CFSG.Open

theorem three_pow_le_natCard_of_card_eq {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q} {k : ℕ}
    (hk : Nat.card E = 3 ^ k) : k ≤ Nat.card Q := by
  have h1 : 3 ^ k ≤ Nat.card Q := hk ▸ Subgroup.card_le_card_group E
  have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
  omega

theorem pRank_three_le_natCard {Q : Type} [Group Q] [Finite Q] (H : Subgroup Q) :
    pRank 3 H ≤ Nat.card Q := by
  unfold pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hk⟩
  exact three_pow_le_natCard_of_card_eq hk

theorem pRank_three_le_glaTwoLocalRank {Q : Type} [Group Q] [Finite Q] {H : Subgroup Q}
    (hH : IsTwoLocal H) : pRank 3 H ≤ GLATwoLocalRank 3 Q :=
  le_csSup ⟨Nat.card Q, by rintro k ⟨H', -, rfl⟩; exact pRank_three_le_natCard H'⟩ ⟨H, hH, rfl⟩

theorem six_le_glaTwoLocalRank_of_central_extension {Q G : Type} [Group Q] [Group G] [Finite Q]
    (ψ : Q →* G) (hψ : Function.Surjective ψ)
    (hker : ∀ x : Q, ψ x = 1 → x ∈ Subgroup.center Q)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center Q)))
    (t : G) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 6)
    (hEt : ∀ e ∈ E, e * t = t * e) :
    6 ≤ GLATwoLocalRank 3 Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ1 : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    have hdvd1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hdvd2 : orderOf z ∣ Nat.card (Subgroup.center Q) := by
      have := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center Q)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : orderOf z ∣ Nat.gcd 3 (Nat.card (Subgroup.center Q)) := Nat.dvd_gcd hdvd1 hdvd2
    rw [Nat.Coprime.gcd_eq_one hZ] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  obtain ⟨s, hs⟩ := hψ t
  have hot : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hn0 : orderOf s ≠ 0 := (orderOf_pos s).ne'
  obtain ⟨k, m, hmodd, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hmpos : 0 < m := Odd.pos hmodd
  have hm0 : m ≠ 0 := hmpos.ne'
  have hord₂ : orderOf (s ^ m) = 2 ^ k := by
    rw [orderOf_pow_of_dvd hm0 ⟨2 ^ k, by rw [hkm, mul_comm]⟩, hkm]
    exact Nat.mul_div_cancel _ hmpos
  have hψt₂ : ψ (s ^ m) = t := by
    rw [map_pow, hs]
    obtain ⟨j, hj⟩ := hmodd
    rw [hj, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have ht₂1 : s ^ m ≠ 1 := by
    intro h
    apply ht1
    rw [← hψt₂, h, map_one]
  have hTcard : Nat.card (Subgroup.zpowers (s ^ m)) = 2 ^ k := by
    rw [Nat.card_zpowers, hord₂]
  have hT2 : IsPGroup 2 (Subgroup.zpowers (s ^ m)) := IsPGroup.iff_card.2 ⟨k, hTcard⟩
  have hTne : Subgroup.zpowers (s ^ m) ≠ ⊥ := by
    intro h
    apply ht₂1
    have hmem : s ^ m ∈ Subgroup.zpowers (s ^ m) := Subgroup.mem_zpowers _
    rw [h] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hH₂ : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers (s ^ m) : Set Q)) :=
    ⟨Subgroup.zpowers (s ^ m), hTne, hT2, rfl⟩
  have hdvdH : Nat.card E ∣ Nat.card (Subgroup.comap ψ E) := by
    let f : Subgroup.comap ψ E →* E := (ψ.comp (Subgroup.comap ψ E).subtype).codRestrict E
      (fun x => x.2)
    have hf : Function.Surjective f := by
      rintro ⟨e, he⟩
      obtain ⟨x, hx⟩ := hψ e
      exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact he⟩, Subtype.ext hx⟩
    exact Subgroup.card_dvd_of_surjective hf
  have hdvd6 : 3 ^ 6 ∣ Nat.card (Subgroup.comap ψ E) := hEcard ▸ hdvdH
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Subgroup.comap ψ E) 3 hdvd6
  set P : Subgroup Q := K.map (Subgroup.comap ψ E).subtype with hPdef
  have hPcard : Nat.card P = 3 ^ 6 := by
    rw [hPdef, Subgroup.card_map_of_injective (Subgroup.comap ψ E).subtype_injective]
    exact hK
  have hPH : P ≤ Subgroup.comap ψ E := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hPE : ∀ x ∈ P, ψ x ∈ E := fun x hx => hPH hx
  have hPcenter : ∀ x ∈ P, ψ x = 1 → x = 1 := by
    intro x hx hψx
    have hmem : x ∈ P ⊓ Subgroup.center Q := ⟨hx, hker x hψx⟩
    have hcard : Nat.card ↥(P ⊓ Subgroup.center Q) = 1 := by
      have h1 : Nat.card ↥(P ⊓ Subgroup.center Q) ∣ Nat.card P :=
        Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(P ⊓ Subgroup.center Q) ∣ Nat.card (Subgroup.center Q) :=
        Subgroup.card_dvd_of_le inf_le_right
      have h3 : Nat.card ↥(P ⊓ Subgroup.center Q) ∣
          Nat.gcd (Nat.card P) (Nat.card (Subgroup.center Q)) := Nat.dvd_gcd h1 h2
      rw [hPcard, Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left 6 hZ)] at h3
      exact Nat.dvd_one.1 h3
    rw [Subgroup.eq_bot_of_card_eq _ hcard] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hPinj : ∀ a ∈ P, ∀ b ∈ P, ψ a = ψ b → a = b := by
    intro a ha b hb hab
    have h1 : a * b⁻¹ ∈ P := P.mul_mem ha (P.inv_mem hb)
    have h2 : ψ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hPcenter _ h1 h2)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h := hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩
    exact congrArg Subtype.val h
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    apply hPinj _ (P.mul_mem hx hy) _ (P.mul_mem hy hx)
    rw [map_mul, map_mul]
    exact hEcomm _ (hPE x hx) _ (hPE y hy)
  have hPexp : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hPcenter _ (P.pow_mem hx 3)
    rw [map_pow]
    exact hE.2 _ (hPE x hx)
  have hPel : IsElemAbelian 3 P :=
    ⟨⟨⟨fun a b => Subtype.ext (hPcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hPexp x hx⟩
  have hPcent : ∀ y ∈ P, y * s ^ m = s ^ m * y := by
    intro y hy
    have hψz : ψ ((s ^ m)⁻¹ * y * s ^ m * y⁻¹) = 1 := by
      have hc : ψ y * t = t * ψ y := hEt (ψ y) (hPE y hy)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hψt₂]
      rw [show t⁻¹ * ψ y * t = ψ y from by rw [mul_assoc, hc, inv_mul_cancel_left]]
      exact mul_inv_cancel _
    set z : Q := (s ^ m)⁻¹ * y * s ^ m * y⁻¹ with hzdef
    have hzc : z ∈ Subgroup.center Q := hker z hψz
    have hzy : Commute z y := (Subgroup.mem_center_iff.1 hzc y).symm
    have hconj : ((s ^ m)⁻¹ * y * s ^ m) ^ 3 = 1 := by
      have hc3 := conj_pow (a := (s ^ m)⁻¹) (b := y) (i := 3)
      simp only [inv_inv] at hc3
      rw [hc3, hPexp y hy, mul_one, inv_mul_cancel]
    have hzeq : (s ^ m)⁻¹ * y * s ^ m = z * y := by
      rw [hzdef]
      group
    rw [hzeq, hzy.mul_pow] at hconj
    have hz3 : z ^ 3 = 1 := by
      have h3 : z ^ 3 * y ^ 3 = 1 := hconj
      rwa [hPexp y hy, mul_one] at h3
    have hzone : z = 1 := hZ1 z hzc hz3
    have h4 : (s ^ m)⁻¹ * y * s ^ m = y := by
      have h5 : (s ^ m)⁻¹ * y * s ^ m * y⁻¹ = 1 := hzone
      exact mul_inv_eq_one.1 h5
    calc y * s ^ m = s ^ m * ((s ^ m)⁻¹ * y * s ^ m) := by group
      _ = s ^ m * y := by rw [h4]
  have hdir : ∀ z ∈ P, ∀ g ∈ Subgroup.zpowers (s ^ m), z * g * z⁻¹ ∈ Subgroup.zpowers (s ^ m) := by
    intro z hz g hg
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hc : z * (s ^ m) ^ k' = (s ^ m) ^ k' * z :=
      ((show Commute z (s ^ m) from hPcent z hz).zpow_right k').eq
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k'
  have hPnorm : ∀ y ∈ P, y ∈ Subgroup.normalizer (Subgroup.zpowers (s ^ m) : Set Q) := by
    intro y hy
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hdir y hy h hh, fun hh => ?_⟩
    have h' := hdir y⁻¹ (P.inv_mem hy) _ hh
    convert h' using 1
    group
  have hPH₂ : P ≤ Subgroup.normalizer (Subgroup.zpowers (s ^ m) : Set Q) := fun y hy => hPnorm y hy
  have hPmem : 6 ≤ pRank 3 (Subgroup.normalizer (Subgroup.zpowers (s ^ m) : Set Q)) := by
    unfold pRank
    refine le_csSup ⟨Nat.card Q, ?_⟩ ⟨P, hPH₂, hPel, hPcard⟩
    rintro k ⟨E', -, -, hk⟩
    exact three_pow_le_natCard_of_card_eq hk
  exact hPmem.trans (pRank_three_le_glaTwoLocalRank hH₂)

end CFSG.LocalAnalysis.GLTheoremA.SFM10

end
