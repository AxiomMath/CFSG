module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.SectionRank.EvenCover Subgroup

section PrimeKernel

variable {K : Type*} [Group K] {r : ℕ} [hr : Fact r.Prime]

theorem eq_bot_of_no_prime_order_cover
    (H : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* K),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.card π.ker = r → False) :
    ∀ (n : ℕ) (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* K),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup r π.ker →
      Nat.card π.ker = n → π.ker = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ π hπ hC hp hn
    by_contra hne
    have : Finite K := Finite.of_surjective π hπ
    have : Nontrivial π.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hne (Subgroup.eq_bot_of_card_eq _ hk)
    have hdvd : r ∣ Nat.card π.ker := by
      rw [hk]
      exact dvd_pow_self r hk0
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hcker : (c : E) ∈ π.ker := c.2
    have hccen : (c : E) ∈ Subgroup.center E := hC hcker
    have hcord : orderOf (c : E) = r := by rw [Subgroup.orderOf_coe, hc]
    have hNcen : Subgroup.zpowers (c : E) ≤ Subgroup.center E := Subgroup.zpowers_le.2 hccen
    have hNn : (Subgroup.zpowers (c : E)).Normal := ⟨fun x hx g => by
      have h1 : g * x = x * g := Subgroup.mem_center_iff.1 (hNcen hx) g
      rw [h1, mul_inv_cancel_right]
      exact hx⟩
    have hNker : Subgroup.zpowers (c : E) ≤ π.ker := Subgroup.zpowers_le.2 hcker
    have hNcard : Nat.card (Subgroup.zpowers (c : E)) = r := by rw [Nat.card_zpowers, hcord]
    let π' : E ⧸ Subgroup.zpowers (c : E) →* K :=
      QuotientGroup.lift (Subgroup.zpowers (c : E)) π fun x hx => MonoidHom.mem_ker.1 (hNker hx)
    have hπ' : Function.Surjective π' := by
      intro y
      obtain ⟨e, he⟩ := hπ y
      exact ⟨(e : E ⧸ Subgroup.zpowers (c : E)), he⟩
    have hC' : π'.ker ≤ Subgroup.center (E ⧸ Subgroup.zpowers (c : E)) := by
      intro q hq
      obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
      have he : e ∈ π.ker := hq
      have hec := hC he
      rw [Subgroup.mem_center_iff]
      intro g'
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hec g]
    have hKc : 0 < Nat.card K := Nat.card_pos
    have h1 : Nat.card E = Nat.card K * Nat.card π.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
    have h2 : Nat.card (E ⧸ Subgroup.zpowers (c : E)) = Nat.card K * Nat.card π'.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π'.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π' hπ').toEquiv]
    have h3 : Nat.card E = Nat.card (E ⧸ Subgroup.zpowers (c : E)) * r := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (c : E)), hNcard]
    have hker : Nat.card π.ker = Nat.card π'.ker * r := by
      have : Nat.card K * Nat.card π.ker = Nat.card K * (Nat.card π'.ker * r) := by
        rw [← h1, h3, h2]
        ring
      exact Nat.eq_of_mul_eq_mul_left hKc this
    have hp' : IsPGroup r π'.ker := by
      have hdvd' : Nat.card π'.ker ∣ r ^ k := by
        rw [← hk, hker]
        exact Dvd.intro _ rfl
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr.out).1 hdvd'
      exact IsPGroup.iff_card.2 ⟨i, hi⟩
    have hlt : Nat.card π'.ker < n := by
      rw [← hn, hker]
      have h2r : 2 ≤ r := hr.out.two_le
      have hpos : 0 < Nat.card π'.ker := Nat.card_pos
      nlinarith
    have hbot := ih _ hlt (E ⧸ Subgroup.zpowers (c : E)) π' hπ' hC' hp' rfl
    refine H E π hπ hC ?_
    rw [hker, hbot, Subgroup.card_bot, one_mul]

theorem ker_eq_bot_of_no_prime_order_cover
    (H : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* K),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.card π.ker = r → False)
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup r π.ker) :
    π.ker = ⊥ :=
  eq_bot_of_no_prime_order_cover H _ E π hπ hC hp rfl

end PrimeKernel

section CoverMap

theorem exists_cover_map_of_odd_splitting {H L : Type} [Group H] [Finite H] [Group L] [Finite L]
    [Group.IsPerfect L] {D : Subgroup H} [D.Normal] (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* H ⧸ D)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : H →* E, ∀ g, π (s g) = g) :
    ∃ φ : H →* L, Function.Surjective φ ∧ φ.ker ≤ D ∧ D.map φ = Subgroup.center L := by
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ⟩ := hsplit _ _ hsurj hcen (Odd.of_dvd_nat hodd hdvd)
  exact perfect_cover_map_of_section e σ hσ

theorem bijective_of_scalar_cover {H L : Type} [Group H] [Finite H] [Group L] [Finite L]
    {D : Subgroup H} [D.Normal] (e : L ⧸ Subgroup.center L ≃* H ⧸ D)
    (h3 : Nat.card (Subgroup.center L) = 3) (hD : Nat.card D ∣ 3) {φ : H →* L}
    (hφ : Function.Surjective φ) : Nat.card D = 3 ∧ Function.Bijective φ := by
  have hL : Nat.card L = Nat.card (H ⧸ D) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L), h3,
      Nat.card_congr e.toEquiv]
  have hH : Nat.card H = Nat.card (H ⧸ D) * Nat.card D :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup D
  have hle : Nat.card L ≤ Nat.card H := Nat.card_le_card_of_surjective φ hφ
  have hpos : 0 < Nat.card (H ⧸ D) := Nat.card_pos
  have hD3 : 3 ≤ Nat.card D := by
    by_contra hlt
    push Not at hlt
    rw [hL, hH] at hle
    have := Nat.le_of_mul_le_mul_left hle hpos
    omega
  have hD3' : Nat.card D = 3 := (Nat.le_of_dvd (by norm_num) hD).antisymm hD3
  refine ⟨hD3', hφ.bijective_of_nat_card_le ?_⟩
  rw [hH, hL, hD3']

end CoverMap

theorem false_of_isPGroup_two_of_card_three {G : Type*} [Group G] [Finite G] (h2 : IsPGroup 2 G)
    (h3 : Nat.card G = 3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
  rw [h3] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · norm_num at hn
  · have : 2 ∣ 2 ^ n := dvd_pow_self 2 hpos.ne'
    rw [← hn] at this
    omega

theorem ker_comp_mk'_center_eq {X K : Type*} [Group X] [Group K]
    (e : X ⧸ Subgroup.center X ≃* K) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem surjective_comp_mk'_center {X K : Type*} [Group X] [Group K]
    (e : X ⧸ Subgroup.center X ≃* K) :
    Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem false_of_odd_cover_trivial {X K : Type*} [Group X] [Finite X] [Group K]
    (h3 : Nat.card (Subgroup.center X) = 3) (e : X ⧸ Subgroup.center X ≃* K)
    (H : ∀ π : X →* K, Function.Surjective π → π.ker ≤ Subgroup.center X →
      Odd (Nat.card π.ker) → π.ker = ⊥) : False := by
  have hker := ker_comp_mk'_center_eq e
  have hbot := H _ (surjective_comp_mk'_center e) hker.le (by rw [hker, h3]; decide)
  rw [hker] at hbot
  rw [hbot, Subgroup.card_bot] at h3
  omega

end CFSG.QuasithinUnique.Ch1
