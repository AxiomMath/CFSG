module

public import CFSG.GH74.SmallRanks.Basic
public import CFSG.CGT.T75K.ExoticLevi

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.GH74 CFSG.GH74.SmallRanks CFSG.SectionRank

@[expose] def alt6Elt : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem orderOf_alt6Elt : orderOf alt6Elt = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 1)
  · decide
  · decide

theorem factorization_two_card_alt6 :
    (Nat.card (alternatingGroup (Fin 6))).factorization 2 = 3 := by
  have h : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h]
  exact factorization_two_pow_mul_odd (by decide)

theorem twoRank_alternatingGroup_six_le_two : twoRank (alternatingGroup (Fin 6)) ≤ 2 :=
  twoRank_le_two_of_orderOf alt6Elt 2 orderOf_alt6Elt factorization_two_card_alt6

@[expose] def alt7Elt : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem orderOf_alt7Elt : orderOf alt7Elt = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 1)
  · decide
  · decide

theorem factorization_two_card_alt7 :
    (Nat.card (alternatingGroup (Fin 7))).factorization 2 = 3 := by
  have h : Nat.card (alternatingGroup (Fin 7)) = 2 ^ 3 * 315 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h]
  exact factorization_two_pow_mul_odd (by decide)

theorem twoRank_alternatingGroup_seven_le_two' : twoRank (alternatingGroup (Fin 7)) ≤ 2 :=
  twoRank_le_two_of_orderOf alt7Elt 2 orderOf_alt7Elt factorization_two_card_alt7

variable {G : Type} [Group G] {T T₁ H : Subgroup G} {n m : ℕ}

theorem no_hat_aux (hc : Sec6Ctx T T₁ n m) (hL₁H : normIn T₁ T ≤ H)
    [hN : (T.subgroupOf H).Normal] {k : ℕ} (hk : twoRank (alternatingGroup (Fin k)) ≤ 2)
    (h8 : Nat.card ↥(normIn T₁ T) = 2 ^ 3) (hhat : IsHatA k (↥H ⧸ T.subgroupOf H)) : False := by
  have := hc.finite
  obtain ⟨-, Z, -, hZcard, hZn, ⟨ε⟩⟩ := hhat
  let f : ↥(normIn T₁ T) →* alternatingGroup (Fin k) :=
    ε.toMonoidHom.comp ((QuotientGroup.mk' Z).comp
      ((QuotientGroup.mk' (T.subgroupOf H)).comp (Subgroup.inclusion hL₁H)))
  have hsq : ∀ u : ↥(normIn T₁ T), u * u = 1 := fun u =>
    Subtype.ext (elemAbelian_mul_self hc.sec3.cfg.wc₁.1 (normIn_le _ _ u.2))
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : QuotientGroup.mk' Z (QuotientGroup.mk' (T.subgroupOf H)
        (Subgroup.inclusion hL₁H u)) = 1 := by
      have : ε (QuotientGroup.mk' Z (QuotientGroup.mk' (T.subgroupOf H)
          (Subgroup.inclusion hL₁H u))) = 1 := hu
      exact (map_eq_one_iff ε ε.injective).1 this
    have h2 : QuotientGroup.mk' (T.subgroupOf H) (Subgroup.inclusion hL₁H u) ∈ Z :=
      (QuotientGroup.eq_one_iff _).1 h1
    set ub := QuotientGroup.mk' (T.subgroupOf H) (Subgroup.inclusion hL₁H u) with hub
    have hub2 : ub * ub = 1 := by
      rw [hub, ← map_mul, ← map_mul, hsq u, map_one, map_one]
    have hord : orderOf (⟨ub, h2⟩ : ↥Z) = 1 := by
      have h3 : orderOf (⟨ub, h2⟩ : ↥Z) ∣ 2 := by
        apply orderOf_dvd_of_pow_eq_one
        apply Subtype.ext
        simpa [pow_two] using hub2
      have h4 : orderOf (⟨ub, h2⟩ : ↥Z) ∣ 3 := (orderOf_dvd_natCard _).trans hZcard
      have := Nat.dvd_gcd h3 h4
      simpa using this
    have hub1 : ub = 1 := by
      have := orderOf_eq_one_iff.1 hord
      exact congrArg Subtype.val this
    have h5 : (Subgroup.inclusion hL₁H u : ↥H) ∈ T.subgroupOf H :=
      (QuotientGroup.eq_one_iff _).1 hub1
    have h6 : (u : G) ∈ T := Subgroup.mem_subgroupOf.1 h5
    have h7 : (u : G) ∈ T ⊓ T₁ := ⟨h6, normIn_le _ _ u.2⟩
    rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at h7
    exact Subtype.ext h7
  have hrank := le_pRank_of_injective Nat.one_lt_two
    (fun a b => Subtype.ext (elemAbelian_mul_comm hc.sec3.cfg.wc₁.1 (normIn_le _ _ a.2)
      (normIn_le _ _ b.2)))
    (fun a => by rw [pow_two]; exact hsq a) (k := 3) h8 f hfinj (H := ⊤) le_top
  unfold twoRank at hk
  omega

theorem no_hat (hc : Sec6Ctx T T₁ n m) (hn : 4 ≤ n) (h16 : Nat.card T = 16)
    (hL₁H : normIn T₁ T ≤ H) [hN : (T.subgroupOf H).Normal]
    (hhat : IsHatA 6 (↥H ⧸ T.subgroupOf H) ∨ IsHatA 7 (↥H ⧸ T.subgroupOf H)) : False := by
  have hm0 : m ≠ 0 := m_ne_zero hc
  have e : 2 ^ (m * n) = 2 ^ 4 := by
    rw [pow_mul, ← hc.hT, h16]
    norm_num
  have h1 : m * n = 4 := Nat.pow_right_injective (le_refl 2) e
  have h2 : n ≤ m * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm0)
  have hn4 : n = 4 := by omega
  subst hn4
  have hm1 : m = 1 := by omega
  subst hm1
  have h8 : Nat.card ↥(normIn T₁ T) = 2 ^ 3 := by
    rw [hc.card_normIn_swap, hc.card_normIn]
    norm_num
  rcases hhat with h | h
  · exact no_hat_aux hc hL₁H twoRank_alternatingGroup_six_le_two h8 h
  · exact no_hat_aux hc hL₁H twoRank_alternatingGroup_seven_le_two' h8 h

end CFSG.CGT.T75K
