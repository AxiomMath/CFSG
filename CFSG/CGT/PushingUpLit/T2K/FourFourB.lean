module

public import CFSG.CGT.PushingUpLit.T2K.FourFourA

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

section Cyclic

variable {G : Type} [Group G] {s : G}

theorem sq_ne_one_of_orderOf_four (hs : orderOf s = 4) : s ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hs] at this
  omega

theorem pow_four_eq_one_of_orderOf_four (hs : orderOf s = 4) : s ^ 4 = 1 := by
  rw [← hs]
  exact pow_orderOf_eq_one s

theorem zpowers_sq_eq_one (hs : orderOf s = 4) {x : G} (hx : x ∈ Subgroup.zpowers s)
    (hx2 : x ^ 2 = 1) : x = 1 ∨ x = s ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h4 : s ^ (4 : ℤ) = 1 := by simpa using pow_four_eq_one_of_orderOf_four hs
  have h2ne : s ^ (2 : ℤ) ≠ 1 := by simpa using sq_ne_one_of_orderOf_four hs
  have hsq : (s ^ (2 : ℤ)) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    simpa using h4
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · have e : s ^ (2 * m) = (s ^ (2 : ℤ)) ^ m := zpow_mul s 2 m
    rcases zpow_eq_one_or_self hsq m with h | h
    · left
      rw [e, h]
    · right
      rw [e, h]
      simp
  · exfalso
    have e : (s ^ (2 * m + 1)) ^ 2 = (s ^ (4 : ℤ)) ^ m * s ^ (2 : ℤ) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
      congr 1
      push_cast
      ring
    rw [e, h4, one_zpow, one_mul] at hx2
    exact h2ne hx2

end Cyclic

namespace T2Hyp

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} {s : G}
variable (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple) (hs : orderOf s = 4)
  (hX : Subgroup.centralizer (L : Set G) = Subgroup.zpowers s)
include h hE1 hs hX

theorem z4_central {m : G} (hm : m ∈ M) : m * s ^ 2 * m⁻¹ = s ^ 2 := by
  have hmem : m * s ^ 2 * m⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
    (Subgroup.mem_normalizer_iff.1 (h.le_normalizer_centralizer hE1 hm) (s ^ 2)).1 (by
      rw [hX]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers s) 2)
  rw [hX] at hmem
  have hsq : (m * s ^ 2 * m⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ← pow_mul]
    simp [pow_four_eq_one_of_orderOf_four hs]
  have hne : m * s ^ 2 * m⁻¹ ≠ 1 := by
    intro h1
    apply sq_ne_one_of_orderOf_four hs
    have e : s ^ 2 = m⁻¹ * (m * s ^ 2 * m⁻¹) * m := by group
    rw [e, h1]
    group
  rcases zpowers_sq_eq_one hs hmem hsq with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem z4_cent_le {c : G} (hc : c * s ^ 2 * c⁻¹ = s ^ 2) : c ∈ M := by
  have hz2 : (s ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact pow_four_eq_one_of_orderOf_four hs
  have hloc := isPLocal_centralizer_of_sq hz2 (sq_ne_one_of_orderOf_four hs)
  have hle : M ≤ Subgroup.centralizer ({s ^ 2} : Set G) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have := h.z4_central hE1 hs hX hm
      calc m * s ^ 2 = (m * s ^ 2 * m⁻¹) * m := by group
        _ = s ^ 2 * m := by rw [this])
  have heq : M = Subgroup.centralizer ({s ^ 2} : Set G) := by
    by_contra hne
    exact h.maxLocal.2 _ (lt_of_le_of_ne hle hne) hloc
  rw [heq]
  exact Subgroup.mem_centralizer_singleton_iff.2 (by
    calc c * s ^ 2 = (c * s ^ 2 * c⁻¹) * c := by group
      _ = s ^ 2 * c := by rw [hc])

omit hE1 in
theorem z4_TI {g : G} (hg : g ∉ M) {x : G} (hx : x ∈ Subgroup.centralizer (L : Set G))
    (hxg : x ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom) : x = 1 := by
  have hodd := h.odd_inf_conj hg
  set K : Subgroup G := Subgroup.centralizer (L : Set G) ⊓
    (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom with hK
  have hXcard : Nat.card ↥(Subgroup.centralizer (L : Set G)) = 4 := by
    rw [hX]
    simp only [Nat.card_zpowers]
    exact hs
  have hdvd : Nat.card ↥K ∣ 2 ^ 2 := by
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4, ← hXcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).1 hdvd
  have hi0 : i = 0 := by
    by_contra hne
    have : Even (Nat.card ↥K) := by
      rw [hi]
      exact Nat.even_pow.2 ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hi0, pow_zero] at hi
  have hbot : K = ⊥ := Subgroup.eq_bot_of_card_eq _ hi
  have : x ∈ K := ⟨hx, hxg⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.1 this

theorem z4_TI_conj {g k x : G}
    (hx : x ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom)
    (hx' : x ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj k).toMonoidHom) (hx1 : x ≠ 1) :
    (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      (Subgroup.centralizer (L : Set G)).map (MulAut.conj k).toMonoidHom := by
  by_cases hgk : g⁻¹ * k ∈ M
  · ext y
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have hnorm := Subgroup.mem_normalizer_iff.1 (h.le_normalizer_centralizer hE1 hgk) (k⁻¹ * y * k)
    have e : (g⁻¹ * k) * (k⁻¹ * y * k) * (g⁻¹ * k)⁻¹ = g⁻¹ * y * g := by group
    rw [e] at hnorm
    exact hnorm.symm
  · exfalso
    apply hx1
    rw [mem_map_conj_iff] at hx hx'
    have h1 : g⁻¹ * x * g = 1 := by
      refine h.z4_TI hs hX hgk hx ?_
      rw [mem_map_conj_iff]
      have e : (g⁻¹ * k)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * k) = k⁻¹ * x * k := by group
      rw [e]
      exact hx'
    have e2 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e2, h1]
    group

omit [Finite G] h hE1 in
theorem z4_pow_four {x : G} (hx : x ∈ Subgroup.centralizer (L : Set G)) : x ^ 4 = 1 := by
  rw [hX] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    pow_four_eq_one_of_orderOf_four hs, one_zpow]

theorem z4_le_sylow (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Subgroup.centralizer (L : Set G) ≤ T := by
  refine le_of_isPGroup_normal hT (h.centralizer_le hE1) (h.le_normalizer_centralizer hE1) ?_
  intro x
  exact ⟨2, Subtype.ext (by simpa using z4_pow_four hs hX x.2)⟩

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
