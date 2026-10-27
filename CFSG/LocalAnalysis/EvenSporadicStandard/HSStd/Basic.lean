module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

theorem commute_of_odd_of_mem_normalizer {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    [IsCyclic T] (hT : IsPGroup 2 T) {x : G} (hx : Odd (orderOf x))
    (hn : x ∈ normalizer (T : Set G)) : ∀ y ∈ T, x * y = y * x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : MulAut T := T.normalizerMonoidHom ⟨x, hn⟩ with hφ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  have h1 : orderOf φ ∣ orderOf x := by
    have := orderOf_map_dvd T.normalizerMonoidHom (⟨x, hn⟩ : normalizer (T : Set G))
    simpa [Subgroup.orderOf_mk] using this
  have h2 : orderOf φ ∣ 2 ^ k := by
    have h3 : orderOf φ ∣ Nat.card (MulAut T) := orderOf_dvd_natCard φ
    rw [IsCyclic.card_mulAut, hk] at h3
    refine h3.trans ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk0]
      exact ⟨2, by
        have : k = (k - 1) + 1 := by omega
        rw [this, pow_succ]; simp [mul_comm]⟩
  have hodd : Odd (orderOf φ) := hx.of_dvd_nat h1
  have hcop : Nat.Coprime (orderOf φ) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have hone : orderOf φ = 1 := Nat.Coprime.eq_one_of_dvd hcop h2
  have hφ1 : φ = 1 := orderOf_eq_one_iff.mp hone
  intro y hy
  have h := congrArg (fun f : MulAut T => ((f ⟨y, hy⟩ : T) : G)) hφ1
  have h' : x * y * x⁻¹ = y := h
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [h']

theorem exists_pow_eq_of_ne_one {G : Type*} [Group G] [Finite G] {T : Subgroup G} [IsCyclic T]
    (hT : IsPGroup 2 T) {t : G} (ht : t ∈ T) (ht2 : orderOf t = 2) {u : G} (hu : u ∈ T)
    (hu1 : u ≠ 1) : ∃ k : ℕ, u ^ k = t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨u, hu⟩
  rw [Subgroup.orderOf_mk] at he
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hu1 (orderOf_eq_one_iff.mp (by simpa using he))
  refine ⟨2 ^ (e - 1), ?_⟩
  have hord : orderOf (u ^ 2 ^ (e - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [he]; exact pow_dvd_pow 2 (Nat.sub_le e 1)), he,
      Nat.pow_div (Nat.sub_le e 1) (by norm_num)]
    have : e - (e - 1) = 1 := by omega
    rw [this]
  exact CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.eq_of_orderOf_eq_two_of_isCyclic
    inferInstance (pow_mem hu _) ht hord ht2

end CFSG.EvenSporadicStandard.HSStd
