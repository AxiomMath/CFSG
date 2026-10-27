module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

theorem forall_pow_eq_one_sylow_of_mulEquiv {p n : ℕ} [Fact p.Prime] {K M : Type*} [Group K]
    [Group M] [Finite K] (e : K ≃* M) (h : ∀ T : Sylow p M, ∀ y ∈ (T : Subgroup M), y ^ n = 1)
    (S : Sylow p K) : ∀ x ∈ (S : Subgroup K), x ^ n = 1 := by
  intro x hx
  have hx' : e x ∈ ((S.mapSurjective (f := (e : K →* M)) e.surjective : Sylow p M) :
      Subgroup M) :=
    Subgroup.mem_map_of_mem (e : K →* M) hx
  exact e.injective (by rw [map_pow, h _ _ hx', map_one])

theorem forall_pow_eq_one_of_map_mk' {p m : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    {N : Subgroup H} [N.Normal] (hN : ¬ p ∣ Nat.card N) {P : Subgroup H} (hP : IsPGroup p P)
    (h : ∀ y ∈ P.map (QuotientGroup.mk' N), y ^ m = 1) : ∀ x ∈ P, x ^ m = 1 := by
  intro x hx
  have hxN : x ^ m ∈ N := (QuotientGroup.eq_one_iff _).mp (by
    rw [QuotientGroup.mk_pow]
    exact h _ (Subgroup.mem_map_of_mem _ hx))
  obtain ⟨k, hk⟩ := hP ⟨x ^ m, pow_mem hx m⟩
  have h1 : orderOf (⟨x ^ m, hxN⟩ : N) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using congrArg Subtype.val hk))
  have h2 := Nat.dvd_gcd h1 (orderOf_dvd_natCard (⟨x ^ m, hxN⟩ : N))
  rw [(Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN)).gcd_eq_one,
    Nat.dvd_one, orderOf_eq_one_iff] at h2
  simpa using congrArg Subtype.val h2

end CFSG.GroupTheory
