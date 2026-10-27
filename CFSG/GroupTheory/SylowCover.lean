module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] {H K : Subgroup G}

theorem le_of_forall_prime_pow_dvd_card_inf [Finite H]
    (h : ∀ p : ℕ, p.Prime → p ^ (Nat.card H).factorization p ∣ Nat.card ↥(H ⊓ K)) :
    H ≤ K := by
  have hfin : Finite ↥(H ⊓ K) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hH0 : Nat.card H ≠ 0 := (Nat.card_pos (α := H)).ne'
  have hI0 : Nat.card ↥(H ⊓ K) ≠ 0 :=
    (@Nat.card_pos ↥(H ⊓ K) inferInstance hfin).ne'
  have hdvd : Nat.card H ∣ Nat.card ↥(H ⊓ K) := by
    refine (Nat.factorization_prime_le_iff_dvd hH0 hI0).mp ?_
    intro p hp
    exact (hp.pow_dvd_iff_le_factorization hI0).mp (h p hp)
  have hcard : Nat.card H ≤ Nat.card ↥(H ⊓ K) :=
    Nat.le_of_dvd (@Nat.card_pos ↥(H ⊓ K) inferInstance hfin) hdvd
  have heq : H ⊓ K = H := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
  rw [← heq]
  exact inf_le_right

theorem le_of_forall_exists_isSylowIn_le [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∃ P : Subgroup G, CFSG.Quasithin.IsSylowIn p P H ∧ P ≤ K) :
    H ≤ K := by
  refine le_of_forall_prime_pow_dvd_card_inf (K := K) fun p hp => ?_
  obtain ⟨P, hP, hPK⟩ := h p hp
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card P = p ^ (Nat.card H).factorization p := by
    have h1 := Sylow.card_eq_multiplicity hP.toSylow
    rwa [CFSG.Quasithin.IsSylowIn.coe_toSylow,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.le).toEquiv] at h1
  rw [← hcard]
  exact Subgroup.card_dvd_of_le (le_inf hP.le hPK)

theorem le_of_isPGroup_of_forall_notMem_mul_self {D U P : Subgroup G}
    (hD : ∀ d ∈ D, d ∉ U → d * d = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hPD : P ≤ D) : P ≤ U := by
  intro x hxP
  by_contra hxU
  have hx2 : x ^ 2 = 1 := by
    have h := hD x (hPD hxP) hxU
    simpa [pow_two] using h
  obtain ⟨k, hk⟩ := hP.exists_pow_pow_eq_one ⟨x, hxP⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have hcop : Nat.Coprime (p ^ k) 2 :=
    (Nat.coprime_two_right.mpr (hp.odd_of_ne_two hp2)).pow_left k
  have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact hxU (by rw [orderOf_eq_one_iff.mp hone]; exact U.one_mem)

end CFSG.GroupTheory

namespace CFSG.Quasithin.IsSylowIn

theorem exists_sylow_eq_of_top {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsSylowIn p P ⊤) : ∃ S : Sylow p G, (S : Subgroup G) = P :=
  ⟨hP.isPGroup.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.not_dvd_relIndex), rfl⟩

end CFSG.Quasithin.IsSylowIn

end
