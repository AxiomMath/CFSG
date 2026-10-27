module

public import CFSG.GH74.GLS.Stage4.Q9.Rigidity

public section

namespace CFSG.GH74.GLS.Stage4.Q9

private theorem subgroup_comm_of_card_dvd_prime_sq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (X : Subgroup G) (hX : Nat.card X ∣ p ^ 2) : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ a b : X, a * b = b * a := by
    obtain ⟨k, hk, hXk⟩ := (Nat.dvd_prime_pow hp).1 hX
    interval_cases k
    · have : Subsingleton X := (Nat.card_eq_one_iff_unique.1 (by simpa using hXk)).1
      exact fun a b => Subsingleton.elim _ _
    · have : IsCyclic X := isCyclic_of_prime_card (by simpa using hXk)
      exact fun a b => (IsCyclic.isMulCommutative (α := X)).is_comm.comm a b
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hXk).is_comm.comm
  intro a ha b hb
  exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem dvd_nine_of_dvd_of_not_five_dvd {n N : ℕ} (hN : N ≠ 0) (hn : n ∣ N)
    (h5 : ¬ 5 ∣ n) (hprime : ∀ r : ℕ, r.Prime → r ∣ N → r = 3 ∨ r = 5)
    (h3 : N.factorization 3 ≤ 2) : n ∣ 9 := by
  have hn0 : n ≠ 0 := fun h => hN (by simpa [h] using hn)
  rw [← Nat.factorization_prime_le_iff_dvd hn0 (by norm_num)]
  intro q hq
  by_cases hq3 : q = 3
  · subst hq3
    have h9 : (9 : ℕ).factorization 3 = 2 := by
      have : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [this, Nat.Prime.factorization_pow Nat.prime_three]
      simp
    rw [h9]
    exact ((Nat.factorization_le_iff_dvd hn0 hN).2 hn 3).trans h3
  · have : n.factorization q = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hqn
      rcases hprime q hq (hqn.trans hn) with h | h
      · exact hq3 h
      · exact h5 (h ▸ hqn)
    omega

private theorem subsingleton_sylow_five {H : Type*} [Group H] [Finite H]
    (hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 3 ∨ r = 5)
    (h3 : (Nat.card H).factorization 3 ≤ 2) : Subsingleton (Sylow 5 H) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 H) := inferInstance
  have hmod := card_sylow_modEq_one 5 H
  have hdvd : Nat.card (Sylow 5 H) ∣ Nat.card H :=
    (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)
  have h5 : ¬ 5 ∣ Nat.card (Sylow 5 H) := not_dvd_card_sylow 5 H
  have h9 := dvd_nine_of_dvd_of_not_five_dvd Nat.card_pos.ne' hdvd h5 hprime h3
  have hle : Nat.card (Sylow 5 H) ≤ 9 := Nat.le_of_dvd (by norm_num) h9
  have hone : Nat.card (Sylow 5 H) = 1 := by
    unfold Nat.ModEq at hmod
    generalize Nat.card (Sylow 5 H) = n at *
    interval_cases n <;> omega
  exact (Nat.card_eq_one_iff_unique.1 hone).1

theorem odd_core_small3 {G : Type*} [Group G] [Finite G] {z : G} (_hz : orderOf z = 2)
    (A O Kb : Subgroup G) (_hOodd : Odd (Nat.card O)) (_hOleA : O ≤ A)
    (hOA : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O)
    (hKbA : Kb ≤ A) (hzKb : z ∈ Kb) (_hzcent : ∀ k ∈ Kb, z * k = k * z)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (eb : ↥Kb ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card O → r = 3 ∨ r = 5)
    (h3 : (Nat.card O).factorization 3 ≤ 2) (h5 : (Nat.card O).factorization 5 ≤ 2)
    (hz3 : ∀ o ∈ O, z * o = o * z → ∃ n : ℕ, orderOf o = 3 ^ n) :
    ∀ o ∈ O, z * o = o * z := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsub : Subsingleton (Sylow 5 O) := subsingleton_sylow_five hprime h3
  obtain ⟨P⟩ : Nonempty (Sylow 5 O) := inferInstance
  have hchar : (P : Subgroup O).Characteristic := inferInstance
  set R : Subgroup G := (P : Subgroup O).map O.subtype with hRdef
  have hRO : R ≤ O := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hRcard : Nat.card R = 5 ^ (Nat.card O).factorization 5 := by
    rw [hRdef, Subgroup.card_map_of_injective O.subtype_injective]
    exact P.card_eq_multiplicity
  have hR25 : Nat.card R ∣ 5 ^ 2 := by
    rw [hRcard]
    exact pow_dvd_pow 5 h5
  have hRcomm := subgroup_comm_of_card_dvd_prime_sq Nat.prime_five R hR25
  have hRnorm : ∀ k ∈ Kb, ∀ x ∈ R, k * x * k⁻¹ ∈ R := by
    intro k hk x hx
    obtain ⟨r, hr, rfl⟩ := hx
    let c : O ≃* O :=
      { toFun := fun o => ⟨k * o * k⁻¹, hOA k (hKbA hk) o o.2⟩
        invFun := fun o => ⟨k⁻¹ * o * k, by simpa using hOA k⁻¹ (A.inv_mem (hKbA hk)) o o.2⟩
        left_inv := fun o => Subtype.ext (by simp [mul_assoc])
        right_inv := fun o => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hcr : c r ∈ (P : Subgroup O) := by
      have h : r ∈ (P : Subgroup O).comap c.toMonoidHom := by
        rw [hchar.fixed c]
        exact hr
      exact h
    exact ⟨c r, hcr, rfl⟩
  have hKR := sl2_nine_centralizes_small hF eb hRnorm hRcomm (Or.inl (by simpa using hR25))
  have hRbot : R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨n, hn⟩ := hz3 x (hRO hx) (hKR z hzKb x hx)
    have hord : orderOf x ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : R)
      rwa [Subgroup.orderOf_mk] at this
    rw [hRcard, hn] at hord
    have hcop : Nat.Coprime (3 ^ n) (5 ^ (Nat.card O).factorization 5) :=
      Nat.Coprime.pow _ _ (by norm_num)
    rw [← orderOf_eq_one_iff, hn]
    exact hcop.eq_one_of_dvd hord
  have h5N : ¬ 5 ∣ Nat.card O := by
    intro h
    apply P.ne_bot_of_dvd_card h
    exact (Subgroup.map_eq_bot_iff_of_injective _ O.subtype_injective).1 hRbot
  have hO9 : Nat.card O ∣ 9 :=
    dvd_nine_of_dvd_of_not_five_dvd Nat.card_pos.ne' dvd_rfl h5N hprime h3
  have hOcomm := subgroup_comm_of_card_dvd_prime_sq Nat.prime_three O (by simpa using hO9)
  have hKO := sl2_nine_centralizes_small hF eb (fun k hk x hx => hOA k (hKbA hk) x hx) hOcomm
    (Or.inr hO9)
  exact fun o ho => hKO z hzKb o ho

end CFSG.GH74.GLS.Stage4.Q9
