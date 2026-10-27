module

public import CFSG.ClassicalInvolution.Q3.TL4D1MBaseB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Wr

variable {n : ℕ}

theorem permBar_mem_of_mem {P : Subgroup (Equiv.Perm (Fin n))} {x : AEQ n}
    (hx : x ∈ aeBarOver P) : permBar n x ∈ P := by
  obtain ⟨a, ha, rfl⟩ := hx
  rw [permBar_mkQ]
  exact ha.2

theorem map_permBar_normal {P : Subgroup (Equiv.Perm (Fin n))}
    (hPA : ∀ σ ∈ P, Equiv.Perm.sign σ = 1) {N : Subgroup (AEQ n)}
    (hNn : ∀ x ∈ aeBarOver P, ∀ y ∈ N, x * y * x⁻¹ ∈ N) :
    ∀ g ∈ P, ∀ q ∈ N.map (permBar n), g * q * g⁻¹ ∈ N.map (permBar n) := by
  rintro g hg _ ⟨y, hy, rfl⟩
  refine ⟨mkQ n (ofPerm g) * y * (mkQ n (ofPerm g))⁻¹,
    hNn _ (mkQ_mem_aeBarOver (ofPerm_mem_aeSubOver hg (hPA g hg))) y hy, ?_⟩
  rw [map_mul, map_mul, map_inv, permBar_mkQ]
  rfl

theorem aeBarOver_normal {P : Subgroup (Equiv.Perm (Fin n))}
    (hPA : ∀ σ ∈ P, Equiv.Perm.sign σ = 1)
    (hP : ∀ Q : Subgroup (Equiv.Perm (Fin n)), Q ≤ P → (∀ g ∈ P, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) →
      ¬ IsPGroup 2 Q → Q = P) (htr : PairTrans P) : ModelNormal (aeBarOver P) := by
  intro N hNM hNn
  by_cases h2 : IsPGroup 2 N
  · exact Or.inl h2
  right
  obtain ⟨y, hyN, hyo, hy1⟩ := exists_odd_of_not_isPGroup h2
  have hQ : N.map (permBar n) = P := by
    refine hP _ ?_ (map_permBar_normal hPA hNn) fun hQ2 => hy1 ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact permBar_mem_of_mem (hNM hx)
    · have hp1 : permBar n y = 1 := by
        obtain ⟨j, hj⟩ := hQ2 ⟨permBar n y, y, hyN, rfl⟩
        have hj' : permBar n y ^ 2 ^ j = 1 := by
          have := congrArg Subtype.val hj
          simpa using this
        have hodd : Odd (orderOf (permBar n y)) :=
          hyo.of_dvd_nat (orderOf_map_dvd (permBar n) y)
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
          (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)) dvd_rfl
          (orderOf_dvd_of_pow_eq_one hj'))
      have hy2 := mul_self_of_permBar_eq_one hp1
      have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
      have h1' : orderOf y = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact h
        · rw [h] at hyo
          exact absurd hyo (by decide)
      exact orderOf_eq_one_iff.mp h1'
  have hpair : ∀ j k : Fin n, j ≠ k → mkQ n (ofVec (pairVec j k)) ∈ N := by
    intro j k hjk
    obtain ⟨g, hg, i, -, hgi, hgk⟩ := htr j k hjk
    rw [← hQ] at hg
    obtain ⟨x, hxN, hxg⟩ := hg
    obtain ⟨a, ha, rfl⟩ := hNM hxN
    rw [permBar_mkQ] at hxg
    have hu := mkQ_mem_aeBarOver (ofVec_mem_aeSubOver (P := P) (sum_pairVec i k))
    have hc : mkQ n a * (mkQ n (ofVec (pairVec i k)) * (mkQ n a)⁻¹ *
        (mkQ n (ofVec (pairVec i k)))⁻¹) ∈ N :=
      N.mul_mem hxN (hNn _ hu _ (N.inv_mem hxN))
    rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← mul_assoc, ← mul_assoc,
      comm_pairVec a (hxg ▸ hgi) (hxg ▸ hgk)] at hc
  refine le_antisymm hNM ?_
  rintro _ ⟨a, ha, rfl⟩
  have hg : a.perm ∈ N.map (permBar n) := hQ ▸ ha.2
  obtain ⟨x, hxN, hxa⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hNM hxN
  rw [permBar_mkQ] at hxa
  have hv : b⁻¹ * a = ofVec (b⁻¹ * a).vec := by
    conv_lhs => rw [eq_ofVec_mul_ofPerm (b⁻¹ * a)]
    rw [show (b⁻¹ * a).perm = 1 by rw [mul_perm, inv_perm, hxa, inv_mul_cancel], ofPerm_one,
      mul_one]
  have hsum : ∑ i, (b⁻¹ * a).vec i = 0 := (aeSubOver P).mul_mem ((aeSubOver P).inv_mem hb) ha |>.1.1
  have hva : mkQ n (b⁻¹ * a) ∈ N := by
    rw [hv]
    exact mem_of_pairVec hpair hsum
  have : mkQ n a = mkQ n b * mkQ n (b⁻¹ * a) := by rw [← map_mul, mul_inv_cancel_left]
  rw [this]
  exact N.mul_mem hxN hva

end CFSG.ClassicalInvolution.Q3.TL4
