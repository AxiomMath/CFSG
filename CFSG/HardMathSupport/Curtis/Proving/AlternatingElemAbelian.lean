module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open Equiv Equiv.Perm

theorem exists_elemAbelian_of_disjoint {G : Type*} [Group G] {α : Type*} [Fintype α]
    [DecidableEq α] (φ : G →* Perm α) (hφ : Function.Injective φ) {a b : G}
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hdisj : ∀ x, φ a x = x ∨ φ b x = x) :
    ∃ E : Subgroup G, (∀ g, g ∈ E ↔ ∃ n k : ℕ, g = a ^ n * b ^ k) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hab : Commute a b := by
    apply hφ
    rw [map_mul, map_mul]
    exact (Perm.Disjoint.commute hdisj).eq
  have hinvA : ∀ n : ℕ, (a ^ n)⁻¹ = a ^ (2 * n) := fun n =>
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_add, show n + 2 * n = 3 * n by ring, pow_mul, ha3, one_pow])
  have hinvB : ∀ n : ℕ, (b ^ n)⁻¹ = b ^ (2 * n) := fun n =>
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_add, show n + 2 * n = 3 * n by ring, pow_mul, hb3, one_pow])
  have hfix : ∀ k l : ℕ, a ^ k = b ^ l → a ^ k = 1 := by
    intro k l h
    have h' : (φ a) ^ k = (φ b) ^ l := by rw [← map_pow, ← map_pow, h]
    apply hφ
    rw [map_pow, map_one]
    ext x
    simp only [Perm.one_apply]
    rcases hdisj x with hx | hx
    · exact Perm.pow_apply_eq_self_of_apply_eq_self hx k
    · rw [h']
      exact Perm.pow_apply_eq_self_of_apply_eq_self hx l
  have hdvd_a : ∀ k : ℕ, a ^ k = 1 → 3 ∣ k := fun k hk => by
    have := orderOf_dvd_of_pow_eq_one hk
    rwa [hoa] at this
  have hdvd_b : ∀ k : ℕ, b ^ k = 1 → 3 ∣ k := fun k hk => by
    have := orderOf_dvd_of_pow_eq_one hk
    rwa [hob] at this
  have hkey : ∀ n k n' k' : ℕ, a ^ n * b ^ k = a ^ n' * b ^ k' →
      a ^ (2 * n' + n) = b ^ (k' + 2 * k) := by
    intro n k n' k' h
    have h1 : a ^ n = a ^ n' * b ^ k' * (b ^ k)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact h
    have h2 : (a ^ n')⁻¹ * a ^ n = b ^ k' * (b ^ k)⁻¹ := by
      rw [h1, ← mul_assoc, inv_mul_cancel_left]
    rw [hinvA, hinvB] at h2
    rw [← pow_add, ← pow_add] at h2
    exact h2
  have hswap : ∀ n k n' k' : ℕ, (a ^ n) * (b ^ k) * ((a ^ n') * (b ^ k'))
      = a ^ (n + n') * b ^ (k + k') := by
    intro n k n' k'
    have hc : b ^ k * a ^ n' = a ^ n' * b ^ k := ((hab.pow_pow n' k).eq).symm
    calc a ^ n * b ^ k * (a ^ n' * b ^ k')
        = a ^ n * (b ^ k * a ^ n') * b ^ k' := by simp only [mul_assoc]
      _ = a ^ n * (a ^ n' * b ^ k) * b ^ k' := by rw [hc]
      _ = a ^ n * a ^ n' * (b ^ k * b ^ k') := by simp only [mul_assoc]
      _ = a ^ (n + n') * b ^ (k + k') := by rw [pow_add, pow_add]
  let E : Subgroup G :=
    { carrier := {g | ∃ n k : ℕ, g = a ^ n * b ^ k}
      mul_mem' := by
        rintro _ _ ⟨n, k, rfl⟩ ⟨n', k', rfl⟩
        exact ⟨n + n', k + k', hswap n k n' k'⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, k, rfl⟩
        refine ⟨2 * n, 2 * k, ?_⟩
        rw [mul_inv_rev, hinvA, hinvB]
        exact ((hab.pow_pow (2 * n) (2 * k)).eq).symm }
  have hmem : ∀ g, g ∈ E ↔ ∃ n k : ℕ, g = a ^ n * b ^ k := fun g => Iff.rfl
  refine ⟨E, hmem, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨n, k, hn⟩ := (hmem _).mp x.2
    obtain ⟨n', k', hn'⟩ := (hmem _).mp y.2
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [hn, hn', hswap, hswap, add_comm n' n, add_comm k' k]
  · intro x hx
    obtain ⟨n, k, rfl⟩ := (hmem x).mp hx
    have e1 : (a ^ n) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha3, one_pow]
    have e2 : (b ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hb3, one_pow]
    rw [(hab.pow_pow n k).mul_pow, e1, e2, one_mul]
  · have hbij : Function.Bijective
        (fun p : Fin 3 × Fin 3 => (⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), (hmem _).mpr
          ⟨_, _, rfl⟩⟩ : E)) := by
      constructor
      · rintro ⟨i, j⟩ ⟨i', j'⟩ h
        have h' : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (i' : ℕ) * b ^ (j' : ℕ) :=
          congrArg Subtype.val h
        have hk := hkey _ _ _ _ h'
        have h1 : a ^ (2 * (i' : ℕ) + (i : ℕ)) = 1 := hfix _ _ hk
        have h2 : b ^ ((j' : ℕ) + 2 * (j : ℕ)) = 1 := by rw [← hk]; exact h1
        have h3 := hdvd_a _ h1
        have h4 := hdvd_b _ h2
        have hi := i.isLt
        have hi' := i'.isLt
        have hj := j.isLt
        have hj' := j'.isLt
        refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
        · show (i : ℕ) = (i' : ℕ)
          omega
        · show (j : ℕ) = (j' : ℕ)
          omega
      · rintro ⟨g, hg⟩
        obtain ⟨n, k, rfl⟩ := (hmem g).mp hg
        refine ⟨(⟨n % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩),
          Subtype.ext ?_⟩
        have ha' := pow_mod_orderOf a n
        have hb' := pow_mod_orderOf b k
        rw [hoa] at ha'
        rw [hob] at hb'
        show a ^ (n % 3) * b ^ (k % 3) = a ^ n * b ^ k
        rw [ha', hb']
    have := Nat.card_eq_of_bijective _ hbij
    rw [← this]
    simp

end CFSG.HardMathSupport.Curtis.Proving

end
