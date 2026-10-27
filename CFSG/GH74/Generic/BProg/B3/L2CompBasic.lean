module

public import CFSG.GH74.Generic.BProg.B2.WeakSigGen
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup

namespace L2CompBasic

theorem closure_dihedral_pow_four {G : Type*} [Group G] {a b : G} (ha4 : a ^ 4 = 1)
    (hb2 : b * b = 1) (hba : b * a * b⁻¹ = a⁻¹) : ∀ x ∈ closure ({a, b} : Set G), x ^ 4 = 1 := by
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hainv : a⁻¹ = a ^ 3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact ha4
  have hba' : b * a = a ^ 3 * b := by
    rw [hbi] at hba
    calc b * a = (b * a * b) * b := by rw [mul_assoc, hb2, mul_one]
      _ = a ^ 3 * b := by rw [hba, hainv]
  have hbak : ∀ k : ℕ, b * a ^ k = a ^ (3 * k) * b := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      calc b * a ^ (n + 1) = (b * a ^ n) * a := by rw [pow_succ, mul_assoc]
        _ = a ^ (3 * n) * (b * a) := by rw [ih]; simp only [mul_assoc]
        _ = a ^ (3 * n) * (a ^ 3 * b) := by rw [hba']
        _ = a ^ (3 * (n + 1)) * b := by rw [← mul_assoc, ← pow_add]; congr 2
  have hmod' : ∀ m k : ℕ, a ^ (m + 4 * k) = a ^ m := by
    intro m k
    rw [pow_add, pow_mul, ha4, one_pow, mul_one]
  have hinvpow : ∀ i : ℕ, (a ^ i)⁻¹ = a ^ (3 * i) := by
    intro i
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    have : i + 3 * i = 4 * i := by ring
    rw [this, pow_mul, ha4, one_pow]
  have hNF : ∀ x ∈ closure ({a, b} : Set G), ∃ i : ℕ, x = a ^ i ∨ x = a ^ i * b := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, Or.inl (pow_one _).symm⟩
      · exact ⟨0, Or.inr (by simp)⟩
    | one => exact ⟨0, Or.inl (by simp)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, hi⟩ := hx
      obtain ⟨k, hk⟩ := hy
      rcases hi with rfl | rfl <;> rcases hk with rfl | rfl
      · exact ⟨i + k, Or.inl (pow_add _ _ _).symm⟩
      · exact ⟨i + k, Or.inr (by rw [pow_add, mul_assoc])⟩
      · refine ⟨i + 3 * k, Or.inr ?_⟩
        calc a ^ i * b * a ^ k = a ^ i * (b * a ^ k) := by simp only [mul_assoc]
          _ = a ^ i * (a ^ (3 * k) * b) := by rw [hbak]
          _ = a ^ (i + 3 * k) * b := by rw [pow_add]; simp only [mul_assoc]
      · refine ⟨i + 3 * k, Or.inl ?_⟩
        calc a ^ i * b * (a ^ k * b) = a ^ i * (b * a ^ k) * b := by simp only [mul_assoc]
          _ = a ^ i * (a ^ (3 * k) * b) * b := by rw [hbak]
          _ = a ^ (i + 3 * k) * (b * b) := by rw [pow_add]; simp only [mul_assoc]
          _ = a ^ (i + 3 * k) := by rw [hb2, mul_one]
    | inv x _ hx =>
      obtain ⟨i, hi⟩ := hx
      rcases hi with rfl | rfl
      · exact ⟨3 * i, Or.inl (hinvpow i)⟩
      · refine ⟨i, Or.inr ?_⟩
        calc (a ^ i * b)⁻¹ = b * (a ^ i)⁻¹ := by rw [mul_inv_rev, hbi]
          _ = b * a ^ (3 * i) := by rw [hinvpow]
          _ = a ^ (3 * (3 * i)) * b := hbak _
          _ = a ^ (i + 4 * (2 * i)) * b := by congr 2; ring
          _ = a ^ i * b := by rw [hmod']
  intro x hx
  obtain ⟨i, hi⟩ := hNF x hx
  rcases hi with rfl | rfl
  · rw [← pow_mul, mul_comm, pow_mul, ha4, one_pow]
  · have h2 : (a ^ i * b) * (a ^ i * b) = 1 := by
      calc (a ^ i * b) * (a ^ i * b) = a ^ i * (b * a ^ i) * b := by simp only [mul_assoc]
        _ = a ^ i * (a ^ (3 * i) * b) * b := by rw [hbak]
        _ = a ^ (i + 3 * i) * (b * b) := by rw [pow_add]; simp only [mul_assoc]
        _ = 1 := by
          rw [hb2, mul_one]
          have : i + 3 * i = 4 * i := by ring
          rw [this, pow_mul, ha4, one_pow]
    calc (a ^ i * b) ^ 4 = ((a ^ i * b) * (a ^ i * b)) * ((a ^ i * b) * (a ^ i * b)) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [h2, one_mul]

theorem isPGroup_closure_dihedral {G : Type*} [Group G] {a b : G} (ha4 : a ^ 4 = 1)
    (hb2 : b * b = 1) (hba : b * a * b⁻¹ = a⁻¹) : IsPGroup 2 (closure ({a, b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have h4 : (g : G) ^ 4 = 1 := closure_dihedral_pow_four ha4 hb2 hba g g.2
  have h4' : g ^ 4 = 1 := Subtype.ext (by simpa using h4)
  have hd : orderOf g ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one h4'
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨k, hk⟩

theorem mem_fixedIn_zpowers_iff {X : Type} [Group X] {y : MulAut X} {x : X} :
    x ∈ B2.fixedIn X (zpowers y) ↔ y x = x := by
  rw [B2.mem_fixedIn]
  constructor
  · intro h
    exact h y (mem_zpowers y)
  · intro h φ hφ
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hφ
    have hinv : y⁻¹ x = x := by
      have := congrArg (fun z => y⁻¹ z) h
      simpa using this.symm
    clear hφ
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, MulAut.mul_apply, h, ih]
    | pred k ih =>
      rw [zpow_sub_one, MulAut.mul_apply, hinv, ih]

end L2CompBasic

end CFSG.GH74.Generic.BProg.B3
