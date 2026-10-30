module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open
open scoped commutatorElement

section Elem

variable {Y : Type*} [Group Y]

theorem i253_isElementaryAbelian {A : Subgroup Y} (hA : IsElemAbelian 3 A) :
    CFSG.IsElementaryAbelian 3 ↥A where
  is_comm := hA.1.is_comm
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hA.2 x x.2)

theorem i253_isPGroup_zpowers {p : ℕ} {x : Y} {k : ℕ} (h : x ^ (p ^ k) = 1) :
    IsPGroup p ↥(Subgroup.zpowers x) := by
  intro g
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨k, Subtype.ext ?_⟩
  show (g : Y) ^ (p ^ k) = 1
  rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem i253_exists_not_mem_zpowers [Finite Y] {A : Subgroup Y} (hA9 : Nat.card A = 9) {b : Y}
    (hbA : b ∈ A) (hb3 : orderOf b = 3) : ∃ a ∈ A, a ∉ Subgroup.zpowers b := by
  by_contra h
  push Not at h
  have hle : A ≤ Subgroup.zpowers b := h
  have := Subgroup.card_le_card_group (G := Y) (Subgroup.zpowers b)
  have h1 : Nat.card A ≤ Nat.card (Subgroup.zpowers b) := by
    have := Subgroup.card_le_of_le hle
    exact this
  rw [Nat.card_zpowers, hb3, hA9] at h1
  omega

theorem i253_comm_of_generators [Finite Y] {A : Subgroup Y} (hA9 : Nat.card A = 9) {b a₀ u : Y}
    (hbA : b ∈ A) (ha₀A : a₀ ∈ A) (hb3 : orderOf b = 3) (ha₀ : a₀ ∉ Subgroup.zpowers b)
    (hub : u * b = b * u) (hua : u * a₀ = a₀ * u) : ∀ a ∈ A, u * a = a * u := by
  set H : Subgroup Y := A ⊓ Subgroup.centralizer {u} with hH
  have hbH : b ∈ H := Subgroup.mem_inf.2 ⟨hbA, Subgroup.mem_centralizer_singleton_iff.2 hub.symm⟩
  have ha₀H : a₀ ∈ H := Subgroup.mem_inf.2 ⟨ha₀A, Subgroup.mem_centralizer_singleton_iff.2 hua.symm⟩
  have hHA : H ≤ A := inf_le_left
  have hzH : Subgroup.zpowers b ≤ H := by
    rw [Subgroup.zpowers_le]; exact hbH
  have hcardz : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb3]
  have hdvd1 : Nat.card (Subgroup.zpowers b) ∣ Nat.card H := Subgroup.card_dvd_of_le hzH
  have hdvd2 : Nat.card H ∣ Nat.card A := Subgroup.card_dvd_of_le hHA
  rw [hcardz] at hdvd1
  rw [hA9] at hdvd2
  have hHcard : Nat.card H = 3 ∨ Nat.card H = 9 := by
    have h9' : Nat.card H ∣ 3 ^ 2 := by simpa using hdvd2
    obtain ⟨i, hi, hHi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h9'
    interval_cases i
    · rw [hHi] at hdvd1; omega
    · exact Or.inl hHi
    · exact Or.inr (by simpa using hHi)
  rcases hHcard with h3 | h9
  · exfalso
    have : Subgroup.zpowers b = H :=
      Subgroup.eq_of_le_of_card_ge hzH (by rw [hcardz, h3])
    exact ha₀ (this ▸ ha₀H)
  · have : H = A := Subgroup.eq_of_le_of_card_ge hHA (by rw [h9, hA9])
    intro a ha
    have : a ∈ H := by rw [this]; exact ha
    exact ((Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 this).2)).symm

theorem i253_mem_of_mem_sup {Z Q : Subgroup Y} {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hcomm : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    (hQ : IsPGroup q ↥Q) {b : Y} (hb3 : b ^ 3 = 1) (hb : b ∈ Z ⊔ Q) : b ∈ Z := by
  have key : ∀ y ∈ Z ⊔ Q, ∃ z ∈ Z, ∃ x ∈ Q, y = z * x := by
    intro y hy
    rw [Subgroup.sup_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, Q.one_mem, by simp⟩
      · exact ⟨1, Z.one_mem, y, hy, by simp⟩
    | one => exact ⟨1, Z.one_mem, 1, Q.one_mem, by simp⟩
    | mul y y' _ _ ihy ihy' =>
      obtain ⟨z, hz, x, hx, rfl⟩ := ihy
      obtain ⟨z', hz', x', hx', rfl⟩ := ihy'
      refine ⟨z * z', Z.mul_mem hz hz', x * x', Q.mul_mem hx hx', ?_⟩
      have := hcomm z' hz' x hx
      calc z * x * (z' * x') = z * (x * z') * x' := by group
        _ = z * (z' * x) * x' := by rw [← this]
        _ = z * z' * (x * x') := by group
    | inv y _ ihy =>
      obtain ⟨z, hz, x, hx, rfl⟩ := ihy
      refine ⟨z⁻¹, Z.inv_mem hz, x⁻¹, Q.inv_mem hx, ?_⟩
      have := hcomm z hz x hx
      calc (z * x)⁻¹ = x⁻¹ * z⁻¹ := by group
        _ = z⁻¹ * x⁻¹ := by
          have h1 : x * z = z * x := this.symm
          have : z⁻¹ * x⁻¹ = (x * z)⁻¹ := by group
          rw [this, h1]; group
  obtain ⟨z, hz, x, hx, rfl⟩ := key b hb
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have hxk : x ^ (q ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hzx : Commute z x := hcomm z hz x hx
  have hb3' : z ^ 3 * x ^ 3 = 1 := by rw [← hzx.mul_pow]; exact hb3
  have hx3 : x ^ 3 = (z ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hb3'
  have hcop : Nat.Coprime (q ^ k) 3 :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq Nat.prime_three).2 hq3)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, x = (x ^ 3) ^ m := by
    have hord : Nat.Coprime 3 (orderOf x) := by
      have : orderOf x ∣ q ^ k := orderOf_dvd_of_pow_eq_one hxk
      exact Nat.Coprime.coprime_dvd_right this hcop.symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hord
    exact ⟨m, hm.symm⟩
  have hxZ : x ∈ Z := by
    rw [hm, hx3]
    exact Z.pow_mem (Z.inv_mem (Z.pow_mem hz 3)) m
  exact Z.mul_mem hz hxZ

theorem i253_cube_trick {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) {b x : Y} (hb3 : b ^ 3 = 1)
    (hg : b * (b * x * b⁻¹ * x⁻¹) = (b * x * b⁻¹ * x⁻¹) * b) {k : ℕ}
    (hgk : (b * x * b⁻¹ * x⁻¹) ^ (q ^ k) = 1) : b * x * b⁻¹ * x⁻¹ = 1 := by
  set g := b * x * b⁻¹ * x⁻¹ with hgdef
  have hy : b * x * b⁻¹ = g * x := by rw [hgdef]; group
  have h1 : b * (g * x) * b⁻¹ = g * (g * x) := by
    have : b * g * b⁻¹ = g := by rw [hg]; group
    calc b * (g * x) * b⁻¹ = (b * g * b⁻¹) * (b * x * b⁻¹) := by group
      _ = g * (g * x) := by rw [this, hy]
  have hpow : ∀ n : ℕ, b ^ n * x * (b ^ n)⁻¹ = g ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : b ^ (n + 1) * x * (b ^ (n + 1))⁻¹ = b * (b ^ n * x * (b ^ n)⁻¹) * b⁻¹ := by
        rw [pow_succ']; group
      rw [this, ih]
      calc b * (g ^ n * x) * b⁻¹ = (b * g ^ n * b⁻¹) * (b * x * b⁻¹) := by group
        _ = g ^ n * (g * x) := by
          have : b * g ^ n * b⁻¹ = g ^ n := by
            rw [show b * g ^ n = g ^ n * b from (Commute.pow_right (show Commute b g from hg) n).eq]
            group
          rw [this, hy]
        _ = g ^ (n + 1) * x := by rw [pow_succ']; group
  have h3 : g ^ 3 = 1 := by
    have := hpow 3
    rw [hb3] at this
    simpa using this.symm
  have hcop : Nat.Coprime (q ^ k) 3 :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq Nat.prime_three).2 hq3)
  have hord : orderOf g ∣ Nat.gcd (q ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hgk) (orderOf_dvd_of_pow_eq_one h3)
  rw [hcop] at hord
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)

end Elem

end CFSG.HardMathSupport.Solomon.Coordinator
