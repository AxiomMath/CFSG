module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.ClassCount
public import CFSG.Sporadic.Mathieu.M11
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.Sporadic.Mathieu.M11
public import CFSG.GH74.KGroups.M11Inputs
public meta import CFSG.GH74.KGroups.M11Inputs
public import Certificates.Certificate5125

public section

namespace CFSG.GH74.KGroups.M11

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem Q_valid :
    Q.check = true ∧ Q.orderCertificate = 7920 :=
  Certificates.certificate5125.1

theorem Q_ok : ValidSchreier Q := Q_valid.1

theorem Q_subgroup : Q.originalSubgroup = NativeSporadic.M11 := by
  rw [Q, certificate_originalSubgroup, m11_eq]
  congr 1
  ext g
  simp

theorem Q_closure : Q.originalSubgroup = Subgroup.closure {m11gA, m11gB} := by
  rw [Q_subgroup]; rfl

theorem card_M11 : Nat.card NativeSporadic.M11 = 7920 := by
  rw [← Q_subgroup, card_group Q Q_ok, Q_valid.2]

theorem gA_mem : m11gA ∈ NativeSporadic.M11 := m11a.2

theorem invol_conj :
    ∀ x ∈ NativeSporadic.M11, orderOf x = 2 → x ∈ conjSet NativeSporadic.M11 m11gA := by
  have h := Certificates.certificate5125
  intro x hx hx2
  obtain ⟨r, hr, hxr⟩ := conj_of_order_count NativeSporadic.M11 NativeSporadic.M11
    (conj_mem_self _) 2 [m11gA] (by simpa using ⟨gA_mem, h.2.1.1⟩) (by simp)
    (by simp [card_M11, h.2.2.2.2.1, h.2.2.2.1]) x hx hx2
  rw [List.mem_singleton] at hr
  rwa [hr] at hxr

theorem three_conj :
    ∀ x ∈ NativeSporadic.M11, orderOf x = 3 → x ∈ conjSet NativeSporadic.M11 m11x0 := by
  have h := Certificates.certificate5125
  intro x hx hx3
  obtain ⟨r, hr, hxr⟩ := conj_of_order_count NativeSporadic.M11 NativeSporadic.M11
    (conj_mem_self _) 3 [m11x0] (by simpa using h.2.2.1) (by simp)
    (by simp [card_M11, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1]) x hx hx3
  rw [List.mem_singleton] at hr
  rwa [hr] at hxr

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl | rfl <;> norm_num

theorem count_le :
    Nat.card {p : NativeSporadic.M11 × NativeSporadic.M11 //
      orderOf p.1 = 2 ∧ orderOf p.2 = 4 ∧ PairInv ws p.1 p.2} ≤ Nat.card NativeSporadic.M11 := by
  have h := Certificates.certificate5125
  refine (card_pairs_le NativeSporadic.M11 NativeSporadic.M11 m11gA (conj_mem_self _) 2 4 ws
    invol_conj).trans ?_
  have e : Nat.card {x // x ∈ NativeSporadic.M11 ∧ orderOf x = 2} *
      Nat.card {y // y ∈ NativeSporadic.M11 ∧ orderOf y = 4 ∧ PairInv ws m11gA y} =
      Nat.card NativeSporadic.M11 := by
    rw [h.2.2.2.1, h.2.2.2.2.2.1, card_M11]
  exact e.le

theorem primeFactors_48 : (48 : ℕ).primeFactors = {2, 3} := by
  rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  rfl

theorem autModel
    {K : Type} [Group K] (h : NativeSporadic.IsSporadic K .M11) :
    ∃ M : AutModel K (Equiv.Perm (Fin 11)), M.P = Q.originalSubgroup ∧
      M.A = Q.originalSubgroup := by
  obtain ⟨e⟩ := h
  have hc := Certificates.certificate5125
  rw [Q_subgroup]
  exact autModel_of_card NativeSporadic.M11 NativeSporadic.M11 m11gA m11gB m11_eq 2 4 ws
    hc.2.1.1 hc.2.1.2.1 hc.2.1.2.2 (conj_mem_self _) hc.2.2.2.2.2.2.1 count_le e

section Consequences

variable {K : Type} [Group K] (h : NativeSporadic.IsSporadic K .M11)

include h

theorem finite_K : Finite K := by
  obtain ⟨M, -, -⟩ := autModel h
  exact Finite.of_equiv M.P M.e.symm.toEquiv

theorem inner3
    (φ : MulAut K) (hφ : φ ^ 3 = 1) : ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  obtain ⟨M, hP, hA⟩ := autModel h
  exact M.inner3 (fun g hg _ => by rw [hP]; rw [hA] at hg; exact hg) φ hφ

theorem autCentralizer
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) (hcard : Nat.card R = 9)
    (ψ : MulAut K) (hψ : ψ ^ 2 = 1) (hc : ∀ r ∈ R, ψ * r = r * ψ) : ψ = 1 := by
  obtain ⟨M, hP, hA⟩ := autModel h
  have he : ∀ τ ∈ Q.originalSubgroup, τ ^ 2 = 1 → τ ≠ 1 → ∀ X ∈ Q.originalSubgroup, X ≠ 1 →
      ∀ Y ∈ Q.originalSubgroup, X ^ 3 = 1 → Y ^ 3 = 1 → X * Y = Y * X → X * τ = τ * X →
      Y * τ = τ * Y → Y = 1 ∨ Y = X ∨ Y = X ^ 2 := by
    rw [Q_subgroup]
    intro τ hτ hτ2 hτ1
    exact forall_of_classes NativeSporadic.M11 {x | x ∈ NativeSporadic.M11 ∧ orderOf x = 2}
      [m11gA] (E9At NativeSporadic.M11)
      (fun x hx => ⟨m11gA, List.mem_singleton_self _, invol_conj x hx.1 hx.2⟩)
      (fun r hr => by
        rw [List.mem_singleton] at hr
        rw [hr]
        exact Certificates.certificate5125.2.2.2.2.2.2.2.2.2.1)
      (fun g hg r hr => e9At_conj hg hr) τ ⟨hτ, orderOf_eq_prime hτ2 hτ1⟩
  rw [← hA] at he
  exact M.autCentralizer he R hR hcard ψ hψ hc

theorem card_mulAut : Nat.card (MulAut K) = 7920 := by
  obtain ⟨M, hP, hA⟩ := autModel h
  rw [M.card_mulAut, hA, card_group Q Q_ok, Q_valid.2]

theorem finite_mulAut : Finite (MulAut K) := by
  obtain ⟨M, -, -⟩ := autModel h
  exact Finite.of_equiv M.A M.Φ.symm.toEquiv

theorem autRank3_le_two
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 9 := by
  have := finite_mulAut h
  have := elemAb_card_le (G := MulAut K) 3 R hR 2 (by rw [card_mulAut h]; norm_num)
  simpa using this

theorem autRank_ge5
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup (MulAut K))
    (hB : ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_mulAut h
  have := elemAb_card_le (G := MulAut K) p B hB 1 (by
    rw [card_mulAut h]
    intro hdvd
    have hle : p ^ 2 ≤ 7920 := Nat.le_of_dvd (by norm_num) hdvd
    have : p ≤ 88 := by nlinarith
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num))
  simpa using this

theorem centralizer3
    (B : Subgroup K) (hB : ElemAb 3 B) (hcard : Nat.card B = 9) (k : K)
    (hk : ∀ b ∈ B, k * b = b * k) : k ∈ B := by
  obtain ⟨e⟩ := h
  have e' : K ≃* Q.originalSubgroup := e.trans (MulEquiv.subgroupCongr Q_subgroup.symm)
  have hc : ∀ x ∈ Q.originalSubgroup, ∀ y ∈ Q.originalSubgroup, x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x → x ≠ 1 → y ∉ ([1, x, x ^ 2] : List (Equiv.Perm (Fin 11))) →
      ∀ k ∈ Q.originalSubgroup, k * x = x * k → k * y = y * k → k ∈ pow3list x y := by
    rw [Q_subgroup]
    intro x hx y hy hx3 hy3 hxy hx1 hyn k hk hkx hky
    have hc3 : Cent3At NativeSporadic.M11 x :=
      forall_of_classes NativeSporadic.M11 {x | x ∈ NativeSporadic.M11 ∧ orderOf x = 3}
        [m11x0] (Cent3At NativeSporadic.M11)
        (fun x hx => ⟨m11x0, List.mem_singleton_self _, three_conj x hx.1 hx.2⟩)
        (fun r hr => by
          rw [List.mem_singleton] at hr
          rw [hr]
          exact Certificates.certificate5125.2.2.2.2.2.2.2.2.2.2)
        (fun g hg r hr => cent3At_conj hg hr) x
        ⟨hx, orderOf_eq_prime hx3 hx1⟩
    exact hc3 y hy hy3 hxy hyn k hk hkx hky
  exact centralizer3_of_model Q.originalSubgroup e' hc B hB hcard k hk

theorem fixed_solvable
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L : Subgroup K)
    (hL : ∀ x ∈ L, α x = x) : Group.IsSolvable L := by
  obtain ⟨M, hP, hA⟩ := autModel h
  refine M.fixed_solvable (fun τ hτ h2 h1 => ?_) α hα2 hα1 L hL
  have hτ' : τ ∈ NativeSporadic.M11 := Q_subgroup ▸ hA ▸ hτ
  rw [hP, Q_subgroup]
  apply isSolvable_of_two_primes
  obtain ⟨g, hg, rfl⟩ := invol_conj τ hτ' (orderOf_eq_prime h2 h1)
  rw [card_inf_centralizer_eq, centCard_conj _ _ _ (normal_iff_of_mem hg),
    Certificates.certificate5125.2.2.2.2.1, primeFactors_48]
  decide

end Consequences

end CFSG.GH74.KGroups.M11
