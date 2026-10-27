module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG Subgroup

theorem isPGroup_quotient_pPrimeCore_of_odd_mul {G : Type*} [Group G] [Finite G]
    (H : Subgroup G)
    (h : ∀ x ∈ H, ∀ y ∈ H, Odd (orderOf x) → Odd (orderOf y) → Odd (orderOf (x * y))) :
    IsPGroup 2 (↥H ⧸ pPrimeCore 2 ↥H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥H :=
    { carrier := {x | Odd (orderOf x)}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have ha' : Odd (orderOf (a : G)) := by rw [Subgroup.orderOf_coe]; exact ha
        have hb' : Odd (orderOf (b : G)) := by rw [Subgroup.orderOf_coe]; exact hb
        show Odd (orderOf (a * b))
        rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
        exact h _ a.2 _ b.2 ha' hb'
      inv_mem' := fun {a} ha => by simpa [orderOf_inv] using ha }
  have hOn : O.Normal := ⟨fun n hn g => by
    show Odd (orderOf (g * n * g⁻¹))
    have := MulEquiv.orderOf_eq (MulAut.conj g) n
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hn⟩
  have hOc : Nat.Coprime 2 (Nat.card O) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hxO : Odd (orderOf (x : ↥H)) := x.2
    rw [Subgroup.orderOf_coe, hx] at hxO
    exact Nat.not_odd_iff_even.mpr even_two hxO
  have hle : O ≤ pPrimeCore 2 ↥H := le_sSup ⟨hOn, hOc⟩
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply hle
    show Odd (orderOf (x ^ 2 ^ k))
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hm

end CFSG.ComponentClassification.AutL2Facts
