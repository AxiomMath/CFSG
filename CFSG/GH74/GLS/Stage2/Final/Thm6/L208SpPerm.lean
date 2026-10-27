module

public import CFSG.GH74.GLS.Stage1.Thm4.L97a

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp

open Equiv Equiv.Perm CFSG.GH74.GLS.Stage1.Thm4.L97

@[expose] def xor8 (a b : Fin 8) : Fin 8 := ⟨a.val ^^^ b.val, by
  have : a.val ^^^ b.val < 2 ^ 3 := Nat.xor_lt_two_pow (n := 3) a.isLt b.isLt
  simpa using this⟩

@[expose] def etaFun (a x : Fin 8) : Fin 8 := xor8 x a

theorem etaFun_invol (a : Fin 8) : Function.Involutive (etaFun a) := by
  intro x
  revert x a
  decide

@[expose] def eta (a : Fin 8) : Perm (Fin 8) := (etaFun_invol a).toPerm _

theorem eta_sq (a : Fin 8) : eta a * eta a = 1 := by
  revert a
  decide

theorem eta_comm (a b : Fin 8) : eta a * eta b = eta b * eta a := by
  revert a b
  decide

theorem eta_mul (a b : Fin 8) : eta a * eta b = eta (xor8 a b) := by
  revert a b
  decide

theorem eta_zero : eta 0 = 1 := by decide

theorem eta_zero_apply (x : Fin 8) : eta x 0 = x := by
  revert x
  decide

theorem eta_self (y : Fin 8) : eta y y = 0 := by
  revert y
  decide

theorem eta_ne (a : Fin 8) (ha : a ≠ 0) : eta a ≠ 1 := by
  revert a
  decide

theorem eta_supp (a : Fin 8) (ha : a ≠ 0) : (eta a).support.card = 8 := by
  revert a
  decide

theorem eta_one_ne (i : Fin 8) : eta 1 i ≠ i := by
  revert i
  decide

@[expose] def emb8s {n : ℕ} (hn : 8 ≤ n) : Fin 8 ≃ {x : Fin n // x.val < 8} where
  toFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hn⟩, i.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def iota {n : ℕ} (hn : 8 ≤ n) : Perm (Fin 8) →* Perm (Fin n) :=
  Equiv.Perm.extendDomainHom (emb8s hn)

theorem cycleType_iota {n : ℕ} (hn : 8 ≤ n) (σ : Perm (Fin 8)) :
    (iota hn σ).cycleType = σ.cycleType :=
  Equiv.Perm.cycleType_extendDomain (emb8s hn)

@[expose] def pt {n : ℕ} (hn : 8 ≤ n) (i : Fin 8) : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt hn⟩

theorem pt_injective {n : ℕ} (hn : 8 ≤ n) : Function.Injective (pt hn) := by
  intro i j h
  apply Fin.ext
  simpa [pt] using congrArg Fin.val h

theorem iota_pt {n : ℕ} (hn : 8 ≤ n) (τ : Perm (Fin 8)) (i : Fin 8) :
    iota hn τ (pt hn i) = pt hn (τ i) := by
  have := Equiv.Perm.extendDomain_apply_image τ (emb8s hn) i
  simpa [iota, pt, emb8s] using this

theorem iota_out {n : ℕ} (hn : 8 ≤ n) (τ : Perm (Fin 8)) {j : Fin n} (hj : 8 ≤ j.val) :
    iota hn τ j = j := by
  have := Equiv.Perm.extendDomain_apply_not_subtype τ (emb8s hn) (b := j) (by simpa using hj)
  simpa [iota] using this

theorem cycleType_of_sq_card {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} {k : ℕ}
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) (hs : σ.support.card = 2 * k) :
    σ.cycleType = Multiset.replicate k 2 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hm, hord, hs] at hsum
  simp only [Multiset.sum_replicate, smul_eq_mul] at hsum
  have hm1 : m + 1 = k := by omega
  rw [hm, hord, hm1]

theorem eta_ct (a : Fin 8) (ha : a ≠ 0) : (eta a).cycleType = {2, 2, 2, 2} :=
  cycleType_of_sq (eta_sq a) (eta_ne a ha) (eta_supp a ha)

theorem mem_alt_eta {n : ℕ} (hn : 8 ≤ n) (a : Fin 8) :
    iota hn (eta a) ∈ alternatingGroup (Fin n) := by
  by_cases ha : a = 0
  · subst ha
    rw [eta_zero, map_one]
    exact one_mem _
  · exact mem_alt_of_ct (by rw [cycleType_iota]; exact eta_ct a ha)

@[expose] def tau0 : Perm (Fin 11) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def vbar1 : Perm (Fin 11) := swap 0 2 * swap 1 3 * swap 6 7 * swap 8 9

@[expose] def vbar2 : Perm (Fin 11) := swap 0 2 * swap 1 3 * swap 6 7 * swap 9 10

theorem iota_eta_one (hn : 8 ≤ 11) : iota hn (eta 1) = tau0 := by
  refine Equiv.ext fun j => ?_
  by_cases hj : j.val < 8
  · have hpt : j = pt hn ⟨j.val, hj⟩ := Fin.ext rfl
    rw [hpt, iota_pt]
    have key : ∀ x : Fin 8,
        pt (by norm_num : 8 ≤ 11) (eta 1 x) = tau0 (pt (by norm_num : 8 ≤ 11) x) := by
      decide
    exact key _
  · rw [iota_out hn _ (by omega)]
    have key : ∀ j : Fin 11, ¬ j.val < 8 → tau0 j = j := by decide
    exact (key j hj).symm

theorem vbar1_sq : vbar1 * vbar1 = 1 := by decide

theorem vbar2_sq : vbar2 * vbar2 = 1 := by decide

theorem vbar1_ct : vbar1.cycleType = {2, 2, 2, 2} :=
  cycleType_of_sq_card (k := 4) vbar1_sq (by decide) (by decide)

theorem vbar2_ct : vbar2.cycleType = {2, 2, 2, 2} :=
  cycleType_of_sq_card (k := 4) vbar2_sq (by decide) (by decide)

theorem vbar1_comm (hn : 8 ≤ 11) : vbar1 * iota hn (eta 1) = iota hn (eta 1) * vbar1 := by
  rw [iota_eta_one]
  decide

theorem vbar2_comm (hn : 8 ≤ 11) : vbar2 * iota hn (eta 1) = iota hn (eta 1) * vbar2 := by
  rw [iota_eta_one]
  decide

theorem vbar1_eta_ct (hn : 8 ≤ 11) : (vbar1 * iota hn (eta 1)).cycleType = {2, 2, 2, 2} := by
  rw [iota_eta_one]
  exact cycleType_of_sq_card (k := 4) (by decide) (by decide) (by decide)

theorem vbar2_eta_ct (hn : 8 ≤ 11) : (vbar2 * iota hn (eta 1)).cycleType = {2, 2, 2, 2} := by
  rw [iota_eta_one]
  exact cycleType_of_sq_card (k := 4) (by decide) (by decide) (by decide)

theorem fixes_first_eight {n : ℕ} (hn : 8 ≤ n) {σ : Perm (Fin n)} (hodd : Odd (orderOf σ))
    (hc : ∀ a : Fin 8, σ * iota hn (eta a) = iota hn (eta a) * σ) (i : Fin 8) :
    σ (pt hn i) = pt hn i := by
  have hcomm : ∀ (a : Fin 8) (x : Fin n), σ (iota hn (eta a) x) = iota hn (eta a) (σ x) :=
    fun a x => by
      have := congrArg (fun f : Perm (Fin n) => f x) (hc a)
      simpa using this
  have hin : ∀ i : Fin 8, ∃ j : Fin 8, σ (pt hn i) = pt hn j := by
    intro i
    by_contra hcon
    push Not at hcon
    have hout : 8 ≤ (σ (pt hn i)).val := by
      by_contra hlt
      push Not at hlt
      exact hcon ⟨(σ (pt hn i)).val, hlt⟩ (Fin.ext rfl)
    have h1 : iota hn (eta 1) (σ (pt hn i)) = σ (pt hn i) := iota_out hn _ hout
    have h2 : iota hn (eta 1) (σ (pt hn i)) = σ (pt hn (eta 1 i)) := by
      rw [← hcomm, iota_pt]
    have h3 : pt hn (eta 1 i) = pt hn i := σ.injective (h2.symm.trans h1)
    exact eta_one_ne i (pt_injective hn h3)
  obtain ⟨y₀, hy₀⟩ := hin 0
  have hσ : ∀ i : Fin 8, σ (pt hn i) = pt hn (eta i y₀) := by
    intro i
    have h1 : pt hn i = iota hn (eta i) (pt hn 0) := by rw [iota_pt, eta_zero_apply]
    rw [h1, hcomm, hy₀, iota_pt]
  have hσ2 : ∀ i : Fin 8, σ (σ (pt hn i)) = pt hn i := by
    intro i
    have h0 : σ (σ (pt hn 0)) = pt hn 0 := by
      rw [hy₀, hσ, eta_self]
    have h1 : pt hn i = iota hn (eta i) (pt hn 0) := by rw [iota_pt, eta_zero_apply]
    rw [h1, hcomm, hcomm, h0]
  obtain ⟨r, hr⟩ := hodd
  have hpow : σ = (σ ^ 2) ^ (r + 1) := by
    rw [← pow_mul]
    have h1 : σ ^ (2 * (r + 1)) = σ ^ (orderOf σ) * σ := by
      rw [hr, ← pow_succ]
      congr 1
    rw [h1, pow_orderOf_eq_one, one_mul]
  have hfix2 : (σ ^ 2) (pt hn i) = pt hn i := by
    rw [pow_two, Perm.mul_apply]
    exact hσ2 i
  conv_lhs => rw [hpow]
  exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix2 (r + 1)

theorem supp_pres {n : ℕ} {σ v : Perm (Fin n)} (h : σ * v = v * σ) {x : Fin n} (hx : v x ≠ x) :
    v (σ x) ≠ σ x := by
  intro hc
  apply hx
  have h1 : σ (v x) = v (σ x) := by simpa using congrArg (fun f : Perm (Fin n) => f x) h
  rw [hc] at h1
  exact σ.injective h1

theorem ge_eight {n : ℕ} {σ : Perm (Fin n)} (hfix : ∀ i : Fin n, i.val < 8 → σ i = i) {i : Fin n}
    (hi : 8 ≤ i.val) : 8 ≤ (σ i).val := by
  by_contra hlt
  push Not at hlt
  have h1 : σ (σ i) = σ i := hfix (σ i) hlt
  have h2 : σ i = i := σ.injective h1
  rw [h2] at hlt
  omega

theorem eq_one_of_sq_of_odd {α : Type*} [Group α] {x : α} (h : x ^ 2 = 1)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf x = 1 ∨ orderOf x = 2 := (Nat.dvd_prime Nat.prime_two).1 h1
  rcases h2 with h2 | h2
  · exact orderOf_eq_one_iff.1 h2
  · rw [h2] at hodd
    exact absurd hodd (by decide)

theorem tail_eleven {σ : Perm (Fin 11)} (hfix : ∀ i : Fin 11, i.val < 8 → σ i = i)
    (h1 : σ * vbar1 = vbar1 * σ) (h2 : σ * vbar2 = vbar2 * σ) : σ = 1 := by
  have hge := fun i (hi : 8 ≤ (i : Fin 11).val) => ge_eight hfix hi
  have h9 : σ 9 = 9 := by
    have hh : ∀ x : Fin 11, 8 ≤ x.val → vbar1 x ≠ x → vbar2 x ≠ x → x = 9 := by decide
    exact hh _ (hge 9 (by decide)) (supp_pres h1 (by decide)) (supp_pres h2 (by decide))
  have h8 : σ 8 = 8 := by
    have hh : ∀ x : Fin 11, 8 ≤ x.val → vbar1 x ≠ x → x ≠ 9 → x = 8 := by decide
    refine hh _ (hge 8 (by decide)) (supp_pres h1 (by decide)) (fun h => ?_)
    have : σ 8 = σ 9 := by rw [h, h9]
    exact absurd (σ.injective this) (by decide)
  have h10 : σ 10 = 10 := by
    have hh : ∀ x : Fin 11, 8 ≤ x.val → vbar2 x ≠ x → x ≠ 9 → x = 10 := by decide
    refine hh _ (hge 10 (by decide)) (supp_pres h2 (by decide)) (fun h => ?_)
    have : σ 10 = σ 9 := by rw [h, h9]
    exact absurd (σ.injective this) (by decide)
  refine Equiv.ext fun i => ?_
  by_cases hi : i.val < 8
  · simpa using hfix i hi
  · have : i = 8 ∨ i = 9 ∨ i = 10 := by
      have h3 : i.val = 8 ∨ i.val = 9 ∨ i.val = 10 := by omega
      rcases h3 with h3 | h3 | h3
      · left
        exact Fin.ext h3
      · right
        left
        exact Fin.ext h3
      · right
        right
        exact Fin.ext h3
    rcases this with rfl | rfl | rfl <;> simp [h8, h9, h10]

theorem tail_le_ten {n : ℕ} (hn' : n ≤ 10) {σ : Perm (Fin n)} (hodd : Odd (orderOf σ))
    (hfix : ∀ i : Fin n, i.val < 8 → σ i = i) : σ = 1 := by
  have hge := fun i (hi : 8 ≤ (i : Fin n).val) => ge_eight hfix hi
  apply eq_one_of_sq_of_odd _ hodd
  refine Equiv.ext fun i => ?_
  rw [pow_two, Perm.mul_apply]
  simp only [Perm.coe_one, id]
  by_cases hi : i.val < 8
  · rw [hfix i hi, hfix i hi]
  · have hσi := hge i (by omega)
    have hlt := (σ i).isLt
    have hlt2 := i.isLt
    have hσσ := hge (σ i) hσi
    have hlt3 := (σ (σ i)).isLt
    by_cases heq : σ i = i
    · rw [heq, heq]
    · have hne : σ (σ i) ≠ σ i := fun h => heq (σ.injective h)
      apply Fin.ext
      have h1 : (σ i).val ≠ i.val := fun h => heq (Fin.ext h)
      have h2 : (σ (σ i)).val ≠ (σ i).val := fun h => hne (Fin.ext h)
      omega

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp
