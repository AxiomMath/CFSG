module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory.SylowOddClasses

open scoped Pointwise

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_card {p : ℕ} [Fact p.Prime] (P : Subgroup G)
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) {g : G} {k : ℕ}
    (hg : orderOf g = p ^ k) : ∃ c : G, c * g * c⁻¹ ∈ P := by
  have hpg : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hg])
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard P hP)
  refine ⟨c, ?_⟩
  have h1 : g ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers g)
  have h2 : MulAut.conj c • g ∈ MulAut.conj c • (Q : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul g _ _ h1
  rw [← Sylow.coe_subgroup_smul, hc, Sylow.coe_ofCard] at h2
  simpa [MulAut.smul_def] using h2

@[expose] def listSubgroup (V : List G) (h1 : (1 : G) ∈ V) (hmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V) :
    Subgroup G where
  carrier := {x | x ∈ V}
  one_mem' := h1
  mul_mem' := fun {x y} hx hy => hmul x hx y hy
  inv_mem' := fun {x} hx => by
    have hpow : ∀ n : ℕ, x ^ n ∈ V := fun n => by
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
    have hpos := orderOf_pos x
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    change x⁻¹ ∈ V
    rw [e]
    exact hpow _

theorem mem_listSubgroup {V : List G} {h1 : (1 : G) ∈ V} {hmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V}
    {x : G} : x ∈ listSubgroup V h1 hmul ↔ x ∈ V :=
  Iff.rfl

theorem card_listSubgroup {V : List G} (h1 : (1 : G) ∈ V) (hmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V)
    (hV : V.Nodup) : Nat.card (listSubgroup V h1 hmul) = V.length := by
  classical
  have e : Nat.card (listSubgroup V h1 hmul) = Nat.card {x // x ∈ V.toFinset} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [mem_listSubgroup])
  rw [e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hV]

theorem orderOf_eq_one_or_prime {H : Subgroup G} {S : ℕ → Prop} {g : G} (hg : g ∈ H)
    (hS : ∀ p, p.Prime → p ∣ orderOf g → S p)
    (h : ∀ x ∈ H, ∀ p q, p.Prime → q.Prime → S p → S q → orderOf x ≠ p * q) :
    orderOf g = 1 ∨ (orderOf g).Prime := by
  by_contra! hn
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn.1
  obtain ⟨m, hm⟩ := hpd
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hn.2 (hm ▸ hp)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hm1
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpq : p * q ∣ orderOf g := by
    rw [hm]
    exact Nat.mul_dvd_mul_left p hqd
  refine h _ (H.pow_mem hg (orderOf g / (p * q))) p q hp hq (hS p hp ⟨m, hm⟩)
    (hS q hq (dvd_trans (dvd_mul_left q p) hpq)) (orderOf_pow_orderOf_div hpos hpq)

end Sylow

section Fix

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def fixCard (σ : Equiv.Perm α) : ℕ := (Finset.univ.filter fun x => σ x = x).card

theorem fixCard_conj (c σ : Equiv.Perm α) : fixCard (c * σ * c⁻¹) = fixCard σ := by
  unfold fixCard
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact (Fintype.card_congr (c.subtypeEquiv fun a => by simp [Equiv.Perm.mul_apply])).symm

theorem fix_modEq {q : ℕ} [Fact q.Prime] {x y : Equiv.Perm α} (hxy : Commute x y)
    (hy : y ^ q = 1) :
    fixCard x ≡ (Finset.univ.filter fun a => x a = a ∧ y a = a).card [MOD q] := by
  have hs : ∀ a, x (y a) = y a ↔ x a = a := fun a => by
    have e : x (y a) = y (x a) := by
      change (x * y) a = (y * x) a
      rw [hxy.eq]
    rw [e]
    exact ⟨fun h => y.injective h, fun h => by rw [h]⟩
  let τ : Equiv.Perm {a // x a = a} := y.subtypePerm hs
  have hτ : τ ^ q ^ 1 = 1 := by
    rw [pow_one, Equiv.Perm.subtypePerm_pow]
    ext a
    simp [hy]
  have h := Equiv.Perm.card_compl_support_modEq hτ
  have e1 : Fintype.card {a // x a = a} = fixCard x := by
    rw [Fintype.card_subtype]
    rfl
  have e2 : τ.supportᶜ.card = (Finset.univ.filter fun a => x a = a ∧ y a = a).card := by
    have e : τ.supportᶜ = Finset.univ.filter fun a : {a // x a = a} => y a = a := by
      ext a
      simp [τ, Equiv.Perm.mem_support, Subtype.ext_iff]
    rw [e]
    refine Finset.card_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ h => Subtype.ext h)
      (fun b hb => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ⟨a.2, ha⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact ⟨⟨b, hb.1⟩, by simpa using hb.2, rfl⟩
  rw [e1, e2] at h
  exact h.symm

@[expose] def pqExcl (p q : ℕ) (Fp Fq : List ℕ) : Bool :=
  Fp.all fun a => Fq.all fun b =>
    (List.range (min a b + 1)).all fun F => !(a % q == F % q && b % p == F % p)

theorem orderOf_ne_of_pqExcl {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {H : Subgroup (Equiv.Perm α)} {Fp Fq : List ℕ}
    (hFp : ∀ x ∈ H, orderOf x = p → fixCard x ∈ Fp)
    (hFq : ∀ y ∈ H, orderOf y = q → fixCard y ∈ Fq) (hex : pqExcl p q Fp Fq = true)
    {g : Equiv.Perm α} (hg : g ∈ H) : orderOf g ≠ p * q := by
  intro ho
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpos : orderOf g ≠ 0 := by rw [ho]; exact Nat.mul_ne_zero hp.ne_zero hq.ne_zero
  have ox : orderOf (g ^ (orderOf g / p)) = p :=
    orderOf_pow_orderOf_div hpos (by rw [ho]; exact dvd_mul_right p q)
  have oy : orderOf (g ^ (orderOf g / q)) = q :=
    orderOf_pow_orderOf_div hpos (by rw [ho]; exact dvd_mul_left q p)
  set x := g ^ (orderOf g / p)
  set y := g ^ (orderOf g / q)
  have hc : Commute x y := Commute.pow_pow_self g _ _
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hy : y ^ q = 1 := by
    rw [← oy]
    exact pow_orderOf_eq_one y
  have hx : x ^ p = 1 := by
    rw [← ox]
    exact pow_orderOf_eq_one x
  have m1 := fix_modEq hc hy
  have m2 := fix_modEq hc.symm hx
  set F := (Finset.univ.filter fun a => x a = a ∧ y a = a).card
  have e : (Finset.univ.filter fun a => y a = a ∧ x a = a).card = F := by
    simp only [F, and_comm]
  rw [e] at m2
  have l1 : F ≤ fixCard x := Finset.card_le_card fun a => by simp +contextual
  have l2 : F ≤ fixCard y := Finset.card_le_card fun a => by simp +contextual
  have ha := hFp x (H.pow_mem hg _) ox
  have hb := hFq y (H.pow_mem hg _) oy
  unfold pqExcl at hex
  have h3 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hex _ ha) _ hb) F
    (List.mem_range.2 (Nat.lt_succ_of_le (le_min l1 l2)))
  have h4 : (fixCard x % q == F % q && fixCard y % p == F % p) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨m1, m2⟩
  rw [h4] at h3
  exact absurd h3 (by decide)

end Fix

end CFSG.GroupTheory.SylowOddClasses

end
