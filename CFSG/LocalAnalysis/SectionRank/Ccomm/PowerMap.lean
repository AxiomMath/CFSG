module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup
open scoped commutatorElement

section ClassTwo

variable {G : Type*} [Group G]

theorem pow_mul_eq_of_commute {x y : G} (hy : Commute y ⁅y, x⁆) (n : ℕ) :
    y ^ n * x = ⁅y, x⁆ ^ n * x * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hyx : y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * ⁅y, x⁆ ^ n * x * y ^ n := by rw [ih]; group
      _ = ⁅y, x⁆ ^ n * (y * x) * y ^ n := by rw [(hy.pow_right n).eq]; group
      _ = ⁅y, x⁆ ^ (n + 1) * x * y ^ (n + 1) := by rw [hyx, pow_succ, pow_succ']; group

theorem mul_pow_eq_of_commute {x y : G} (hx : Commute x ⁅y, x⁆) (hy : Commute y ⁅y, x⁆)
    (n : ℕ) : (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    set c := ⁅y, x⁆ with hc
    have e1 : c ^ n.choose 2 * x = x * c ^ n.choose 2 := ((hx.pow_right _).eq).symm
    have e2 : y ^ n * x = c ^ n * x * y ^ n := pow_mul_eq_of_commute hy n
    have e3 : x ^ n * c ^ n = c ^ n * x ^ n := ((hx.pow_right n).pow_left n).eq
    have e4 : c ^ n.choose 2 * y = y * c ^ n.choose 2 := ((hy.pow_right _).eq).symm
    have e5 : c ^ n * (x ^ (n + 1) * y ^ (n + 1)) = x ^ (n + 1) * y ^ (n + 1) * c ^ n :=
      (((hx.pow_right n).pow_left (n + 1)).mul_left
        ((hy.pow_right n).pow_left (n + 1))).eq.symm
    calc (x * y) ^ (n + 1) = x ^ n * y ^ n * c ^ n.choose 2 * x * y := by
          rw [pow_succ, ih]; group
      _ = x ^ n * (y ^ n * x) * c ^ n.choose 2 * y := by
          rw [mul_assoc _ (c ^ _) x, e1]; group
      _ = (x ^ n * c ^ n) * x * y ^ n * (c ^ n.choose 2 * y) := by rw [e2]; group
      _ = c ^ n * (x ^ (n + 1) * y ^ (n + 1)) * c ^ n.choose 2 := by rw [e3, e4]; group
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + 1).choose 2 := by
          rw [e5, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]; group

theorem commutatorElement_pow_left {x y : G} (h : Commute x ⁅x, y⁆) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ⁅x ^ (n + 1), y⁆ = x * ⁅x ^ n, y⁆ * x⁻¹ * ⁅x, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, ih, (h.pow_right n).eq, pow_succ]; group

theorem dvd_choose_two_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ∣ p.choose 2 :=
  hp.dvd_choose_self (by norm_num) (lt_of_le_of_ne hp.two_le (Ne.symm hp2))

theorem mul_pow_prime_eq_of_commute {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y : G}
    (hx : Commute x ⁅y, x⁆) (hy : Commute y ⁅y, x⁆) (hc : ⁅y, x⁆ ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  obtain ⟨k, hk⟩ := dvd_choose_two_of_ne_two hp hp2
  rw [mul_pow_eq_of_commute hx hy, hk, pow_mul, hc, one_pow, mul_one]

theorem mulAut_pow_apply_of_fixed_displacement (α : MulAut G) (x : G)
    (hfix : α (x⁻¹ * α x) = x⁻¹ * α x) (j : ℕ) : (α ^ j) x = x * (x⁻¹ * α x) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, pow_succ', ← mul_assoc,
      mul_inv_cancel_left]

end ClassTwo

theorem coprime_automorphism_trivial_normal_factors {H : Type*} [Group H] (N : Subgroup H)
    [N.Normal] [Finite N] (φ : MulAut H) {m : ℕ} (_hm : 1 ≤ m) (hφ : φ ^ m = 1)
    (hcop : m.Coprime (Nat.card N)) (hfixN : ∀ n ∈ N, φ n = n)
    (hdisp : ∀ h : H, h⁻¹ * φ h ∈ N) : φ = 1 :=
  CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement N φ m hφ hcop
    hfixN hdisp

section PowerMap

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

theorem central_frattini_odd_power_map (hp2 : p ≠ 2) (hH : IsPGroup p H)
    (hΦ : frattini H ≤ center H) :
    commutator H ≤ center H ∧ (∀ x y : H, ⁅x, y⁆ ^ p = 1) ∧
      (∃ θ : H →* center H, (∀ x, (θ x : H) = x ^ p) ∧ θ.ker = omega₁ (G := H) (p := p)) ∧
      ((omega₁ (G := H) (p := p) : Set H) = {x | x ^ p = 1}) ∧
      (omega₁ (G := H) (p := p)).Characteristic ∧
      (Nontrivial H → omega₁ (G := H) (p := p) ≠ ⊥) := by
  have hZ : ∀ x : H, x ^ p ∈ center H := fun x => hΦ (pow_mem_frattini hH x)
  have hcomm : ∀ x y : H, ⁅x, y⁆ ∈ center H := fun x y => hΦ (commutator_mem_frattini hH x y)
  have hcpow : ∀ x y : H, ⁅x, y⁆ ^ p = 1 := by
    intro x y
    rw [← commutatorElement_pow_left (mem_center_iff.1 (hcomm x y) x),
      commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.1 (hZ x) y).symm
  have hmulpow : ∀ x y : H, (x * y) ^ p = x ^ p * y ^ p := fun x y =>
    mul_pow_prime_eq_of_commute hp.out hp2 (mem_center_iff.1 (hcomm y x) x)
      (mem_center_iff.1 (hcomm y x) y) (hcpow y x)
  let K : Subgroup H :=
    { carrier := {x | x ^ p = 1}
      mul_mem' := fun {x y} hx hy => by
        change (x * y) ^ p = 1
        rw [hmulpow, hx, hy, one_mul]
      one_mem' := one_pow p
      inv_mem' := fun {x} hx => by
        change x⁻¹ ^ p = 1
        rw [inv_pow, hx, inv_one] }
  have hΩ : omega₁ (G := H) (p := p) = K := by
    change Subgroup.closure {x : H | x ^ (p ^ 1) = 1} = K
    simp only [pow_one]
    exact closure_eq K
  refine ⟨?_, hcpow, ?_, by rw [hΩ]; rfl, omega₁_characteristic H, ?_⟩
  · rw [commutator_def, commutator_le]
    exact fun x _ y _ => hcomm x y
  · refine ⟨MonoidHom.mk' (fun x => ⟨x ^ p, hZ x⟩) (fun x y => Subtype.ext (hmulpow x y)),
      fun x => rfl, ?_⟩
    rw [hΩ]
    ext x
    rw [MonoidHom.mem_ker, ← Subtype.val_inj]
    rfl
  · intro hnt
    obtain ⟨n, hn0, hn⟩ := hH.nontrivial_iff_card.1 hnt
    have hdvd : p ∣ Nat.card H := hn ▸ dvd_pow_self p hn0.ne'
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      exact hp.out.one_lt.ne hx
    rw [hΩ]
    intro hK
    have hxK : x ∈ K := by
      change x ^ p = 1
      rw [← hx]
      exact pow_orderOf_eq_one x
    rw [hK, mem_bot] at hxK
    exact hx1 hxK

theorem central_frattini_odd_aut_detection (hp2 : p ≠ 2) (hH : IsPGroup p H)
    (hΦ : frattini H ≤ center H) (α : MulAut H) (hα : (orderOf α).Coprime p)
    (hfix : ∀ x ∈ omega₁ (G := H) (p := p), α x = x) : α = 1 := by
  obtain ⟨-, -, ⟨θ, hθ, -⟩, hset, -, -⟩ := central_frattini_odd_power_map hp2 hH hΦ
  have hpowmul : ∀ x y : H, (x * y) ^ p = x ^ p * y ^ p := fun x y => by
    rw [← hθ, ← hθ, ← hθ, map_mul, Subgroup.coe_mul]
  have key : ∀ i : ℕ, ∀ x : H, x ^ (p ^ i) = 1 → α x = x := by
    intro i
    induction i with
    | zero =>
      intro x hx
      rw [pow_zero, pow_one] at hx
      rw [hx, map_one]
    | succ i ih =>
      intro x hx
      have h1 : α (x ^ p) = x ^ p := ih _ (by rw [← pow_mul, ← pow_succ']; exact hx)
      have hyp : (x⁻¹ * α x) ^ p = 1 := by
        rw [hpowmul, inv_pow, ← map_pow, h1, inv_mul_cancel]
      have hyfix : α (x⁻¹ * α x) = x⁻¹ * α x :=
        hfix _ (by rw [← SetLike.mem_coe, hset]; exact hyp)
      have hm : (x⁻¹ * α x) ^ orderOf α = 1 := by
        have := mulAut_pow_apply_of_fixed_displacement α x hyfix (orderOf α)
        rw [pow_orderOf_eq_one, MulAut.one_apply] at this
        exact mul_eq_left.1 this.symm
      have hord : orderOf (x⁻¹ * α x) ∣ Nat.gcd (orderOf α) p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hyp)
      rw [Nat.Coprime.gcd_eq_one hα, Nat.dvd_one, orderOf_eq_one_iff] at hord
      exact (inv_mul_eq_one.1 hord).symm
  ext x
  obtain ⟨k, hk⟩ := hH x
  exact key k x hk

end PowerMap

end CFSG.SectionRank.Ccomm
