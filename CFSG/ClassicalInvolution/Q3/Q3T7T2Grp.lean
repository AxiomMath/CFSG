module

public import CFSG.ClassicalInvolution.Basic

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7T2

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem sl2Three_pow_eight : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → g ^ 4 = 1 := by decide +kernel

theorem sl2Three_sq : ∀ g : SL(2, ZMod 3), g * g = 1 → g = 1 ∨ g = -1 := by decide +kernel

theorem sl2Three_q8 : ∀ g h : SL(2, ZMod 3), g ^ 4 = 1 → g ≠ 1 → g ≠ -1 → h ^ 4 = 1 →
    h = 1 ∨ h = g * g ∨ ∃ x : SL(2, ZMod 3), h = x * g * x⁻¹ := by decide +kernel

theorem sl2Three_gen : ∀ g : SL(2, ZMod 3), ∃ a b c : SL(2, ZMod 3),
    a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧ g = a * b * c := by decide +kernel

section Engel

variable {G : Type*} [Group G]

theorem engel_step {y t g : G} (hyt : y * t = t * y)
    (hc : y * (g * t * g⁻¹ * t⁻¹) * y⁻¹ = g * t * g⁻¹ * t⁻¹) :
    (g⁻¹ * (y * g * y⁻¹)) * t = t * (g⁻¹ * (y * g * y⁻¹)) := by
  obtain ⟨a, ha⟩ : ∃ a : G, a = y * g * y⁻¹ := ⟨_, rfl⟩
  have hyt' : y * t * y⁻¹ = t := by rw [hyt]; group
  have h1 : y * (g * t * g⁻¹ * t⁻¹) * y⁻¹ = a * t * a⁻¹ * t⁻¹ := by
    calc y * (g * t * g⁻¹ * t⁻¹) * y⁻¹
        = (y * g * y⁻¹) * (y * t * y⁻¹) * (y * g * y⁻¹)⁻¹ * (y * t * y⁻¹)⁻¹ := by group
      _ = a * t * a⁻¹ * t⁻¹ := by rw [hyt', ← ha]
  have h2 : a * t * a⁻¹ = g * t * g⁻¹ := mul_right_cancel (h1.symm.trans hc)
  have h3 : a * t = g * t * g⁻¹ * a := by
    have := congrArg (· * a) h2
    simpa [mul_assoc] using this
  rw [← ha]
  calc g⁻¹ * a * t = g⁻¹ * (a * t) := by rw [mul_assoc]
    _ = g⁻¹ * (g * t * g⁻¹ * a) := by rw [h3]
    _ = t * (g⁻¹ * a) := by group

theorem engel_odd [Finite G] {N : Subgroup G} (hN : IsPGroup 2 N) {y t : G}
    (hyN : ∀ g ∈ N, y * g * y⁻¹ ∈ N) (hy : Odd (orderOf y)) (ht : t ∈ N)
    (hyt : y * t = t * y) (hC : ∀ g ∈ N, g * t = t * g → y * g = g * y) :
    ∀ g ∈ N, y * g = g * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥N := hN.isNilpotent
  have key : ∀ n : ℕ, ∀ g : ↥N, g ∈ Subgroup.upperCentralSeries ↥N n →
      y * (g : G) = (g : G) * y := by
    intro n
    induction n with
    | zero =>
      intro g hg
      rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hg
      rw [hg]
      simp
    | succ n ih =>
      intro g hg
      have hc := ih _ (Subgroup.mem_upperCentralSeries_succ_iff.mp hg ⟨t, ht⟩)
      have hc' : y * ((g : G) * t * (g : G)⁻¹ * t⁻¹) * y⁻¹ = (g : G) * t * (g : G)⁻¹ * t⁻¹ := by
        have : y * ((g : G) * t * (g : G)⁻¹ * t⁻¹) = ((g : G) * t * (g : G)⁻¹ * t⁻¹) * y := by
          simpa [commutatorElement_def] using hc
        rw [this]
        group
      have hd := engel_step hyt hc'
      have hdN : (g : G)⁻¹ * (y * g * y⁻¹) ∈ N :=
        N.mul_mem (N.inv_mem g.2) (hyN _ g.2)
      have hyd : y * ((g : G)⁻¹ * (y * g * y⁻¹)) = ((g : G)⁻¹ * (y * g * y⁻¹)) * y :=
        hC _ hdN hd
      obtain ⟨d, hd'⟩ : ∃ d : G, d = (g : G)⁻¹ * (y * g * y⁻¹) := ⟨_, rfl⟩
      rw [← hd'] at hdN hyd
      have hgd : y * (g : G) * y⁻¹ = (g : G) * d := by rw [hd']; group
      have hyd' : y * d * y⁻¹ = d := by rw [hyd]; group
      have hpow : ∀ k : ℕ, y ^ k * (g : G) * (y ^ k)⁻¹ = (g : G) * d ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          have e1 : y ^ (k + 1) * (g : G) * (y ^ (k + 1))⁻¹
              = y * (y ^ k * (g : G) * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
          rw [e1, ihk]
          have e2 : y * ((g : G) * d ^ k) * y⁻¹ = (y * g * y⁻¹) * (y * d * y⁻¹) ^ k := by
            rw [conj_pow]; group
          rw [e2, hgd, hyd']
          group
      have hk := hpow (orderOf y)
      rw [pow_orderOf_eq_one] at hk
      have hdk : d ^ orderOf y = 1 := by
        have : (g : G) = (g : G) * d ^ orderOf y := by simpa using hk
        exact (mul_eq_left.mp this.symm)
      have hd1 : d = 1 := by
        obtain ⟨m, hm⟩ := hN.exists_orderOf_eq_pow ⟨d, hdN⟩
        have hm' : orderOf d = 2 ^ m := by rwa [Subgroup.orderOf_mk] at hm
        have hdvd : orderOf d ∣ orderOf y := orderOf_dvd_of_pow_eq_one hdk
        have hodd : Odd (orderOf d) := hy.of_dvd_nat hdvd
        rw [hm'] at hodd
        have hm0 : m = 0 := by
          by_contra hne
          exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
        rw [hm0, pow_zero] at hm'
        exact orderOf_eq_one_iff.mp hm'
      rw [hd1, mul_one] at hgd
      have : y * (g : G) = (g : G) * y := by
        calc y * (g : G) = y * (g : G) * y⁻¹ * y := by group
          _ = (g : G) * y := by rw [hgd]
      exact this
  intro g hg
  exact key (Group.nilpotencyClass ↥N) ⟨g, hg⟩
    (by rw [Subgroup.upperCentralSeries_nilpotencyClass]; trivial)

end Engel

section Subnormal

variable {G : Type*} [Group G]

theorem pow_mul_mem_of_normal {A M : Subgroup G}
    (hN : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) {j x : G} (hj : j ∈ A) (hx : x ∈ M) (n : ℕ) :
    ∃ j' ∈ A, (j * x) ^ n = j' * x ^ n := by
  induction n with
  | zero => exact ⟨1, A.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨j', hj', h⟩ := ih
    have hxn : x ^ n ∈ M := M.pow_mem hx n
    refine ⟨j' * (x ^ n * j * (x ^ n)⁻¹), A.mul_mem hj' (hN _ hxn _ hj), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem exists_pow_two_mem {J H X : Subgroup G} (hX : IsPGroup 2 X)
    (hHX : ∀ h ∈ H, ∃ j ∈ J, ∃ x ∈ X, h = j * x) {J' : Subgroup G} (hsub : IsSubnormal J' H) :
    J ≤ J' → ∀ h ∈ H, ∃ n : ℕ, h ^ (2 ^ n) ∈ J' := by
  induction hsub with
  | refl => intro _ h hh; exact ⟨0, by simpa using hh⟩
  | @step J'' M K hle hN hM ih =>
    intro hJJ h hh
    obtain ⟨n, hn⟩ := ih hHX (hJJ.trans hle) h hh
    have hmH : h ^ (2 ^ n) ∈ K := K.pow_mem hh _
    obtain ⟨j, hj, x, hx, hmx⟩ := hHX _ hmH
    have hxM : x ∈ M := by
      have : x = j⁻¹ * h ^ (2 ^ n) := by rw [hmx]; group
      rw [this]
      exact M.mul_mem (M.inv_mem (hle (hJJ hj))) hn
    obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    have hk' : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hN' : ∀ m ∈ M, ∀ a ∈ J'', m * a * m⁻¹ ∈ J'' :=
      fun m hm a ha => (Subgroup.normal_subgroupOf_iff hle).mp hN a m ha hm
    obtain ⟨j', hj', hjx⟩ := pow_mul_mem_of_normal hN' (hJJ hj) hxM (2 ^ k)
    refine ⟨n + k, ?_⟩
    rw [pow_add, pow_mul, hmx, hjx, hk', mul_one]
    exact hj'

theorem mem_of_pow_two_mem {J : Subgroup G} {y : G} (hy : Odd (orderOf y)) {n : ℕ}
    (h : y ^ (2 ^ n) ∈ J) : y ∈ J := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hy))
  rw [← hm]
  exact J.pow_mem h m

theorem le_normalizer_of_odd_closure {J H : Subgroup G} (hJH : J ≤ H)
    (hgen : Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} = J)
    (h2 : ∀ h ∈ H, ∃ n : ℕ, h ^ (2 ^ n) ∈ J) : H ≤ Subgroup.normalizer (J : Set G) := by
  have key : ∀ h ∈ H, ∀ x ∈ J, h * x * h⁻¹ ∈ J := by
    intro h hh x hx
    have hx' : x ∈ Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} := by rwa [hgen]
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem x hx0 =>
      have hyH : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh (hJH hx0.1)) (H.inv_mem hh)
      have hord : orderOf (h * x * h⁻¹) = orderOf x := by
        simpa [MulAut.conj_apply] using
          orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x
      obtain ⟨n, hn⟩ := h2 _ hyH
      exact mem_of_pow_two_mem (hord ▸ hx0.2) hn
    | one => simp
    | mul a b _ _ ha hb =>
      have : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      rw [this]
      exact J.mul_mem ha hb
    | inv a _ ha =>
      have : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
      rw [this]
      exact J.inv_mem ha
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => key h hh g hg
  · intro hg
    have := key h⁻¹ (H.inv_mem hh) _ hg
    simpa [mul_assoc] using this

end Subnormal

end CFSG.ClassicalInvolution.Q3.Q3T7T2
