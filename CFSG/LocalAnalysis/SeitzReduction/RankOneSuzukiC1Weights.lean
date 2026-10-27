module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiTwist
public import Mathlib.Algebra.Order.Star.Basic

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.LocalAnalysis.ComponentInitial

section Sqrt

variable {K : Type*} [Field K] [Fintype K]

theorem bilinear_eq_mul_sqrt_of_equivariant [CharP K 2] {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (hn : 1 ≤ n) (β : K →+ K →+ K) {μ : K} (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hβ : ∀ s x, β (μ * s) (μ * x) = μ * β s x) :
    ∃ c : K, ∀ s x, β s x = c * (s * x) ^ 2 ^ (n - 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨-, hb, -⟩ := finite_field_linearized_map_bases Nat.prime_two hn hcard
  obtain ⟨c, hc, -⟩ := hb β
  have hlt : 2 ^ (n - 1) < Fintype.card K := by
    rw [hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcoef : ∀ i j : Fin n,
      c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) = c i j * μ := by
    have h := eq_zero_of_forall_sum_sum_mul_pow_eq_zero hlt
      (a := fun i j => c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) - c i j * μ) fun u w => by
        have h1 := hβ u w
        rw [hc, hc] at h1
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        calc ∑ i, ∑ j, c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) *
              (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) =
            ∑ i, ∑ j, c i j * ((μ * u) ^ 2 ^ (i : ℕ) * (μ * w) ^ 2 ^ (j : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [mul_pow, mul_pow, pow_add]
              ring
          _ = μ * ∑ i, ∑ j, c i j * (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) := h1
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
    intro i j
    exact sub_eq_zero.mp (congrFun (congrFun h i) j)
  have hzero : ∀ i j : Fin n, ((i : ℕ) ≠ n - 1 ∨ (j : ℕ) ≠ n - 1) → c i j = 0 := by
    intro i j hij
    by_contra hcij
    have hn2 : 2 ≤ n := by omega
    have hμ0 := ne_zero_of_forall_pow_eq_of_two_le hK hn2 hμ
    have h1 := mul_left_cancel₀ hcij (hcoef i j)
    have h1i : 1 ≤ 2 ^ (i : ℕ) := Nat.one_le_two_pow
    have h1j : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
    have hE : μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ) - 1) = 1 := by
      rw [show 2 ^ (i : ℕ) + 2 ^ (j : ℕ) = (2 ^ (i : ℕ) + 2 ^ (j : ℕ) - 1) + 1 by omega,
        pow_succ] at h1
      exact mul_right_cancel₀ hμ0 (h1.trans (one_mul μ).symm)
    have hdvd := orderOf_dvd_of_pow_eq_one hE
    rw [orderOf_eq_of_forall_pow_eq hμ0 hμ, hK] at hdvd
    have := eq_pred_of_dvd_two_pow_add_two_pow_sub_one i.2 j.2 hdvd
    omega
  refine ⟨c ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩, fun s x => ?_⟩
  rw [hc, Finset.sum_eq_single ⟨n - 1, by omega⟩, Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · rw [mul_pow]
  · intro j _ hj
    rw [hzero _ _ (Or.inr fun h => hj (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hzero _ _ (Or.inl fun h => hi (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem bilinear_eq_mul_sqrt_of_equivariant' [CharP K 2] {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (hn : 1 ≤ n) (β : K → K → K) (h1 : ∀ s s' x, β (s + s') x = β s x + β s' x)
    (h2 : ∀ s x x', β s (x + x') = β s x + β s x') {μ : K}
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) (hβ : ∀ s x, β (μ * s) (μ * x) = μ * β s x) :
    ∃ c : K, ∀ s x, β s x = c * (s * x) ^ 2 ^ (n - 1) :=
  bilinear_eq_mul_sqrt_of_equivariant hK hn (AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (β s)
    (h2 s)) fun s s' => AddMonoidHom.ext fun x => h1 s s' x) hμ hβ

end Sqrt

section Delta

variable {K : Type*} [Field K] [Fintype K]

theorem szDelta_eq_of_equivariant [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (δ : K →+ K →+ K) {κ : K}
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hδ : ∀ s b, δ (κ ^ (2 ^ (a + 1) + 1) * s) (κ * b) = κ ^ (2 ^ (a + 1) + 1) * δ s b) :
    ∃ c : K, ∃ ι : K →+ K, ∀ s b, δ s b = c * (s * b) ^ 2 ^ a +
      (ι s * b ^ 2 ^ (a + 1) + (ι s) ^ 2 ^ (a + 1) * b) := by
  obtain ⟨c, hc⟩ := SzCoords.bilinear_of_equivariant' ha hK (fun b s => δ s b)
    (fun b b' s => map_add (δ s) b b') (fun b s s' => by rw [map_add, AddMonoidHom.add_apply])
    hκ fun b s => hδ s b
  refine ⟨c, 0, fun s b => ?_⟩
  rw [hc b s, AddMonoidHom.zero_apply, zero_mul, zero_pow (pow_ne_zero _ two_ne_zero),
    zero_mul, add_zero, add_zero, mul_comm b s]

end Delta

namespace SzC1

section Coeff

variable {K : Type*} [Field K] [Fintype K]

omit [Fintype K] in
theorem frob_add [CharP K 2] (x y : K) (k : ℕ) : (x + y) ^ 2 ^ k = x ^ 2 ^ k + y ^ 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact add_pow_char_pow x y 2 k

theorem exists_coeff {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n) (j : Fin n) :
    ∃ P : (K →+ K) →ₗ[K] K, ∀ (c : Fin n → K) (g : K →+ K),
      (∀ x, g x = ∑ i, c i * x ^ 2 ^ (i : ℕ)) → P g = c j := by
  classical
  have hcard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨-, -, ⟨B, hB⟩, -⟩ := finite_field_linearized_map_bases Nat.prime_two hn hcard
  refine ⟨B.coord j, fun c g hg => ?_⟩
  have e : g = ∑ i, c i • B i := by
    refine AddMonoidHom.ext fun x => ?_
    rw [hg x, AddMonoidHom.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AddMonoidHom.smul_apply, smul_eq_mul, hB]
  rw [Module.Basis.coord_apply, e, Module.Basis.repr_sum_self]

theorem coeff_comp_mul {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n) {j : Fin n}
    {P : (K →+ K) →ₗ[K] K}
    (hP : ∀ (c : Fin n → K) (g : K →+ K), (∀ x, g x = ∑ i, c i * x ^ 2 ^ (i : ℕ)) → P g = c j)
    (g : K →+ K) (κ : K) :
    P (g.comp (AddMonoidHom.mulLeft κ)) = κ ^ 2 ^ (j : ℕ) * P g := by
  have hcard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨h1, -⟩ := finite_field_linearized_map_bases Nat.prime_two hn hcard
  obtain ⟨c, hc, -⟩ := h1 g
  rw [hP c g hc, hP (fun i => c i * κ ^ 2 ^ (i : ℕ)) _ fun x => ?_]
  · ring
  · rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring

end Coeff

end SzC1

section Group

variable {K : Type*} [Field K] [Fintype K]

omit [Fintype K] in
theorem exists_addMonoidHom₂_of_hom {G : Type*} [Group G] {M : Subgroup G} {S : G → K}
    {Φ : G → K → K} (hS : ∀ m ∈ M, ∀ m' ∈ M, S (m * m') = S m + S m')
    (hSsurj : ∀ s : K, ∃ m ∈ M, S m = s)
    (hΦ : ∀ m ∈ M, ∀ m' ∈ M, ∀ b, Φ (m * m') b = Φ m b + Φ m' b)
    (hΦadd : ∀ m ∈ M, ∀ b b', Φ m (b + b') = Φ m b + Φ m b')
    (hker : ∀ m ∈ M, S m = 0 → ∀ b, Φ m b = 0) :
    ∃ D : K →+ K →+ K, ∀ m ∈ M, ∀ b, Φ m b = D (S m) b := by
  choose sec hsecM hsecS using hSsurj
  have key : ∀ m ∈ M, ∀ b, Φ m b = Φ (sec (S m)) b := by
    intro m hm b
    set m₀ := sec (S m) with hm₀
    have hm₀M : m₀ ∈ M := hsecM _
    have hk : m₀⁻¹ * m ∈ M := mul_mem (inv_mem hm₀M) hm
    have hSk : S (m₀⁻¹ * m) = 0 := by
      have h1 := hS m₀ hm₀M _ hk
      rw [mul_inv_cancel_left, hsecS] at h1
      exact left_eq_add.mp h1
    have h2 := hΦ m₀ hm₀M _ hk b
    rw [mul_inv_cancel_left, hker _ hk hSk b, add_zero] at h2
    exact h2
  refine ⟨AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun b => Φ (sec s) b)
    (hΦadd _ (hsecM s))) fun s s' => AddMonoidHom.ext fun b => ?_, fun m hm b => key m hm b⟩
  have hmul := mul_mem (hsecM s) (hsecM s')
  show Φ (sec (s + s')) b = Φ (sec s) b + Φ (sec s') b
  rw [← hΦ _ (hsecM s) _ (hsecM s'), key _ hmul, hS _ (hsecM s) _ (hsecM s'), hsecS, hsecS]

theorem exists_mul_sqrt_of_hom [CharP K 2] {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n)
    {μ : K} (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {G : Type*} [Group G] {M : Subgroup G}
    {S : G → K} {χ : G → K → K} (hS : ∀ m ∈ M, ∀ m' ∈ M, S (m * m') = S m + S m')
    (hSsurj : ∀ s : K, ∃ m ∈ M, S m = s)
    (hχ : ∀ m ∈ M, ∀ m' ∈ M, ∀ x, χ (m * m') x = χ m x + χ m' x)
    (hχadd : ∀ m ∈ M, ∀ x x', χ m (x + x') = χ m x + χ m x')
    (hker : ∀ m ∈ M, S m = 0 → ∀ x, χ m x = 0)
    (hequiv : ∀ m ∈ M, ∃ m' ∈ M, S m' = μ * S m ∧ ∀ x, χ m' (μ * x) = μ * χ m x) :
    ∃ c : K, ∀ m ∈ M, ∀ x, χ m x = c * (S m * x) ^ 2 ^ (n - 1) := by
  obtain ⟨D, hD⟩ := exists_addMonoidHom₂_of_hom hS hSsurj hχ hχadd hker
  obtain ⟨c, hc⟩ := bilinear_eq_mul_sqrt_of_equivariant hK hn D hμ fun s x => by
    obtain ⟨m, hm, rfl⟩ := hSsurj s
    obtain ⟨m', hm', hSm', hm'x⟩ := hequiv m hm
    rw [← hSm', ← hD m' hm', hm'x, hD m hm]
  exact ⟨c, fun m hm x => by rw [hD m hm, hc]⟩

theorem exists_szDelta_const [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {κ : K} (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    {G : Type*} [Group G] {M : Subgroup G} {S : G → K} {Δ : G → K → K}
    (hS : ∀ m ∈ M, ∀ m' ∈ M, S (m * m') = S m + S m')
    (hSsurj : ∀ s : K, ∃ m ∈ M, S m = s)
    (hΔ : ∀ m ∈ M, ∀ m' ∈ M, ∀ b, Δ (m * m') b = Δ m b + Δ m' b)
    (hΔadd : ∀ m ∈ M, ∀ b b', Δ m (b + b') = Δ m b + Δ m b')
    (hker : ∀ m ∈ M, S m = 0 →
      ∃ c : K, ∀ b, Δ m b = c * b ^ 2 ^ (a + 1) + c ^ 2 ^ (a + 1) * b)
    (hequiv : ∀ m ∈ M, ∃ m' ∈ M, S m' = κ ^ (2 ^ (a + 1) + 1) * S m ∧
      ∀ b, Δ m' (κ * b) = κ ^ (2 ^ (a + 1) + 1) * Δ m b) :
    ∃ l : K, ∀ m ∈ M, ∃ c : K, ∀ b,
      Δ m b = l * (S m * b) ^ 2 ^ a + (c * b ^ 2 ^ (a + 1) + c ^ 2 ^ (a + 1) * b) := by
  classical
  have hn1 : 1 ≤ 2 * a + 1 := by omega
  have hκ0 : κ ≠ 0 := ne_zero_of_forall_pow_eq_of_two_le hK (by omega) hκ
  obtain ⟨P, hP⟩ := SzC1.exists_coeff hK hn1 ⟨a + 1, by omega⟩
  have hPinner : ∀ (c : K) (g : K →+ K),
      (∀ b, g b = c * b ^ 2 ^ (a + 1) + c ^ 2 ^ (a + 1) * b) → P g = c := by
    intro c g hg
    have h := hP (fun i => if (i : ℕ) = a + 1 then c else if (i : ℕ) = 0 then c ^ 2 ^ (a + 1)
      else 0) g fun x => by
        rw [hg x, Fintype.sum_eq_add (⟨a + 1, by omega⟩ : Fin (2 * a + 1)) ⟨0, by omega⟩
          (by simp [Fin.ext_iff]) fun i hi => ?_]
        · simp
        · have h1 : (i : ℕ) ≠ a + 1 := fun h => hi.1 (Fin.ext h)
          have h2 : (i : ℕ) ≠ 0 := fun h => hi.2 (Fin.ext h)
          simp [h1, h2]
    simpa using h
  let Δb : G → K →+ K := fun m =>
    if hm : m ∈ M then AddMonoidHom.mk' (Δ m) (hΔadd m hm) else 0
  have hΔb : ∀ m ∈ M, ∀ b, Δb m b = Δ m b := fun m hm b => by simp [Δb, hm]
  set Pm : G → K := fun m => P (Δb m) with hPm
  have hPmul : ∀ m ∈ M, ∀ m' ∈ M, Pm (m * m') = Pm m + Pm m' := by
    intro m hm m' hm'
    have e : Δb (m * m') = Δb m + Δb m' := AddMonoidHom.ext fun b => by
      rw [AddMonoidHom.add_apply, hΔb _ (mul_mem hm hm'), hΔb m hm, hΔb m' hm', hΔ m hm m' hm']
    simp only [hPm, e, map_add]
  obtain ⟨D, hD⟩ := exists_addMonoidHom₂_of_hom (Φ := fun m b =>
      Δ m b - (Pm m * b ^ 2 ^ (a + 1) + Pm m ^ 2 ^ (a + 1) * b)) hS hSsurj
    (fun m hm m' hm' b => by
      rw [hΔ m hm m' hm', hPmul m hm m' hm', SzC1.frob_add]
      ring)
    (fun m hm b b' => by
      rw [hΔadd m hm, SzC1.frob_add]
      ring)
    (fun m hm hSm b => by
      obtain ⟨c, hc⟩ := hker m hm hSm
      have hPc : Pm m = c := hPinner c (Δb m) fun b => by rw [hΔb m hm, hc]
      rw [hPc, hc, sub_self])
  have hDeq : ∀ s b, D (κ ^ (2 ^ (a + 1) + 1) * s) (κ * b) = κ ^ (2 ^ (a + 1) + 1) * D s b := by
    intro s b
    obtain ⟨m, hm, rfl⟩ := hSsurj s
    obtain ⟨m', hm', hSm', hm'b⟩ := hequiv m hm
    have hcomp : (Δb m').comp (AddMonoidHom.mulLeft κ) = κ ^ (2 ^ (a + 1) + 1) • Δb m :=
      AddMonoidHom.ext fun b => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, hΔb m' hm', AddMonoidHom.smul_apply,
          hΔb m hm, smul_eq_mul, hm'b]
    have h1 : κ ^ 2 ^ (a + 1) * Pm m' = κ ^ (2 ^ (a + 1) + 1) * Pm m := by
      have h := SzC1.coeff_comp_mul hK hn1 hP (Δb m') κ
      rw [hcomp, map_smul, smul_eq_mul] at h
      exact h.symm
    have h2 : Pm m' ^ 2 ^ (a + 1) * κ = κ ^ (2 ^ (a + 1) + 1) * Pm m ^ 2 ^ (a + 1) := by
      have h3 := congrArg (fun x => x ^ 2 ^ (a + 1)) h1
      simp only [mul_pow] at h3
      rw [pow_succ κ (2 ^ (a + 1)), mul_pow] at h3
      have hk : (κ ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hκ0)
      have h4 : Pm m' ^ 2 ^ (a + 1) = κ ^ 2 ^ (a + 1) * Pm m ^ 2 ^ (a + 1) := by
        apply mul_left_cancel₀ hk
        rw [h3]
        ring
      rw [h4, pow_succ]
      ring
    rw [← hSm', ← hD m' hm', ← hD m hm, hm'b, mul_pow κ b]
    linear_combination (-(b ^ 2 ^ (a + 1))) * h1 - b * h2
  obtain ⟨l, hl⟩ := SzCoords.bilinear_of_equivariant' ha hK (fun b s => D s b)
    (fun b b' s => map_add (D s) b b') (fun b s s' => by rw [map_add, AddMonoidHom.add_apply])
    hκ fun b s => hDeq s b
  refine ⟨l, fun m hm => ⟨Pm m, fun b => ?_⟩⟩
  have h := hD m hm b
  rw [hl b (S m), mul_comm b (S m)] at h
  linear_combination h

theorem addMonoidHom_eq_zero_of_weight [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (f : K →+ K) {κ : K}
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hf : ∀ s, f (κ ^ (2 ^ (a + 1) + 1) * s) = κ * f s) : f = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card K = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨hb, -⟩ := finite_field_linearized_map_bases Nat.prime_two (by omega) hcard
  obtain ⟨c, hc, -⟩ := hb f
  have hlt : 2 ^ (2 * a + 1 - 1) < Fintype.card K := by
    rw [hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hκ0 : κ ≠ 0 := ne_zero_of_forall_pow_eq_of_two_le hK (by omega) hκ
  have hcoef : ∀ j : Fin (2 * a + 1),
      c j * κ ^ ((2 ^ (a + 1) + 1) * 2 ^ (j : ℕ)) = κ * c j := by
    have h := eq_zero_of_forall_sum_mul_pow_eq_zero hlt
      (a := fun j => c j * κ ^ ((2 ^ (a + 1) + 1) * 2 ^ (j : ℕ)) - κ * c j) fun s => by
        have h1 := hf s
        rw [hc, hc] at h1
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        calc ∑ j, c j * κ ^ ((2 ^ (a + 1) + 1) * 2 ^ (j : ℕ)) * s ^ 2 ^ (j : ℕ) =
            ∑ j, c j * (κ ^ (2 ^ (a + 1) + 1) * s) ^ 2 ^ (j : ℕ) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [mul_pow, ← pow_mul]
              ring
          _ = κ * ∑ j, c j * s ^ 2 ^ (j : ℕ) := h1
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
    intro j
    exact sub_eq_zero.mp (congrFun h j)
  have hzero : ∀ j, c j = 0 := by
    intro j
    by_contra hcj
    have h1 := mul_left_cancel₀ hcj ((hcoef j).trans (mul_comm κ (c j)))
    have hpos : 1 ≤ (2 ^ (a + 1) + 1) * 2 ^ (j : ℕ) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hE : κ ^ ((2 ^ (a + 1) + 1) * 2 ^ (j : ℕ) - 1) = 1 := by
      rw [show (2 ^ (a + 1) + 1) * 2 ^ (j : ℕ) = ((2 ^ (a + 1) + 1) * 2 ^ (j : ℕ) - 1) + 1 by
        omega, pow_succ] at h1
      exact mul_right_cancel₀ hκ0 (h1.trans (one_mul κ).symm)
    have hdvd := orderOf_dvd_of_pow_eq_one hE
    rw [orderOf_eq_of_forall_pow_eq hκ0 hκ, hK] at hdvd
    have hθ : 2 ≤ 2 ^ (a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 2 * 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := by
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdvd' : 2 ^ (2 * a + 1) - 1 ∣ 2 ^ (a + 1) + (2 ^ (a + 1) + 1) * 2 ^ (j : ℕ) +
        (2 ^ (2 * a + 1) - 2 - 2 ^ (a + 1)) := by
      have e : 2 ^ (a + 1) + (2 ^ (a + 1) + 1) * 2 ^ (j : ℕ) +
          (2 ^ (2 * a + 1) - 2 - 2 ^ (a + 1)) =
          ((2 ^ (a + 1) + 1) * 2 ^ (j : ℕ) - 1) + (2 ^ (2 * a + 1) - 1) := by omega
      rw [e]
      exact dvd_add hdvd dvd_rfl
    have := SzCoords.exp_eq_of_dvd ha (i := a + 1) (by omega) j.2 hdvd'
    omega
  refine AddMonoidHom.ext fun s => ?_
  rw [hc, AddMonoidHom.zero_apply]
  simp [hzero]

theorem eq_zero_of_hom_weight [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {κ : K} (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    {G : Type*} [Group G] {M : Subgroup G} {S φ : G → K}
    (hS : ∀ m ∈ M, ∀ m' ∈ M, S (m * m') = S m + S m') (hSsurj : ∀ s : K, ∃ m ∈ M, S m = s)
    (hφ : ∀ m ∈ M, ∀ m' ∈ M, φ (m * m') = φ m + φ m') (hker : ∀ m ∈ M, S m = 0 → φ m = 0)
    (hequiv : ∀ m ∈ M, ∃ m' ∈ M, S m' = κ ^ (2 ^ (a + 1) + 1) * S m ∧ φ m' = κ * φ m) :
    ∀ m ∈ M, φ m = 0 := by
  obtain ⟨D, hD⟩ := exists_addMonoidHom₂_of_hom (Φ := fun m b => φ m * b) hS hSsurj
    (fun m hm m' hm' b => by rw [hφ m hm m' hm', add_mul]) (fun m _ b b' => mul_add _ _ _)
    (fun m hm hSm b => by rw [hker m hm hSm, zero_mul])
  have h0 := addMonoidHom_eq_zero_of_weight ha hK (D.flip 1) hκ fun s => by
    obtain ⟨m, hm, rfl⟩ := hSsurj s
    obtain ⟨m', hm', hSm', hφm'⟩ := hequiv m hm
    rw [AddMonoidHom.flip_apply, AddMonoidHom.flip_apply, ← hSm', ← hD m' hm', ← hD m hm, hφm',
      mul_one, mul_one]
  intro m hm
  have h1 := hD m hm 1
  rw [mul_one] at h1
  rw [h1, ← AddMonoidHom.flip_apply, h0, AddMonoidHom.zero_apply]

omit [Fintype K] in
theorem exists_mul_of_hom {μ : K} (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {G : Type*}
    [Group G] {M : Subgroup G} {S φ : G → K}
    (hS : ∀ m ∈ M, ∀ m' ∈ M, S (m * m') = S m + S m') (hSsurj : ∀ s : K, ∃ m ∈ M, S m = s)
    (hφ : ∀ m ∈ M, ∀ m' ∈ M, φ (m * m') = φ m + φ m') (hker : ∀ m ∈ M, S m = 0 → φ m = 0)
    (hequiv : ∀ m ∈ M, ∃ m' ∈ M, S m' = μ * S m ∧ φ m' = μ * φ m) :
    ∃ ν : K, ∀ m ∈ M, φ m = ν * S m := by
  obtain ⟨D, hD⟩ := exists_addMonoidHom₂_of_hom (Φ := fun m b => φ m * b) hS hSsurj
    (fun m hm m' hm' b => by rw [hφ m hm m' hm', add_mul]) (fun m _ b b' => mul_add _ _ _)
    (fun m hm hSm b => by rw [hker m hm hSm, zero_mul])
  have hlin := SzCoords.linear_of_equivariant (f := fun s => D s 1) (μ := μ) (fun s => by
    obtain ⟨m, hm, rfl⟩ := hSsurj s
    obtain ⟨m', hm', hSm', hφm'⟩ := hequiv m hm
    show D (μ * S m) 1 = μ * D (S m) 1
    rw [← hSm', ← hD m' hm', ← hD m hm, hφm', mul_one, mul_one]) (by
      show D 0 1 = 0
      rw [map_zero, AddMonoidHom.zero_apply]) hμ
  refine ⟨D 1 1, fun m hm => ?_⟩
  have h1 := hD m hm 1
  rw [mul_one] at h1
  rw [h1, hlin (S m)]

end Group

end CFSG.SeitzReduction.RankOne
