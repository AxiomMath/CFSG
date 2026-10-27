module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SemidirectProduct
import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fixed

public section

namespace CFSG.GroupTheory

open CFSG.GH74.GLS.Stage1.Thm6.Sec13

private theorem conj_pow_mem {G : Type*} [Group G] {N : Subgroup G} {f : G}
    (hN : ∀ n ∈ N, f * n * f⁻¹ ∈ N) (k : ℕ) :
    ∀ n ∈ N, f ^ k * n * (f ^ k)⁻¹ ∈ N := by
  induction k with
  | zero =>
    intro n hn
    simpa using hn
  | succ k ih =>
    intro n hn
    rw [pow_succ]
    have h := ih (f * n * f⁻¹) (hN n hn)
    simpa [mul_assoc] using h

private theorem conj_pow_coset_mem {G : Type*} [Group G] {N : Subgroup G} {f g : G}
    (hN : ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hg : g⁻¹ * (f * g * f⁻¹) ∈ N) (k : ℕ) :
    g⁻¹ * (f ^ k * g * (f ^ k)⁻¹) ∈ N := by
  induction k with
  | zero => simpa using N.one_mem
  | succ k ih =>
    rw [pow_succ]
    have h := conj_pow_mem hN k (g⁻¹ * (f * g * f⁻¹)) hg
    have e : g⁻¹ * ((f ^ k * f) * g * (f ^ k * f)⁻¹) =
        (g⁻¹ * (f ^ k * g * (f ^ k)⁻¹)) *
          (f ^ k * (g⁻¹ * (f * g * f⁻¹)) * (f ^ k)⁻¹) := by
      group
    rw [e]
    exact N.mul_mem ih h

private theorem conj_fixed_of_mem_sup {G : Type*} [Group G] {f f₁ f₂ x : G}
    (hf : f ∈ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂)
    (h₁ : f₁ * x * f₁⁻¹ = x) (h₂ : f₂ * x * f₂⁻¹ = x) :
    f * x * f⁻¹ = x := by
  have h₁c : f₁ ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc f₁ * x = (f₁ * x * f₁⁻¹) * f₁ := by group
      _ = x * f₁ := by rw [h₁]
  have h₂c : f₂ ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc f₂ * x = (f₂ * x * f₂⁻¹) * f₂ := by group
      _ = x * f₂ := by rw [h₂]
  have hle : Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ≤
      Subgroup.centralizer ({x} : Set G) := by
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact h₁c
    · rw [Subgroup.zpowers_le]
      exact h₂c
  have hf_comm : f * x = x * f :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hf)
  calc f * x * f⁻¹ = (x * f) * f⁻¹ := by rw [hf_comm]
    _ = x := by group

private theorem mem_sup_zpowers_pow {G : Type*} [Group G] (f : G) {m p k : ℕ}
    (hcop : Nat.Coprime m (p ^ k)) :
    f ∈ Subgroup.zpowers (f ^ m) ⊔ Subgroup.zpowers (f ^ (p ^ k)) := by
  have hbez : (m : ℤ) * Nat.gcdA m (p ^ k) +
      ((p ^ k : ℕ) : ℤ) * Nat.gcdB m (p ^ k) = 1 := by
    have h := Nat.gcd_eq_gcd_ab m (p ^ k)
    rw [hcop.gcd_eq_one] at h
    exact h.symm
  have hf_decomp : f = (f ^ m) ^ (Nat.gcdA m (p ^ k) : ℤ) *
      (f ^ (p ^ k)) ^ (Nat.gcdB m (p ^ k) : ℤ) := by
    rw [← zpow_natCast f m, ← zpow_natCast f (p ^ k)]
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    rw [hbez]
    simp
  have hmem := Subgroup.mul_mem_sup
    (Subgroup.zpow_mem (Subgroup.zpowers (f ^ m)) (Subgroup.mem_zpowers (f ^ m))
      (Nat.gcdA m (p ^ k) : ℤ))
    (Subgroup.zpow_mem (Subgroup.zpowers (f ^ (p ^ k)))
      (Subgroup.mem_zpowers (f ^ (p ^ k))) (Nat.gcdB m (p ^ k) : ℤ))
  rwa [← hf_decomp] at hmem

private theorem exists_prime_power_factor {n : ℕ} (hnpos : 0 < n) (hn1 : n ≠ 1) :
    ∃ p k m : ℕ, p.Prime ∧ k ≠ 0 ∧ n = p ^ k * m ∧ ¬ p ∣ m ∧ 0 < m ∧ m < n := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨k, m, hm_not_dvd, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hnpos.ne' p hp.ne_one
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk, pow_zero, one_mul] at hnm
    exact hm_not_dvd (hnm ▸ hpdvd)
  have hpk_gt1 : 1 < p ^ k := Nat.one_lt_pow hk0 hp.one_lt
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    rw [hm0, mul_zero] at hnm
    exact hnpos.ne' hnm
  have hm_lt_n : m < n := by
    rw [hnm]
    calc m = 1 * m := by rw [one_mul]
      _ < p ^ k * m := Nat.mul_lt_mul_of_pos_right hpk_gt1 hmpos
  exact ⟨p, k, m, hp, hk0, hnm, hm_not_dvd, hmpos, hm_lt_n⟩

private theorem normalize_inf_centralizer {G : Type*} [Group G] {N : Subgroup G} {f₁ f₂ : G}
    (hN₂ : ∀ n ∈ N, f₂ * n * f₂⁻¹ ∈ N) (hcomm : Commute f₂ f₁) :
    ∀ n ∈ N ⊓ Subgroup.centralizer ({f₁} : Set G),
      f₂ * n * f₂⁻¹ ∈ N ⊓ Subgroup.centralizer ({f₁} : Set G) := by
  intro n hn
  simp only [Subgroup.mem_inf] at hn ⊢
  refine ⟨hN₂ n hn.1, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hn ⊢
  have hnf : Commute n f₁ := hn.2
  have hconj := hnf.conj f₂
  rwa [hcomm.mul_inv_cancel] at hconj

private theorem coset_inf_centralizer {G : Type*} [Group G] {N : Subgroup G} {f₁ f₂ g n₀ : G}
    (hN₂ : ∀ n ∈ N, f₂ * n * f₂⁻¹ ∈ N)
    (hg₂ : g⁻¹ * (f₂ * g * f₂⁻¹) ∈ N)
    (hcomm : Commute f₂ f₁) (hn₀N : n₀ ∈ N)
    (hfix₁ : f₁ * (g * n₀) * f₁⁻¹ = g * n₀) :
    (g * n₀)⁻¹ * (f₂ * (g * n₀) * f₂⁻¹) ∈
      N ⊓ Subgroup.centralizer ({f₁} : Set G) := by
  simp only [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · have hn₂ : f₂ * n₀ * f₂⁻¹ ∈ N := hN₂ n₀ hn₀N
    have e : (g * n₀)⁻¹ * (f₂ * (g * n₀) * f₂⁻¹) =
        n₀⁻¹ * (g⁻¹ * (f₂ * g * f₂⁻¹)) * (f₂ * n₀ * f₂⁻¹) := by
      group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.inv_mem hn₀N) hg₂) hn₂
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hx₀comm : Commute (g * n₀) f₁ := by
      rw [Commute]
      calc (g * n₀) * f₁ = (f₁ * (g * n₀) * f₁⁻¹) * f₁ := by rw [hfix₁]
        _ = f₁ * (g * n₀) := by group
    have h1 : Commute (g * n₀)⁻¹ f₁ := hx₀comm.inv_left
    have h2 : Commute ((g * n₀)⁻¹ * f₂) f₁ := h1.mul_left hcomm
    have h3 : Commute ((g * n₀)⁻¹ * f₂ * (g * n₀)) f₁ := h2.mul_left hx₀comm
    have h4 : Commute ((g * n₀)⁻¹ * f₂ * (g * n₀) * f₂⁻¹) f₁ :=
      h3.mul_left hcomm.inv_left
    simpa only [mul_assoc] using h4.eq

private theorem exists_fixed_mem_coset_of_fixed_pow
    {G : Type*} [Group G] {N : Subgroup G} {f f₁ f₂ g n₀ n' : G} {p k m : ℕ}
    (hp : p.Prime) (hm_not_dvd : ¬ p ∣ m)
    (hn₀N : n₀ ∈ N) (hn'N : n' ∈ N)
    (hfix₁ : f₁ * (g * n₀) * f₁⁻¹ = g * n₀)
    (hn'cent : n' ∈ Subgroup.centralizer ({f₁} : Set G))
    (hfix₂ : f₂ * ((g * n₀) * n') * f₂⁻¹ = (g * n₀) * n')
    (hf₁_def : f₁ = f ^ m) (hf₂_def : f₂ = f ^ (p ^ k)) :
    ∃ n ∈ N, f * (g * n) * f⁻¹ = g * n := by
  have hmp : Nat.Coprime m p := ((hp.coprime_iff_not_dvd).mpr hm_not_dvd).symm
  have hm_coprime : Nat.Coprime m (p ^ k) := hmp.pow_right k
  have hf_mem : f ∈ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ := by
    simpa [hf₁_def, hf₂_def] using mem_sup_zpowers_pow f hm_coprime
  have hx : g * (n₀ * n') = (g * n₀) * n' := by group
  have hn'comm : n' * f₁ = f₁ * n' :=
    Subgroup.mem_centralizer_singleton_iff.mp hn'cent
  have hn'fix : f₁ * n' * f₁⁻¹ = n' := by
    calc f₁ * n' * f₁⁻¹ = n' * f₁ * f₁⁻¹ := by rw [← hn'comm]
      _ = n' := by group
  have hfix₁'' : f₁ * ((g * n₀) * n') * f₁⁻¹ = (g * n₀) * n' := by
    calc f₁ * ((g * n₀) * n') * f₁⁻¹ =
        (f₁ * (g * n₀) * f₁⁻¹) * (f₁ * n' * f₁⁻¹) := by group
      _ = (g * n₀) * n' := by rw [hfix₁, hn'fix]
  have hfix' : f * ((g * n₀) * n') * f⁻¹ = (g * n₀) * n' :=
    conj_fixed_of_mem_sup hf_mem hfix₁'' hfix₂
  refine ⟨n₀ * n', N.mul_mem hn₀N hn'N, ?_⟩
  calc f * (g * (n₀ * n')) * f⁻¹ = f * ((g * n₀) * n') * f⁻¹ := by rw [hx]
    _ = (g * n₀) * n' := hfix'
    _ = g * (n₀ * n') := hx.symm

private theorem exists_prime_power_fixed_point
    {G : Type*} [Group G] [Finite G] {N : Subgroup G} {f g : G} {p k m : ℕ}
    (hp : p.Prime) (hk0 : k ≠ 0) (hnm : orderOf f = p ^ k * m)
    (hN : ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hg : g⁻¹ * (f * g * f⁻¹) ∈ N)
    (hcop : Nat.Coprime (orderOf f) (Nat.card N)) :
    ∃ (f₁ f₂ n₀ : G), n₀ ∈ N ∧ f₁ = f ^ m ∧ f₂ = f ^ (p ^ k) ∧
      f₁ * (g * n₀) * f₁⁻¹ = g * n₀ ∧
      (∀ n ∈ N, f₂ * n * f₂⁻¹ ∈ N) ∧
      g⁻¹ * (f₂ * g * f₂⁻¹) ∈ N ∧ Commute f₂ f₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ orderOf f := by
    rw [hnm]
    exact dvd_mul_of_dvd_left (dvd_pow_self p hk0) m
  have hpcop : Nat.Coprime p (Nat.card N) := hcop.coprime_dvd_left hpdvd
  have hNp : ¬ p ∣ Nat.card N := (hp.coprime_iff_not_dvd).mp hpcop
  let f₁ : G := f ^ m
  let f₂ : G := f ^ (p ^ k)
  have hf₁ : f₁ ^ p ^ k = 1 := by
    dsimp [f₁]
    rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  have hN₁ : ∀ n ∈ N, f₁ * n * f₁⁻¹ ∈ N := by
    simpa [f₁] using conj_pow_mem hN m
  have hg₁ : g⁻¹ * (f₁ * g * f₁⁻¹) ∈ N := by
    simpa [f₁] using conj_pow_coset_mem hN hg m
  obtain ⟨n₀, hn₀N, hfix₁⟩ := fixed_in_coset N f₁ g k hf₁ hN₁ hg₁ hNp
  have hN₂ : ∀ n ∈ N, f₂ * n * f₂⁻¹ ∈ N := by
    simpa [f₂] using conj_pow_mem hN (p ^ k)
  have hg₂ : g⁻¹ * (f₂ * g * f₂⁻¹) ∈ N := by
    simpa [f₂] using conj_pow_coset_mem hN hg (p ^ k)
  have hcomm : Commute f₂ f₁ := by
    simpa [f₂, f₁] using Commute.pow_pow_self f (p ^ k) m
  exact ⟨f₁, f₂, n₀, hn₀N, rfl, rfl, hfix₁, hN₂, hg₂, hcomm⟩

private theorem exists_fixed_mem_coset_of_coprime_step
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) {f g : G}
    (hN : ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hg : g⁻¹ * (f * g * f⁻¹) ∈ N)
    (hcop : Nat.Coprime (orderOf f) (Nat.card N))
    (hn1 : orderOf f ≠ 1)
    (ih : ∀ m < orderOf f, ∀ (N : Subgroup G) (f g : G), orderOf f = m →
      (∀ n ∈ N, f * n * f⁻¹ ∈ N) →
      g⁻¹ * (f * g * f⁻¹) ∈ N →
      Nat.Coprime (orderOf f) (Nat.card N) →
      ∃ n ∈ N, f * (g * n) * f⁻¹ = g * n) :
    ∃ n ∈ N, f * (g * n) * f⁻¹ = g * n := by
  have hnpos : 0 < orderOf f := orderOf_pos_iff.mpr (isOfFinOrder_of_finite f)
  obtain ⟨p, k, m, hp, hk0, hnm, hm_not_dvd, hmpos, hm_lt_n⟩ :=
    exists_prime_power_factor hnpos hn1
  obtain ⟨f₁, f₂, n₀, hn₀N, hf₁_def, hf₂_def, hfix₁, hN₂, hg₂, hcomm⟩ :=
    exists_prime_power_fixed_point hp hk0 hnm hN hg hcop
  let N' : Subgroup G := N ⊓ Subgroup.centralizer ({f₁} : Set G)
  have hN' : ∀ n ∈ N', f₂ * n * f₂⁻¹ ∈ N' :=
    normalize_inf_centralizer hN₂ hcomm
  have hg' : (g * n₀)⁻¹ * (f₂ * (g * n₀) * f₂⁻¹) ∈ N' :=
    coset_inf_centralizer hN₂ hg₂ hcomm hn₀N hfix₁
  have hcop' : Nat.Coprime (orderOf f₂) (Nat.card N') := by
    refine Nat.Coprime.of_dvd (by rw [hf₂_def]; exact orderOf_pow_dvd (p ^ k))
      (Subgroup.card_dvd_of_le (show N' ≤ N from inf_le_left)) hcop
  have hf₂_pow_m : f₂ ^ m = 1 := by
    rw [hf₂_def, ← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hdvd₂ : orderOf f₂ ∣ m := orderOf_dvd_of_pow_eq_one hf₂_pow_m
  have hlt : orderOf f₂ < orderOf f :=
    lt_of_le_of_lt (Nat.le_of_dvd hmpos hdvd₂) hm_lt_n
  obtain ⟨n', hn'N', hfix₂⟩ := ih (orderOf f₂) hlt N' f₂ (g * n₀) rfl hN' hg' hcop'
  have hn'inf : n' ∈ N ∧ n' ∈ Subgroup.centralizer ({f₁} : Set G) := by
    simpa only [N', Subgroup.mem_inf] using hn'N'
  exact exists_fixed_mem_coset_of_fixed_pow hp hm_not_dvd hn₀N hn'inf.1 hfix₁
    hn'inf.2 hfix₂ hf₁_def hf₂_def

theorem exists_fixed_mem_coset_of_coprime {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    {f g : G} (hN : ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hg : g⁻¹ * (f * g * f⁻¹) ∈ N)
    (hcop : Nat.Coprime (orderOf f) (Nat.card N)) :
    ∃ n ∈ N, f * (g * n) * f⁻¹ = g * n := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (N : Subgroup G) (f g : G), orderOf f = n →
      (∀ m ∈ N, f * m * f⁻¹ ∈ N) →
      g⁻¹ * (f * g * f⁻¹) ∈ N →
      Nat.Coprime (orderOf f) (Nat.card N) →
      ∃ m ∈ N, f * (g * m) * f⁻¹ = g * m
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih N f g hord hN hg hcop
    by_cases hn1 : n = 1
    · have hf1 : f = 1 := orderOf_eq_one_iff.mp (hord.trans hn1)
      exact ⟨1, N.one_mem, by simp [hf1]⟩
    · refine exists_fixed_mem_coset_of_coprime_step N hN hg hcop ?_ ?_
      · rwa [hord]
      · intro m hm N' f' g' hord' hN' hg' hcop'
        exact ih m (by rwa [hord] at hm) N' f' g' hord' hN' hg' hcop'
  exact Nat.strongRecOn (motive := P) (orderOf f) hP N f g rfl hN hg hcop

private theorem semidirect_invariant_coset {X : Type*} [Group X] (N : Subgroup X)
    (α : MulAut X) {g : X} (hN : ∀ n ∈ N, α n ∈ N) (hg : g⁻¹ * α g ∈ N) :
    let Y := SemidirectProduct X (MulAut X) (MonoidHom.id (MulAut X))
    let N' : Subgroup Y := N.map (SemidirectProduct.inl : X →* Y)
    (∀ n ∈ N', (SemidirectProduct.inr α : Y) * n * (SemidirectProduct.inr α)⁻¹ ∈ N') ∧
      (SemidirectProduct.inl g : Y)⁻¹ *
        ((SemidirectProduct.inr α : Y) * SemidirectProduct.inl g *
          (SemidirectProduct.inr α)⁻¹) ∈ N' := by
  dsimp only
  constructor
  · intro n hn
    rcases Subgroup.mem_map.mp hn with ⟨x, hx, rfl⟩
    have hα : (SemidirectProduct.inr α : SemidirectProduct X (MulAut X)
        (MonoidHom.id (MulAut X))) * SemidirectProduct.inl x *
        (SemidirectProduct.inr α)⁻¹ = SemidirectProduct.inl (α x) := by
      simpa using
        (SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut X)) α x).symm
    rw [hα]
    exact Subgroup.mem_map_of_mem _ (hN x hx)
  · have hα : (SemidirectProduct.inr α : SemidirectProduct X (MulAut X)
        (MonoidHom.id (MulAut X))) * SemidirectProduct.inl g *
        (SemidirectProduct.inr α)⁻¹ = SemidirectProduct.inl (α g) := by
      simpa using
        (SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut X)) α g).symm
    rw [hα]
    have h : (SemidirectProduct.inl g : SemidirectProduct X (MulAut X)
        (MonoidHom.id (MulAut X)))⁻¹ * SemidirectProduct.inl (α g) =
        SemidirectProduct.inl (g⁻¹ * α g) := by simp
    rw [h]
    exact Subgroup.mem_map_of_mem _ hg

theorem exists_fixed_mem_coset_of_coprime_mulAut {X : Type*} [Group X] [Finite X]
    (N : Subgroup X) (α : MulAut X) {g : X} (hN : ∀ n ∈ N, α n ∈ N)
    (hg : g⁻¹ * α g ∈ N) (hcop : Nat.Coprime (orderOf α) (Nat.card N)) :
    ∃ n ∈ N, α (g * n) = g * n := by
  classical
  let Y := SemidirectProduct X (MulAut X) (MonoidHom.id (MulAut X))
  let : Finite Y :=
    Finite.of_injective (fun y : Y => (y.left, y.right)) (by
      intro a b h
      exact SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let N' : Subgroup Y := N.map (SemidirectProduct.inl : X →* Y)
  obtain ⟨hN', hg'⟩ := semidirect_invariant_coset N α hN hg
  have hord : orderOf (SemidirectProduct.inr α : Y) = orderOf α :=
    orderOf_injective (SemidirectProduct.inr : MulAut X →* Y)
      SemidirectProduct.inr_injective α
  have hcard : Nat.card N' = Nat.card N :=
    Subgroup.card_map_of_injective SemidirectProduct.inl_injective
  have hcop' : Nat.Coprime (orderOf (SemidirectProduct.inr α : Y)) (Nat.card N') := by
    rw [hord, hcard]
    exact hcop
  obtain ⟨n, hn, hfix⟩ :=
    exists_fixed_mem_coset_of_coprime N' hN' hg' hcop'
  rcases Subgroup.mem_map.mp hn with ⟨x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  have hfix' : (SemidirectProduct.inr α : Y) * SemidirectProduct.inl (g * x) *
      (SemidirectProduct.inr α)⁻¹ = SemidirectProduct.inl (g * x) := by
    simpa only [map_mul] using hfix
  have h1 : (SemidirectProduct.inl : X →* Y) (α (g * x)) =
      (SemidirectProduct.inl : X →* Y) (g * x) := by
    calc (SemidirectProduct.inl : X →* Y) (α (g * x)) =
        (SemidirectProduct.inr α : Y) * (SemidirectProduct.inl : X →* Y) (g * x) *
          (SemidirectProduct.inr α)⁻¹ := by
          simpa using
            (SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut X)) α (g * x))
      _ = (SemidirectProduct.inl : X →* Y) (g * x) := hfix'
  exact SemidirectProduct.inl_injective h1

end CFSG.GroupTheory
