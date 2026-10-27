module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

variable {A : Type} [Group A] {M : Subgroup A} {Q : Type*} [Group Q] (ρ : ↥M →* Q)

@[expose] def ActsAsPow (B : Subgroup A) (hBM : B ≤ M) (n : ↥M) (e : ℤ) : Prop :=
  ∀ b (hb : b ∈ B), ρ n * ρ ⟨b, hBM hb⟩ * (ρ n)⁻¹ = ρ ⟨b, hBM hb⟩ ^ e

@[expose] def preB (B : Subgroup A) (hBM : B ≤ M) (X' : Subgroup Q) : Subgroup A :=
  ((X'.comap ρ).map M.subtype) ⊓ B

variable {ρ}

theorem mem_preB_iff {B : Subgroup A} {hBM : B ≤ M} {X' : Subgroup Q} {b : A} :
    b ∈ preB ρ B hBM X' ↔ ∃ hb : b ∈ B, ρ ⟨b, hBM hb⟩ ∈ X' := by
  constructor
  · rintro ⟨⟨c, hc, hce⟩, hb⟩
    refine ⟨hb, ?_⟩
    have : c = ⟨b, hBM hb⟩ := Subtype.ext hce
    rw [← this]
    exact hc
  · rintro ⟨hb, hx⟩
    exact ⟨⟨⟨b, hBM hb⟩, hx, rfl⟩, hb⟩

theorem preB_le (B : Subgroup A) (hBM : B ≤ M) (X' : Subgroup Q) : preB ρ B hBM X' ≤ B :=
  inf_le_right

theorem map_conj {n b : A} (hn : n ∈ M) (hb : b ∈ M) :
    ρ ⟨n * b * n⁻¹, M.mul_mem (M.mul_mem hn hb) (M.inv_mem hn)⟩ =
      ρ ⟨n, hn⟩ * ρ ⟨b, hb⟩ * (ρ ⟨n, hn⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem le_normalizer_preB [Finite A] {N B : Subgroup A} (hBM : B ≤ M) (hNM : N ≤ M)
    (hNB : N ≤ Subgroup.normalizer (B : Set A)) {X' : Subgroup Q}
    (h : ∀ n (hn : n ∈ N), ∀ b (hb : b ∈ B), ρ ⟨b, hBM hb⟩ ∈ X' →
      ρ ⟨n, hNM hn⟩ * ρ ⟨b, hBM hb⟩ * (ρ ⟨n, hNM hn⟩)⁻¹ ∈ X') :
    N ≤ Subgroup.normalizer (preB ρ B hBM X' : Set A) := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  obtain ⟨hvB, hvX⟩ := mem_preB_iff.1 hv
  have hnv : n * v * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hNB hn) v).1 hvB
  refine mem_preB_iff.2 ⟨hnv, ?_⟩
  have e : (⟨n * v * n⁻¹, hBM hnv⟩ : ↥M) =
      ⟨n * v * n⁻¹, M.mul_mem (M.mul_mem (hNM hn) (hBM hvB)) (M.inv_mem (hNM hn))⟩ := rfl
  rw [e, map_conj]
  exact h n hn v hvB hvX

theorem eq_one_of_le_frattini [Finite A] {B : Subgroup A}
    (h : B ≤ (frattini ↥B).map B.subtype) {b : A} (hb : b ∈ B) : b = 1 := by
  have htop : frattini ↥B = ⊤ := by
    refine eq_top_iff.2 fun c _ => ?_
    obtain ⟨d, hd, hde⟩ := h c.2
    rwa [show d = c from Subtype.ext hde] at hd
  have hbot : (⊥ : Subgroup ↥B) = ⊤ := frattini_nongenerating (by rw [htop, sup_top_eq])
  have : (⟨b, hb⟩ : ↥B) ∈ (⊥ : Subgroup ↥B) := hbot ▸ Subgroup.mem_top _
  exact congrArg Subtype.val (Subgroup.mem_bot.1 this)

theorem forall_eq_one_of_actsAsPow [Finite A] {N B : Subgroup A} (hBM : B ≤ M) (hNM : N ≤ M)
    (hcyc : ¬ IsCyclic ↥B) (hN : IrredOn N B) (hNB : N ≤ Subgroup.normalizer (B : Set A))
    (hpow : ∀ n (hn : n ∈ N), ∃ e : ℤ, ActsAsPow ρ B hBM ⟨n, hNM hn⟩ e) :
    ∀ b (hb : b ∈ B), ρ ⟨b, hBM hb⟩ = 1 := by
  by_cases hBΦ : B ≤ (frattini ↥B).map B.subtype
  · intro b hb
    have : (⟨b, hBM hb⟩ : ↥M) = 1 := Subtype.ext (eq_one_of_le_frattini hBΦ hb)
    rw [this, map_one]
  obtain ⟨x, hxB, hxΦ⟩ := Set.not_subset.1 hBΦ
  have hDN : N ≤ Subgroup.normalizer (preB ρ B hBM ⊥ : Set A) := by
    refine le_normalizer_preB hBM hNM hNB fun n hn b hb hx => ?_
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, mul_inv_cancel]
  have hVN : N ≤ Subgroup.normalizer
      (preB ρ B hBM (Subgroup.zpowers (ρ ⟨x, hBM hxB⟩)) : Set A) := by
    refine le_normalizer_preB hBM hNM hNB fun n hn b hb hx => ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨e, he⟩ := hpow n hn
    rw [← hk, ← conj_zpow, he x hxB, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  have hVB : preB ρ B hBM (Subgroup.zpowers (ρ ⟨x, hBM hxB⟩)) = B := hN _ (preB_le B hBM _)
    (fun h => hxΦ (h (mem_preB_iff.2 ⟨hxB, Subgroup.mem_zpowers _⟩))) hVN
  have hBle : B ≤ preB ρ B hBM ⊥ ⊔ Subgroup.zpowers x := by
    intro b hb
    have hbV : b ∈ preB ρ B hBM (Subgroup.zpowers (ρ ⟨x, hBM hxB⟩)) := by
      rw [hVB]
      exact hb
    obtain ⟨hb', hbx⟩ := mem_preB_iff.1 hbV
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbx
    have hbk : b * (x ^ k)⁻¹ ∈ preB ρ B hBM ⊥ := by
      refine mem_preB_iff.2 ⟨B.mul_mem hb (B.inv_mem (B.zpow_mem hxB k)), ?_⟩
      rw [Subgroup.mem_bot]
      have e : (⟨b * (x ^ k)⁻¹, hBM (B.mul_mem hb (B.inv_mem (B.zpow_mem hxB k)))⟩ : ↥M) =
          ⟨b, hBM hb⟩ * (⟨x, hBM hxB⟩ ^ k)⁻¹ := rfl
      rw [e, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    have hmem : b * (x ^ k)⁻¹ * x ^ k ∈ preB ρ B hBM ⊥ ⊔ Subgroup.zpowers x :=
      Subgroup.mul_mem _ (le_sup_left (b := Subgroup.zpowers x) hbk)
        (le_sup_right (a := preB ρ B hBM ⊥) (Subgroup.zpow_mem_zpowers x k))
    simpa using hmem
  have hDB : preB ρ B hBM ⊥ = B :=
    eq_of_le_sup_zpowers hcyc hN (preB_le B hBM _) hDN hxB hBle
  intro b hb
  have hbD : b ∈ preB ρ B hBM ⊥ := by
    rw [hDB]
    exact hb
  obtain ⟨hb', h1⟩ := mem_preB_iff.1 hbD
  exact Subgroup.mem_bot.1 h1

theorem forall_eq_one_of_cyclic [Finite A] {N B : Subgroup A} (hBM : B ≤ M) (hNM : N ≤ M)
    (hcyc : ¬ IsCyclic ↥B) (hN : IrredOn N B) (hNB : N ≤ Subgroup.normalizer (B : Set A))
    {x : A} (hxB : x ∈ B)
    (hgen : ∀ b (hb : b ∈ B), ρ ⟨b, hBM hb⟩ ∈ Subgroup.zpowers (ρ ⟨x, hBM hxB⟩)) :
    ∀ b (hb : b ∈ B), ρ ⟨b, hBM hb⟩ = 1 := by
  have hDN : N ≤ Subgroup.normalizer (preB ρ B hBM ⊥ : Set A) := by
    refine le_normalizer_preB hBM hNM hNB fun n hn b hb hx => ?_
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, mul_inv_cancel]
  have hBle : B ≤ preB ρ B hBM ⊥ ⊔ Subgroup.zpowers x := by
    intro b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen b hb)
    have hbk : b * (x ^ k)⁻¹ ∈ preB ρ B hBM ⊥ := by
      refine mem_preB_iff.2 ⟨B.mul_mem hb (B.inv_mem (B.zpow_mem hxB k)), ?_⟩
      rw [Subgroup.mem_bot]
      have e : (⟨b * (x ^ k)⁻¹, hBM (B.mul_mem hb (B.inv_mem (B.zpow_mem hxB k)))⟩ : ↥M) =
          ⟨b, hBM hb⟩ * (⟨x, hBM hxB⟩ ^ k)⁻¹ := rfl
      rw [e, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    have hmem : b * (x ^ k)⁻¹ * x ^ k ∈ preB ρ B hBM ⊥ ⊔ Subgroup.zpowers x :=
      Subgroup.mul_mem _ (le_sup_left (b := Subgroup.zpowers x) hbk)
        (le_sup_right (a := preB ρ B hBM ⊥) (Subgroup.zpow_mem_zpowers x k))
    simpa using hmem
  have hDB : preB ρ B hBM ⊥ = B :=
    eq_of_le_sup_zpowers hcyc hN (preB_le B hBM _) hDN hxB hBle
  intro b hb
  have hbD : b ∈ preB ρ B hBM ⊥ := by
    rw [hDB]
    exact hb
  obtain ⟨hb', h1⟩ := mem_preB_iff.1 hbD
  exact Subgroup.mem_bot.1 h1

theorem eq_one_of_pow_two_pow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : G} {j k : ℕ} (hj : y ^ p ^ j = 1) (hk : y ^ 2 ^ k = 1) : y = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one hj
  have h2 := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (p ^ j) (2 ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem actsAsPow_of_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup A} (hBM : B ≤ M)
    (hBp : IsPGroup p ↥B) {n : ↥M} (hnB : ∀ b ∈ B, (n : A) * b * (n : A)⁻¹ ∈ B) (e : ℤ)
    (h : ∀ b (hb : b ∈ B), ∃ k : ℕ,
      (ρ n * ρ ⟨b, hBM hb⟩ * (ρ n)⁻¹ * (ρ ⟨b, hBM hb⟩ ^ e)⁻¹) ^ 2 ^ k = 1) :
    ActsAsPow ρ B hBM n e := by
  intro b hb
  obtain ⟨k, hk⟩ := h b hb
  have hy : (n : A) * b * (n : A)⁻¹ * (b ^ e)⁻¹ ∈ B :=
    B.mul_mem (hnB b hb) (B.inv_mem (B.zpow_mem hb e))
  obtain ⟨j, hj⟩ := hBp ⟨_, hy⟩
  have hρy : ρ ⟨_, hBM hy⟩ = ρ n * ρ ⟨b, hBM hb⟩ * (ρ n)⁻¹ * (ρ ⟨b, hBM hb⟩ ^ e)⁻¹ := by
    have e' : (⟨(n : A) * b * (n : A)⁻¹ * (b ^ e)⁻¹, hBM hy⟩ : ↥M) =
        n * ⟨b, hBM hb⟩ * n⁻¹ * (⟨b, hBM hb⟩ ^ e)⁻¹ := rfl
    rw [e', map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow]
  have hj' : (ρ n * ρ ⟨b, hBM hb⟩ * (ρ n)⁻¹ * (ρ ⟨b, hBM hb⟩ ^ e)⁻¹) ^ p ^ j = 1 := by
    rw [← hρy, ← map_pow]
    have : (⟨_, hBM hy⟩ : ↥M) ^ p ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
    rw [this, map_one]
  have h1 := eq_one_of_pow_two_pow hp hp2 hj' hk
  exact mul_inv_eq_one.1 h1

@[expose] def eigen (X : Subgroup Q) (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (g : Q) (t : ℤ) :
    Subgroup Q where
  carrier := {x | x ∈ X ∧ g * x * g⁻¹ = x ^ t}
  one_mem' := ⟨X.one_mem, by simp⟩
  mul_mem' := fun {x y} hx hy => ⟨X.mul_mem hx.1 hy.1, by
    have hc : Commute x y := hX x hx.1 y hy.1
    calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      _ = x ^ t * y ^ t := by rw [hx.2, hy.2]
      _ = (x * y) ^ t := (hc.mul_zpow t).symm⟩
  inv_mem' := fun {x} hx => ⟨X.inv_mem hx.1, by
    calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      _ = (x ^ t)⁻¹ := by rw [hx.2]
      _ = x⁻¹ ^ t := (inv_zpow x t).symm⟩

theorem mem_zpowers_zpow_of_isCoprime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {x : G}
    {j : ℕ} (hx : x ^ p ^ j = 1) {k : ℤ} (hk : IsCoprime k (p : ℤ)) :
    x ∈ Subgroup.zpowers (x ^ k) := by
  rw [mem_zpowers_zpow_iff]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hx)
  rw [hi]
  have : IsCoprime k ((p : ℤ) ^ i) := hk.pow_right
  rw [← Int.isCoprime_iff_gcd_eq_one]
  exact_mod_cast this

theorem forall_eq_one_of_index_two [Finite A] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {N N₀ B : Subgroup A} (hBM : B ≤ M) (hNM : N ≤ M) (hBp : IsPGroup p ↥B)
    (hcyc : ¬ IsCyclic ↥B) (hN : IrredOn N B) (hNB : N ≤ Subgroup.normalizer (B : Set A))
    (hab : ∀ b₁ (h₁ : b₁ ∈ B) b₂ (h₂ : b₂ ∈ B),
      ρ ⟨b₁, hBM h₁⟩ * ρ ⟨b₂, hBM h₂⟩ = ρ ⟨b₂, hBM h₂⟩ * ρ ⟨b₁, hBM h₁⟩)
    (hN₀ : N₀ ≤ N) (hidx : ∀ m ∈ N, ∀ n ∈ N, m ∉ N₀ → n ∉ N₀ → m⁻¹ * n ∈ N₀)
    (hpow : ∀ n (hn : n ∈ N₀), ∃ e : ℤ, ActsAsPow ρ B hBM ⟨n, hNM (hN₀ hn)⟩ e)
    (hsq : ∀ n (hn : n ∈ N), n ∉ N₀ → ∃ s : ℤ, IsCoprime s (p : ℤ) ∧
      ActsAsPow ρ B hBM ⟨n * n, hNM (N.mul_mem hn hn)⟩ (s * s)) :
    ∀ b (hb : b ∈ B), ρ ⟨b, hBM hb⟩ = 1 := by
  by_cases hall : ∀ n ∈ N, n ∈ N₀
  · exact forall_eq_one_of_actsAsPow hBM hNM hcyc hN hNB fun n hn => hpow n (hall n hn)
  push Not at hall
  obtain ⟨γ, hγN, hγ0⟩ := hall
  obtain ⟨s, hs, hγs⟩ := hsq γ hγN hγ0
  obtain ⟨g, hg⟩ : ∃ g, g = ρ ⟨γ, hNM hγN⟩ := ⟨_, rfl⟩
  set X : Subgroup Q := (ρ.comp (Subgroup.inclusion hBM)).range with hXdef
  have hmemX : ∀ b (hb : b ∈ B), ρ ⟨b, hBM hb⟩ ∈ X := fun b hb => ⟨⟨b, hb⟩, rfl⟩
  have hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    rintro _ ⟨⟨b₁, h₁⟩, rfl⟩ _ ⟨⟨b₂, h₂⟩, rfl⟩
    exact hab b₁ h₁ b₂ h₂
  have hconjB : ∀ n ∈ N, ∀ b ∈ B, n * b * n⁻¹ ∈ B := fun n hn b hb =>
    (Subgroup.mem_normalizer_iff.1 (hNB hn) b).1 hb
  have hgg : ∀ x ∈ X, g * g * x * (g * g)⁻¹ = x ^ (s * s) := by
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    have h := hγs b hb
    have e : (⟨γ * γ, hNM (N.mul_mem hγN hγN)⟩ : ↥M) = ⟨γ, hNM hγN⟩ * ⟨γ, hNM hγN⟩ := rfl
    rw [e, map_mul, ← hg] at h
    exact h
  have hfac : ∀ n (hn : n ∈ N), n ∉ N₀ → ∃ m, ∃ hm : m ∈ N₀,
      ρ ⟨n, hNM hn⟩ = g * ρ ⟨m, hNM (hN₀ hm)⟩ := by
    intro n hn hn0
    refine ⟨γ⁻¹ * n, hidx γ hγN n hn hγ0 hn0, ?_⟩
    rw [hg, ← map_mul]
    congr 1
    ext
    simp
  have hpowX : ∀ n (hn : n ∈ N₀), ∃ e : ℤ, ∀ x ∈ X,
      ρ ⟨n, hNM (hN₀ hn)⟩ * x * (ρ ⟨n, hNM (hN₀ hn)⟩)⁻¹ = x ^ e := by
    intro n hn
    obtain ⟨e, he⟩ := hpow n hn
    exact ⟨e, by rintro _ ⟨⟨b, hb⟩, rfl⟩; exact he b hb⟩
  have hEN : ∀ t : ℤ, ∀ n (hn : n ∈ N), ∀ x ∈ eigen X hX g t,
      ρ ⟨n, hNM hn⟩ * x * (ρ ⟨n, hNM hn⟩)⁻¹ ∈ eigen X hX g t := by
    intro t n hn x hx
    by_cases hn0 : n ∈ N₀
    · obtain ⟨e, he⟩ := hpowX n hn0
      rw [he x hx.1]
      exact Subgroup.zpow_mem _ hx _
    · obtain ⟨m, hm, hρm⟩ := hfac n hn hn0
      obtain ⟨e, he⟩ := hpowX m hm
      rw [hρm, mul_inv_rev,
        show g * ρ ⟨m, hNM (hN₀ hm)⟩ * x * ((ρ ⟨m, hNM (hN₀ hm)⟩)⁻¹ * g⁻¹) =
          g * (ρ ⟨m, hNM (hN₀ hm)⟩ * x * (ρ ⟨m, hNM (hN₀ hm)⟩)⁻¹) * g⁻¹ by group,
        he x hx.1, ← conj_zpow, hx.2, ← zpow_mul]
      exact Subgroup.zpow_mem _ hx _
  have hVN : ∀ t : ℤ, N ≤ Subgroup.normalizer (preB ρ B hBM (eigen X hX g t) : Set A) :=
    fun t => le_normalizer_preB hBM hNM hNB fun n hn b hb hx => hEN t n hn _ hx
  have hall_of : ∀ t : ℤ, preB ρ B hBM (eigen X hX g t) = B →
      ∀ b (hb : b ∈ B), ρ ⟨b, hBM hb⟩ = 1 := by
    intro t ht
    have hgt : ∀ x ∈ X, g * x * g⁻¹ = x ^ t := by
      rintro _ ⟨⟨b, hb⟩, rfl⟩
      have hb' : b ∈ preB ρ B hBM (eigen X hX g t) := by
        rw [ht]
        exact hb
      obtain ⟨hb'', h⟩ := mem_preB_iff.1 hb'
      exact h.2
    refine forall_eq_one_of_actsAsPow hBM hNM hcyc hN hNB fun n hn => ?_
    by_cases hn0 : n ∈ N₀
    · exact hpow n hn0
    · obtain ⟨m, hm, hρm⟩ := hfac n hn hn0
      obtain ⟨e, he⟩ := hpowX m hm
      refine ⟨e * t, fun b hb => ?_⟩
      rw [hρm, mul_inv_rev,
        show g * ρ ⟨m, hNM (hN₀ hm)⟩ * ρ ⟨b, hBM hb⟩ * ((ρ ⟨m, hNM (hN₀ hm)⟩)⁻¹ * g⁻¹) =
          g * (ρ ⟨m, hNM (hN₀ hm)⟩ * ρ ⟨b, hBM hb⟩ * (ρ ⟨m, hNM (hN₀ hm)⟩)⁻¹) * g⁻¹ by group,
        he _ (hmemX b hb), hgt _ (X.zpow_mem (hmemX b hb) e), ← zpow_mul]
  by_cases hPlus : preB ρ B hBM (eigen X hX g s) ≤ (frattini ↥B).map B.subtype
  · by_cases hMinus : preB ρ B hBM (eigen X hX g (-s)) ≤ (frattini ↥B).map B.subtype
    ·
      have hBle : B ≤ (frattini ↥B).map B.subtype := by
        intro b hb
        have hγb : γ * b * γ⁻¹ ∈ B := hconjB γ hγN b hb
        have hργb : ρ ⟨γ * b * γ⁻¹, hBM hγb⟩ = g * ρ ⟨b, hBM hb⟩ * g⁻¹ := by
          rw [hg]
          exact map_conj (hNM hγN) (hBM hb)
        set x := ρ ⟨b, hBM hb⟩ with hx
        have hxX : x ∈ X := hmemX b hb
        have hgxX : g * x * g⁻¹ ∈ X := hργb ▸ hmemX _ hγb
        have hgg' : g * (g * x * g⁻¹) * g⁻¹ = x ^ (s * s) := by
          rw [← hgg x hxX]
          group
        have hyB : b ^ s * (γ * b * γ⁻¹) ∈ B := B.mul_mem (B.zpow_mem hb s) hγb
        have hzB : b ^ s * (γ * b * γ⁻¹)⁻¹ ∈ B := B.mul_mem (B.zpow_mem hb s) (B.inv_mem hγb)
        have hρy : ρ ⟨_, hBM hyB⟩ = x ^ s * (g * x * g⁻¹) := by
          have e : (⟨b ^ s * (γ * b * γ⁻¹), hBM hyB⟩ : ↥M) =
              ⟨b, hBM hb⟩ ^ s * ⟨γ * b * γ⁻¹, hBM hγb⟩ := rfl
          rw [e, map_mul, map_zpow, hργb]
        have hρz : ρ ⟨_, hBM hzB⟩ = x ^ s * (g * x * g⁻¹)⁻¹ := by
          have e : (⟨b ^ s * (γ * b * γ⁻¹)⁻¹, hBM hzB⟩ : ↥M) =
              ⟨b, hBM hb⟩ ^ s * (⟨γ * b * γ⁻¹, hBM hγb⟩)⁻¹ := rfl
          rw [e, map_mul, map_zpow, map_inv, hργb]
        have hc : Commute (x ^ s) (g * x * g⁻¹) := hX _ (X.zpow_mem hxX s) _ hgxX
        have hyE : b ^ s * (γ * b * γ⁻¹) ∈ preB ρ B hBM (eigen X hX g s) := by
          refine mem_preB_iff.2 ⟨hyB, ?_⟩
          rw [hρy]
          refine ⟨X.mul_mem (X.zpow_mem hxX s) hgxX, ?_⟩
          rw [show g * (x ^ s * (g * x * g⁻¹)) * g⁻¹ =
              (g * x * g⁻¹) ^ s * (g * (g * x * g⁻¹) * g⁻¹) by
            rw [conj_zpow]; group, hgg', hc.mul_zpow, ← zpow_mul]
          exact hX _ (X.zpow_mem hgxX s) _ (X.zpow_mem hxX (s * s))
        have hzE : b ^ s * (γ * b * γ⁻¹)⁻¹ ∈ preB ρ B hBM (eigen X hX g (-s)) := by
          refine mem_preB_iff.2 ⟨hzB, ?_⟩
          rw [hρz]
          refine ⟨X.mul_mem (X.zpow_mem hxX s) (X.inv_mem hgxX), ?_⟩
          have hc' : Commute (x ^ s) (g * x * g⁻¹)⁻¹ := hc.inv_right
          rw [show g * (x ^ s * (g * x * g⁻¹)⁻¹) * g⁻¹ =
              (g * x * g⁻¹) ^ s * (g * (g * x * g⁻¹) * g⁻¹)⁻¹ by
            rw [conj_zpow]; group, hgg', hc'.mul_zpow, ← zpow_mul, inv_zpow', neg_neg, mul_neg,
            zpow_neg]
          exact hX _ (X.zpow_mem hgxX s) _ (X.inv_mem (X.zpow_mem hxX (s * s)))
        have hcB : (b ^ s * (γ * b * γ⁻¹) * (b ^ s * (γ * b * γ⁻¹)⁻¹))⁻¹ * b ^ (2 * s) ∈
            preB ρ B hBM (eigen X hX g s) := by
          have hmem : (b ^ s * (γ * b * γ⁻¹) * (b ^ s * (γ * b * γ⁻¹)⁻¹))⁻¹ * b ^ (2 * s) ∈ B :=
            B.mul_mem (B.inv_mem (B.mul_mem hyB hzB)) (B.zpow_mem hb _)
          refine mem_preB_iff.2 ⟨hmem, ?_⟩
          have e : (⟨_, hBM hmem⟩ : ↥M) = (⟨_, hBM hyB⟩ * ⟨_, hBM hzB⟩)⁻¹ * ⟨b, hBM hb⟩ ^ (2 * s) :=
            rfl
          rw [e, map_mul, map_inv, map_mul, hρy, hρz, map_zpow]
          have h1 : x ^ s * (g * x * g⁻¹) * (x ^ s * (g * x * g⁻¹)⁻¹) = x ^ (2 * s) := by
            rw [show x ^ s * (g * x * g⁻¹) * (x ^ s * (g * x * g⁻¹)⁻¹) =
                x ^ s * ((g * x * g⁻¹) * x ^ s) * (g * x * g⁻¹)⁻¹ by group, ← hc.eq]
            rw [show x ^ s * (x ^ s * (g * x * g⁻¹)) * (g * x * g⁻¹)⁻¹ = x ^ s * x ^ s by group,
              ← zpow_add, two_mul]
          rw [← hx, h1, inv_mul_cancel]
          exact Subgroup.one_mem _
        have h2s : b ^ (2 * s) ∈ preB ρ B hBM (eigen X hX g s) ⊔
            preB ρ B hBM (eigen X hX g (-s)) := by
          have e : b ^ (2 * s) = b ^ s * (γ * b * γ⁻¹) * (b ^ s * (γ * b * γ⁻¹)⁻¹) *
              ((b ^ s * (γ * b * γ⁻¹) * (b ^ s * (γ * b * γ⁻¹)⁻¹))⁻¹ * b ^ (2 * s)) := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (le_sup_left (b := preB ρ B hBM
            (eigen X hX g (-s))) hyE) (le_sup_right (a := preB ρ B hBM (eigen X hX g s)) hzE))
            (le_sup_left (b := preB ρ B hBM (eigen X hX g (-s))) hcB)
        obtain ⟨j, hj⟩ := hBp ⟨b, hb⟩
        have hbj : b ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
        have h2 : IsCoprime (2 * s) (p : ℤ) := by
          refine IsCoprime.mul_left ?_ hs
          rw [Int.isCoprime_iff_gcd_eq_one]
          have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
          exact_mod_cast this
        have hbz := mem_zpowers_zpow_of_isCoprime hp hbj h2
        have hle : Subgroup.zpowers (b ^ (2 * s)) ≤ preB ρ B hBM (eigen X hX g s) ⊔
            preB ρ B hBM (eigen X hX g (-s)) := (Subgroup.zpowers_le).2 h2s
        exact sup_le hPlus hMinus (hle hbz)
      intro b hb
      have : (⟨b, hBM hb⟩ : ↥M) = 1 := Subtype.ext (eq_one_of_le_frattini hBle hb)
      rw [this, map_one]
    · exact hall_of (-s) (hN _ (preB_le B hBM _) hMinus (hVN (-s)))
  · exact hall_of s (hN _ (preB_le B hBM _) hPlus (hVN s))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
