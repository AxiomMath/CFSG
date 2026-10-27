module

public import CFSG.GH74.Uniqueness.SU.KI1r4QAbs
public import CFSG.GroupTheory.KleinFourAutomorphism
public import Mathlib.Data.Int.Star
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.Q64

open Subgroup

theorem eq_two_pow_mul_three_pow (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3) :
    n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 := by
  have h32 : (Nat.factorization 3) 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have h23 : (Nat.factorization 2) 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  apply Nat.eq_of_factorization_eq hn (by positivity)
  intro p
  by_cases hp : p.Prime
  · by_cases h2 : p = 2
    · subst h2
      simp [Nat.factorization_mul, Nat.factorization_pow, Nat.prime_two.factorization, h32]
    · by_cases h3 : p = 3
      · subst h3
        simp [Nat.factorization_mul, Nat.factorization_pow, Nat.prime_three.factorization, h23]
      · have hnd : ¬ p ∣ n := fun hd => by
          rcases h p hp hd with rfl | rfl
          · exact h2 rfl
          · exact h3 rfl
        have h0 : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
        rw [h0]
        have h2' : (Nat.factorization 2) p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd
            (fun hd => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
        have h3' : (Nat.factorization 3) p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd
            (fun hd => h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
        simp [Nat.factorization_mul, Nat.factorization_pow, h2', h3']
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem card_eq_of_odd_bound {G : Type*} [Group G] [Finite G]
    (hodd : ∀ P : Subgroup G, ¬ 2 ∣ Nat.card P → Nat.card P ∣ 9)
    (T : Sylow 2 G) (P : Sylow 3 G) : Nat.card G = Nat.card T * Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3 := by
    intro p hp hdvd
    by_cases h2 : p = 2
    · exact Or.inl h2
    · right
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p hdvd
      have hcard : Nat.card (zpowers g) = p := by rw [Nat.card_zpowers, hg]
      have hnd : ¬ 2 ∣ Nat.card (zpowers g) := by
        rw [hcard]
        intro h
        exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
      have h9 := hodd _ hnd
      rw [hcard] at h9
      have : p ∣ 3 ^ 2 := by simpa using h9
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow this)
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h := eq_two_pow_mul_three_pow _ hn hprime
  rw [Sylow.card_eq_multiplicity T, Sylow.card_eq_multiplicity P]
  exact h

theorem exists_sylow_data {G : Type*} [Group G] [Finite G] (R : Subgroup G) [R.Normal]
    (hR2 : IsPGroup 2 R) (T : Sylow 2 G) (hT : Nat.card T = 2 * Nat.card R) (x y : G)
    (hx2 : x * x = 1) (hxR : x ∉ R) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hxy : x * y * x⁻¹ = y⁻¹)
    (hfree : ∀ r ∈ R, y * r * y⁻¹ = r → r = 1)
    (hodd : ∀ P : Subgroup G, ¬ 2 ∣ Nat.card P → Nat.card P ∣ 9) :
    ∃ (P₃ : Subgroup G) (x' : G), IsPGroup 3 P₃ ∧ y ∈ P₃ ∧
      (Nat.card P₃ = 3 ∨ Nat.card P₃ = 9) ∧ Nat.card G = 2 * Nat.card R * Nat.card P₃ ∧
      R ⊓ P₃ = ⊥ ∧ x' * x' = 1 ∧ x' ∉ R ∧ x' ∉ R ⊔ P₃ ∧
      (∀ p, p ∈ P₃ ↔ x' * p * x'⁻¹ ∈ P₃) ∧ x' * y * x'⁻¹ = y⁻¹ ∧
      ∃ r ∈ R, x' = r⁻¹ * x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord3 : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hy : IsPGroup 3 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord3, pow_one])
  obtain ⟨P, hP⟩ := hy.exists_le_sylow
  have hyP : y ∈ (P : Subgroup G) := hP (mem_zpowers y)
  have hP3 : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).mp hP3
  have hnd2 : ¬ 2 ∣ Nat.card (P : Subgroup G) := by
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have h9 : Nat.card (P : Subgroup G) ∣ 9 := hodd _ hnd2
  have h3dvd : 3 ∣ Nat.card (P : Subgroup G) := by
    have := orderOf_dvd_natCard (⟨y, hyP⟩ : (P : Subgroup G))
    rwa [← Subgroup.orderOf_coe, hord3] at this
  have hPcard : Nat.card (P : Subgroup G) = 3 ∨ Nat.card (P : Subgroup G) = 9 := by
    have hle : Nat.card (P : Subgroup G) ≤ 9 := Nat.le_of_dvd (by norm_num) h9
    rw [hk] at h3dvd hle ⊢
    have hk1 : 1 ≤ k := by
      by_contra h
      have : k = 0 := by omega
      rw [this] at h3dvd
      omega
    have hk2 : k ≤ 2 := by
      by_contra h
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> simp
  have hGcard : Nat.card G = 2 * Nat.card R * Nat.card (P : Subgroup G) := by
    rw [card_eq_of_odd_bound hodd T P, hT]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hR2
  have hcop : Nat.Coprime (Nat.card R) (Nat.card (P : Subgroup G)) := by
    rw [ha, hk]; exact Nat.Coprime.pow _ _ (by norm_num)
  have hinf : R ⊓ (P : Subgroup G) = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  set K : Subgroup G := R ⊔ (P : Subgroup G) with hK
  have hKcard : Nat.card K = Nat.card R * Nat.card (P : Subgroup G) := by
    apply le_antisymm
    · have hnorm : (P : Subgroup G) ≤ normalizer (R : Set G) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top
      have := card_sup_le_of_le_normalizer (P : Subgroup G) R hnorm
      rw [sup_comm] at this
      linarith
    · have h1 : Nat.card R ∣ Nat.card K := Subgroup.card_dvd_of_le le_sup_left
      have h2 : Nat.card (P : Subgroup G) ∣ Nat.card K := Subgroup.card_dvd_of_le le_sup_right
      exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd h1 h2)
  have hKindex : K.index = 2 := by
    have h := K.card_mul_index
    rw [hKcard] at h
    have h2 : Nat.card G = Nat.card R * Nat.card (P : Subgroup G) * 2 := by rw [hGcard]; ring
    have hpos : 0 < Nat.card R * Nat.card (P : Subgroup G) := Nat.mul_pos Nat.card_pos Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h.trans h2)
  have hKn : K.Normal := Subgroup.normal_of_index_eq_two hKindex
  obtain ⟨r, hr, hxP⟩ := exists_normalizing_conj R P hR2 hP3 x (fun k => by
    constructor
    · intro hk
      exact hKn.conj_mem k hk x
    · intro hk
      have := hKn.conj_mem _ hk x⁻¹
      simpa [mul_assoc] using this)
  set x' : G := r⁻¹ * x with hx'
  have hxP' : ∀ p ∈ (P : Subgroup G), x' * p * x'⁻¹ ∈ (P : Subgroup G) := hxP
  have hRn : ∀ g : G, ∀ s ∈ R, g * s * g⁻¹ ∈ R := fun g s hs => ‹R.Normal›.conj_mem s hs g
  have hqR : x' * x' ∈ R := by
    have h1 : x' * x' = r⁻¹ * (x * r⁻¹ * x⁻¹) * (x * x) := by rw [hx']; group
    rw [h1, hx2, mul_one]
    exact R.mul_mem (R.inv_mem hr) (hRn x _ (R.inv_mem hr))
  have hqc : ∀ p ∈ (P : Subgroup G), (x' * x') * p * (x' * x')⁻¹ = p := by
    intro p hp
    have h1 : (x' * x') * p * (x' * x')⁻¹ ∈ (P : Subgroup G) := by
      have := hxP' _ (hxP' p hp)
      have e : x' * (x' * p * x'⁻¹) * x'⁻¹ = (x' * x') * p * (x' * x')⁻¹ := by group
      rwa [e] at this
    have h2 : (x' * x') * p * (x' * x')⁻¹ * p⁻¹ ∈ R := by
      have e : (x' * x') * p * (x' * x')⁻¹ * p⁻¹ = (x' * x') * (p * (x' * x')⁻¹ * p⁻¹) := by group
      rw [e]
      exact R.mul_mem hqR (hRn p _ (R.inv_mem hqR))
    have h3 : (x' * x') * p * (x' * x')⁻¹ * p⁻¹ ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem h1 ((P : Subgroup G).inv_mem hp)
    have h4 : (x' * x') * p * (x' * x')⁻¹ * p⁻¹ ∈ R ⊓ (P : Subgroup G) := ⟨h2, h3⟩
    rw [hinf, Subgroup.mem_bot] at h4
    exact (mul_inv_eq_one.mp h4)
  have hx'2 : x' * x' = 1 := by
    apply hfree _ hqR
    have h5 : (x' * x') * y = y * (x' * x') := by
      have := congrArg (· * (x' * x')) (hqc y hyP)
      simpa [mul_assoc] using this
    calc y * (x' * x') * y⁻¹ = (x' * x') * y * y⁻¹ := by rw [← h5]
      _ = x' * x' := by group
  have hx'R : x' ∉ R := by
    intro h
    apply hxR
    have : x = r * x' := by rw [hx']; group
    rw [this]
    exact R.mul_mem hr h
  have hx'y : x' * y * x'⁻¹ = y⁻¹ := by
    have hw : x' * y * x'⁻¹ ∈ (P : Subgroup G) := hxP' y hyP
    have e : x' * y * x'⁻¹ = r⁻¹ * y⁻¹ * r := by
      have : x' * y * x'⁻¹ = r⁻¹ * (x * y * x⁻¹) * r := by rw [hx']; group
      rw [this, hxy]
    have h1 : x' * y * x'⁻¹ * y ∈ R := by
      have : x' * y * x'⁻¹ * y = r⁻¹ * (y⁻¹ * r * y) := by rw [e]; group
      rw [this]
      have hyr : y⁻¹ * r * y ∈ R := by simpa using hRn y⁻¹ r hr
      exact R.mul_mem (R.inv_mem hr) hyr
    have h2 : x' * y * x'⁻¹ * y ∈ (P : Subgroup G) := (P : Subgroup G).mul_mem hw hyP
    have h3 : x' * y * x'⁻¹ * y ∈ R ⊓ (P : Subgroup G) := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact mul_eq_one_iff_eq_inv.mp h3
  have hx'K : x' ∉ K := by
    intro hmem
    obtain ⟨ρ, hρ, p, hp, hρp⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hpp : p * p ∈ R := by
      have h1 : (ρ * p) * (ρ * p) = 1 := by rw [hρp]; exact hx'2
      have h2 : ρ * (p * ρ * p⁻¹) * (p * p) = 1 := by
        calc ρ * (p * ρ * p⁻¹) * (p * p) = (ρ * p) * (ρ * p) := by group
          _ = 1 := h1
      have h3 : p * p = (ρ * (p * ρ * p⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h2
      rw [h3]
      exact R.inv_mem (R.mul_mem hρ (hRn p ρ hρ))
    have hppP : p * p ∈ (P : Subgroup G) := (P : Subgroup G).mul_mem hp hp
    have h4 : p * p ∈ R ⊓ (P : Subgroup G) := ⟨hpp, hppP⟩
    rw [hinf, Subgroup.mem_bot] at h4
    obtain ⟨k, hk⟩ := hP3 ⟨p, hp⟩
    have hk' : p ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have hp2 : p ^ 2 = 1 := by rw [pow_two]; exact h4
    have hcop2 : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have h5 : p ^ Nat.gcd 2 (3 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hp2, hk'⟩
    rw [hcop2, pow_one] at h5
    apply hx'R
    rw [← hρp, h5, mul_one]
    exact hρ
  refine ⟨P, x', hP3, hyP, hPcard, hGcard, hinf, hx'2, hx'R, hx'K, ?_, hx'y, r, hr, rfl⟩
  intro p
  constructor
  · exact hxP' p
  · intro h
    have := hxP' _ h
    have e : x' * (x' * p * x'⁻¹) * x'⁻¹ = (x' * x') * p * (x' * x')⁻¹ := by group
    rwa [e, hx'2, one_mul, inv_one, mul_one] at this

theorem mem_sup_zpowers_or {G : Type*} [Group G] (P : Subgroup G) (x : G) (hx2 : x * x = 1)
    (hxP : ∀ p, p ∈ P ↔ x * p * x⁻¹ ∈ P) {c : G} (hc : c ∈ zpowers x ⊔ P) :
    c ∈ P ∨ ∃ p ∈ P, c = x * p := by
  have hn : zpowers x ≤ normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    exact hxP
  have hco := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers x) P hn
  have hc' : c ∈ (↑(zpowers x ⊔ P) : Set G) := hc
  rw [hco] at hc'
  obtain ⟨s, hs, p, hp, rfl⟩ := hc'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hsq : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx2]
  have hk : x ^ k = 1 ∨ x ^ k = x := by
    have e : x ^ k = (x ^ (2 : ℤ)) ^ (k / 2) * x ^ (k % 2) := by
      have h' : 2 * (k / 2) + k % 2 = k := by omega
      rw [← zpow_mul, ← zpow_add, h']
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [e, hsq, one_zpow, one_mul, h, zpow_zero]
    · right; rw [e, hsq, one_zpow, one_mul, h, zpow_one]
  rcases hk with h | h
  · left; show x ^ k * p ∈ P; rw [h, one_mul]; exact hp
  · right; exact ⟨p, hp, by rw [h]⟩

theorem mem_of_cube_eq_one {G : Type*} [Group G] (P : Subgroup G) (x : G) (hx2 : x * x = 1)
    (hxP : ∀ p, p ∈ P ↔ x * p * x⁻¹ ∈ P) (hxn : x ∉ P) {c : G} (hc : c ∈ zpowers x ⊔ P)
    (hc3 : c ^ 3 = 1) : c ∈ P := by
  rcases mem_sup_zpowers_or P x hx2 hxP hc with h | ⟨p, hp, rfl⟩
  · exact h
  · exfalso
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have h2 : (x * p) * (x * p) ∈ P := by
      have : (x * p) * (x * p) = (x * p * x⁻¹) * p := by rw [hxi]; group
      rw [this]; exact P.mul_mem ((hxP p).mp hp) hp
    have h3 : x * p = ((x * p) * (x * p))⁻¹ := by
      have : ((x * p) * (x * p)) * (x * p) = 1 := by
        have := hc3
        rwa [pow_succ, pow_two] at this
      exact eq_inv_of_mul_eq_one_right this
    have h4 : x * p ∈ P := by rw [h3]; exact P.inv_mem h2
    apply hxn
    have : x = (x * p) * p⁻¹ := by group
    rw [this]
    exact P.mul_mem h4 (P.inv_mem hp)

theorem card_mul_le_card_sup {G : Type*} [Group G] [Finite G] (S T : Subgroup G)
    (h : S ⊓ T = ⊥) : Nat.card S * Nat.card T ≤ Nat.card ↥(S ⊔ T) := by
  let f : ↥S × ↥T → ↥(S ⊔ T) := fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem _
    (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ hst
    have h1 : (s : G) * t = s' * t' := congrArg Subtype.val hst
    have h2 : (s' : G)⁻¹ * s = t' * (t : G)⁻¹ := by
      calc (s' : G)⁻¹ * s = (s' : G)⁻¹ * (s * t) * (t : G)⁻¹ := by group
        _ = (s' : G)⁻¹ * (s' * t') * (t : G)⁻¹ := by rw [h1]
        _ = t' * (t : G)⁻¹ := by group
    have h3 : (s' : G)⁻¹ * s ∈ S ⊓ T := ⟨S.mul_mem (S.inv_mem s'.2) s.2, by
      rw [h2]; exact T.mul_mem t'.2 (T.inv_mem t.2)⟩
    rw [h, Subgroup.mem_bot] at h3
    have hs : (s : G) = s' := by
      have := congrArg (fun g => (s' : G) * g) h3
      simpa using this
    have ht : (t : G) = t' := by
      have h4 : (s : G) * t = s * t' := by rw [h1, hs]
      exact mul_left_cancel h4
    exact Prod.ext (Subtype.ext hs) (Subtype.ext ht)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem card_sup_zpowers {G : Type*} [Group G] [Finite G] (P : Subgroup G) (x : G)
    (hx2 : x * x = 1) (hxP : ∀ p, p ∈ P ↔ x * p * x⁻¹ ∈ P) (hxn : x ∉ P) :
    Nat.card ↥(zpowers x ⊔ P) = 2 * Nat.card P := by
  have hn : zpowers x ≤ normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    exact hxP
  have h1 := card_sup_le_of_le_normalizer (zpowers x) P hn
  have h2 : Nat.card (zpowers x) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2))
  apply le_antisymm
  · calc Nat.card ↥(zpowers x ⊔ P) ≤ Nat.card (zpowers x) * Nat.card P := h1
      _ ≤ 2 * Nat.card P := Nat.mul_le_mul h2 le_rfl
  · obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_right : P ≤ zpowers x ⊔ P)
    have hk1 : k ≠ 1 := by
      rintro rfl
      have hle : zpowers x ⊔ P = P :=
        (Subgroup.eq_of_le_of_card_ge (le_sup_right : P ≤ zpowers x ⊔ P)
          (by rw [hk, mul_one])).symm
      exact hxn (hle ▸ mem_sup_left (mem_zpowers x))
    have hk0 : k ≠ 0 := by
      rintro rfl
      have : Nat.card ↥(zpowers x ⊔ P) = 0 := by rw [hk, mul_zero]
      exact (Nat.card_pos (α := ↥(zpowers x ⊔ P))).ne' this
    rw [hk]
    have : 2 ≤ k := by omega
    calc 2 * Nat.card P = Nat.card P * 2 := by ring
      _ ≤ Nat.card P * k := Nat.mul_le_mul_left _ this

theorem pow_three_eq_one_of_mem_two_group {G : Type*} [Group G] (R : Subgroup G)
    (hR2 : IsPGroup 2 R) (y : G) (hy : IsPGroup 3 (zpowers y)) (h : y ^ 3 ∈ R) : y ^ 3 = 1 := by
  obtain ⟨n, hn⟩ := hR2 ⟨y ^ 3, h⟩
  obtain ⟨m, hm⟩ := hy ⟨y ^ 3, Subgroup.pow_mem _ (mem_zpowers y) 3⟩
  have hn' : (y ^ 3) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hm' : (y ^ 3) ^ 3 ^ m = 1 := congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ n) (3 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
  have h1 : (y ^ 3) ^ Nat.gcd (2 ^ n) (3 ^ m) = 1 := pow_gcd_eq_one.mpr ⟨hn', hm'⟩
  rwa [hcop, pow_one] at h1

theorem mem_iff_conj_of_involution {G : Type*} [Group G] (R : Subgroup G) (x : G)
    (hx2 : x * x = 1) (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (p : G) : p ∈ R ↔ x * p * x⁻¹ ∈ R := by
  refine ⟨hN p, fun h => ?_⟩
  have := hN _ h
  have e : x * (x * p * x⁻¹) * x⁻¹ = p := by
    calc x * (x * p * x⁻¹) * x⁻¹ = (x * x) * p * (x * x)⁻¹ := by group
      _ = p := by rw [hx2]; group
  rwa [e] at this

variable {G : Type*} [Group G]

@[expose] noncomputable def actNI (A : Subgroup G) [A.Normal] :
    G →* Equiv.Perm {a : ↥A // a ≠ 1} :=
  (CFSG.nonidentityAutomorphismAction ↥A).comp MulAut.conjNormal

theorem mem_ker_actNI (A : Subgroup G) [A.Normal] (g : G) :
    g ∈ (actNI A).ker ↔ ∀ a ∈ A, g * a * g⁻¹ = a := by
  constructor
  · intro h a ha
    by_cases h1 : a = 1
    · subst h1; simp
    · have h1' : (⟨a, ha⟩ : ↥A) ≠ 1 := fun h => h1 (by simpa using congrArg Subtype.val h)
      have := congrArg (fun σ : Equiv.Perm {a : ↥A // a ≠ 1} =>
        ((σ ⟨⟨a, ha⟩, h1'⟩ : {a : ↥A // a ≠ 1}) : ↥A)) (MonoidHom.mem_ker.mp h)
      have h2 := congrArg Subtype.val this
      exact h2
  · intro h
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    rintro ⟨a, ha⟩
    apply Subtype.ext
    apply Subtype.ext
    exact h a a.2

theorem centralizer_eq_ker_actNI (A : Subgroup G) [A.Normal] :
    centralizer (A : Set G) = (actNI A).ker := by
  ext g
  rw [mem_ker_actNI, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    rw [mul_inv_eq_iff_eq_mul]
    exact (h a ha).symm
  · intro h a ha
    have := h a ha
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm

theorem card_nonidentity_four (A : Subgroup G) (hA : Nat.card A = 4) [Finite G] :
    Nat.card {a : ↥A // a ≠ 1} = 3 := by
  classical
  let : Fintype ↥A := Fintype.ofFinite _
  have h1 : Fintype.card {x : ↥A // x = 1} = 1 := by simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : ↥A => x = 1), h1]
  rw [Nat.card_eq_fintype_card] at hA
  omega

theorem exists_E_structure [Finite G] (A P₃ : Subgroup G) [A.Normal]
    (hA : Nat.card A = 4) (hP39 : Nat.card P₃ = 3 ∨ Nat.card P₃ = 9)
    (x y : G) (hx2 : x * x = 1) (hxn : x ∉ P₃) (hyP : y ∈ P₃) (hy3 : y ^ 3 = 1)
    (hxP : ∀ p, p ∈ P₃ ↔ x * p * x⁻¹ ∈ P₃) (hxy : x * y * x⁻¹ = y⁻¹)
    (hyA : ∀ a ∈ A, a ≠ 1 → y * a * y⁻¹ ≠ a)
    (hnot : Nat.card P₃ = 9 → ∃ p ∈ P₃, x * p * x⁻¹ ≠ p⁻¹) :
    ∃ E E₀ : Subgroup G, E = zpowers x ⊔ P₃ ∧ E₀ = zpowers x ⊔ zpowers y ∧ E₀ ≤ E ∧
      Nat.card E = 2 * Nat.card P₃ ∧ Nonempty (↥E₀ ≃* Equiv.Perm (Fin 3)) ∧
      (Nonempty (↥E ≃* Equiv.Perm (Fin 3)) ∨
        Nonempty (↥E ≃* Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) ∧
      E = E₀ ⊔ (centralizer (A : Set G) ⊓ E) ∧ E₀ ⊓ (centralizer (A : Set G) ⊓ E) = ⊥ ∧
      (∀ a ∈ E₀, ∀ c ∈ centralizer (A : Set G) ⊓ E, a * c = c * a) ∧
      (Nat.card ↥(centralizer (A : Set G) ⊓ E) = 1 ∨
        Nat.card ↥(centralizer (A : Set G) ⊓ E) = 3) ∧
      (∀ a ∈ E₀, orderOf a = 3 → a ∈ zpowers y) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right (by rw [← pow_three, hy3])
  have hyyi : (y * y)⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_three', hy3])
  set E : Subgroup G := zpowers x ⊔ P₃ with hE
  set E₀ : Subgroup G := zpowers x ⊔ zpowers y with hE₀
  set K : Subgroup G := centralizer (A : Set G) ⊓ E with hK
  have hxE : x ∈ E := mem_sup_left (mem_zpowers x)
  have hxE₀ : x ∈ E₀ := mem_sup_left (mem_zpowers x)
  have hyE₀ : y ∈ E₀ := mem_sup_right (mem_zpowers y)
  have hE₀E : E₀ ≤ E := sup_le_sup_left (zpowers_le.mpr hyP) _
  have hEcard : Nat.card E = 2 * Nat.card P₃ := card_sup_zpowers P₃ x hx2 hxP hxn
  let : Fintype {a : ↥A // a ≠ 1} := Fintype.ofFinite _
  have hX : Fintype.card {a : ↥A // a ≠ 1} = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact card_nonidentity_four A hA
  have hA1 : ∃ a : ↥A, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : A = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have := hno ⟨g, hg⟩
      simpa using congrArg Subtype.val this
    rw [this, Subgroup.card_bot] at hA
    omega
  let ρ : ↥E₀ →* Equiv.Perm {a : ↥A // a ≠ 1} := (actNI A).comp E₀.subtype
  have hρy : ρ ⟨y, hyE₀⟩ ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := hA1
    have hker := (mem_ker_actNI A y).mp (MonoidHom.mem_ker.mpr h) a a.2
    exact hyA a a.2 (fun h => ha (Subtype.ext h)) hker
  have hρx : ρ ⟨x, hxE₀⟩ ≠ 1 := by
    intro h
    have hxk := (mem_ker_actNI A x).mp (MonoidHom.mem_ker.mpr h)
    obtain ⟨a, ha⟩ := hA1
    have hnorm : ∀ b ∈ A, y * b * y⁻¹ ∈ A := fun b hb => ‹A.Normal›.conj_mem b hb y
    have h2 : ∀ b ∈ A, y⁻¹ * b * y = y * b * y⁻¹ := by
      intro b hb
      have e1 : y⁻¹ * b * y = x * (y * (x⁻¹ * b * x) * y⁻¹) * x⁻¹ := by
        have : y⁻¹ = x * y * x⁻¹ := hxy.symm
        calc y⁻¹ * b * y = (x * y * x⁻¹) * b * (x * y * x⁻¹)⁻¹ := by rw [← this]; group
          _ = x * (y * (x⁻¹ * b * x) * y⁻¹) * x⁻¹ := by group
      have e2 : x⁻¹ * b * x = b := by rw [hxi]; have := hxk b hb; rwa [hxi] at this
      rw [e1, e2]
      exact hxk _ (hnorm b hb)
    have h3 : y * (y * a * y⁻¹) * y⁻¹ = a := by
      have := h2 (y * a * y⁻¹) (hnorm a a.2)
      calc y * (y * a * y⁻¹) * y⁻¹ = y⁻¹ * (y * a * y⁻¹) * y := by rw [this]
        _ = a := by group
    apply hyA a a.2 (fun h => ha (Subtype.ext h))
    calc y * a * y⁻¹ = y⁻¹ * a * y := (h2 a a.2).symm
      _ = (y * y) * a * (y * y)⁻¹ := by rw [hyyi, hyi]
      _ = y * (y * a * y⁻¹) * y⁻¹ := by group
      _ = a := h3
  have hbij : Function.Bijective ρ :=
    bijective_of_perm_three hX E₀ x y hxE₀ hyE₀ rfl hx2 hy3 hxy ρ hρy hρx
  have hker : centralizer (A : Set G) = (actNI A).ker := centralizer_eq_ker_actNI A
  have hKnorm : ∀ e ∈ E, ∀ k, k ∈ K ↔ e * k * e⁻¹ ∈ K := by
    have hfwd : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ ∈ K := by
      intro e he k hk
      refine ⟨?_, E.mul_mem (E.mul_mem he hk.2) (E.inv_mem he)⟩
      rw [hker]
      exact (MonoidHom.normal_ker (actNI A)).conj_mem k (hker ▸ hk.1) e
    intro e he k
    exact ⟨hfwd e he k, fun h => by
      have := hfwd e⁻¹ (E.inv_mem he) _ h
      simpa [mul_assoc] using this⟩
  have hK₀ : E₀ ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg0, hgK1, hgK2⟩
    have hkerg : g ∈ (actNI A).ker := hker ▸ hgK1
    have h1 : ρ ⟨g, hg0⟩ = ρ 1 := by rw [map_one]; exact MonoidHom.mem_ker.mp hkerg
    have := hbij.1 h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hEK : E = E₀ ⊔ K := by
    apply le_antisymm
    · intro e he
      obtain ⟨⟨e₀, he₀⟩, h0⟩ := hbij.2 (actNI A e)
      have h1 : actNI A e₀ = actNI A e := h0
      have h2 : e₀⁻¹ * e ∈ K := by
        have h4 : e₀⁻¹ * e ∈ (actNI A).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
        exact ⟨hker ▸ h4, E.mul_mem (E.inv_mem (hE₀E he₀)) he⟩
      have h3 : e = e₀ * (e₀⁻¹ * e) := by group
      rw [h3]
      exact Subgroup.mul_mem _ (mem_sup_left he₀) (mem_sup_right h2)
    · exact sup_le hE₀E inf_le_right
  have hE₀card : Nat.card E₀ = 6 := by
    rw [Nat.card_congr (Equiv.ofBijective ρ hbij), Nat.card_perm, card_nonidentity_four A hA]
    rfl
  have hE₀norm : E₀ ≤ normalizer (K : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    exact fun k => hKnorm g (hE₀E hg) k
  have hKcard : Nat.card E = 6 * Nat.card K := by
    apply le_antisymm
    · have := card_sup_le_of_le_normalizer E₀ K hE₀norm
      rw [← hEK, hE₀card] at this; exact this
    · have := card_mul_le_card_sup E₀ K hK₀
      rw [← hEK, hE₀card] at this; exact this
  have hKc : Nat.card K = 1 ∨ Nat.card K = 3 := by
    rcases hP39 with h | h
    · left; rw [h] at hEcard; omega
    · right; rw [h] at hEcard; omega
  have hcomm : ∀ a ∈ E₀, ∀ k ∈ K, a * k = k * a := by
    rcases hKc with h1 | h3
    · have hKbot : K = ⊥ := Subgroup.eq_bot_of_card_eq K h1
      intro a _ k hk
      rw [hKbot, Subgroup.mem_bot] at hk
      subst hk; simp
    · have hP9 : Nat.card P₃ = 9 := by rcases hP39 with h | h <;> omega
      have hKP : K ≤ P₃ := by
        intro k hk
        have hk3 : k ^ 3 = 1 := by
          have := pow_card_eq_one' (G := ↥K) (x := ⟨k, hk⟩)
          rw [h3] at this
          exact congrArg Subtype.val this
        exact mem_of_cube_eq_one P₃ x hx2 hxP hxn hk.2 hk3
      have hPcommI : IsMulCommutative ↥P₃ :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP9]; norm_num)
      have hPcomm' : ∀ a ∈ P₃, ∀ b ∈ P₃, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val (hPcommI.is_comm.comm (⟨a, ha⟩ : ↥P₃) ⟨b, hb⟩)
      obtain ⟨c, hcK, hc1⟩ : ∃ c ∈ K, c ≠ 1 := by
        by_contra hno
        push Not at hno
        have : K = ⊥ := by
          rw [eq_bot_iff]; intro g hg; exact Subgroup.mem_bot.mpr (hno g hg)
        rw [this, Subgroup.card_bot] at h3; omega
      have hc3 : c ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥K) (x := ⟨c, hcK⟩); rw [h3] at this
        exact congrArg Subtype.val this
      have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
      have hKz : K = zpowers c :=
        (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hcK)
          (by rw [Nat.card_zpowers, hcord, h3])).symm
      have hxcK : x * c * x⁻¹ ∈ K := (hKnorm x hxE c).mp hcK
      have hdis : x * c * x⁻¹ = c ∨ x * c * x⁻¹ = c⁻¹ := by
        rw [hKz] at hxcK
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxcK
        rw [← hk]
        have hmod : c ^ (k % 3) = c ^ k := by
          have := zpow_mod_orderOf c k
          rwa [hcord] at this
        have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
        have h3' : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
        have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases hcases with h | h | h
        · exfalso
          rw [h, zpow_zero] at hmod
          have : x * c * x⁻¹ = 1 := by rw [← hk, ← hmod]
          apply hc1
          have := congrArg (fun g => x⁻¹ * g * x) this
          simpa [mul_assoc] using this
        · left; rw [h, zpow_one] at hmod; rw [← hmod]
        · right
          rw [h] at hmod
          rw [← hmod]
          have : c ^ (2 : ℤ) * c = 1 := by
            rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num]; simpa using hc3
          exact eq_inv_of_mul_eq_one_left this
      have hyK : ∀ k ∈ K, y * k = k * y := fun k hk => hPcomm' y hyP k (hKP hk)
      rcases hdis with hxc | hxc
      · have hxK : ∀ k ∈ K, x * k = k * x := by
          intro k hk
          rw [hKz] at hk
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
          have hcm : Commute x c := mul_inv_eq_iff_eq_mul.mp hxc
          exact (Commute.zpow_right hcm j)
        intro a ha k hk
        have hle : E₀ ≤ centralizer (K : Set G) := by
          apply sup_le
          · rw [zpowers_le, Subgroup.mem_centralizer_iff]; intro k hk; exact (hxK k hk).symm
          · rw [zpowers_le, Subgroup.mem_centralizer_iff]; intro k hk; exact (hyK k hk).symm
        exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) k hk).symm
      · exfalso
        obtain ⟨p, hp, hpne⟩ := hnot hP9
        let I : Subgroup G :=
          { carrier := {q | q ∈ P₃ ∧ x * q * x⁻¹ = q⁻¹}
            one_mem' := ⟨P₃.one_mem, by simp⟩
            mul_mem' := by
              rintro a b ⟨ha, hxa⟩ ⟨hb, hxb⟩
              refine ⟨P₃.mul_mem ha hb, ?_⟩
              calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
                _ = a⁻¹ * b⁻¹ := by rw [hxa, hxb]
                _ = b⁻¹ * a⁻¹ := hPcomm' a⁻¹ (P₃.inv_mem ha) b⁻¹ (P₃.inv_mem hb)
                _ = (a * b)⁻¹ := by group
            inv_mem' := by
              rintro a ⟨ha, hxa⟩
              refine ⟨P₃.inv_mem ha, ?_⟩
              calc x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
                _ = a⁻¹⁻¹ := by rw [hxa] }
        have hyI : y ∈ I := ⟨hyP, hxy⟩
        have hcI : c ∈ I := ⟨hKP hcK, hxc⟩
        have hSle : zpowers y ⊔ zpowers c ≤ I := sup_le (zpowers_le.mpr hyI) (zpowers_le.mpr hcI)
        have hSP : zpowers y ⊔ zpowers c ≤ P₃ :=
          sup_le (zpowers_le.mpr hyP) (zpowers_le.mpr (hKP hcK))
        have hS3 : Nat.card ↥(zpowers y ⊔ zpowers c) ≠ 3 := by
          intro h3S
          have hzS : zpowers c = zpowers y ⊔ zpowers c :=
            Subgroup.eq_of_le_of_card_ge (le_sup_right) (by rw [h3S, Nat.card_zpowers, hcord])
          have hyKm : y ∈ K := by
            rw [hKz, hzS]; exact mem_sup_left (mem_zpowers y)
          obtain ⟨a, ha⟩ := hA1
          have := (mem_ker_actNI A y).mp (hker ▸ hyKm.1) a a.2
          exact hyA a a.2 (fun h => ha (Subtype.ext h)) this
        have hS9 : Nat.card ↥(zpowers y ⊔ zpowers c) = 9 := by
          have hd1 : 3 ∣ Nat.card ↥(zpowers y ⊔ zpowers c) := by
            have := Subgroup.card_dvd_of_le (le_sup_right : zpowers c ≤ zpowers y ⊔ zpowers c)
            rwa [Nat.card_zpowers, hcord] at this
          have hd2 : Nat.card ↥(zpowers y ⊔ zpowers c) ∣ 3 ^ 2 := by
            have := Subgroup.card_dvd_of_le hSP
            rwa [hP9] at this
          obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd2
          rw [hk']
          interval_cases k
          · rw [hk'] at hd1; norm_num at hd1
          · exfalso; exact hS3 (by rw [hk']; norm_num)
          · norm_num
        have hSeq : zpowers y ⊔ zpowers c = P₃ :=
          Subgroup.eq_of_le_of_card_ge hSP (by rw [hS9, hP9])
        apply hpne
        have hpS : p ∈ I := hSle (hSeq ▸ hp)
        exact hpS.2
  have hxP' : ∀ p, p ∈ zpowers y ↔ x * p * x⁻¹ ∈ zpowers y := by
    have hfwd : ∀ w ∈ zpowers y, x * w * x⁻¹ ∈ zpowers y := by
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← conj_zpow, hxy]
      exact zpow_mem (inv_mem (mem_zpowers y)) k
    intro p
    refine ⟨hfwd p, fun h => ?_⟩
    have := hfwd _ h
    have e : x * (x * p * x⁻¹) * x⁻¹ = p := by
      calc x * (x * p * x⁻¹) * x⁻¹ = (x * x) * p * (x * x)⁻¹ := by group
        _ = p := by rw [hx2]; group
    rwa [e] at this
  have hxny : x ∉ zpowers y := fun h => hxn (zpowers_le.mpr hyP h)
  have hord3 : ∀ a ∈ E₀, orderOf a = 3 → a ∈ zpowers y := by
    intro a ha hao
    refine mem_of_cube_eq_one (zpowers y) x hx2 hxP' hxny ha ?_
    have := pow_orderOf_eq_one a
    rwa [hao] at this
  have hE₀S3 : Nonempty (↥E₀ ≃* Equiv.Perm (Fin 3)) :=
    ⟨(MulEquiv.ofBijective ρ hbij).trans (permCongrMulEquiv (Fintype.equivFinOfCardEq hX))⟩
  refine ⟨E, E₀, rfl, rfl, hE₀E, hEcard, hE₀S3, ?_, hEK, hK₀, hcomm, hKc, hord3⟩
  rcases hKc with h1 | h3
  · left
    have hKbot : K = ⊥ := Subgroup.eq_bot_of_card_eq K h1
    have hEE₀ : E = E₀ := by rw [hEK, hKbot, sup_bot_eq]
    obtain ⟨e⟩ := hE₀S3
    exact ⟨(MulEquiv.subgroupCongr hEE₀).trans e⟩
  · right
    obtain ⟨e1⟩ := hE₀S3
    obtain ⟨e2⟩ := nonempty_mulEquiv_zmod_three K h3
    obtain ⟨e3⟩ := nonempty_mulEquiv_prod_of_commute E₀ K hcomm hK₀
    exact ⟨(MulEquiv.subgroupCongr hEK).trans (e3.trans (MulEquiv.prodCongr e1 e2))⟩

theorem card_fixed_ge_four {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    (hU16 : Nat.card U = 16) (hsq : ∀ u ∈ U, u * u = 1) (x : G) (hx2 : x * x = 1)
    (hxU : ∀ u : G, u ∈ U ↔ x * u * x⁻¹ ∈ U) :
    4 ≤ Nat.card ↥(centralizer ({x} : Set G) ⊓ U) := by
  classical
  have hcommG : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b) * (a * b) = 1 := hsq _ (U.mul_mem ha hb)
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have h3 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h2, h3]
  have hcU : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu => (hxU u).mp hu
  let g : ↥U → ↥U := fun u => ⟨(u : G) * (x * u * x⁻¹), U.mul_mem u.2 (hcU u u.2)⟩
  let f : ↥U →* ↥U := MonoidHom.mk' g (by
    intro a b
    apply Subtype.ext
    show ((a * b : ↥U) : G) * (x * ((a * b : ↥U) : G) * x⁻¹) =
      (a : G) * (x * a * x⁻¹) * ((b : G) * (x * b * x⁻¹))
    have hc : (x * (a : G) * x⁻¹) * (b : G) = (b : G) * (x * (a : G) * x⁻¹) :=
      hcommG _ (hcU a a.2) _ b.2
    calc ((a * b : ↥U) : G) * (x * ((a * b : ↥U) : G) * x⁻¹)
        = (a : G) * (b : G) * (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹) := by
          rw [Subgroup.coe_mul]; group
      _ = (a : G) * ((b : G) * (x * (a : G) * x⁻¹)) * (x * (b : G) * x⁻¹) := by group
      _ = (a : G) * ((x * (a : G) * x⁻¹) * (b : G)) * (x * (b : G) * x⁻¹) := by rw [hc]
      _ = (a : G) * (x * a * x⁻¹) * ((b : G) * (x * b * x⁻¹)) := by group)
  set Cu : Subgroup ↥U := (centralizer ({x} : Set G) ⊓ U).subgroupOf U with hCu
  have hCcard : Nat.card Cu = Nat.card ↥(centralizer ({x} : Set G) ⊓ U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv
  have hker : f.ker ≤ Cu := by
    intro u hu
    have h1 : (u : G) * (x * u * x⁻¹) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
    have h2 : x * (u : G) * x⁻¹ = (u : G)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    have h3 : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u u.2)
    rw [h3] at h2
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, u.2⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (u : G) * x = x * (u : G) * x⁻¹ * x := by rw [h2]
      _ = x * u := by group
  have hrange : f.range ≤ Cu := by
    rintro _ ⟨u, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, (f u).2⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (u : G) * (x * u * x⁻¹) * x = x * ((u : G) * (x * u * x⁻¹))
    have hc : (x * (u : G) * x⁻¹) * (u : G) = (u : G) * (x * (u : G) * x⁻¹) :=
      hcommG _ (hcU u u.2) _ u.2
    have e1 : x * (x * (u : G) * x⁻¹) * x⁻¹ = u := by
      calc x * (x * (u : G) * x⁻¹) * x⁻¹ = (x * x) * (u : G) * (x * x)⁻¹ := by group
        _ = u := by rw [hx2]; group
    have hw : x * ((u : G) * (x * u * x⁻¹)) * x⁻¹ = (u : G) * (x * u * x⁻¹) := by
      calc x * ((u : G) * (x * u * x⁻¹)) * x⁻¹
          = (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) := by group
        _ = (x * (u : G) * x⁻¹) * u := by rw [e1]
        _ = (u : G) * (x * u * x⁻¹) := hc
    exact (mul_inv_eq_iff_eq_mul.mp hw).symm
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hU16] at hmul
  have h1 : Nat.card f.ker ≤ Nat.card Cu := Subgroup.card_le_of_le hker
  have h2 : Nat.card f.range ≤ Nat.card Cu := Subgroup.card_le_of_le hrange
  rw [← hCcard]
  by_contra hlt
  push Not at hlt
  have : Nat.card f.ker * Nat.card f.range ≤ 3 * 3 := Nat.mul_le_mul (by omega) (by omega)
  omega

end CFSG.GH74.Uniqueness.SU.K.R4.Q64
