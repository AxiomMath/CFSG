module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type*} [Group G]

theorem eq_or_eq_sq_of_orderOf_three {A : Type*} [Group A] [Finite A] [IsCyclic A] {y z : A}
    (hy : orderOf y = 3) (hz : orderOf z = 3) : y = z ∨ y = z ^ 2 := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; omega
  have hz2 : z ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hz] at this
    omega
  have hzz : z ≠ z ^ 2 := fun h => hz1 (by
    have : z * z = z * 1 := by rw [mul_one, ← pow_two]; exact h.symm
    exact mul_left_cancel this)
  have hsub : ({1, z, z ^ 2} : Finset A) ⊆ Finset.univ.filter (fun a : A => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h3 : z ^ 3 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz] at this
    rcases ha with rfl | rfl | rfl
    · simp
    · exact h3
    · rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  have hcard3 : ({1, z, z ^ 2} : Finset A).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hzz]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hz1 h.symm, fun h => hz2 h.symm⟩
  have hle : (Finset.univ.filter (fun a : A => a ^ 3 = 1)).card ≤ 3 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hymem : y ∈ Finset.univ.filter (fun a : A => a ^ 3 = 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hy]
    exact pow_orderOf_eq_one y
  rw [← heq] at hymem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
  rcases hymem with h | h | h
  · exact absurd (by rw [h, orderOf_one] at hy; exact hy) (by norm_num)
  · exact Or.inl h
  · exact Or.inr h

theorem commute_of_coprime_cyclic [Finite G] {R : Subgroup G} (hR : IsPGroup 3 R)
    (hcyc : IsCyclic R) {z : G} (hz : z ∈ R) (hz3 : orderOf z = 3) {t : G}
    (ht : t ∈ Subgroup.normalizer (R : Set G)) {m : ℕ} (hm : ¬ 3 ∣ m) (htm : t ^ m = 1)
    (hzc : t * z = z * t) : ∀ r ∈ R, t * r = r * t := by
  classical
  have hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    have := (IsCyclic.commGroup (α := ↥R)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hconj : ∀ s ∈ R, t * s * t⁻¹ ∈ R := fun s hs => (Subgroup.mem_normalizer_iff.mp ht s).mp hs
  set rc : G → G := fun s => t * s * t⁻¹ * s⁻¹ with hrc
  have hrc_mem : ∀ s ∈ R, rc s ∈ R := fun s hs => R.mul_mem (hconj s hs) (R.inv_mem hs)
  have hrc_eq : ∀ s, t * s * t⁻¹ = rc s * s := fun s => by simp [hrc]
  have hpow : ∀ s ∈ R, ∀ k : ℕ, rc (s ^ k) = rc s ^ k := by
    intro s hs k
    have hc : Commute (rc s) s := hcomm _ (hrc_mem s hs) _ hs
    have : t * s ^ k * t⁻¹ = (t * s * t⁻¹) ^ k := by rw [conj_pow]
    simp only [hrc]
    rw [this, hrc_eq s, hc.mul_pow]
    simp only [hrc]
    group
  have order3 : ∀ r ∈ R, r ^ m = 1 → r = 1 := by
    intro r hr hrm
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    have hk' : r ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf r ∣ m := orderOf_dvd_of_pow_eq_one hrm
    have h2 : orderOf r ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime m (3 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm
    have hself : Nat.Coprime (orderOf r) (orderOf r) :=
      (hcop.coprime_dvd_left h1).coprime_dvd_right h2
    exact orderOf_eq_one_iff.mp (Nat.coprime_self _ |>.mp hself)
  have claim1 : ∀ s ∈ R, t * rc s * t⁻¹ = rc s → rc s = 1 := by
    intro s hs hfix
    have hit : ∀ i : ℕ, t ^ i * s * (t ^ i)⁻¹ = rc s ^ i * s := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have h1 : t ^ (i + 1) * s * (t ^ (i + 1))⁻¹ = t * (t ^ i * s * (t ^ i)⁻¹) * t⁻¹ := by
          rw [pow_succ', mul_inv_rev]; group
        rw [h1, ih]
        have h2 : t * (rc s ^ i * s) * t⁻¹ = (t * rc s * t⁻¹) ^ i * (t * s * t⁻¹) := by
          rw [conj_pow]; group
        rw [h2, hfix, hrc_eq s, pow_succ']
        group
    have := hit m
    rw [htm] at this
    simp at this
    exact order3 _ (hrc_mem s hs) this
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hr, hne⟩ := hcon
  have hu1 : rc r ≠ 1 := fun h => hne (by
    have : t * r * t⁻¹ = r := by
      have := hrc_eq r
      rw [h, one_mul] at this
      exact this
    calc t * r = t * r * t⁻¹ * t := by group
      _ = r * t := by rw [this])
  set u := rc r with hu
  have humem : u ∈ R := hrc_mem r hr
  obtain ⟨k, hk⟩ := hR ⟨u, humem⟩
  have hk' : u ^ 3 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simp at hord
      exact absurd hord hu1
    · exact h
  set y := u ^ 3 ^ (j - 1) with hy
  have hyord : orderOf y = 3 := by
    rw [hy, orderOf_pow_of_dvd (by positivity) (by
      rw [hord]; exact pow_dvd_pow 3 (by omega)), hord,
      Nat.pow_div (by omega) (by norm_num)]
    have : j - (j - 1) = 1 := by omega
    rw [this]
  have hyR : y ∈ R := R.pow_mem humem _
  have hyrc : y = rc (r ^ 3 ^ (j - 1)) := by
    rw [hpow r hr, ← hu]
  have hzmem : (⟨z, hz⟩ : R) ∈ (⊤ : Subgroup R) := trivial
  have hz3' : orderOf (⟨z, hz⟩ : R) = 3 := by rw [Subgroup.orderOf_mk]; exact hz3
  have hy3' : orderOf (⟨y, hyR⟩ : R) = 3 := by rw [Subgroup.orderOf_mk]; exact hyord
  have hcases := eq_or_eq_sq_of_orderOf_three (A := R) hy3' hz3'
  have hzfix : t * z * t⁻¹ = z := by rw [hzc]; group
  rcases hcases with h | h
  · have hyz : y = z := congrArg Subtype.val h
    have := claim1 (r ^ 3 ^ (j - 1)) (R.pow_mem hr _) (by rw [← hyrc, hyz]; exact hzfix)
    rw [← hyrc, hyz] at this
    rw [this, orderOf_one] at hz3
    omega
  · have hyz : y = z ^ 2 := congrArg Subtype.val h
    have hz_eq : z = y ^ 2 := by
      have h3 : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
      rw [hyz]
      calc z = z * z ^ 3 := by rw [h3, mul_one]
        _ = (z ^ 2) ^ 2 := by group
    have hy2 : y ^ 2 = rc ((r ^ 3 ^ (j - 1)) ^ 2) := by
      rw [hpow _ (R.pow_mem hr _), ← hyrc]
    have := claim1 ((r ^ 3 ^ (j - 1)) ^ 2) (R.pow_mem (R.pow_mem hr _) _)
      (by rw [← hy2, ← hz_eq]; exact hzfix)
    rw [← hy2, ← hz_eq] at this
    rw [this, orderOf_one] at hz3
    omega

theorem normalizer_le_centralizer_of_cyclic_sylow [Finite G] (R : Sylow 3 G)
    (hcyc : IsCyclic ↥(R : Subgroup G))
    {z : G} (hz : z ∈ (R : Subgroup G)) (hz3 : orderOf z = 3) (hzc : ∀ g : G, g * z = z * g) :
    Subgroup.normalizer ((R : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((R : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hcomm : ∀ a ∈ (R : Subgroup G), ∀ b ∈ (R : Subgroup G), a * b = b * a := by
    intro a ha b hb
    have := (IsCyclic.commGroup (α := ↥(R : Subgroup G))).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  obtain ⟨b, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t).ne' 3
    (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hord
    exact (orderOf_pos t).ne' hord
  set t₁ := t ^ m with ht₁
  set t₂ := t ^ 3 ^ b with ht₂
  have ht₁N : t₁ ∈ Subgroup.normalizer ((R : Subgroup G) : Set G) :=
    (Subgroup.normalizer ((R : Subgroup G) : Set G)).pow_mem ht m
  have ht₂N : t₂ ∈ Subgroup.normalizer ((R : Subgroup G) : Set G) :=
    (Subgroup.normalizer ((R : Subgroup G) : Set G)).pow_mem ht _
  have hord₁ : orderOf t₁ = 3 ^ b := by
    rw [ht₁, orderOf_pow_of_dvd hm0 (by rw [hord]; exact dvd_mul_left m _), hord]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hP₁ : IsPGroup 3 (Subgroup.zpowers t₁) :=
    IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hord₁])
  have ht₁R : t₁ ∈ (R : Subgroup G) := by
    have hmem : t₁ ∈ Subgroup.zpowers t₁ ⊓ Subgroup.normalizer ((R : Subgroup G) : Set G) :=
      ⟨Subgroup.mem_zpowers t₁, ht₁N⟩
    have h := hP₁.inf_normalizer_sylow R
    have hmem' : t₁ ∈ Subgroup.zpowers t₁ ⊓ (R : Subgroup G) := by
      rw [← h]
      exact hmem
    exact hmem'.2
  have hc₁ : t₁ * r = r * t₁ := hcomm _ ht₁R _ hr
  have hc₂ : t₂ * r = r * t₂ := by
    have hord₂ : t₂ ^ m = 1 := by
      rw [ht₂, ← pow_mul, ← hord]
      exact pow_orderOf_eq_one t
    exact commute_of_coprime_cyclic R.isPGroup' hcyc hz hz3 ht₂N hm hord₂
      (hzc t₂) r hr
  have hcop : IsCoprime (m : ℤ) ((3 ^ b : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm
  obtain ⟨a, c, hac⟩ := hcop
  have htt : t = t₁ ^ a * t₂ ^ c := by
    have h1 : ((m : ℤ) * a + ((3 ^ b : ℕ) : ℤ) * c) = 1 := by linarith [hac]
    calc t = t ^ (1 : ℤ) := (zpow_one t).symm
      _ = t ^ ((m : ℤ) * a + ((3 ^ b : ℕ) : ℤ) * c) := by rw [h1]
      _ = (t ^ (m : ℤ)) ^ a * (t ^ ((3 ^ b : ℕ) : ℤ)) ^ c := by
        rw [zpow_add, zpow_mul, zpow_mul]
      _ = t₁ ^ a * t₂ ^ c := by rw [zpow_natCast, zpow_natCast]
  rw [htt]
  have h1 : Commute r t₁ := hc₁.symm
  have h2 : Commute r t₂ := hc₂.symm
  exact ((h1.zpow_right a).mul_right (h2.zpow_right c)).eq

theorem exists_normal_complement_of_cyclic_sylow [Finite G] (R : Sylow 3 G)
    (hcyc : IsCyclic ↥(R : Subgroup G))
    {z : G} (hz : z ∈ (R : Subgroup G)) (hz3 : orderOf z = 3) (hzc : ∀ g : G, g * z = z * g) :
    ∃ K : Subgroup G, K.Normal ∧ Subgroup.IsComplement' K (R : Subgroup G) := by
  have hN := normalizer_le_centralizer_of_cyclic_sylow R hcyc hz hz3 hzc
  exact ⟨(MonoidHom.transferSylow R hN).ker, inferInstance,
    MonoidHom.ker_transferSylow_isComplement' R hN⟩

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
