module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57F

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem mem_of_pow_odd_mem {H : Subgroup G} {g : G} {m e : ℕ} (hm : Odd m) (h1 : g ^ m ∈ H)
    (h2 : g ^ 2 ^ e ∈ H) : g ∈ H := by
  have hc : Nat.Coprime m (2 ^ e) := Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hm)
  have hg := Nat.gcd_eq_gcd_ab m (2 ^ e)
  rw [hc.gcd_eq_one, Nat.cast_one] at hg
  have h3 : g = (g ^ m) ^ (Nat.gcdA m (2 ^ e)) * (g ^ 2 ^ e) ^ (Nat.gcdB m (2 ^ e)) := by
    rw [← zpow_natCast g m, ← zpow_natCast g (2 ^ e), ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg,
      zpow_one]
  rw [h3]
  exact mul_mem (zpow_mem h1 _) (zpow_mem h2 _)

theorem exists_odd_pow_eq_L512 (i r : ℕ) :
    ∃ s : ℕ, (2 * i + 1) ^ r = 1 + 2 * i * s ∧ s % 2 = r % 2 := by
  induction r with
  | zero => exact ⟨0, by simp, rfl⟩
  | succ r ih =>
    obtain ⟨s, hs, hs2⟩ := ih
    refine ⟨1 + s * (2 * i + 1), ?_, ?_⟩
    · rw [pow_succ, hs]
      ring
    · have h1 : s * (2 * i + 1) = 2 * (i * s) + s := by ring
      rw [h1]
      generalize i * s = u
      omega

theorem pow_mul_mem_coset_L512 {U : Subgroup G} {p : G} (hpU : ∀ u ∈ U, p⁻¹ * u * p ∈ U)
    (c : ℕ) : ∀ (a : ℕ) {u : G}, u ∈ U → (p ^ (c * a))⁻¹ * (p ^ c * u) ^ a ∈ U := by
  have h3 : ∀ k : ℕ, ∀ w ∈ U, (p ^ k)⁻¹ * w * p ^ k ∈ U := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ihk =>
      intro w hw
      have h4 := hpU _ (ihk w hw)
      rw [show (p ^ (k + 1))⁻¹ * w * p ^ (k + 1) = p⁻¹ * ((p ^ k)⁻¹ * w * p ^ k) * p by
        rw [pow_succ]; group]
      exact h4
  intro a
  induction a with
  | zero => intro u _; simp
  | succ a ih =>
    intro u hu
    have h1 := ih hu
    set v := (p ^ (c * a))⁻¹ * (p ^ c * u) ^ a with hv
    have h2 : (p ^ c * u) ^ a = p ^ (c * a) * v := by rw [hv]; group
    rw [pow_succ, h2, show (p ^ (c * (a + 1)))⁻¹ * (p ^ (c * a) * v * (p ^ c * u)) =
      ((p ^ c)⁻¹ * v * p ^ c) * u by rw [mul_add, mul_one, pow_add]; group]
    exact mul_mem (h3 c v h1) hu

theorem conj_mem_of_cyclic_mod {M U : Subgroup G} (hUn : ∀ k ∈ M, ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    {p₀ : G} (hp₀ : p₀ ∈ M) (hcyc : ∀ k ∈ M, ∃ j : ℕ, ∃ u ∈ U, k = p₀ ^ j * u) {e : ℕ}
    (he : p₀ ^ 2 ^ e ∈ U) {n : G} (hnM : ∀ k ∈ M, n * k * n⁻¹ ∈ M)
    (hnU : ∀ u ∈ U, n * u * n⁻¹ ∈ U) {m : ℕ} (hm : Odd m) (hnm : n ^ m = 1) {k : G}
    (hk : k ∈ M) : k⁻¹ * (n * k * n⁻¹) ∈ U := by
  have hp₀U : ∀ u ∈ U, p₀⁻¹ * u * p₀ ∈ U := fun u hu => by
    have h1 := hUn _ (inv_mem hp₀) u hu
    rwa [inv_inv] at h1
  obtain ⟨j, u₀, hu₀, hj⟩ := hcyc _ (hnM p₀ hp₀)
  have hB : ∀ r : ℕ, (p₀ ^ j ^ r)⁻¹ * (n ^ r * p₀ * (n ^ r)⁻¹) ∈ U := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      set u := (p₀ ^ j ^ r)⁻¹ * (n ^ r * p₀ * (n ^ r)⁻¹) with hu
      have h1 : n ^ r * p₀ * (n ^ r)⁻¹ = p₀ ^ j ^ r * u := by rw [hu]; group
      have h2 : n ^ (r + 1) * p₀ * (n ^ (r + 1))⁻¹ = (p₀ ^ j * u₀) ^ j ^ r * (n * u * n⁻¹) := by
        calc n ^ (r + 1) * p₀ * (n ^ (r + 1))⁻¹ = n * (n ^ r * p₀ * (n ^ r)⁻¹) * n⁻¹ := by
              rw [pow_succ']; group
          _ = n * (p₀ ^ j ^ r * u) * n⁻¹ := by rw [h1]
          _ = (n * p₀ * n⁻¹) ^ j ^ r * (n * u * n⁻¹) := by rw [conj_pow]; group
          _ = (p₀ ^ j * u₀) ^ j ^ r * (n * u * n⁻¹) := by rw [hj]
      rw [h2, pow_succ', ← mul_assoc]
      exact mul_mem (pow_mul_mem_coset_L512 hp₀U j (j ^ r) hu₀) (hnU u ih)
  have hm1 : (p₀ ^ j ^ m)⁻¹ * p₀ ∈ U := by
    have h1 := hB m
    rwa [hnm, one_mul, inv_one, mul_one] at h1
  have hm0 : m ≠ 0 := fun h0 => by rw [h0] at hm; exact Nat.not_odd_zero hm
  have hcase : p₀ ∈ U ∨ p₀⁻¹ * (n * p₀ * n⁻¹) ∈ U := by
    rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
    · left
      obtain ⟨c, hc⟩ : Even (j ^ m) := Nat.even_pow.mpr ⟨⟨i, hi⟩, hm0⟩
      rcases Nat.eq_zero_or_pos c with hc0 | hc0
      · rw [hc, hc0] at hm1
        simpa using hm1
      · have h1 : (p₀ ^ (2 * (c - 1) + 1))⁻¹ ∈ U := by
          have h2 : (p₀ ^ j ^ m)⁻¹ * p₀ = (p₀ ^ (2 * (c - 1) + 1))⁻¹ := by
            rw [hc, show c + c = 2 * (c - 1) + 1 + 1 by omega, pow_succ']
            group
          rw [← h2]
          exact hm1
        exact mem_of_pow_odd_mem ⟨c - 1, rfl⟩ (by simpa using inv_mem h1) he
    · right
      obtain ⟨s, hs, hs2⟩ := exists_odd_pow_eq_L512 i m
      rw [← hi] at hs
      have hsodd : Odd s := Nat.odd_iff.mpr (by rw [hs2]; exact Nat.odd_iff.mp hm)
      have h1 : (p₀ ^ (2 * i)) ^ s ∈ U := by
        have h2 : (p₀ ^ j ^ m)⁻¹ * p₀ = ((p₀ ^ (2 * i)) ^ s)⁻¹ := by
          rw [hs, pow_add, pow_one, ← pow_mul]
          group
        rw [h2] at hm1
        simpa using inv_mem hm1
      have h2 : (p₀ ^ (2 * i)) ^ 2 ^ e ∈ U := by
        rw [← pow_mul, mul_comm, pow_mul]
        exact pow_mem he _
      have h3 := mem_of_pow_odd_mem hsodd h1 h2
      rw [hj, hi, pow_succ', show p₀⁻¹ * (p₀ * p₀ ^ (2 * i) * u₀) = p₀ ^ (2 * i) * u₀ by group]
      exact mul_mem h3 hu₀
  obtain ⟨i, u, hu, rfl⟩ := hcyc k hk
  rcases hcase with hp | hp
  · have hkU : p₀ ^ i * u ∈ U := mul_mem (pow_mem hp i) hu
    exact mul_mem (inv_mem hkU) (hnU _ hkU)
  · set u₁ := p₀⁻¹ * (n * p₀ * n⁻¹) with hu₁
    have h1 : n * p₀ * n⁻¹ = p₀ * u₁ := by rw [hu₁]; group
    have h2 := pow_mul_mem_coset_L512 hp₀U 1 i hp
    rw [one_mul, pow_one] at h2
    have h3 : (p₀ ^ i * u)⁻¹ * (n * (p₀ ^ i * u) * n⁻¹) =
        u⁻¹ * ((p₀ ^ i)⁻¹ * (p₀ * u₁) ^ i) * (n * u * n⁻¹) := by
      rw [← h1, conj_pow]
      group
    rw [h3]
    exact mul_mem (mul_mem (inv_mem hu) h2) (hnU u hu)

section Finite

variable [Finite G]

theorem mem_normalizer_of_conj_mem_L512 {P : Subgroup G} {n : G}
    (hn : ∀ q ∈ P, n * q * n⁻¹ ∈ P) : n ∈ normalizer (P : Set G) := by
  have hle : P.map (MulAut.conj n).toMonoidHom ≤ P := by
    rintro _ ⟨q, hq, rfl⟩
    exact hn q hq
  have heq := eq_of_le_of_card_ge hle
    (le_of_eq (card_map_of_injective (MulAut.conj n).injective).symm)
  rw [mem_normalizer_iff]
  intro q
  refine ⟨hn q, fun hq => ?_⟩
  have h1 : n * q * n⁻¹ ∈ P.map (MulAut.conj n).toMonoidHom := by rw [heq]; exact hq
  obtain ⟨q', hq', h2⟩ := h1
  have h3 : n * q' * n⁻¹ = n * q * n⁻¹ := h2
  rw [mul_left_inj, mul_right_inj] at h3
  rwa [← h3]

theorem commute_of_normalizes_of_cyclic_mod {K P W : Subgroup G} (hP : IsSylowOf 2 P K)
    (hWP : W ≤ P) (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k) {p₀ : G} (hp₀ : p₀ ∈ P)
    (hcyc : ∀ q ∈ P, ∃ j : ℕ, ∃ w ∈ W, q = p₀ ^ j * w) {n : G} (hnK : n ∈ K)
    (hnP : ∀ q ∈ P, n * q * n⁻¹ ∈ P) {q : G} (hq : q ∈ P) : n * q = q * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPK := hP.le
  have hP2 := hP.isPGroup
  have hpow2 : ∀ x ∈ P, ∃ e : ℕ, x ^ 2 ^ e = 1 := fun x hx => by
    obtain ⟨e, he⟩ := hP2 ⟨x, hx⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, w, hw, rfl⟩ := hcyc a ha
    obtain ⟨i', w', hw', rfl⟩ := hcyc b hb
    have h1 : p₀ ^ i' * w = w * p₀ ^ i' :=
      (hKW _ (pow_mem (hPK hp₀) i') w hw)
    have h2 : p₀ ^ i * w' = w' * p₀ ^ i :=
      (hKW _ (pow_mem (hPK hp₀) i) w' hw')
    have h3 : w * w' = w' * w := hKW w (hPK (hWP hw)) w' hw'
    calc p₀ ^ i * w * (p₀ ^ i' * w') = p₀ ^ i * (w * p₀ ^ i') * w' := by group
      _ = p₀ ^ i * p₀ ^ i' * (w * w') := by rw [← h1]; group
      _ = p₀ ^ i' * p₀ ^ i * (w' * w) := by rw [pow_mul_comm p₀ i i', h3]
      _ = p₀ ^ i' * (p₀ ^ i * w') * w := by group
      _ = p₀ ^ i' * w' * (p₀ ^ i * w) := by rw [h2]; group
  have hnN : n ∈ normalizer (P : Set G) := mem_normalizer_of_conj_mem_L512 hnP
  obtain ⟨m, hm, k, hk⟩ := exists_odd_pow_two_element n
  have hn₂P : n ^ m ∈ P := by
    have hz2 : IsPGroup 2 (zpowers (n ^ m)) := isPGroup_zpowers_of_pow_two hk
    have hzN : zpowers (n ^ m) ≤ normalizer (P : Set G) := zpowers_le.mpr (pow_mem hnN m)
    have hsup := IsPGroup.to_sup_of_normal_left' hP2 hz2 hzN
    have hle : P ⊔ zpowers (n ^ m) ≤ K := sup_le hPK (zpowers_le.mpr (pow_mem hnK m))
    have heq := hP.eq_of_le le_sup_left hle hsup
    rw [← heq]
    exact mem_sup_right (mem_zpowers _)
  set n₁ := n ^ 2 ^ k with hn₁
  have hn₁m : n₁ ^ m = 1 := by rw [hn₁, ← pow_mul, mul_comm, pow_mul, hk]
  have hn₁N : n₁ ∈ normalizer (P : Set G) := pow_mem hnN _
  have hn₁K : n₁ ∈ K := pow_mem hnK _
  have hn₁P : ∀ x ∈ P, n₁ * x * n₁⁻¹ ∈ P := fun x hx => (mem_normalizer_iff.mp hn₁N x).mp hx
  obtain ⟨e, he⟩ := hpow2 p₀ hp₀
  have hδ : ∀ x ∈ P, x⁻¹ * (n₁ * x * n₁⁻¹) ∈ W := fun x hx =>
    conj_mem_of_cyclic_mod (M := P) (U := W)
      (fun a ha u hu => by rw [hKW a (hPK ha) u hu, mul_inv_cancel_right]; exact hu)
      hp₀ hcyc (e := e) (by rw [he]; exact one_mem _) hn₁P
      (fun u hu => by rw [hKW n₁ hn₁K u hu, mul_inv_cancel_right]; exact hu) hm hn₁m hx
  have hn₁q : n₁ * q = q * n₁ := by
    set δ := q⁻¹ * (n₁ * q * n₁⁻¹) with hδdef
    have hδW : δ ∈ W := hδ q hq
    have hqδ : n₁ * q * n₁⁻¹ = q * δ := by rw [hδdef]; group
    have h1 : n₁ * δ * n₁⁻¹ = δ := by rw [hKW n₁ hn₁K δ hδW, mul_inv_cancel_right]
    have hpowδ : ∀ r : ℕ, n₁ ^ r * q * (n₁ ^ r)⁻¹ = q * δ ^ r := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
        calc n₁ ^ (r + 1) * q * (n₁ ^ (r + 1))⁻¹ = n₁ * (n₁ ^ r * q * (n₁ ^ r)⁻¹) * n₁⁻¹ := by
              rw [pow_succ']; group
          _ = n₁ * (q * δ ^ r) * n₁⁻¹ := by rw [ih]
          _ = (n₁ * q * n₁⁻¹) * (n₁ * δ * n₁⁻¹) ^ r := by rw [conj_pow]; group
          _ = q * δ ^ (r + 1) := by rw [h1, hqδ, pow_succ', mul_assoc]
    have h2 := hpowδ m
    rw [hn₁m, one_mul, inv_one, mul_one] at h2
    have hδm : δ ^ m = 1 := by
      have h3 : q * δ ^ m = q * 1 := by rw [← h2, mul_one]
      exact mul_left_cancel h3
    obtain ⟨e', he'⟩ := hpow2 δ (hWP hδW)
    have hδ1 : δ ∈ (⊥ : Subgroup G) := mem_of_pow_odd_mem hm (by rw [hδm]; exact one_mem _)
      (by rw [he']; exact one_mem _)
    rw [mem_bot] at hδ1
    rw [hδ1, mul_one] at hqδ
    calc n₁ * q = n₁ * q * n₁⁻¹ * n₁ := by group
      _ = q * n₁ := by rw [hqδ]
  have hC : n ∈ centralizer ({q} : Set G) := by
    refine mem_of_pow_odd_mem (H := centralizer ({q} : Set G)) (e := k) hm ?_ ?_
    · exact mem_centralizer_singleton_iff.mpr (hPab _ hn₂P q hq)
    · exact mem_centralizer_singleton_iff.mpr hn₁q
  exact mem_centralizer_singleton_iff.mp hC

theorem exists_normal_two_complement {K P : Subgroup G} (hP : IsSylowOf 2 P K)
    (hNC : ∀ n ∈ K, (∀ q ∈ P, n * q * n⁻¹ ∈ P) → ∀ q ∈ P, n * q = q * n) :
    ∃ O : Subgroup G, O ≤ K ∧ Odd (Nat.card O) ∧ (∀ k ∈ K, Odd (orderOf k) → k ∈ O) ∧
      (∀ k ∈ K, ∃ o ∈ O, ∃ q ∈ P, k = o * q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₂, hQ₂⟩ := hP.exists_sylow_eq_subgroupOf
  have hmemQ : ∀ x : K, x ∈ (Q₂ : Subgroup K) ↔ (x : G) ∈ P := fun x => by
    rw [hQ₂, mem_subgroupOf]
  have hNC' : normalizer ((Q₂ : Subgroup K) : Set K) ≤
      centralizer ((Q₂ : Subgroup K) : Set K) := by
    intro n hn
    rw [mem_centralizer_iff]
    intro q hq
    have hqP : (q : G) ∈ P := (hmemQ q).mp hq
    have h1 := hNC n n.2 (fun q' hq' => by
      have h2 : (⟨q', hP.le hq'⟩ : K) ∈ (Q₂ : Subgroup K) := (hmemQ _).mpr hq'
      have h3 := (mem_normalizer_iff.mp hn _).mp h2
      exact (hmemQ _).mp h3) q hqP
    exact Subtype.ext h1.symm
  have hcomp : IsComplement' (MonoidHom.transferSylow Q₂ hNC').ker (Q₂ : Subgroup K) :=
    MonoidHom.ker_transferSylow_isComplement' Q₂ hNC'
  have hN2 : ¬ 2 ∣ Nat.card (MonoidHom.transferSylow Q₂ hNC').ker :=
    MonoidHom.not_dvd_card_ker_transferSylow Q₂ hNC'
  have hNn : (MonoidHom.transferSylow Q₂ hNC').ker.Normal := inferInstance
  generalize (MonoidHom.transferSylow Q₂ hNC').ker = N at hcomp hN2 hNn
  have hNidx : N.index = Nat.card (Q₂ : Subgroup K) := hcomp.symm.index_eq_card
  refine ⟨N.map K.subtype, map_subtype_le N, ?_, ?_, ?_⟩
  · rw [card_map_of_injective K.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hN2)
  · intro k hk hko
    obtain ⟨e, he⟩ := Q₂.isPGroup'.exists_card_eq
    have h2 := N.pow_index_mem (⟨k, hk⟩ : K)
    rw [hNidx, he] at h2
    have h3 : (⟨k, hk⟩ : K) ^ orderOf k ∈ N := by
      rw [show (⟨k, hk⟩ : K) ^ orderOf k = 1 from Subtype.ext (by simp [pow_orderOf_eq_one])]
      exact one_mem _
    exact ⟨⟨k, hk⟩, mem_of_pow_odd_mem hko h3 h2, rfl⟩
  · intro k hk
    obtain ⟨⟨a, b⟩, hab⟩ := (hcomp.existsUnique ⟨k, hk⟩).exists
    refine ⟨((a : K) : G), ⟨a, a.2, rfl⟩, ((b : K) : G), (hmemQ b).mp b.2, ?_⟩
    have h1 := congrArg Subtype.val hab
    simpa using h1.symm

end Finite

end CFSG.ComponentClassification.Foote5
