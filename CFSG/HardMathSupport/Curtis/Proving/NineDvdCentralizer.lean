module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open Equiv Equiv.Perm

theorem exists_nine_le_centralizer_of_orderOf_three {G : Type*} [Group G] {a b : G}
    (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : Commute a b)
    (hnot : a ∉ Subgroup.zpowers b) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({a} : Set G) ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hdvd_a : ∀ k : ℕ, a ^ k = 1 → 3 ∣ k := fun k hk => by
    have := orderOf_dvd_of_pow_eq_one hk
    rwa [ha] at this
  have hdvd_b : ∀ k : ℕ, b ^ k = 1 → 3 ∣ k := fun k hk => by
    have := orderOf_dvd_of_pow_eq_one hk
    rwa [hb] at this
  have hfix : ∀ k l : ℕ, a ^ k = b ^ l → a ^ k = 1 := by
    intro k l h
    by_contra hne
    apply hnot
    have h3k : ¬ 3 ∣ k := fun hd => hne (by
      obtain ⟨m, rfl⟩ := hd
      rw [pow_mul, ha3, one_pow])
    have hkk : k * k % 3 = 1 := by
      have : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
    have hak : a = a ^ (k * k) := by
      have := pow_mod_orderOf a (k * k)
      rw [ha, hkk, pow_one] at this
      exact this
    have hab' : a = (a ^ k) ^ k := by
      calc a = a ^ (k * k) := hak
        _ = (a ^ k) ^ k := pow_mul a k k
    rw [h, ← pow_mul] at hab'
    rw [hab']
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) _
  have hinvA : ∀ n : ℕ, (a ^ n)⁻¹ = a ^ (2 * n) := fun n =>
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_add, show n + 2 * n = 3 * n by ring, pow_mul, ha3, one_pow])
  have hinvB : ∀ n : ℕ, (b ^ n)⁻¹ = b ^ (2 * n) := fun n =>
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_add, show n + 2 * n = 3 * n by ring, pow_mul, hb3, one_pow])
  have hkey : ∀ n k n' k' : ℕ, a ^ n * b ^ k = a ^ n' * b ^ k' →
      a ^ (2 * n' + n) = b ^ (k' + 2 * k) := by
    intro n k n' k' h
    have h1 : a ^ n = a ^ n' * b ^ k' * (b ^ k)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact h
    have h2 : (a ^ n')⁻¹ * a ^ n = b ^ k' * (b ^ k)⁻¹ := by
      rw [h1, ← mul_assoc, inv_mul_cancel_left]
    rw [hinvA, hinvB] at h2
    rw [← pow_add, ← pow_add] at h2
    exact h2
  have hswap : ∀ n k n' k' : ℕ, (a ^ n) * (b ^ k) * ((a ^ n') * (b ^ k'))
      = a ^ (n + n') * b ^ (k + k') := by
    intro n k n' k'
    have hc : b ^ k * a ^ n' = a ^ n' * b ^ k := ((hab.pow_pow n' k).eq).symm
    calc a ^ n * b ^ k * (a ^ n' * b ^ k')
        = a ^ n * (b ^ k * a ^ n') * b ^ k' := by simp only [mul_assoc]
      _ = a ^ n * (a ^ n' * b ^ k) * b ^ k' := by rw [hc]
      _ = a ^ n * a ^ n' * (b ^ k * b ^ k') := by simp only [mul_assoc]
      _ = a ^ (n + n') * b ^ (k + k') := by rw [pow_add, pow_add]
  let E : Subgroup G :=
    { carrier := {g | ∃ n k : ℕ, g = a ^ n * b ^ k}
      mul_mem' := by
        rintro _ _ ⟨n, k, rfl⟩ ⟨n', k', rfl⟩
        exact ⟨n + n', k + k', hswap n k n' k'⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, k, rfl⟩
        refine ⟨2 * n, 2 * k, ?_⟩
        rw [mul_inv_rev, hinvA, hinvB]
        exact ((hab.pow_pow (2 * n) (2 * k)).eq).symm }
  have hmem : ∀ g, g ∈ E ↔ ∃ n k : ℕ, g = a ^ n * b ^ k := fun g => Iff.rfl
  refine ⟨E, ?_, ?_⟩
  · intro g hg
    obtain ⟨n, k, rfl⟩ := (hmem g).mp hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hc : Commute a (a ^ n * b ^ k) :=
      ((Commute.refl a).pow_right n).mul_right (hab.pow_right k)
    exact hc.eq
  · have hbij : Function.Bijective
        (fun p : Fin 3 × Fin 3 => (⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), (hmem _).mpr
          ⟨_, _, rfl⟩⟩ : E)) := by
      constructor
      · rintro ⟨i, j⟩ ⟨i', j'⟩ h
        have h' : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (i' : ℕ) * b ^ (j' : ℕ) :=
          congrArg Subtype.val h
        have hk := hkey _ _ _ _ h'
        have h1 : a ^ (2 * (i' : ℕ) + (i : ℕ)) = 1 := hfix _ _ hk
        have h2 : b ^ ((j' : ℕ) + 2 * (j : ℕ)) = 1 := by rw [← hk]; exact h1
        have h3 := hdvd_a _ h1
        have h4 := hdvd_b _ h2
        have hi := i.isLt
        have hi' := i'.isLt
        have hj := j.isLt
        have hj' := j'.isLt
        refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
        · show (i : ℕ) = (i' : ℕ)
          omega
        · show (j : ℕ) = (j' : ℕ)
          omega
      · rintro ⟨g, hg⟩
        obtain ⟨n, k, rfl⟩ := (hmem g).mp hg
        refine ⟨(⟨n % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩),
          Subtype.ext ?_⟩
        have ha' := pow_mod_orderOf a n
        have hb' := pow_mod_orderOf b k
        rw [ha] at ha'
        rw [hb] at hb'
        show a ^ (n % 3) * b ^ (k % 3) = a ^ n * b ^ k
        rw [ha', hb']
    have := Nat.card_eq_of_bijective _ hbij
    rw [← this]
    simp

theorem nine_dvd_card_centralizer_of_orderOf_eq_three {G : Type*} [Group G] [Finite G]
    (h9 : 9 ∣ Nat.card G) {u : G} (hu : orderOf u = 3) :
    9 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨P, hPu⟩ := IsPGroup.exists_le_sylow hZ
  have huQ : u ∈ (P : Subgroup G) := hPu (Subgroup.mem_zpowers u)
  have h9Q : 9 ∣ Nat.card (P : Subgroup G) := by
    have := P.pow_dvd_card_of_pow_dvd_card (n := 2) (by norm_num; exact h9)
    norm_num at this
    exact this
  have hQ : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  have hQpos : 9 ≤ Nat.card (P : Subgroup G) :=
    Nat.le_of_dvd (Nat.card_pos) h9Q
  have : Nontrivial (P : Subgroup G) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  by_cases huc : (⟨u, huQ⟩ : (P : Subgroup G)) ∈ Subgroup.center (P : Subgroup G)
  ·
    have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hc : g * u = u * g :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp huc ⟨g, hg⟩)
      exact hc.symm
    exact dvd_trans h9Q (Subgroup.card_dvd_of_le hle)
  ·
    have : Nontrivial (Subgroup.center (P : Subgroup G)) :=
      IsPGroup.center_nontrivial hQ
    obtain ⟨w, hw⟩ : ∃ w : (P : Subgroup G), w ∈ Subgroup.center (P : Subgroup G) ∧ w ≠ 1 := by
      obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center (P : Subgroup G))
      exact ⟨w, w.2, fun h => hw (Subtype.ext h)⟩
    obtain ⟨hwc, hw1⟩ := hw
    obtain ⟨k, hk⟩ := hQ.exists_orderOf_eq_pow w
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 : orderOf w = 1 := by rw [hk, pow_zero]
      exact hw1 (orderOf_eq_one_iff.mp h1)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z, hzdef⟩ : ∃ z : (P : Subgroup G), z = w ^ (3 ^ j) := ⟨_, rfl⟩
    have hnot : ¬ z ^ 3 ^ 0 = 1 := by
      rw [pow_zero, pow_one, hzdef]
      intro h1
      have hd := orderOf_dvd_of_pow_eq_one h1
      rw [hk] at hd
      have hle := Nat.le_of_dvd (by positivity) hd
      have hlt : 3 ^ j < 3 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j)
      omega
    have hfin : z ^ 3 ^ (0 + 1) = 1 := by
      have e : 3 ^ j * 3 ^ (0 + 1) = 3 ^ (j + 1) := by ring
      rw [hzdef, ← pow_mul, e, ← hk]
      exact pow_orderOf_eq_one w
    have hz3 : orderOf z = 3 := by
      have h := orderOf_eq_prime_pow hnot hfin
      simpa using h
    have hzc : z ∈ Subgroup.center (P : Subgroup G) := by
      rw [hzdef]
      exact Subgroup.pow_mem _ hwc _
    have hz3G : orderOf (z : G) = 3 := (Subgroup.orderOf_coe z).trans hz3
    have hcomm' : u * (z : G) = (z : G) * u :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨u, huQ⟩)
    have hcomm : Commute u (z : G) := hcomm'
    have hnotG : u ∉ Subgroup.zpowers (z : G) := by
      intro hmem
      apply huc
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hem : (⟨u, huQ⟩ : (P : Subgroup G)) = z ^ m :=
        Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
      rw [hem]
      exact Subgroup.zpow_mem _ hzc m
    obtain ⟨E, hEle, hEcard⟩ := exists_nine_le_centralizer_of_orderOf_three hu hz3G hcomm hnotG
    have hdvd := Subgroup.card_dvd_of_le hEle
    rwa [hEcard] at hdvd

end CFSG.HardMathSupport.Curtis.Proving
