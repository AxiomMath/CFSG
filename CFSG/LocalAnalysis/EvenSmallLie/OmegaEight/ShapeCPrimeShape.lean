module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Sylow

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup

variable {G : Type*} [Group G] {t c : G} {L N : Subgroup G}

theorem mul_self_of_orderOf (ht : orderOf t = 2) : t * t = 1 := by
  rw [← pow_two, ← ht, pow_orderOf_eq_one]

theorem c_comm_t (hc : c * c = t) : c * t = t * c := by rw [← hc, mul_assoc]

theorem exists_mem_N (ht : orderOf t = 2) (hc : c * c = t) (hcN : c ∈ normalizer (N : Set G))
    {h : G} (hh : h ∈ N ⊔ zpowers c) :
    ∃ n ∈ N, h = n ∨ h = n * c ∨ h = n * t ∨ h = n * (c * t) := by
  have hle : zpowers c ≤ normalizer (N : Set G) := zpowers_le.2 hcN
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left N (zpowers c) hle] at hh
  obtain ⟨n, hn, z, hz, rfl⟩ := hh
  obtain ⟨k, rfl⟩ := hz
  have h4 : c ^ (4 : ℕ) = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_two c, hc, pow_two, mul_self_of_orderOf ht]
  refine ⟨n, hn, ?_⟩
  change n * c ^ k = n ∨ n * c ^ k = n * c ∨ n * c ^ k = n * t ∨ n * c ^ k = n * (c * t)
  rw [zpow_eq_zpow_emod' k h4]
  have hcases : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨ k % ((4 : ℕ) : ℤ) = 2 ∨
      k % ((4 : ℕ) : ℤ) = 3 := by omega
  rcases hcases with h | h | h | h <;> rw [h]
  · exact Or.inl (by rw [zpow_zero, mul_one])
  · exact Or.inr (Or.inl (by rw [zpow_one]))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, pow_two, hc]
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, pow_succ, pow_two, hc, c_comm_t hc]

theorem sq_mem_N_mul_t (ht : orderOf t = 2) (hc : c * c = t)
    (hNt : N ≤ centralizer ({t} : Set G)) (hcN : c ∈ normalizer (N : Set G)) {n : G}
    (hn : n ∈ N) :
    (∃ m ∈ N, n * c * (n * c) = m * t) ∧ ∃ m ∈ N, n * (c * t) * (n * (c * t)) = m * t := by
  have hm : c * n * c⁻¹ ∈ N := (mem_normalizer_iff.1 hcN n).1 hn
  have htt := mul_self_of_orderOf ht
  refine ⟨⟨n * (c * n * c⁻¹), mul_mem hn hm, ?_⟩, ⟨n * (c * n * c⁻¹), mul_mem hn hm, ?_⟩⟩
  · calc n * c * (n * c) = n * (c * n * c⁻¹) * (c * c) := by group
      _ = n * (c * n * c⁻¹) * t := by rw [hc]
  · have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 (hNt hn)
    calc n * (c * t) * (n * (c * t)) = n * c * (t * n) * c * t := by group
      _ = n * c * (n * t) * c * t := by rw [hnt]
      _ = n * (c * n * c⁻¹) * (c * (t * c)) * t := by group
      _ = n * (c * n * c⁻¹) * (c * (c * t)) * t := by rw [c_comm_t hc]
      _ = n * (c * n * c⁻¹) * ((c * c) * (t * t)) := by group
      _ = n * (c * n * c⁻¹) * t := by rw [hc, htt, mul_one]

theorem mem_sup_t_iff (ht : orderOf t = 2) (hNt : N ≤ centralizer ({t} : Set G)) {x : G} :
    x ∈ N ⊔ zpowers t ↔ ∃ n ∈ N, x = n ∨ x = n * t := by
  have htt := mul_self_of_orderOf ht
  have hz : ∀ z ∈ zpowers t, z = 1 ∨ z = t := by
    rintro z ⟨k, rfl⟩
    change t ^ k = 1 ∨ t ^ k = t
    rw [← zpow_mod_orderOf, ht]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h]
    · exact Or.inl (zpow_zero t)
    · exact Or.inr (zpow_one t)
  constructor
  · intro hx
    obtain ⟨n, hn, z, hzt, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => by
        rcases hz b hb with rfl | rfl
        · rw [mul_one, one_mul]
        · exact mem_centralizer_singleton_iff.1 (hNt ha)) hx
    rcases hz z hzt with rfl | rfl
    · exact ⟨n, hn, Or.inl (mul_one n)⟩
    · exact ⟨n, hn, Or.inr rfl⟩
  · rintro ⟨n, hn, rfl | rfl⟩
    · exact mem_sup_left hn
    · exact mul_mem (mem_sup_left hn) (mem_sup_right (mem_zpowers t))

theorem mul_self_mem_N (ht : orderOf t = 2) (hNt : N ≤ centralizer ({t} : Set G)) {x : G}
    (hx : x ∈ N ⊔ zpowers t) : x * x ∈ N := by
  obtain ⟨n, hn, rfl | rfl⟩ := (mem_sup_t_iff ht hNt).1 hx
  · exact mul_mem hn hn
  · have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 (hNt hn)
    have h : n * t * (n * t) = n * n * (t * t) := by
      rw [mul_assoc n t, ← mul_assoc t n, ← hnt, mul_assoc n t t, ← mul_assoc n n]
    rw [h, mul_self_of_orderOf ht, mul_one]
    exact mul_mem hn hn

theorem ShapeCPrime.of_sup (ht : orderOf t = 2) (hc : c * c = t) (hLN : L ≤ N)
    (hNt : N ≤ centralizer ({t} : Set G)) (htN : t ∉ N) (hcN : c ∈ normalizer (N : Set G))
    (hH : centralizer ({t} : Set G) = N ⊔ zpowers c) (hodd : ∀ x ∈ N, x * x ∈ L → x ∈ L) :
    ShapeCPrime t L c := by
  have htt := mul_self_of_orderOf ht
  have hcNt : c ∉ N ⊔ zpowers t := fun h => htN (hc ▸ mul_self_mem_N ht hNt h)
  have htNt : t ∈ N ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hnc : ∀ n ∈ N, n * c ∉ N ⊔ zpowers t := fun n hn h =>
    hcNt (by simpa using mul_mem (inv_mem (mem_sup_left hn)) h)
  have hnct : ∀ n ∈ N, n * (c * t) ∉ N ⊔ zpowers t := fun n hn h =>
    hcNt (by simpa [mul_assoc] using mul_mem (mul_mem (inv_mem (mem_sup_left hn)) h) (inv_mem htNt))
  refine ⟨ht, hc, fun h => htN (hLN h), hLN.trans hNt, ?_, ?_⟩
  · intro h hh h2
    rw [hH] at hh
    obtain ⟨n, hn, rfl | rfl | rfl | rfl⟩ := exists_mem_N ht hc hcN hh
    · exact mem_sup_left (hodd h hn (h2 ▸ one_mem L))
    · obtain ⟨m, hm, hmt⟩ := (sq_mem_N_mul_t ht hc hNt hcN hn).1
      rw [hmt] at h2
      exact absurd (by rw [eq_inv_of_mul_eq_one_right h2]; exact inv_mem hm) htN
    · have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 (hNt hn)
      have hnn : n * n = 1 := by
        have h : n * t * (n * t) = n * n * (t * t) := by
          rw [mul_assoc n t, ← mul_assoc t n, ← hnt, mul_assoc n t t, ← mul_assoc n n]
        rwa [h, htt, mul_one] at h2
      exact mul_mem (mem_sup_left (hodd n hn (hnn ▸ one_mem L))) (mem_sup_right (mem_zpowers t))
    · obtain ⟨m, hm, hmt⟩ := (sq_mem_N_mul_t ht hc hNt hcN hn).2
      rw [hmt] at h2
      exact absurd (by rw [eq_inv_of_mul_eq_one_right h2]; exact inv_mem hm) htN
  · intro hmem
    apply htN
    refine (closure_le N).2 (fun g hg => ?_) hmem
    obtain ⟨hgt, k, hk⟩ := hg
    have hgC : g ∈ N ⊔ zpowers c := hH ▸ mem_centralizer_singleton_iff.2 hgt
    have hg1 : g = (g * g) ^ (k + 1) := by
      have h1 : g ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one g
      calc g = g ^ (2 * k + 1) * g := by rw [h1, one_mul]
        _ = (g * g) ^ (k + 1) := by rw [← pow_two, ← pow_mul, ← pow_succ]; ring_nf
    obtain ⟨n, hn, h | h | h | h⟩ := exists_mem_N ht hc hcN hgC
    · rw [h]; exact hn
    · exfalso
      obtain ⟨m, hm, hmt⟩ := (sq_mem_N_mul_t ht hc hNt hcN hn).1
      have : g ∈ N ⊔ zpowers t := by
        rw [hg1, h, hmt]
        exact pow_mem (mul_mem (mem_sup_left hm) htNt) _
      exact hnc n hn (h ▸ this)
    · exfalso
      have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 (hNt hn)
      have h1 : g ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one g
      rw [h, (Commute.mul_pow hnt _), pow_succ t, pow_mul t, pow_two, htt, one_pow,
        one_mul] at h1
      exact htN (by rw [eq_inv_of_mul_eq_one_right h1]; exact inv_mem (pow_mem hn _))
    · exfalso
      obtain ⟨m, hm, hmt⟩ := (sq_mem_N_mul_t ht hc hNt hcN hn).2
      have : g ∈ N ⊔ zpowers t := by
        rw [hg1, h, hmt]
        exact pow_mem (mul_mem (mem_sup_left hm) htNt) _
      exact hnct n hn (h ▸ this)

theorem mem_of_pow_two_pow {x : G} (hx : x ∈ N) (hodd : ∀ x ∈ N, x * x ∈ L → x ∈ L) :
    ∀ k : ℕ, x ^ 2 ^ k ∈ L → x ∈ L := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro h
    apply ih
    apply hodd _ (pow_mem hx _)
    rwa [← pow_two, ← pow_mul, ← pow_succ]

theorem sylow_of_sup (hcN : c ∈ normalizer (N : Set G))
    (hH : centralizer ({t} : Set G) = N ⊔ zpowers c) (hodd : ∀ x ∈ N, x * x ∈ L → x ∈ L)
    {U : Subgroup G} (hUL : U ≤ L)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) :
    ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
      U ⊔ zpowers c ≤ V → V = U ⊔ zpowers c := by
  intro V hVH hV hUV
  refine le_antisymm (fun v hv => ?_) hUV
  have hle : zpowers c ≤ normalizer (N : Set G) := zpowers_le.2 hcN
  have hvH := hVH hv
  rw [hH, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left N (zpowers c) hle] at hvH
  obtain ⟨n, hn, z, hz, hvz⟩ := hvH
  have hzV : z ∈ V := hUV (mem_sup_right hz)
  have hnV : n ∈ V := by
    have := mul_mem hv (inv_mem hzV)
    rwa [← hvz, mul_inv_cancel_right] at this
  have hnL : n ∈ L := by
    obtain ⟨k, hk⟩ := hV ⟨n, hnV⟩
    have h1 : n ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact mem_of_pow_two_pow hn hodd k (h1 ▸ one_mem L)
  have hVL := hUmax (V ⊓ L) inf_le_right (hV.to_le inf_le_left)
    (le_inf (le_sup_left.trans hUV) hUL)
  have hnU : n ∈ U := hVL ▸ Subgroup.mem_inf.2 ⟨hnV, hnL⟩
  rw [← hvz]
  exact mul_mem (mem_sup_left hnU) (mem_sup_right hz)

theorem normalizer_E_of_sup (ht : orderOf t = 2) (hc : c * c = t) (htL : t ∉ L)
    (hLt : L ≤ centralizer ({t} : Set G)) (hH : centralizer ({t} : Set G) = N ⊔ zpowers c)
    (hcN : c ∈ normalizer (N : Set G)) (hNL : N ≤ normalizer (L : Set G)) {Q : Subgroup G}
    (hQL : Q ≤ L) (hcQ : c ∈ normalizer (Q : Set G))
    (hNQ : ∀ n ∈ N, n ∈ normalizer (Q : Set G) → n ∈ L) :
    centralizer ({t} : Set G) ⊓ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤
      (L ⊓ normalizer (Q : Set G)) ⊔ zpowers c := by
  intro h hh
  obtain ⟨hht, hhE⟩ := Subgroup.mem_inf.1 hh
  have hle : zpowers c ≤ normalizer (N : Set G) := zpowers_le.2 hcN
  rw [hH, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left N (zpowers c) hle] at hht
  obtain ⟨l, hl, z, hz, rfl⟩ := hht
  have hcE : c ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    Stage1.mem_normalizer_sup hcQ (Stage1.mem_normalizer_zpowers (c_comm_t hc))
  have hzE : z ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    zpowers_le.2 hcE hz
  have hlE : l ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
    have := mul_mem hhE (inv_mem hzE)
    rwa [mul_inv_cancel_right] at this
  have hEL : ∀ x ∈ Q ⊔ zpowers t, x ∈ L → x ∈ Q := by
    intro x hx hxL
    obtain ⟨q, hq, rfl | rfl⟩ := (mem_sup_t_iff ht (hQL.trans hLt)).1 hx
    · exact hq
    · exact absurd (by simpa using mul_mem (inv_mem (hQL hq)) hxL) htL
  have hconj : ∀ g ∈ normalizer (L : Set G),
      g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) → ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
    fun g hg hgE q hq =>
    hEL _ ((mem_normalizer_iff.1 hgE q).1 (mem_sup_left hq))
      ((mem_normalizer_iff.1 hg q).1 (hQL hq))
  have hlQ : l ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 fun q => ⟨fun hq => hconj l (hNL hl) hlE q hq, fun hq => ?_⟩
    have := hconj l⁻¹ (inv_mem (hNL hl)) (inv_mem hlE) _ hq
    simpa [mul_assoc] using this
  exact mul_mem (mem_sup_left ⟨hNQ l hl hlQ, hlQ⟩) (mem_sup_right hz)

end CFSG.EvenSmallLie.OmegaEight.CPrime
