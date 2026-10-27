module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixA

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp

variable {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} {v u₀ y₀ : G}

structure GoodCore (C : SixAY t u P V v u₀ y₀) (x : G) (n : ℕ) : Prop where
  dih : I21.DihRel t x
  ord : orderOf x = 2 ^ (n - 1)
  three_le : 3 ≤ n
  x_mem : x ∈ P
  u₀_x : u₀ * x = x * u₀
  y₀_mem : y₀ ∈ zpowers x

structure Good (C : SixAY t u P V v u₀ y₀) (x : G) (n : ℕ) : Prop extends GoodCore C x n where
  gen : closure ({t, x} : Set G) =
    closure {s : G | TConj t s ∧ s ∈ closure ({t, x} : Set G)}
  no_mixed : ∀ (s : G) (k : ℤ) (q : G), q ∈ closure ({t, x} : Set G) → TConj t s →
    s = u₀ ^ k * q → s ∈ closure ({t, x} : Set G)

namespace GoodCore

variable {C : SixAY t u P V v u₀ y₀} {x : G} {n : ℕ} (hG : GoodCore C x n)

include hG

theorem zx_eq : x ^ 2 ^ (n - 2) = u ^ 2 := by
  have h := C.secTwo
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hG.y₀_mem
  have h2 : x ^ (k * 2) = u ^ 2 := by rw [zpow_mul, zpow_ofNat, hk, C.y₀_sq]
  have hsq : (x ^ (k * 2)) ^ 2 = 1 := by rw [h2]; exact h.z_sq
  rcases I21.eq_one_or_eq_z_of_sq_eq_one hG.ord (by have := hG.three_le; omega) (k * 2) hsq with
    h1 | h1
  · exact absurd (h2 ▸ h1) h.z_ne_one
  · rw [← h1, h2]

theorem Q_le_P : closure ({t, x} : Set G) ≤ P := by
  rw [closure_le]
  intro g hg
  rcases hg with h1 | h1
  · rw [h1]; exact C.R_le SecTwoHyp.t_mem_R
  · rw [h1]; exact hG.x_mem

theorem u₀_comm {q : G} (hq : q ∈ closure ({t, x} : Set G)) : u₀ * q = q * u₀ := by
  have hle : closure ({t, x} : Set G) ≤ centralizer ({u₀} : Set G) := by
    rw [closure_le]
    intro g hg
    rcases hg with h1 | h1
    · rw [h1, SetLike.mem_coe, mem_centralizer_singleton_iff]; exact C.t_u₀
    · rw [h1, SetLike.mem_coe, mem_centralizer_singleton_iff]; exact hG.u₀_x.symm
  exact (mem_centralizer_singleton_iff.mp (hle hq)).symm

theorem y₀_inv : y₀⁻¹ = y₀ * u ^ 2 := by
  have h := C.secTwo
  refine inv_eq_of_mul_eq_one_right ?_
  calc y₀ * (y₀ * u ^ 2) = y₀ ^ 2 * u ^ 2 := by rw [pow_two y₀, mul_assoc]
    _ = u ^ 2 * u ^ 2 := by rw [C.y₀_sq]
    _ = 1 := by rw [← pow_add]; exact h.u_pow_four

theorem sq_eq_z {q : G} (hq : q ∈ closure ({t, x} : Set G)) (hq2 : q ^ 2 = u ^ 2) :
    q = y₀ ∨ q = y₀⁻¹ := by
  have h := C.secTwo
  rcases hG.dih.mem_closure_iff.mp hq with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hG.y₀_mem
    have hsq : (x ^ (k - m)) ^ 2 = 1 := by
      rw [← zpow_ofNat, ← zpow_mul, show (k - m) * 2 = k * 2 - m * 2 by ring, zpow_sub,
        zpow_mul, zpow_mul, zpow_ofNat, zpow_ofNat, hq2, hm, C.y₀_sq, mul_inv_cancel]
    rcases I21.eq_one_or_eq_z_of_sq_eq_one hG.ord (by have := hG.three_le; omega) (k - m)
      hsq with h1 | h1
    · left
      rw [zpow_sub, mul_inv_eq_one, hm] at h1
      exact h1
    · right
      rw [hG.zx_eq, zpow_sub, hm, mul_inv_eq_iff_eq_mul] at h1
      rw [y₀_inv hG, h1]
      exact (C.z_central C.y₀_mem_P).symm
  · exfalso
    have := hG.dih.refl_sq k
    rw [hq2] at this
    exact h.z_ne_one this

theorem Q_le_normalizer_U :
    closure ({t, x} : Set G) ≤ normalizer (zpowers u₀ : Set G) := by
  intro q hq
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  rintro g ⟨k, rfl⟩
  have hc : u₀ * q = q * u₀ := hG.u₀_comm hq
  exact (Commute.zpow_left (show Commute u₀ q from hc) k).eq

theorem mem_PP_iff {s : G} :
    s ∈ zpowers u₀ ⊔ closure ({t, x} : Set G) ↔
      ∃ (k : ℤ) (q : G), q ∈ closure ({t, x} : Set G) ∧ s = u₀ ^ k * q := by
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (zpowers u₀)
    (closure ({t, x} : Set G)) hG.Q_le_normalizer_U
  rw [← SetLike.mem_coe, hcoe, Set.mem_mul]
  constructor
  · rintro ⟨a, ⟨k, rfl⟩, q, hq, rfl⟩
    exact ⟨k, q, hq, rfl⟩
  · rintro ⟨k, q, hq, rfl⟩
    exact ⟨u₀ ^ k, ⟨k, rfl⟩, q, hq, rfl⟩

theorem PP_le_P : zpowers u₀ ⊔ closure ({t, x} : Set G) ≤ P :=
  sup_le ((zpowers_le).mpr C.u₀_mem_P) hG.Q_le_P

theorem R_le_PP : secTwoR t u ≤ zpowers u₀ ⊔ closure ({t, x} : Set G) := by
  intro r hr
  obtain ⟨a, b, rfl⟩ := C.R_nf hr
  have htQ : t ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  exact mul_mem (le_sup_right (a := zpowers u₀) (pow_mem htQ a))
    (le_sup_left (b := closure ({t, x} : Set G)) (pow_mem (mem_zpowers u₀) b))

theorem mem_U_of_centralizes {k : ℤ} {q : G} (hq : q ∈ closure ({t, x} : Set G))
    (hc : ∀ q' ∈ closure ({t, x} : Set G), (u₀ ^ k * q) * q' = q' * (u₀ ^ k * q)) :
    u₀ ^ k * q ∈ zpowers u₀ := by
  have h := C.secTwo
  have hqc : ∀ q' ∈ closure ({t, x} : Set G), q * q' = q' * q := by
    intro q' hq'
    have h1 := hc q' hq'
    have hu : u₀ ^ k * q' = q' * u₀ ^ k :=
      (Commute.zpow_left (show Commute u₀ q' from hG.u₀_comm hq') k).eq
    calc q * q' = (u₀ ^ k)⁻¹ * ((u₀ ^ k * q) * q') := by group
      _ = (u₀ ^ k)⁻¹ * (q' * (u₀ ^ k * q)) := by rw [h1]
      _ = (u₀ ^ k)⁻¹ * (q' * u₀ ^ k) * q := by group
      _ = (u₀ ^ k)⁻¹ * (u₀ ^ k * q') * q := by rw [hu]
      _ = q' * q := by group
  have htQ : t ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have hxQ : x ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have hn3 : 4 ≤ 2 ^ (n - 1) := by
    have := hG.three_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hG.dih.mem_closure_iff.mp hq with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hcomm : t * x ^ j = x ^ j * t := (hqc t htQ).symm
    have h2 := (hG.dih.commute_zpow_iff j).mp hcomm
    rcases I21.eq_one_or_eq_z_of_sq_eq_one hG.ord (by have := hG.three_le; omega) j h2 with
      h1 | h1
    · rw [h1, mul_one]; exact zpow_mem (mem_zpowers u₀) k
    · rw [h1, hG.zx_eq, ← C.u₀_sq]
      exact mul_mem (zpow_mem (mem_zpowers u₀) k) (pow_mem (mem_zpowers u₀) 2)
  · exfalso
    have hcx : (t * x ^ j) * x = x * (t * x ^ j) := hqc x hxQ
    have h1 : x ^ (j + 1) = x ^ (j - 1) := by
      have e1 : (t * x ^ j) * x = t * x ^ (j + 1) := by rw [mul_assoc, ← zpow_add_one]
      have e2 : x * (t * x ^ j) = t * x ^ (-1 + j) := by
        rw [← mul_assoc]
        have := hG.dih.zpow_mul_t 1
        rw [zpow_one] at this
        rw [this, mul_assoc, ← zpow_add]
      rw [e1, e2] at hcx
      have := mul_left_cancel hcx
      rw [this]; ring_nf
    have h2 : x ^ 2 = 1 := by
      have : x ^ (j + 1) * (x ^ (j - 1))⁻¹ = 1 := by rw [h1, mul_inv_cancel]
      rw [← zpow_neg, ← zpow_add] at this
      have h3 : (j + 1 + -(j - 1)) = 2 := by ring
      rw [h3] at this
      simpa using this
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hG.ord] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem y₀_mem_Q : y₀ ∈ closure ({t, x} : Set G) := by
  have : zpowers x ≤ closure ({t, x} : Set G) := by
    rw [zpowers_le]; exact subset_closure (by simp)
  exact this hG.y₀_mem

theorem sq_u₀_zpow_mul {q : G} (hq : q ∈ closure ({t, x} : Set G)) (k : ℤ) :
    (u₀ ^ k * q) ^ 2 = u₀ ^ (2 * k) * q ^ 2 := by
  have hc : u₀ ^ k * q = q * u₀ ^ k :=
    (Commute.zpow_left (show Commute u₀ q from hG.u₀_comm hq) k).eq
  rw [pow_two, pow_two]
  calc u₀ ^ k * q * (u₀ ^ k * q) = u₀ ^ k * (q * u₀ ^ k) * q := by group
    _ = u₀ ^ k * (u₀ ^ k * q) * q := by rw [hc]
    _ = u₀ ^ (2 * k) * q * q := by
      rw [← mul_assoc, ← zpow_add, two_mul]
    _ = u₀ ^ (2 * k) * (q * q) := by group

theorem no_mixed' {s q : G} {k : ℤ} (hq : q ∈ closure ({t, x} : Set G)) (hs : TConj t s)
    (hsq : s = u₀ ^ k * q) : s ∈ closure ({t, x} : Set G) := by
  have h := C.secTwo
  have hyQ := hG.y₀_mem_Q
  have hz : u ^ 2 ∈ closure ({t, x} : Set G) := by
    rw [← C.y₀_sq]; exact pow_mem hyQ 2
  have hs2 : s ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := hs
    rw [conj_pow, h.t_sq]; group
  have hk : u₀ ^ k = u₀ ^ (k % 4) := by
    rw [← zpow_mod_orderOf, C.u₀_order]; rfl
  have hu₀z : u₀ ^ (2 : ℤ) = u ^ 2 := by rw [zpow_ofNat, C.u₀_sq]
  have hu₀3 : u₀ ^ (3 : ℤ) = u₀ * u ^ 2 := by
    rw [zpow_ofNat, show u₀ ^ 3 = u₀ * u₀ ^ 2 by group, C.u₀_sq]
  have hzc : ∀ p : G, p ∈ P → p * u ^ 2 = u ^ 2 * p := fun p hp => C.z_central hp
  have hw₁ := C.u₀_y₀_mem_V
  have hzV := C.z_mem_V
  have hyinv := hG.y₀_inv
  have hodd : ∀ m : ℤ, (m = 1 ∨ m = 3) → s = u₀ ^ m * q → False := by
    intro m hm hsm
    have hsq2 : (u₀ ^ m * q) ^ 2 = u ^ 2 * q ^ 2 := by
      rw [hG.sq_u₀_zpow_mul hq m]
      rcases hm with rfl | rfl
      · rw [show 2 * (1 : ℤ) = 2 by norm_num, hu₀z]
      · rw [show 2 * (3 : ℤ) = 6 by norm_num, show (6 : ℤ) = 2 + 4 by norm_num, zpow_add, hu₀z,
          zpow_ofNat, C.u₀_four, mul_one]
    have hq2 : q ^ 2 = u ^ 2 := by
      rw [hsm] at hs2
      rw [hsq2] at hs2
      have := eq_inv_of_mul_eq_one_right hs2
      rw [this]; exact h.z_inv
    have hqy := hG.sq_eq_z hq hq2
    have hyP := C.y₀_mem_P
    have hzz : u ^ 2 * u ^ 2 = 1 := by rw [← pow_add]; exact h.u_pow_four
    have hw : u₀ * y₀ * u ^ 2 ∈ V := mul_mem hw₁ hzV
    have hsV : s ∈ V := by
      rw [hsm]
      rcases hm with hm1 | hm1 <;> rcases hqy with hq1 | hq1 <;> rw [hm1, hq1]
      · rw [zpow_one]; exact hw₁
      · rw [zpow_one, hyinv, ← mul_assoc]; exact hw
      · rw [hu₀3]
        have e : u₀ * u ^ 2 * y₀ = u₀ * y₀ * u ^ 2 := by
          calc u₀ * u ^ 2 * y₀ = u₀ * (u ^ 2 * y₀) := by rw [mul_assoc]
            _ = u₀ * (y₀ * u ^ 2) := by rw [hzc y₀ hyP]
            _ = u₀ * y₀ * u ^ 2 := by rw [mul_assoc]
        rw [e]; exact hw
      · rw [hu₀3, hyinv]
        have e : u₀ * u ^ 2 * (y₀ * u ^ 2) = u₀ * y₀ := by
          calc u₀ * u ^ 2 * (y₀ * u ^ 2) = u₀ * (u ^ 2 * y₀) * u ^ 2 := by simp only [mul_assoc]
            _ = u₀ * (y₀ * u ^ 2) * u ^ 2 := by rw [hzc y₀ hyP]
            _ = u₀ * y₀ * (u ^ 2 * u ^ 2) := by simp only [mul_assoc]
            _ = u₀ * y₀ := by rw [hzz, mul_one]
        rw [e]; exact hw₁
    exact C.V_no_tConj hsV hs
  have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hcases with h0 | h0 | h0 | h0
  · rw [hsq, hk, h0, zpow_zero, one_mul]; exact hq
  · exact (hodd 1 (Or.inl rfl) (by rw [hsq, hk, h0])).elim
  · rw [hsq, hk, h0, hu₀z]; exact mul_mem hz hq
  · exact (hodd 3 (Or.inr rfl) (by rw [hsq, hk, h0])).elim

end GoodCore

section ElemAbelianInsert

variable {K : Type*} [Group K]

theorem sq_eq_one_of_mem_closure_insert {V : Subgroup K} (hV : IsElemAbelian 2 V) {s : K}
    (hs2 : s ^ 2 = 1) (hcomm : ∀ v ∈ V, s * v = v * s) :
    ∀ e ∈ closure ((V : Set K) ∪ {s}), e ^ 2 = 1 := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hs2)
  have hsc : ∀ (c : ℕ) (v : K), v ∈ V → s ^ c * v = v * s ^ c := fun c v hv =>
    (Commute.pow_left (show Commute s v from hcomm v hv) c).eq
  have key : ∀ e ∈ closure ((V : Set K) ∪ {s}), ∃ v ∈ V, ∃ c : ℕ, e = v * s ^ c := by
    intro e he
    refine closure_induction (p := fun e _ => ∃ v ∈ V, ∃ c : ℕ, e = v * s ^ c) ?_ ?_ ?_ ?_ he
    · rintro g (hg | hg)
      · exact ⟨g, hg, 0, by simp⟩
      · rw [Set.mem_singleton_iff] at hg
        exact ⟨1, one_mem V, 1, by simp [hg]⟩
    · exact ⟨1, one_mem V, 0, by simp⟩
    · rintro a b - - ⟨v, hv, c, rfl⟩ ⟨v', hv', c', rfl⟩
      refine ⟨v * v', mul_mem hv hv', c + c', ?_⟩
      calc v * s ^ c * (v' * s ^ c') = v * (s ^ c * v') * s ^ c' := by group
        _ = v * (v' * s ^ c) * s ^ c' := by rw [hsc c v' hv']
        _ = v * v' * s ^ (c + c') := by rw [pow_add]; group
    · rintro a - ⟨v, hv, c, rfl⟩
      refine ⟨v⁻¹, inv_mem hv, c, ?_⟩
      have hsq : (s ^ c) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hs2, one_pow]
      have hsci : (s ^ c)⁻¹ = s ^ c := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq)
      calc (v * s ^ c)⁻¹ = (s ^ c)⁻¹ * v⁻¹ := by rw [mul_inv_rev]
        _ = s ^ c * v⁻¹ := by rw [hsci]
        _ = v⁻¹ * s ^ c := hsc c v⁻¹ (inv_mem hv)
  intro e he
  obtain ⟨v, hv, c, rfl⟩ := key e he
  have hv2 : v ^ 2 = 1 := hV.2 v hv
  have hsq : (s ^ c) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hs2, one_pow]
  rw [pow_two, show v * s ^ c * (v * s ^ c) = v * (s ^ c * v) * s ^ c by group, hsc c v hv]
  calc v * (v * s ^ c) * s ^ c = (v * v) * (s ^ c * s ^ c) := by simp only [mul_assoc]
    _ = v ^ 2 * (s ^ c) ^ 2 := by rw [← pow_two, ← pow_two]
    _ = 1 := by rw [hv2, hsq, one_mul]

end ElemAbelianInsert

namespace Good

variable {C : SixAY t u P V v u₀ y₀} {x : G} {n : ℕ} (hG : Good C x n)

include hG

omit hG in
theorem conj_Q_of_gens (hG : Good C x n) (s : G)
    (hgens : ∀ g : G, TConj t g → g ∈ closure ({t, x} : Set G) →
      s * g * s⁻¹ ∈ closure ({t, x} : Set G))
    {q : G} (hq : q ∈ closure ({t, x} : Set G)) : s * q * s⁻¹ ∈ closure ({t, x} : Set G) := by
  rw [hG.gen] at hq
  refine closure_induction (p := fun q _ => s * q * s⁻¹ ∈ closure ({t, x} : Set G))
    ?_ ?_ ?_ ?_ hq
  · rintro g ⟨hgT, hgQ⟩
    exact hgens g hgT hgQ
  · simpa using one_mem (closure ({t, x} : Set G))
  · rintro a b - - ha hb
    rw [show s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) by group]
    exact mul_mem ha hb
  · rintro a - ha
    rw [show s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ by group]
    exact inv_mem ha

theorem conj_Q_mem {s : G}
    (hsN : s ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x} : Set G) : Subgroup G) : Set G))
    {q : G} (hq : q ∈ closure ({t, x} : Set G)) : s * q * s⁻¹ ∈ closure ({t, x} : Set G) := by
  refine conj_Q_of_gens hG s ?_ hq
  intro g hgT hgQ
  have hP' : g ∈ zpowers u₀ ⊔ closure ({t, x} : Set G) := Subgroup.mem_sup_right hgQ
  have hmem : s * g * s⁻¹ ∈ zpowers u₀ ⊔ closure ({t, x} : Set G) :=
    (mem_normalizer_iff.mp hsN g).mp hP'
  obtain ⟨k, q', hq', hk⟩ := (hG.toGoodCore.mem_PP_iff).mp hmem
  exact hG.no_mixed' hq' (hgT.conj s) hk

theorem conj_u₀_mem {s : G}
    (hsN : s ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x} : Set G) : Subgroup G) : Set G)) :
    s * u₀ * s⁻¹ ∈ zpowers u₀ := by
  have hu₀P' : u₀ ∈ zpowers u₀ ⊔ closure ({t, x} : Set G) :=
    Subgroup.mem_sup_left (mem_zpowers u₀)
  have hmem : s * u₀ * s⁻¹ ∈ zpowers u₀ ⊔ closure ({t, x} : Set G) :=
    (mem_normalizer_iff.mp hsN u₀).mp hu₀P'
  obtain ⟨k, q, hq, hk⟩ := (hG.toGoodCore.mem_PP_iff).mp hmem
  rw [hk]
  refine hG.toGoodCore.mem_U_of_centralizes hq fun q' hq' => ?_
  rw [← hk]
  have hs : s⁻¹ * q' * s ∈ closure ({t, x} : Set G) := by
    have := hG.conj_Q_mem (inv_mem hsN) hq'
    simpa using this
  have hc := hG.u₀_comm hs
  calc s * u₀ * s⁻¹ * q' = s * (u₀ * (s⁻¹ * q' * s)) * s⁻¹ := by group
    _ = s * ((s⁻¹ * q' * s) * u₀) * s⁻¹ := by rw [hc]
    _ = q' * (s * u₀ * s⁻¹) := by group

theorem V_le_PP : V ≤ zpowers u₀ ⊔ closure ({t, x} : Set G) := by
  intro a ha
  have hz : u ^ 2 ∈ closure ({t, x} : Set G) := by
    rw [← C.y₀_sq]
    exact pow_mem (hG.y₀_mem_Q) 2
  have hw : u₀ * y₀ ∈ zpowers u₀ ⊔ closure ({t, x} : Set G) :=
    mul_mem (Subgroup.mem_sup_left (mem_zpowers u₀)) (Subgroup.mem_sup_right hG.y₀_mem_Q)
  have hzP : u ^ 2 ∈ zpowers u₀ ⊔ closure ({t, x} : Set G) := Subgroup.mem_sup_right hz
  rcases C.V_eq C.u₀_y₀_mem_V C.u₀_y₀_ne.1 C.u₀_y₀_ne.2 a ha with h1 | h1 | h1 | h1
  · rw [h1]; exact one_mem _
  · rw [h1]; exact hzP
  · rw [h1]; exact hw
  · rw [h1]; exact mul_mem hw hzP

theorem commute_u₀_ext {s : G} (hsP : s ∈ P) (hsT : TConj t s)
    (hsN : s ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x} : Set G) : Subgroup G) : Set G))
    (hsn : s ∉ zpowers u₀ ⊔ closure ({t, x} : Set G)) {x₁ : G} (hx₁ : x₁ = s * t)
    (hd₁ : I21.DihRel t x₁) (hy₁ : y₀ ∈ zpowers x₁) : s * u₀ * s⁻¹ = u₀ := by
  have h := C.secTwo
  have hs2 : s ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := hsT
    rw [conj_pow, h.t_sq]; group
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hs2)
  have hw₁V := C.u₀_y₀_mem_V
  have hw₁ne := C.u₀_y₀_ne
  have hne : s * (u₀ * y₀) * s⁻¹ ≠ u₀ * y₀ := by
    intro heq
    have hcV : ∀ a ∈ V, s * a = a * s := by
      intro a ha
      have hz : s * u ^ 2 = u ^ 2 * s := C.z_central hsP
      have hw : s * (u₀ * y₀) = (u₀ * y₀) * s := by
        calc s * (u₀ * y₀) = (s * (u₀ * y₀) * s⁻¹) * s := by group
          _ = (u₀ * y₀) * s := by rw [heq]
      rcases C.V_eq hw₁V hw₁ne.1 hw₁ne.2 a ha with h1 | h1 | h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact hz
      · rw [h1]; exact hw
      · rw [h1]
        calc s * (u₀ * y₀ * u ^ 2) = (s * (u₀ * y₀)) * u ^ 2 := by group
          _ = (u₀ * y₀) * s * u ^ 2 := by rw [hw]
          _ = (u₀ * y₀) * (s * u ^ 2) := by group
          _ = (u₀ * y₀) * (u ^ 2 * s) := by rw [hz]
          _ = u₀ * y₀ * u ^ 2 * s := by group
    have hK2 := sq_eq_one_of_mem_closure_insert C.V_elem hs2 hcV
    set K : Subgroup G := closure ((V : Set G) ∪ {s}) with hK
    have hKs : K ≤ centralizer ({s} : Set G) := by
      rw [hK, closure_le]
      rintro g (hg | hg)
      · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        exact (hcV g hg).symm
      · rw [Set.mem_singleton_iff] at hg
        rw [hg, SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hcard := h.card_le_four_conj hsT hK2 hKs
    have hsK : s ∈ K := subset_closure (Or.inr rfl)
    have hVK : V < K := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [hK]; intro a ha; exact subset_closure (Or.inl ha)
      · intro hVK'
        apply hsn
        have hsV : s ∈ V := hVK' ▸ hsK
        exact hG.V_le_PP hsV
    have := Subgroup.card_lt_of_lt hVK
    rw [C.V_card] at this
    omega
  have hsw : s * (u₀ * y₀) * s⁻¹ = u₀ * y₀ * u ^ 2 := by
    rcases C.toSixACtx.V_conj hw₁V hw₁ne.1 hw₁ne.2 hsP with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hsy : s * y₀ * s⁻¹ = y₀⁻¹ := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hy₁
    have hs_refl : s = t * x₁ ^ (-1 : ℤ) := by
      rw [zpow_neg_one, hx₁, mul_inv_rev, h.t_inv, hsi]
      calc s = t * t * s := by rw [h.t_mul_t, one_mul]
        _ = t * (t * s) := by rw [mul_assoc]
    have h1 := hd₁.refl_conj_rot (-1) m
    rw [← hs_refl, hm, zpow_neg, hm] at h1
    exact h1
  obtain ⟨e, he⟩ := mem_zpowers_iff.mp (hG.conj_u₀_mem hsN)
  have h5 : u₀ ^ e * y₀⁻¹ = u₀ * y₀⁻¹ := by
    calc u₀ ^ e * y₀⁻¹ = (s * u₀ * s⁻¹) * (s * y₀ * s⁻¹) := by rw [he, hsy]
      _ = s * (u₀ * y₀) * s⁻¹ := by group
      _ = u₀ * y₀ * u ^ 2 := hsw
      _ = u₀ * (y₀ * u ^ 2) := by rw [mul_assoc]
      _ = u₀ * y₀⁻¹ := by rw [← hG.y₀_inv]
  have h6 := mul_right_cancel h5
  rw [← he, h6]

omit hG in
theorem _root_.CFSG.LocalAnalysis.EvenBN.Tits.GoodCore.toGood
    {C : SixAY t u P V v u₀ y₀} {x : G} {n : ℕ} (hG : GoodCore C x n)
    (hgen : closure ({t, x} : Set G) =
      closure {s : G | TConj t s ∧ s ∈ closure ({t, x} : Set G)}) : Good C x n :=
  ⟨hG, hgen, fun _ _ _ hq hs hsq => hG.no_mixed' hq hs hsq⟩

theorem extend {s : G} (hsP : s ∈ P) (hsT : TConj t s)
    (hsN : s ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x} : Set G) : Subgroup G) : Set G))
    (hsn : s ∉ zpowers u₀ ⊔ closure ({t, x} : Set G)) :
    Good C (s * t) (n + 1) ∧ closure ({t, x} : Set G) < closure ({t, s * t} : Set G) := by
  have h := C.secTwo
  have hn3 := hG.three_le
  have hs2 : s ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := hsT
    rw [conj_pow, h.t_sq]; group
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hs2)
  have htQ : t ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have hxQ : x ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have htP : t ∈ P := C.R_le SecTwoHyp.t_mem_R
  have ht'Q : s * t * s⁻¹ ∈ closure ({t, x} : Set G) := hG.conj_Q_mem hsN htQ
  have ht'2 : (s * t * s⁻¹) ^ 2 = 1 := by rw [conj_pow, h.t_sq]; group
  obtain ⟨a, ha⟩ : ∃ a : ℤ, s * t * s⁻¹ = t * x ^ a := by
    rcases hG.dih.mem_closure_iff.mp ht'Q with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have h2 : (x ^ k) ^ 2 = 1 := by rw [← hk]; exact ht'2
      rcases I21.eq_one_or_eq_z_of_sq_eq_one hG.ord (by omega) k h2 with h1 | h1
      · apply h.t_ne_one
        have h3 : s * t * s⁻¹ = 1 := by rw [hk, h1]
        calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
          _ = 1 := by rw [h3]; group
      · exact C.z_not_tConj ⟨s, by rw [hk, h1, hG.zx_eq]⟩
    · exact ⟨k, hk⟩
  have hodd : Odd a := by
    by_contra hna
    rw [Int.not_odd_iff_even] at hna
    obtain ⟨j, hj⟩ := hna
    have hc := hG.dih.conj_t_x_zpow (-j)
    have e1 : s * t * s⁻¹ = x ^ (-j) * t * (x ^ (-j))⁻¹ := by
      rw [ha, hc, hj]; congr 2; ring
    have hcomm : (x ^ j * s) * t = t * (x ^ j * s) := by
      calc x ^ j * s * t = x ^ j * (s * t * s⁻¹) * s := by group
        _ = x ^ j * (x ^ (-j) * t * (x ^ (-j))⁻¹) * s := by rw [e1]
        _ = t * (x ^ j * s) := by group
    have hxjP : x ^ j * s ∈ P := mul_mem (zpow_mem hG.x_mem j) hsP
    have hR : x ^ j * s ∈ secTwoR t u := h.mem_R_of_commute C.pgroup C.R_le hxjP hcomm
    apply hsn
    have : s = x ^ (-j) * (x ^ j * s) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right (zpow_mem hxQ (-j))) (hG.toGoodCore.R_le_PP hR)
  obtain ⟨hd₁, hord₁, hpow₁, hxmem⟩ := hG.dih.ext_step hG.ord hn3 hs2 hodd ha
  have hy₁ : y₀ ∈ zpowers (s * t) := (zpowers_le).mpr hxmem hG.y₀_mem
  have hx₁Q : s * t ∈ closure ({t, s * t} : Set G) := subset_closure (by simp)
  have htQ₁ : t ∈ closure ({t, s * t} : Set G) := subset_closure (by simp)
  have hsQ₁ : s ∈ closure ({t, s * t} : Set G) := by
    have := mul_mem hx₁Q htQ₁
    rwa [mul_assoc, h.t_mul_t, mul_one] at this
  have hQ₁ : closure ({t, x} : Set G) ≤ closure ({t, s * t} : Set G) := by
    rw [closure_le]
    intro g hg
    rcases hg with h1 | h1
    · rw [h1]; exact htQ₁
    · rw [h1]
      exact (zpowers_le.mpr hx₁Q) hxmem
  have hcu : s * u₀ * s⁻¹ = u₀ := hG.commute_u₀_ext hsP hsT hsN hsn rfl hd₁ hy₁
  have hcs : s * u₀ = u₀ * s := by
    have := hcu
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hcore : GoodCore C (s * t) (n + 1) :=
    { dih := hd₁
      ord := by simpa using hord₁
      three_le := by omega
      x_mem := mul_mem hsP htP
      u₀_x := by
        calc u₀ * (s * t) = (u₀ * s) * t := by rw [mul_assoc]
          _ = (s * u₀) * t := by rw [hcs]
          _ = s * (u₀ * t) := by rw [mul_assoc]
          _ = s * (t * u₀) := by rw [C.t_u₀.symm]
          _ = (s * t) * u₀ := by rw [mul_assoc]
      y₀_mem := hy₁ }
  refine ⟨hcore.toGood ?_, lt_of_le_of_ne hQ₁ ?_⟩
  · apply le_antisymm
    · rw [closure_le]
      intro g hg
      rcases hg with h1 | h1
      · rw [h1]; exact subset_closure ⟨tConj_self t, htQ₁⟩
      · rw [h1]
        exact mul_mem (subset_closure ⟨hsT, hsQ₁⟩) (subset_closure ⟨tConj_self t, htQ₁⟩)
    · rw [closure_le]
      intro g hg
      exact hg.2
  · intro heq
    apply hsn
    have : s ∈ closure ({t, x} : Set G) := heq ▸ hsQ₁
    exact Subgroup.mem_sup_right this

theorem close
    (hcl : ∀ s : G, s ∈ P → TConj t s →
      s ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x} : Set G) : Subgroup G) : Set G) →
        s ∈ zpowers u₀ ⊔ closure ({t, x} : Set G)) :
    (∀ m ∈ P, m ∈ normalizer (closure ({t, x} : Set G) : Set G)) ∧
      (∀ m ∈ P, m ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x} : Set G) : Subgroup G) : Set G)) ∧
      ∀ s ∈ P, TConj t s → s ∈ closure ({t, x} : Set G) := by
  have h := C.secTwo
  set PP : Subgroup G := zpowers u₀ ⊔ closure ({t, x} : Set G) with hPP
  set H : Subgroup G := P ⊓ normalizer (PP : Set G) with hH
  have hPPH : PP ≤ H := fun g hg => ⟨hG.toGoodCore.PP_le_P hg, le_normalizer hg⟩
  have hQconj : ∀ m ∈ P, m ∈ normalizer (H : Set G) → ∀ q ∈ closure ({t, x} : Set G),
      m * q * m⁻¹ ∈ closure ({t, x} : Set G) := by
    intro m hmP hmH q hq
    refine conj_Q_of_gens hG m ?_ hq
    intro g hgT hgQ
    have hgH : g ∈ H := hPPH (Subgroup.mem_sup_right hgQ)
    have hmgH : m * g * m⁻¹ ∈ H := (mem_normalizer_iff.mp hmH g).mp hgH
    have hPP' : m * g * m⁻¹ ∈ PP := hcl _ hmgH.1 (hgT.conj m) hmgH.2
    obtain ⟨k, q', hq', hk⟩ := (hG.toGoodCore.mem_PP_iff).mp hPP'
    exact hG.no_mixed' hq' (hgT.conj m) hk
  have hQnorm : ∀ m ∈ P, m ∈ normalizer (H : Set G) →
      m ∈ normalizer (closure ({t, x} : Set G) : Set G) := by
    intro m hmP hmH
    rw [mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hQconj m hmP hmH q hq, fun hq => ?_⟩
    have := hQconj m⁻¹ (inv_mem hmP) (inv_mem hmH) _ hq
    simpa [mul_assoc] using this
  have hclaim : ∀ m ∈ P, m ∈ normalizer (H : Set G) → ∀ g ∈ PP, m * g * m⁻¹ ∈ PP := by
    intro m hmP hmH g hg
    have hmQ := hQnorm m hmP hmH
    obtain ⟨k, q, hq, rfl⟩ := (hG.toGoodCore.mem_PP_iff).mp hg
    have hu₀H : m * u₀ * m⁻¹ ∈ H :=
      (mem_normalizer_iff.mp hmH u₀).mp (hPPH (Subgroup.mem_sup_left (mem_zpowers u₀)))
    have hcommQ : ∀ q' ∈ closure ({t, x} : Set G),
        (m * u₀ * m⁻¹) * q' = q' * (m * u₀ * m⁻¹) := by
      intro q' hq'
      have hq'' : m⁻¹ * q' * m ∈ closure ({t, x} : Set G) := by
        have := hQconj m⁻¹ (inv_mem hmP) (inv_mem hmH) q' hq'
        simpa using this
      have hc := hG.u₀_comm hq''
      calc m * u₀ * m⁻¹ * q' = m * (u₀ * (m⁻¹ * q' * m)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * q' * m) * u₀) * m⁻¹ := by rw [hc]
        _ = q' * (m * u₀ * m⁻¹) := by group
    have htQ : t ∈ closure ({t, x} : Set G) := subset_closure (by simp)
    have hu₀R : m * u₀ * m⁻¹ ∈ secTwoR t u := by
      refine h.mem_R_of_commute C.pgroup C.R_le hu₀H.1 ?_
      exact hcommQ t htQ
    obtain ⟨k', q', hq', hk'⟩ := (hG.toGoodCore.mem_PP_iff).mp (hG.toGoodCore.R_le_PP hu₀R)
    have hU : m * u₀ * m⁻¹ ∈ zpowers u₀ := by
      rw [hk']
      refine hG.toGoodCore.mem_U_of_centralizes hq' fun q'' hq'' => ?_
      rw [← hk']; exact hcommQ q'' hq''
    have hmq : m * q * m⁻¹ ∈ closure ({t, x} : Set G) := hQconj m hmP hmH q hq
    have hconj : m * (u₀ ^ k * q) * m⁻¹ = (m * u₀ * m⁻¹) ^ k * (m * q * m⁻¹) := by
      rw [conj_zpow]; group
    rw [hconj]
    exact mul_mem (Subgroup.mem_sup_left (zpow_mem hU k)) (Subgroup.mem_sup_right hmq)
  have hstar : ∀ m ∈ P, m ∈ normalizer (H : Set G) → m ∈ normalizer (PP : Set G) := by
    intro m hmP hmH
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hclaim m hmP hmH g hg, fun hg => ?_⟩
    have := hclaim m⁻¹ (inv_mem hmP) (inv_mem hmH) _ hg
    simpa [mul_assoc] using this
  have hHP : H = P := by
    by_contra hne
    obtain ⟨m, hmP, hmH, hmnorm⟩ := secTwo_exists_mem_normalizer C.pgroup
      (inf_le_left : H ≤ P) hne
    exact hmH ⟨hmP, hstar m hmP hmnorm⟩
  have hnormP : ∀ m ∈ P, m ∈ normalizer (H : Set G) := fun m hm => by
    rw [hHP]; exact le_normalizer hm
  have hnormPP : ∀ m ∈ P, m ∈ normalizer (PP : Set G) := fun m hm => hstar m hm (hnormP m hm)
  refine ⟨fun m hm => hQnorm m hm (hnormP m hm), hnormPP, fun s hsP hsT => ?_⟩
  have hPP' : s ∈ PP := hcl s hsP hsT (hnormPP s hsP)
  obtain ⟨k, q', hq', hk⟩ := (hG.toGoodCore.mem_PP_iff).mp hPP'
  exact hG.no_mixed' hq' hsT hk

end Good

namespace SixAY

variable {C : SixAY t u P V v u₀ y₀}

theorem y₀_mem_N (C : SixAY t u P V v u₀ y₀) : y₀ ∈ nsub t u P := by
  rcases C.y₀_def with h1 | h1
  · have := C.toSixAW.nf_mem_N 0 1 1
    simpa [h1] using this
  · have := C.toSixAW.nf_mem_N 0 3 1
    simpa [h1] using this

theorem conj_N_mem_Q₀ (C : SixAY t u P V v u₀ y₀) :
    t * u₀ * v ∈ closure ({t, y₀} : Set G) ∧ t * u₀ ^ 3 * v ∈ closure ({t, y₀} : Set G) := by
  have h := C.secTwo
  have htQ : t ∈ closure ({t, y₀} : Set G) := subset_closure (by simp)
  have hyQ : y₀ ∈ closure ({t, y₀} : Set G) := subset_closure (by simp)
  have hzQ : u ^ 2 ∈ closure ({t, y₀} : Set G) := by
    rw [← C.y₀_sq]; exact pow_mem hyQ 2
  have hty : t * y₀ ∈ closure ({t, y₀} : Set G) := mul_mem htQ hyQ
  have htyz : t * y₀ * u ^ 2 ∈ closure ({t, y₀} : Set G) := mul_mem hty hzQ
  have hvu : v * u₀ ^ 2 = u₀ ^ 2 * v := by simpa using C.nrel.v_pow_w_pow 1 2
  rcases C.y₀_def with h1 | h1
  · refine ⟨by rw [mul_assoc, ← h1]; exact hty, ?_⟩
    have : t * u₀ ^ 3 * v = t * y₀ * u ^ 2 := by
      rw [h1, ← C.u₀_sq]
      calc t * u₀ ^ 3 * v = t * u₀ * (u₀ ^ 2 * v) := by group
        _ = t * u₀ * (v * u₀ ^ 2) := by rw [hvu]
        _ = t * (u₀ * v) * u₀ ^ 2 := by group
    rw [this]; exact htyz
  · refine ⟨?_, by rw [mul_assoc, ← h1]; exact hty⟩
    have : t * u₀ * v = t * y₀ * u ^ 2 := by
      rw [h1, ← C.u₀_sq]
      calc t * u₀ * v = t * u₀ ^ 5 * v := by
            rw [show u₀ ^ 5 = u₀ ^ 4 * u₀ by rw [pow_succ], C.u₀_four, one_mul]
        _ = t * (u₀ ^ 3 * v) * u₀ ^ 2 := by
            calc t * u₀ ^ 5 * v = t * u₀ ^ 3 * (u₀ ^ 2 * v) := by group
              _ = t * u₀ ^ 3 * (v * u₀ ^ 2) := by rw [hvu]
              _ = t * (u₀ ^ 3 * v) * u₀ ^ 2 := by group
    rw [this]; exact htyz

end SixAY

theorem good_init (C : SixAY t u P V v u₀ y₀) : Good C y₀ 3 where
  toGoodCore :=
    { dih := C.dihRel
      ord := by simp [C.y₀_order]
      three_le := le_refl 3
      x_mem := C.y₀_mem_P
      u₀_x := C.u₀_y₀
      y₀_mem := mem_zpowers y₀ }
  gen := by
    have htQ : t ∈ closure ({t, y₀} : Set G) := subset_closure (by simp)
    have hyQ : y₀ ∈ closure ({t, y₀} : Set G) := subset_closure (by simp)
    apply le_antisymm
    · rw [closure_le]
      intro g hg
      have ht : t ∈ closure {s : G | TConj t s ∧ s ∈ closure ({t, y₀} : Set G)} :=
        subset_closure ⟨tConj_self t, htQ⟩
      have hty : t * y₀ ∈ closure {s : G | TConj t s ∧ s ∈ closure ({t, y₀} : Set G)} :=
        subset_closure ⟨C.ty₀_conj, mul_mem htQ hyQ⟩
      rcases hg with h1 | h1
      · rw [h1]; exact ht
      · rw [h1]
        have hmul := mul_mem ht hty
        rwa [← mul_assoc, C.secTwo.t_mul_t, one_mul] at hmul
    · rw [closure_le]
      intro s hs
      exact hs.2
  no_mixed := by
    intro s k q hq hs hsq
    have h := C.secTwo
    have htQ : t ∈ closure ({t, y₀} : Set G) := subset_closure (by simp)
    have hyQ : y₀ ∈ closure ({t, y₀} : Set G) := subset_closure (by simp)
    have hzQ : u ^ 2 ∈ closure ({t, y₀} : Set G) := by
      rw [← C.y₀_sq]; exact pow_mem hyQ 2
    have htN : t ∈ nsub t u P := ⟨C.R_le SecTwoHyp.t_mem_R, le_normalizer SecTwoHyp.t_mem_R⟩
    have hwN : u₀ ∈ nsub t u P := ⟨C.u₀_mem_P, le_normalizer C.u₀_mem_R⟩
    have hQN : closure ({t, y₀} : Set G) ≤ nsub t u P := by
      rw [closure_le]
      intro g hg
      rcases hg with h1 | h1
      · rw [h1]; exact htN
      · rw [h1]; exact C.y₀_mem_N
    have hsN : s ∈ nsub t u P := by
      rw [hsq]; exact mul_mem (zpow_mem hwN k) (hQN hq)
    rcases C.N_conj_cases hs hsN with h1 | h1 | h1 | h1
    · rw [h1]; exact htQ
    · rw [h1]; exact mul_mem htQ hzQ
    · rw [h1]; exact C.conj_N_mem_Q₀.1
    · rw [h1]; exact C.conj_N_mem_Q₀.2

theorem exists_closed_good (C : SixAY t u P V v u₀ y₀) :
    ∃ (x : G) (n : ℕ), Good C x n ∧
      ∀ s : G, s ∈ P → TConj t s →
        s ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x} : Set G) : Subgroup G) : Set G) →
          s ∈ zpowers u₀ ⊔ closure ({t, x} : Set G) := by
  have key : ∀ m : ℕ, ∀ (x : G) (n : ℕ), Good C x n →
      Nat.card P - Nat.card (closure ({t, x} : Set G)) = m →
      ∃ (x' : G) (n' : ℕ), Good C x' n' ∧
        ∀ s : G, s ∈ P → TConj t s →
          s ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x'} : Set G) : Subgroup G) : Set G) →
            s ∈ zpowers u₀ ⊔ closure ({t, x'} : Set G) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x n hG hm
      by_cases hcl : ∀ s : G, s ∈ P → TConj t s →
          s ∈ normalizer ((zpowers u₀ ⊔ closure ({t, x} : Set G) : Subgroup G) : Set G) →
            s ∈ zpowers u₀ ⊔ closure ({t, x} : Set G)
      · exact ⟨x, n, hG, hcl⟩
      · push Not at hcl
        obtain ⟨s, hsP, hsT, hsN, hsn⟩ := hcl
        obtain ⟨hG₁, hlt⟩ := hG.extend hsP hsT hsN hsn
        have hcard := Subgroup.card_lt_of_lt hlt
        have hle := Subgroup.card_le_of_le (H := closure ({t, s * t} : Set G)) (K := P)
          hG₁.toGoodCore.Q_le_P
        exact ih (Nat.card P - Nat.card (closure ({t, s * t} : Set G))) (by omega)
          (s * t) (n + 1) hG₁ rfl
  exact key _ y₀ 3 (good_init C) rfl

end CFSG.LocalAnalysis.EvenBN.Tits
