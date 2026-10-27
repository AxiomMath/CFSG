module

public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Close

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

namespace Q8Cfg

omit [Finite G] in
theorem orderOf_zpow_odd (h : Q8Cfg D c) {n : ℤ} (hn : Odd n) : orderOf (c ^ n) = orderOf c := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]
  · obtain ⟨t, ht⟩ := mem_zpowers_iff.mp (h.mem_zpowers_zpow_odd_K (mem_zpowers c) hn)
    apply orderOf_dvd_of_pow_eq_one
    have : c ^ orderOf (c ^ n) = ((c ^ n) ^ t) ^ orderOf (c ^ n) := by rw [ht]
    rw [this, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]

theorem zpow_odd_sq_ne_one (h : Q8Cfg D c) {m : ℤ} (hm : Odd m) : c ^ m * c ^ m ≠ 1 := by
  intro h1
  have h2 : (c ^ (2 : ℤ)) ^ m = 1 := by
    rw [← zpow_mul, mul_comm, zpow_mul, zpow_two]
    exact h1
  have h3 : c ^ (2 : ℤ) = 1 := eq_one_of_zpow_odd_K h (zpow_mem (mem_zpowers c) 2) hm h2
  exact h.c_mul_c_ne_one (by rw [← zpow_two]; exact h3)

omit [Finite G] in
theorem conj_zpow' (v a : G) (n : ℤ) : (a⁻¹ * v * a) ^ n = a⁻¹ * v ^ n * a := by
  have := conj_zpow (a := a⁻¹) (b := v) (i := n)
  simpa using this

namespace Setup

variable {h : Q8Cfg D c} {S : Subgroup G} {y' u : G} {l : ℤ} (hs : Setup h S y' u l)
include hs

theorem Th_Q_not_D {x : G} (hx : Th c x) (hxQ : x ∈ hs.Q) (hxD : x ∉ D) :
    ∃ σ : ℤ, x = y' * c ^ σ := by
  have hsq := Th_sq h hx
  rcases hs.mem_Q.mp hxQ with hD | ⟨d, hd, hxd⟩
  · exact absurd hD hxD
  · rcases refl_cases h hs.hu hs.huK hd with hK | ⟨i, hi⟩
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hK
      exact ⟨i, by rw [hxd, ← hi]⟩
    · exfalso
      rw [hxd, hi] at hsq
      have h1 := hs.r.sq_y_c_u i
      rw [mul_assoc y' (c ^ i) u] at h1
      have h2 : cz c * c ^ (l - 2 * i) = cz c := h1.symm.trans hsq
      have h3 : c ^ (l - 2 * i) = 1 := mul_left_cancel (h2.trans (mul_one (cz c)).symm)
      obtain ⟨b, hb⟩ := hs.hl
      have h4 : c = 1 := eq_one_of_zpow_odd_K h (mem_zpowers c)
        (⟨b - i, by omega⟩ : Odd (l - 2 * i)) h3
      exact h.c_mul_c_ne_one (by rw [h4, one_mul])

theorem conj_setup {t : G} (hDt : D ≤ cjS S t) (hyt : y' ∈ cjS S t) :
    Setup h (cjS S t) y' u l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨isSylowOf_of_card le_top ?_, hDt, hs.hu, hs.huK, hyt, hs.hy, hs.hyD, hs.r, hs.hl⟩
  rw [card_cjS]
  exact hs.hS.card_eq

theorem U_closed {i : ℤ} {s : G} (hsdef : s = y' * (c ^ i * u)) {a : G}
    (hsa : a⁻¹ * s * a ∈ S) : a⁻¹ * s * a ∈ hs.Q := by
  have hSN := hs.le_norm
  obtain ⟨m, hm3, hm⟩ := h.two_pow
  have hssq : s * s = cz c * c ^ (l - 2 * i) := by
    have := hs.r.sq_y_c_u i
    rwa [mul_assoc y' (c ^ i) u, ← hsdef] at this
  obtain ⟨b, hb⟩ := hs.hl
  obtain ⟨q4, hq4⟩ := h.h4
  set n : ℤ := ((orderOf c / 2 : ℕ) : ℤ) + (l - 2 * i) with hn
  have hnodd : Odd n := by
    refine ⟨(orderOf c / 4 : ℕ) + b - i, ?_⟩
    rw [hn]
    have : orderOf c / 2 = 2 * (orderOf c / 4) := by omega
    rw [this]
    push_cast
    omega
  have hκ : s * s = c ^ n := by rw [hssq, hn, zpow_add, cz, zpow_natCast]
  have hκK : s * s ∈ zpowers c := by rw [hκ]; exact zpow_mem (mem_zpowers c) _
  have hκord : orderOf (s * s) = 2 ^ m := by rw [hκ, h.orderOf_zpow_odd hnodd, hm]
  have hKκ : c ∈ zpowers (s * s) := by
    rw [hκ]
    exact h.mem_zpowers_zpow_odd_K (mem_zpowers c) hnodd
  have hκne : s * s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hκord
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    omega
  have hKs : zpowers c ≤ zpowers s := by
    refine (zpowers_le.mpr hKκ).trans (zpowers_le.mpr ?_)
    exact ⟨2, by show s ^ (2 : ℤ) = s * s; exact zpow_two s⟩
  have hs'sq : (a⁻¹ * s * a) * (a⁻¹ * s * a) = a⁻¹ * (s * s) * a := by group
  have hκaS : a⁻¹ * (s * s) * a ∈ S := by
    rw [← hs'sq]
    exact mul_mem hsa hsa
  have hκaD := claim3 h hs.hS hs.hDS m hm3 hκK hκord hκaS
  have hκaord : orderOf (a⁻¹ * (s * s) * a) = 2 ^ m := by rw [orderOf_conj', hκord]
  have hκaK : a⁻¹ * (s * s) * a ∈ zpowers c := by
    rcases h.dih _ hκaD with h1 | ⟨h1, -⟩
    · exact h1
    · exfalso
      have h2 : orderOf (a⁻¹ * (s * s) * a) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
      rw [hκaord] at h2
      have h3 := Nat.le_of_dvd (by norm_num) h2
      have h4 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
      omega
  have hKa : ∀ x ∈ zpowers c, a⁻¹ * x * a ∈ zpowers c := by
    intro x hx
    obtain ⟨t, rfl⟩ := mem_zpowers_iff.mp ((zpowers_le.mpr hKκ) hx)
    rw [← conj_zpow']
    exact zpow_mem hκaK t
  have hsy : s * cy c = cy c * s := by
    obtain ⟨t, ht⟩ := mem_zpowers_iff.mp (hKs (cy_mem h))
    rw [← ht]
    exact (Commute.self_zpow s t).eq
  have hsQ : s ∈ hs.Q := hs.mem_Q.mpr (Or.inr ⟨c ^ i * u, mul_mem (zpow_mem h.mem i) hs.hu, hsdef⟩)
  have hUQ : zpowers s ≤ hs.Q := zpowers_le.mpr hsQ
  have hSU : S ≤ normalizer ((zpowers s : Subgroup G) : Set G) := by
    refine le_normalizer_of_forall fun t ht v hv => ?_
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    rw [← conj_zpow]
    refine zpow_mem ?_ j
    have htN := hSN ht
    obtain ⟨jt, hjt⟩ := conj_c h htN
    obtain ⟨lt, hlt⟩ := conj_refl h htN hs.hu hs.huK
    have htQ : t ∈ normalizer ((hs.Q : Subgroup G) : Set G) := hs.S_le_norm_Q ht
    have hTh : Th c (t * y' * t⁻¹) := by
      have := Th_conj hs.hy t⁻¹
      rwa [inv_inv] at this
    have hmemQ : t * y' * t⁻¹ ∈ hs.Q := (mem_normalizer_iff.mp htQ y').mp hs.y_mem_Q
    have hnotD : t * y' * t⁻¹ ∉ D := fun hD => hs.hyD ((mem_normalizer_iff.mp htN y').mpr hD)
    obtain ⟨σ, hσ⟩ := hs.Th_Q_not_D hTh hmemQ hnotD
    have key : t * s * t⁻¹ = s * c ^ (i - (σ + jt * i + lt)) := by
      calc t * s * t⁻¹ = (t * y' * t⁻¹) * (t * c ^ i * t⁻¹) * (t * u * t⁻¹) := by
            rw [hsdef]; group
        _ = (y' * c ^ σ) * c ^ (jt * i) * (c ^ lt * u) := by
            rw [hσ, ← conj_zpow, hjt, ← zpow_mul, hlt]
        _ = y' * c ^ i * (u * c ^ (i - (σ + jt * i + lt)) * u⁻¹) * u := by
            rw [hs.r.u_conj_zpow_c]
            group
        _ = s * c ^ (i - (σ + jt * i + lt)) := by rw [hsdef]; group
    rw [key]
    exact mul_mem (mem_zpowers s) (hKs (zpow_mem (mem_zpowers c) _))
  generalize hs' : a⁻¹ * s * a = s' at hsa hs'sq
  have hs'y : s' * cy c = cy c * s' := by
    have hKy := hKa _ (cy_mem h)
    have hsqy : (a⁻¹ * cy c * a) * (a⁻¹ * cy c * a) = cz c := Th_sq h (Th_conj Th_cy a)
    have hc : s' * (a⁻¹ * cy c * a) = (a⁻¹ * cy c * a) * s' := by
      calc s' * (a⁻¹ * cy c * a) = a⁻¹ * (s * cy c) * a := by rw [← hs']; group
        _ = a⁻¹ * (cy c * s) * a := by rw [hsy]
        _ = (a⁻¹ * cy c * a) * s' := by rw [← hs']; group
    rcases eq_cy_or_inv h hKy hsqy with e | e
    · rwa [e] at hc
    · rw [e] at hc
      have h3 : Commute s' (cy c)⁻¹ := hc
      have h4 := h3.inv_right
      rw [inv_inv] at h4
      exact h4.eq
  have hs'K : s' * s' ∈ zpowers c := by rw [hs'sq]; exact hκaK
  have hs'ne : s' * s' ≠ 1 := by
    intro h1
    rw [hs'sq] at h1
    rw [h1, orderOf_one] at hκaord
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    omega
  have hnorm := normalizes_zpowers h (hSN hsa) hs'y hs'K hs'ne
  have hs'ord : orderOf (s' * s') = 2 ^ m := by rw [hs'sq, hκaord]
  have hzeq : zpowers (s' * s') = zpowers c :=
    eq_of_le_of_card_ge (zpowers_le.mpr hs'K)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hs'ord, hm])
  have hKs' : zpowers c ≤ zpowers s' := by
    rw [← hzeq]
    exact zpowers_le.mpr ⟨2, by show s' ^ (2 : ℤ) = s' * s'; exact zpow_two s'⟩
  have hy's' : y' * s' * y'⁻¹ ∈ zpowers s' := by
    have hs'N : s' ∈ normalizer ((hs.Q : Subgroup G) : Set G) := hs.S_le_norm_Q hsa
    have hmemQ : s' * y' * s'⁻¹ ∈ hs.Q := (mem_normalizer_iff.mp hs'N y').mp hs.y_mem_Q
    have hTh : Th c (s' * y' * s'⁻¹) := by
      have := Th_conj hs.hy s'⁻¹
      rwa [inv_inv] at this
    have hnotD : s' * y' * s'⁻¹ ∉ D := fun hD =>
      hs.hyD ((mem_normalizer_iff.mp (hSN hsa) y').mpr hD)
    obtain ⟨σ, hσ⟩ := hs.Th_Q_not_D hTh hmemQ hnotD
    have e1 : s' * y' * s'⁻¹ * y'⁻¹ = c ^ (-σ) := by rw [hσ, hs.r.conj_zpow_c]
    have e2 : y' * s' * y'⁻¹ * s'⁻¹ = c ^ σ := by
      have := congrArg Inv.inv e1
      rw [show (s' * y' * s'⁻¹ * y'⁻¹)⁻¹ = y' * s' * y'⁻¹ * s'⁻¹ by group, ← zpow_neg,
        neg_neg] at this
      exact this
    have e3 : y' * s' * y'⁻¹ = c ^ σ * s' := mul_inv_eq_iff_eq_mul.mp e2
    rw [e3]
    exact mul_mem (hKs' (zpow_mem (mem_zpowers c) σ)) (mem_zpowers s')
  have hQN : (hs.Q : Subgroup G) ≤ normalizer ((zpowers s' : Subgroup G) : Set G) := by
    refine le_normalizer_of_forall fun q hq v hv => ?_
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    rw [← conj_zpow]
    refine zpow_mem ?_ j
    rcases hs.mem_Q.mp hq with hqD | ⟨d, hd, rfl⟩
    · exact hnorm q hqD
    · obtain ⟨t, ht⟩ := mem_zpowers_iff.mp (hnorm d hd)
      have h5 : y' * (d * s' * d⁻¹) * y'⁻¹ ∈ zpowers s' := by
        rw [← ht, ← conj_zpow]
        exact zpow_mem hy's' t
      have e : y' * d * s' * (y' * d)⁻¹ = y' * (d * s' * d⁻¹) * y'⁻¹ := by group
      rw [e]
      exact h5
  have hUa : cjS (zpowers s) a = zpowers s' := zpowers_cjS hs'
  have hQN' : (hs.Q : Subgroup G) ≤ normalizer ((cjS (zpowers s) a : Subgroup G) : Set G) := by
    rw [hUa]
    exact hQN
  obtain ⟨t, htU, hQt⟩ := exists_conj_sylow hs.hS hSU a
    (hs.hS.isPGroup.to_le hs.Q_le_S) hQN'
  have hs'U : s' ∈ cjS (zpowers s) t := by
    rw [htU, hUa]
    exact mem_zpowers s'
  have hts' : t * s' * t⁻¹ ∈ zpowers s := mem_cjS.mp hs'U
  have hDt : D ≤ cjS S t := fun d hd => hQt (hs.D_le_Q hd)
  have hy't : y' ∈ cjS S t := hQt hs.y_mem_Q
  have hs_t := hs.conj_setup hDt hy't
  have hQt' : ∀ q ∈ hs.Q, t⁻¹ * q * t ∈ hs.Q := by
    intro q hq
    have hDq : ∀ d ∈ D, t⁻¹ * d * t ∈ D := fun d hd =>
      h.weak_closed (isPGroup_cjS hs.hS.isPGroup t) hDt (g := t)
        (fun d' hd' => by
          rw [mem_cjS, show t * (t⁻¹ * d' * t) * t⁻¹ = d' by group]
          exact hs.hDS hd') hd
    have hyq : t⁻¹ * y' * t ∈ hs.Q := by
      have h1 : t⁻¹ * y' * t ∈ cjS S t := by
        rw [mem_cjS, show t * (t⁻¹ * y' * t) * t⁻¹ = y' by group]
        exact hs.hyS
      exact hs_t.Th_le_Q h1 (Th_conj hs.hy t)
    rcases hs.mem_Q.mp hq with hqD | ⟨d, hd, rfl⟩
    · exact hs.D_le_Q (hDq q hqD)
    · rw [show t⁻¹ * (y' * d) * t = (t⁻¹ * y' * t) * (t⁻¹ * d * t) by group]
      exact mul_mem hyq (hs.D_le_Q (hDq d hd))
  have : s' = t⁻¹ * (t * s' * t⁻¹) * t := by group
  rw [this]
  exact hQt' _ (hUQ hts')

theorem rot_closed {x a : G} (hxK : x ∈ zpowers c) (hxa : a⁻¹ * x * a ∈ S) :
    a⁻¹ * x * a ∈ hs.Q := by
  obtain ⟨m, hm3, hm⟩ := h.two_pow
  have hx : x ^ (2 ^ m) = 1 := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hxK
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hm, pow_orderOf_eq_one,
      one_zpow]
  obtain ⟨e, he, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  have hxpow : x ^ (2 ^ e) = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ 3 ≤ e by omega) with rfl | rfl | rfl | he3
  · have : x = 1 := by simpa using hxpow
    rw [this, show a⁻¹ * 1 * a = 1 by group]
    exact one_mem _
  · have hx2 : x * x = 1 := by simpa [sq] using hxpow
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      omega
    have hxz : x = cz c := (eq_one_or_eq_cz h.h4 hxK hx2).resolve_left hx1
    rw [hxz, show a⁻¹ * cz c * a = cz c by
      have := h.conj_cz_eq a⁻¹
      rwa [inv_inv] at this]
    exact hs.D_le_Q (cz_mem h.mem)
  · have hx4 : x * x * (x * x) = 1 := by
      have : x ^ 4 = 1 := by simpa using hxpow
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq] at this
      exact this
    have hx2 : x * x ≠ 1 := by
      intro h1
      have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
      rw [hord] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hxz : x * x = cz c :=
      (eq_one_or_eq_cz h.h4 (mul_mem hxK hxK) hx4).resolve_left hx2
    have hTh : Th c x := by
      rcases eq_cy_or_inv h hxK hxz with e1 | e1
      · rw [e1]
        exact Th_cy
      · rw [e1]
        exact Th_inv_cy h hs.hu hs.huK
    exact hs.Th_le_Q hxa (Th_conj hTh a)
  · exact hs.D_le_Q (claim3 h hs.hS hs.hDS e he3 hxK hord hxa)

theorem inv_Q_le_D {x : G} (hxQ : x ∈ hs.Q) (hx2 : x * x = 1) : x ∈ D := by
  rcases hs.mem_Q.mp hxQ with hD | ⟨d, hd, hxd⟩
  · exact hD
  · exfalso
    rcases refl_cases h hs.hu hs.huK hd with hK | ⟨i, hi⟩
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hK
      rw [hxd, ← hi] at hx2
      exact cz_ne_one' h ((hs.r.sq_y_c i).symm.trans hx2)
    · rw [hxd, hi] at hx2
      have h1 := hs.r.sq_y_c_u i
      rw [mul_assoc y' (c ^ i) u] at h1
      have h2 : cz c * c ^ (l - 2 * i) = 1 := h1.symm.trans hx2
      have h3 : c ^ (l - 2 * i) = cz c := by
        have := eq_inv_of_mul_eq_one_right h2
        rw [this, cz_inv' h]
      obtain ⟨b, hb⟩ := hs.hl
      refine zpow_odd_sq_ne_one h (⟨b - i, by omega⟩ : Odd (l - 2 * i)) ?_
      rw [h3]
      exact cz_mul_cz h.h4

theorem Q_stronglyClosed : Open.fusionStronglyClosed ((hs.Q : Subgroup G) : Set G) S := by
  intro x hxQ a hxa
  rcases hs.mem_Q.mp hxQ with hD | ⟨d, hd, hxd⟩
  · rcases h.dih x hD with hK | ⟨hx2, -⟩
    · exact hs.rot_closed hK hxa
    · exact hs.D_le_Q (h.inv_fuse hs.hS.isPGroup hs.hDS hD hx2 hxa)
  · rcases refl_cases h hs.hu hs.huK hd with hK | ⟨i, hi⟩
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hK
      have hTh : Th c x := by
        rw [hxd, ← hi]
        exact Th_y_c h hs.r hs.hl hs.hy i
      exact hs.Th_le_Q hxa (Th_conj hTh a)
    · exact hs.U_closed (i := i) (s := x) (by rw [hxd, hi]) hxa

end Setup

end Q8Cfg

end CFSG.ComponentClassification.Foote5.HallGen
