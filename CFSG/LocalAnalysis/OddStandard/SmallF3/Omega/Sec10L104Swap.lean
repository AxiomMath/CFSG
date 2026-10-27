module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TQ8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem sec10L104_conj_invol {s x : G} (hs2 : s * s = 1) :
    s * (s * x * s⁻¹) * s⁻¹ = x := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
    _ = x := by rw [hs', hs2]; group

private theorem sec10L104_comm_prod {P Q : Subgroup G}
    (hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a)
    {a1 b1 a2 b2 : G} (ha1 : a1 ∈ P) (hb1 : b1 ∈ P) (ha2 : a2 ∈ Q) (hb2 : b2 ∈ Q) :
    ⁅a1 * a2, b1 * b2⁆ = ⁅a1, b1⁆ * ⁅a2, b2⁆ := by
  have h21 : ⁅a2, b1⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc b1 hb1 a2 ha2).symm
  have h12 : ⁅a1, b2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc a1 ha1 b2 hb2)
  have hX : ⁅a2, b2⁆ ∈ Q :=
    Subgroup.commutator_le_self Q (Subgroup.commutator_mem_commutator ha2 hb2)
  have haX : a1 * ⁅a2, b2⁆ * a1⁻¹ = ⁅a2, b2⁆ := by
    rw [hc a1 ha1 ⁅a2, b2⁆ hX, mul_assoc, mul_inv_cancel, mul_one]
  have hbX : b1 * ⁅a2, b2⁆ * b1⁻¹ = ⁅a2, b2⁆ := by
    rw [hc b1 hb1 ⁅a2, b2⁆ hX, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅a1 * a2, b1 * b2⁆
      = (a1 * ⁅a2, b1⁆ * a1⁻¹ * ⁅a1, b1⁆) * b1 *
          (a1 * ⁅a2, b2⁆ * a1⁻¹ * ⁅a1, b2⁆) * b1⁻¹ := by
        rw [commutatorElement_mul_right_eq_mul_conj,
            commutatorElement_mul_left_eq_conj_mul,
            commutatorElement_mul_left_eq_conj_mul]
    _ = ⁅a1, b1⁆ * b1 * (a1 * ⁅a2, b2⁆ * a1⁻¹) * b1⁻¹ := by
        rw [h21, h12]
        group
    _ = ⁅a1, b1⁆ * b1 * ⁅a2, b2⁆ * b1⁻¹ := by rw [haX]
    _ = ⁅a1, b1⁆ * (b1 * ⁅a2, b2⁆ * b1⁻¹) := by group
    _ = ⁅a1, b1⁆ * ⁅a2, b2⁆ := by rw [hbX]

theorem sec10L104_two_pow_twoCoreIn {X : Subgroup G} {x : G} (hx : x ∈ twoCoreIn X) :
    ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := isPGroup_twoCoreIn X (⟨x, hx⟩ : ↥(twoCoreIn X))
  exact ⟨m, congrArg Subtype.val hm⟩

theorem sec10L104_two_elem_sup {N K : Subgroup G} (hNodd : ∀ n ∈ N, Odd (orderOf n))
    (hNc : ∀ n ∈ N, ∀ y ∈ K, n * y = y * n) (hNd : ∀ x ∈ N, x ∈ K → x = 1) {n y : G}
    (hn : n ∈ N) (hy : y ∈ K) {m : ℕ} (h : (n * y) ^ (2 ^ m) = 1) : n = 1 := by
  have hc : Commute n y := hNc n hn y hy
  have h1 : n ^ (2 ^ m) * y ^ (2 ^ m) = 1 := by rw [← hc.mul_pow]; exact h
  have h2 : n ^ (2 ^ m) = (y ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : n ^ (2 ^ m) = 1 :=
    hNd _ (Subgroup.pow_mem _ hn _) (by rw [h2]; exact K.inv_mem (Subgroup.pow_mem K hy _))
  exact sec10L104_eq_one_of_odd_two (hNodd n hn) ⟨m, h3⟩

theorem sec10L104_swap_data [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {N : Subgroup G} (hNodd : ∀ n ∈ N, Odd (orderOf n))
    (hN1 : ∀ n ∈ N, ∀ a ∈ K1, n * a = a * n) (hN2 : ∀ n ∈ N, ∀ a ∈ K2, n * a = a * n)
    (hN2d : ∀ x ∈ N, x ∈ K2 → x = 1) {s : G} (hs2 : s * s = 1) (hsz : s * z = z * s)
    (hsw : ∀ x ∈ K1, ∃ n ∈ N, ∃ y ∈ K2, s * x * s⁻¹ = n * y) :
    ∃ g ∈ twoCoreIn K1, g ∉ zpowers z ∧ s * g * s⁻¹ ∈ twoCoreIn K2 ∧
      ∃ x1 x2 : G, Odd (orderOf x1) ∧ Odd (orderOf x2) ∧ x1 * s = s * x1 ∧ x2 * s = s * x2 ∧
        x1 * z = z * x1 ∧ x2 * z = z * x2 ∧
        ∃ e ∈ zpowers z, (s * g * s⁻¹)⁻¹ * g = x2 * x1⁻¹ * e := by
  obtain ⟨k, hkK1, hkodd, g0, hg0Q1, hg0nc⟩ := sec10T_exists_comm3 hP5 hC5 hpsp hctx
  have hg0K1 : g0 ∈ K1 := twoCoreIn_le_self K1 hg0Q1
  have hcommK : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hszc : Commute s z := hsz
  obtain ⟨nk, hnk, yk, hykK2, hk'eq⟩ := hsw k hkK1
  obtain ⟨n0, hn0, y0, hy0K2, hg0'eq⟩ := hsw g0 hg0K1
  obtain ⟨m, hm⟩ := sec10L104_two_pow_twoCoreIn hg0Q1
  have hn01 : n0 = 1 := by
    refine sec10L104_two_elem_sup hNodd hN2 hN2d hn0 hy0K2 (m := m) ?_
    rw [← hg0'eq]
    have h := congrArg (fun x => s * x * s⁻¹) hm
    simp only [mul_one, mul_inv_cancel] at h
    rw [show s * g0 ^ (2 ^ m) * s⁻¹ = (s * g0 * s⁻¹) ^ (2 ^ m) by rw [conj_pow]] at h
    exact h
  have hg0'y0 : s * g0 * s⁻¹ = y0 := by rw [hg0'eq, hn01, one_mul]
  have hy0Q2 : y0 ∈ twoCoreIn K2 := by
    refine sec10T_two_elem_Q1 hP5 hC5 hpsp hctx.swap hy0K2 ⟨m, ?_⟩
    rw [← hg0'y0, conj_pow, hm, mul_one, mul_inv_cancel]
  set g0' : G := y0 with hg0'def
  have hg0'K2 : g0' ∈ K2 := twoCoreIn_le_self K2 hy0Q2
  have hsg0 : s * g0 * s⁻¹ = g0' := hg0'y0
  set k' : G := s * k * s⁻¹ with hk'def
  have hk'K : k' = nk * yk := hk'eq
  set x1 : G := k * k' with hx1def
  set w : G := g0 * g0' with hwdef
  have hkk' : k * k' = k' * k := by
    rw [hk'K]
    calc k * (nk * yk) = (k * nk) * yk := by group
      _ = (nk * k) * yk := by rw [← hN1 nk hnk k hkK1]
      _ = nk * (k * yk) := by group
      _ = nk * (yk * k) := by rw [hcommK k hkK1 yk hykK2]
      _ = nk * yk * k := by group
  have hk'order : orderOf k' = orderOf k := by
    rw [hk'def, ← MulAut.conj_apply]
    exact (MulAut.conj s).orderOf_eq k
  have hk'pow : k' ^ orderOf k = 1 := by
    rw [← hk'order]
    exact pow_orderOf_eq_one k'
  have hkk'c : Commute k k' := hkk'
  have hx1pow : x1 ^ orderOf k = 1 := by
    rw [hx1def, hkk'c.mul_pow, pow_orderOf_eq_one, hk'pow, mul_one]
  have hx1odd : Odd (orderOf x1) :=
    Odd.of_dvd_nat hkodd (orderOf_dvd_of_pow_eq_one hx1pow)
  have hk'back : s * k' * s⁻¹ = k := by rw [hk'def]; exact sec10L104_conj_invol hs2
  have hsx1 : s * x1 * s⁻¹ = x1 := by
    rw [hx1def]
    have hmul : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    rw [hmul, ← hk'def, hk'back, ← hkk']
  have hx1s : x1 * s = s * x1 := by
    calc x1 * s = (s * x1 * s⁻¹) * s := by rw [hsx1]
      _ = s * x1 := by group
  have hg0'back : s * g0' * s⁻¹ = g0 := by
    rw [← hsg0]; exact sec10L104_conj_invol hs2
  have hwc : g0 * g0' = g0' * g0 := hcommK g0 hg0K1 g0' hg0'K2
  have hsw' : s * w * s⁻¹ = w := by
    rw [hwdef]
    have hmul : s * (g0 * g0') * s⁻¹ = (s * g0 * s⁻¹) * (s * g0' * s⁻¹) := by group
    rw [hmul, hsg0, hg0'back]
    exact hwc.symm
  set x2 : G := w * x1 * w⁻¹ with hx2def
  have hsx2 : s * x2 * s⁻¹ = x2 := by
    rw [hx2def]
    have hsplit : s * (w * x1 * w⁻¹) * s⁻¹ =
        (s * w * s⁻¹) * (s * x1 * s⁻¹) * (s * w * s⁻¹)⁻¹ := by group
    rw [hsplit, hsw', hsx1]
  have hx2s : x2 * s = s * x2 := by
    calc x2 * s = (s * x2 * s⁻¹) * s := by rw [hsx2]
      _ = s * x2 := by group
  have hx2order : orderOf x2 = orderOf x1 := by
    rw [hx2def, ← MulAut.conj_apply]
    exact (MulAut.conj w).orderOf_eq x1
  have hx2odd : Odd (orderOf x2) := by rw [hx2order]; exact hx1odd
  have hzK1 : ∀ a ∈ K1, a * z = z * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.pocket1.2.1 ha).2
  have hzK2 : ∀ a ∈ K2, a * z = z * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.pocket2.2.1 ha).2
  have hkz : Commute k z := hzK1 k hkK1
  have hk'z : Commute k' z := by
    rw [hk'def]
    exact (hszc.mul_left hkz).mul_left hszc.inv_left
  have hg0z : Commute g0 z := hzK1 g0 hg0K1
  have hg0'z : Commute g0' z := hzK2 g0' hg0'K2
  have hx1zc : Commute x1 z := by
    rw [hx1def]
    exact hkz.mul_left hk'z
  have hwzc : Commute w z := by
    rw [hwdef]
    exact hg0z.mul_left hg0'z
  have hx2zc : Commute x2 z := by
    rw [hx2def]
    exact (hwzc.mul_left hx1zc).mul_left hwzc.inv_left
  set g : G := g0 * k * g0⁻¹ * k⁻¹ with hgdef
  have hconj : k * g0 * k⁻¹ ∈ twoCoreIn K1 :=
    (Subgroup.normal_subgroupOf_iff (twoCoreIn_le_self K1)).mp (normal_subgroupOf_twoCoreIn K1)
      g0 k hg0Q1 hkK1
  have hprod : k * g0 * k⁻¹ * g0⁻¹ ∈ twoCoreIn K1 :=
    Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hg0Q1)
  have hg_eq_inv : g = (k * g0 * k⁻¹ * g0⁻¹)⁻¹ := by rw [hgdef]; group
  have hgQ1 : g ∈ twoCoreIn K1 := by rw [hg_eq_inv]; exact Subgroup.inv_mem _ hprod
  have hgK1 : g ∈ K1 := twoCoreIn_le_self K1 hgQ1
  have hg_inv_eq : g⁻¹ = k * g0 * k⁻¹ * g0⁻¹ := by rw [hg_eq_inv]; group
  have hg_notZ : g ∉ zpowers z := fun hZ => hg0nc (hg_inv_eq ▸ Subgroup.inv_mem _ hZ)
  set gk : G := g0' * yk * g0'⁻¹ * yk⁻¹ with hgkdef
  have hgkQ2 : gk ∈ twoCoreIn K2 := by
    have h1 : yk * g0'⁻¹ * yk⁻¹ ∈ twoCoreIn K2 :=
      (Subgroup.normal_subgroupOf_iff (twoCoreIn_le_self K2)).mp (normal_subgroupOf_twoCoreIn K2)
        g0'⁻¹ yk (Subgroup.inv_mem _ hy0Q2) hykK2
    have h2 := Subgroup.mul_mem _ hy0Q2 h1
    have e : g0' * (yk * g0'⁻¹ * yk⁻¹) = gk := by rw [hgkdef]; group
    rwa [e] at h2
  have hgkK2 : gk ∈ K2 := twoCoreIn_le_self K2 hgkQ2
  have hg's : s * g * s⁻¹ = gk := by
    have h1 : s * g * s⁻¹ = g0' * k' * g0'⁻¹ * k'⁻¹ := by
      rw [hgdef, hk'def, ← hsg0]
      group
    rw [h1, hk'K]
    have hn_g0' : nk * g0' = g0' * nk := hN2 nk hnk g0' hg0'K2
    have hn_gk : nk * gk = gk * nk := hN2 nk hnk gk hgkK2
    calc g0' * (nk * yk) * g0'⁻¹ * (nk * yk)⁻¹
        = (g0' * nk) * yk * g0'⁻¹ * yk⁻¹ * nk⁻¹ := by group
      _ = (nk * g0') * yk * g0'⁻¹ * yk⁻¹ * nk⁻¹ := by rw [← hn_g0']
      _ = nk * (g0' * yk * g0'⁻¹ * yk⁻¹) * nk⁻¹ := by group
      _ = nk * gk * nk⁻¹ := by rw [hgkdef]
      _ = gk := by rw [hn_gk]; group
  have hsgQ2 : s * g * s⁻¹ ∈ twoCoreIn K2 := by rw [hg's]; exact hgkQ2
  have hg'2 : gk * gk ∈ zpowers z :=
    (sec10KS_Qi_elem hP5 hC5 hpsp hctx.swap gk hgkQ2 gk hgkQ2).2
  set e : G := (gk * gk)⁻¹ with hedef
  have heZ : e ∈ zpowers z := by rw [hedef]; exact Subgroup.inv_mem _ hg'2
  have hx2x1 : x2 * x1⁻¹ = g * gk := by
    have hx1eq : x1 = nk * (k * yk) := by
      rw [hx1def, hk'K]
      calc k * (nk * yk) = (k * nk) * yk := by group
        _ = (nk * k) * yk := by rw [← hN1 nk hnk k hkK1]
        _ = nk * (k * yk) := by group
    have hnw : nk * w = w * nk := by
      rw [hwdef]
      calc nk * (g0 * g0') = (nk * g0) * g0' := by group
        _ = (g0 * nk) * g0' := by rw [hN1 nk hnk g0 hg0K1]
        _ = g0 * (nk * g0') := by group
        _ = g0 * (g0' * nk) := by rw [hN2 nk hnk g0' hg0'K2]
        _ = g0 * g0' * nk := by group
    have hcomm : w * (k * yk) * w⁻¹ * (k * yk)⁻¹ = g * gk := by
      have h := sec10L104_comm_prod hcommK hg0K1 hkK1 hg0'K2 hykK2
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def] at h
      rw [hwdef]
      rw [h]
    have hng : nk * g = g * nk := hN1 nk hnk g hgK1
    have hngk : nk * gk = gk * nk := hN2 nk hnk gk hgkK2
    rw [hx2def, hx1eq]
    calc w * (nk * (k * yk)) * w⁻¹ * (nk * (k * yk))⁻¹
        = (w * nk) * (k * yk) * w⁻¹ * (k * yk)⁻¹ * nk⁻¹ := by group
      _ = (nk * w) * (k * yk) * w⁻¹ * (k * yk)⁻¹ * nk⁻¹ := by rw [← hnw]
      _ = nk * (w * (k * yk) * w⁻¹ * (k * yk)⁻¹) * nk⁻¹ := by group
      _ = nk * (g * gk) * nk⁻¹ := by rw [hcomm]
      _ = g * gk := by
        have hngg : nk * (g * gk) = (g * gk) * nk := by
          rw [← mul_assoc, hng, mul_assoc, hngk, ← mul_assoc]
        rw [hngg]
        group
  have hgg' : Commute g gk := hcommK g hgK1 gk hgkK2
  have hfinal : (s * g * s⁻¹)⁻¹ * g = x2 * x1⁻¹ * e := by
    rw [hg's, hx2x1, hedef]
    have h1 : (g * gk) * (gk * gk)⁻¹ = g * gk⁻¹ := by group
    rw [h1, hgg'.inv_right.eq]
  exact ⟨g, hgQ1, hg_notZ, hsgQ2, x1, x2, hx1odd, hx2odd, hx1s, hx2s, hx1zc.eq, hx2zc.eq,
    e, heZ, hfinal⟩

end CFSG.OddStandard.SmallF3.Omega
