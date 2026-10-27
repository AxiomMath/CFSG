module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem twoCoreIn_le_X (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem conj_mem_twoCoreIn {X : Subgroup G} {x y : G} (hx : x ∈ X)
    (hy : y ∈ twoCoreIn X) : x * y * x⁻¹ ∈ twoCoreIn X := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * m * ⟨x, hx⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem m hm ⟨x, hx⟩
  · simp

private theorem mem_twoCoreIn_iff' {X : Subgroup G} {x : G} (hx : x ∈ X) :
    x ∈ twoCoreIn X ↔ (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
  unfold twoCoreIn CFSG.inSubgroup
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem eq_neg_one_of_orderOf_eq_two {X : Subgroup G} (e : ↥X ≃* SL23) {z : G}
    (hz : z ∈ X) (hz2 : orderOf z = 2) : e ⟨z, hz⟩ = -1 := by
  have hsq : (⟨z, hz⟩ : ↥X) * ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    change z * z = (1 : G)
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hsq' : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by rw [← map_mul, hsq, map_one]
  rcases sl23_unique_involution _ hsq' with h | h
  · exfalso
    have hz1 : (⟨z, hz⟩ : ↥X) = 1 := by apply e.injective; rw [h, map_one]
    have hzG : z = 1 := by simpa using congrArg Subtype.val hz1
    have : orderOf z = 1 := by rw [hzG]; exact orderOf_one
    omega
  · exact h

private theorem z_central_of_equiv {X : Subgroup G} (e : ↥X ≃* SL23) {z : G} (hz : z ∈ X)
    (hz2 : orderOf z = 2) : ∀ a ∈ X, z * a = a * z := by
  intro a ha
  have hneg : e ⟨z, hz⟩ = -1 := eq_neg_one_of_orderOf_eq_two e hz hz2
  have h' : (⟨z, hz⟩ : ↥X) * ⟨a, ha⟩ = ⟨a, ha⟩ * ⟨z, hz⟩ := by
    apply e.injective
    rw [map_mul, map_mul, hneg]
    exact (by decide : ∀ x : SL23, (-1) * x = x * (-1)) (e ⟨a, ha⟩)
  exact congrArg Subtype.val h'

private theorem mem_zpowers_of_mul_self_eq_one {X : Subgroup G} (e : ↥X ≃* SL23) {z w : G}
    (hz : z ∈ X) (hz2 : orderOf z = 2) (hw : w ∈ X) (hw2 : w * w = 1) :
    w ∈ zpowers z := by
  have hw' : (⟨w, hw⟩ : ↥X) * ⟨w, hw⟩ = 1 := Subtype.ext (by simpa using hw2)
  have hwe : e ⟨w, hw⟩ * e ⟨w, hw⟩ = 1 := by rw [← map_mul, hw', map_one]
  rcases sl23_unique_involution (e ⟨w, hw⟩) hwe with h | h
  · have hw1 : (⟨w, hw⟩ : ↥X) = 1 := by apply e.injective; rw [h, map_one]
    rw [show w = 1 from congrArg Subtype.val hw1]
    exact Subgroup.one_mem _
  · have hwz : (⟨w, hw⟩ : ↥X) = ⟨z, hz⟩ := by
      apply e.injective
      rw [h, eq_neg_one_of_orderOf_eq_two e hz hz2]
    rw [show w = z from congrArg Subtype.val hwz]
    exact Subgroup.mem_zpowers z

private theorem mem_twoCoreIn_of_orderOf_eq_two {X : Subgroup G} (e : ↥X ≃* SL23) {z : G}
    (hz : z ∈ X) (hz2 : orderOf z = 2) : z ∈ twoCoreIn X := by
  rw [mem_twoCoreIn_iff' hz]
  have hmem : e ⟨z, hz⟩ ∈ CFSG.pCore 2 SL23 := by
    rw [eq_neg_one_of_orderOf_eq_two e hz hz2]
    exact sl23_neg_one_mem_pCore
  rw [← CFSG.pCore_map_iso 2 e] at hmem
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
  have hy' : y = ⟨z, hz⟩ := e.injective hye
  rwa [hy'] at hy

private theorem zpowers_mul_self_eq_one {z c : G} (hz : z * z = 1) (hc : c ∈ zpowers z) :
    c * c = 1 := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [← hn, ← zpow_add]
  have hn' : n + n = 2 * n := by ring
  rw [hn', zpow_mul]
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  rw [h2, one_zpow]

private theorem mem_zpowers_eq_one_or_self {z c : G} (hz : z * z = 1) (hc : c ∈ zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [← hn, hk, zpow_mul]
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
    rw [h2, one_zpow]
  · right
    rw [← hn, hk, zpow_add, zpow_one]
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
    rw [zpow_mul, h2, one_zpow, one_mul]

private theorem square_prod_of_commute {Q1 Q2 : Subgroup G}
    (hc : ∀ a ∈ Q1, ∀ b ∈ Q2, a * b = b * a)
    {a1 a2 : G} (ha1 : a1 ∈ Q1) (ha2 : a2 ∈ Q2) :
    (a1 * a2) * (a1 * a2) = (a1 * a1) * (a2 * a2) := by
  calc (a1 * a2) * (a1 * a2) = a1 * (a2 * a1) * a2 := by group
    _ = a1 * (a1 * a2) * a2 := by rw [(hc a1 ha1 a2 ha2).symm]
    _ = (a1 * a1) * (a2 * a2) := by group

private theorem sl23_exists_conj_not_comm' (x : SL23) (hx : x ^ 4 = 1) (hx2 : x * x ≠ 1) :
    ∃ g : SL23, (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹) :=
  (by decide : ∀ x : SL23, x ^ 4 = 1 → x * x ≠ 1 →
    ∃ g : SL23, (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹)) x hx hx2

private theorem not_commute_of_map_not_commute {X : Subgroup G} (e : ↥X ≃* SL23) {a b : G}
    (ha : a ∈ X) (hb : b ∈ X) (h : e ⟨a, ha⟩ * e ⟨b, hb⟩ ≠ e ⟨b, hb⟩ * e ⟨a, ha⟩) :
    a * b ≠ b * a := by
  intro hab
  apply h
  rw [← map_mul, ← map_mul]
  exact congrArg e (Subtype.ext hab)

theorem sec11_exists_swap_conj [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {q : G} (hq : q ∈ secQ K1 K2) (hq2 : q * q = 1)
    (hqz : q ∉ zpowers z) :
    ∃ g ∈ K1 ⊔ K2, g * q * g⁻¹ * q = q * (g * q * g⁻¹) ∧ g * q * g⁻¹ ≠ q ∧
      g * q * g⁻¹ ≠ q * z := by
  obtain ⟨e1⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  obtain ⟨e2⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).2
  have hsup := sec10KS_twoCore_sup hP5 hC5 hpsp hctx
  have hcommQ : ∀ a ∈ twoCoreIn K1, ∀ b ∈ twoCoreIn K2, a * b = b * a := by
    intro a ha b hb
    exact sec10Z_comm hP5 hpsp hctx a (twoCoreIn_le_X K1 ha) b (twoCoreIn_le_X K2 hb)
  have hcomm12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  obtain ⟨q1, hq1, q2, hq2mem, hqeq⟩ :=
    exists_mul_of_mem_sup_of_commute hcommQ (by rw [← hsup]; exact hq)
  have hq1K1 : q1 ∈ K1 := twoCoreIn_le_X K1 hq1
  have hq2K2 : q2 ∈ K2 := twoCoreIn_le_X K2 hq2mem
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  have hzK2 : z ∈ K2 := hctx.pocket2.1
  have hzQ2 : z ∈ twoCoreIn K2 := mem_twoCoreIn_of_orderOf_eq_two e2 hzK2 hz2
  have hzcen1 : ∀ a ∈ K1, z * a = a * z := z_central_of_equiv e1 hzK1 hz2
  have hzcen2 : ∀ a ∈ K2, z * a = a * z := z_central_of_equiv e2 hzK2 hz2
  have hsq : q * q = (q1 * q1) * (q2 * q2) := by
    rw [hqeq]
    exact square_prod_of_commute hcommQ hq1 hq2mem
  have hq1sq : q1 * q1 ≠ 1 := by
    intro h1
    have hq2sq : q2 * q2 = 1 := by
      have h := hsq
      rw [hq2, h1, one_mul] at h
      exact h.symm
    have hz1 : q1 ∈ zpowers z := mem_zpowers_of_mul_self_eq_one e1 hzK1 hz2 hq1K1 h1
    have hz2' : q2 ∈ zpowers z := mem_zpowers_of_mul_self_eq_one e2 hzK2 hz2 hq2K2 hq2sq
    exact hqz (by rw [hqeq]; exact Subgroup.mul_mem _ hz1 hz2')
  have hq2sq : q2 * q2 ≠ 1 := by
    intro h2
    have hq1sq' : q1 * q1 = 1 := by
      have h := hsq
      rw [hq2, h2, mul_one] at h
      exact h.symm
    have hz1 : q1 ∈ zpowers z := mem_zpowers_of_mul_self_eq_one e1 hzK1 hz2 hq1K1 hq1sq'
    have hz2' : q2 ∈ zpowers z := mem_zpowers_of_mul_self_eq_one e2 hzK2 hz2 hq2K2 h2
    exact hqz (by rw [hqeq]; exact Subgroup.mul_mem _ hz1 hz2')
  have hq1four : q1 ^ 4 = 1 := by
    have hmem : q1 * q1 ∈ zpowers z := (sec10KS_Qi_elem hP5 hC5 hpsp hctx q1 hq1 q1 hq1).2
    have hsq1 := zpowers_mul_self_eq_one hzsq hmem
    have hpow : q1 ^ 4 = (q1 * q1) * (q1 * q1) := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [hpow]
    exact hsq1
  let x1 : SL23 := e1 ⟨q1, hq1K1⟩
  have hx1_4 : x1 ^ 4 = 1 := by
    have h : (⟨q1, hq1K1⟩ : ↥K1) ^ 4 = 1 := by
      apply Subtype.ext
      change q1 ^ 4 = (1 : G)
      exact hq1four
    change (e1 ⟨q1, hq1K1⟩) ^ 4 = 1
    rw [← map_pow, h, map_one]
  have hx1_2 : x1 * x1 ≠ 1 := by
    intro h
    apply hq1sq
    have h' : (⟨q1, hq1K1⟩ : ↥K1) * ⟨q1, hq1K1⟩ = 1 := by
      apply e1.injective
      rw [map_mul, h, map_one]
    exact congrArg Subtype.val h'
  obtain ⟨c1, hc1⟩ := sl23_exists_conj_not_comm' x1 hx1_4 hx1_2
  let g1 : G := (e1.symm c1 : ↥K1)
  have hg1K1 : g1 ∈ K1 := (e1.symm c1).2
  have hg1_eq : e1 ⟨g1, hg1K1⟩ = c1 := e1.apply_symm_apply c1
  set q1' : G := g1 * q1 * g1⁻¹ with hq1'def
  have hq1'mem : q1' ∈ twoCoreIn K1 := by
    rw [hq1'def]; exact conj_mem_twoCoreIn hg1K1 hq1
  have hq1'K1 : q1' ∈ K1 := twoCoreIn_le_X K1 hq1'mem
  have he1_q1' : e1 ⟨q1', hq1'K1⟩ = c1 * x1 * c1⁻¹ := by
    have hsub : (⟨q1', hq1'K1⟩ : ↥K1) =
        ⟨g1, hg1K1⟩ * ⟨q1, hq1K1⟩ * ⟨g1, hg1K1⟩⁻¹ := by
      apply Subtype.ext
      simp [hq1'def]
    rw [hsub, map_mul, map_mul, map_inv, hg1_eq]
  have hnotcomm1 : q1' * q1 ≠ q1 * q1' := by
    apply not_commute_of_map_not_commute e1 hq1'K1 hq1K1
    rw [he1_q1']
    change (c1 * x1 * c1⁻¹) * x1 ≠ x1 * (c1 * x1 * c1⁻¹)
    exact hc1
  have hq2four : q2 ^ 4 = 1 := by
    have hmem : q2 * q2 ∈ zpowers z :=
      (sec10KS_Qi_elem hP5 hC5 hpsp hctx.swap q2 hq2mem q2 hq2mem).2
    have hsq2 := zpowers_mul_self_eq_one hzsq hmem
    have hpow : q2 ^ 4 = (q2 * q2) * (q2 * q2) := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [hpow]
    exact hsq2
  let x2 : SL23 := e2 ⟨q2, hq2K2⟩
  have hx2_4 : x2 ^ 4 = 1 := by
    have h : (⟨q2, hq2K2⟩ : ↥K2) ^ 4 = 1 := by
      apply Subtype.ext
      change q2 ^ 4 = (1 : G)
      exact hq2four
    change (e2 ⟨q2, hq2K2⟩) ^ 4 = 1
    rw [← map_pow, h, map_one]
  have hx2_2 : x2 * x2 ≠ 1 := by
    intro h
    apply hq2sq
    have h' : (⟨q2, hq2K2⟩ : ↥K2) * ⟨q2, hq2K2⟩ = 1 := by
      apply e2.injective
      rw [map_mul, h, map_one]
    exact congrArg Subtype.val h'
  obtain ⟨c2, hc2⟩ := sl23_exists_conj_not_comm' x2 hx2_4 hx2_2
  let g2 : G := (e2.symm c2 : ↥K2)
  have hg2K2 : g2 ∈ K2 := (e2.symm c2).2
  have hg2_eq : e2 ⟨g2, hg2K2⟩ = c2 := e2.apply_symm_apply c2
  set q2' : G := g2 * q2 * g2⁻¹ with hq2'def
  have hq2'mem : q2' ∈ twoCoreIn K2 := by
    rw [hq2'def]; exact conj_mem_twoCoreIn hg2K2 hq2mem
  have hq2'K2 : q2' ∈ K2 := twoCoreIn_le_X K2 hq2'mem
  have he2_q2' : e2 ⟨q2', hq2'K2⟩ = c2 * x2 * c2⁻¹ := by
    have hsub : (⟨q2', hq2'K2⟩ : ↥K2) =
        ⟨g2, hg2K2⟩ * ⟨q2, hq2K2⟩ * ⟨g2, hg2K2⟩⁻¹ := by
      apply Subtype.ext
      simp [hq2'def]
    rw [hsub, map_mul, map_mul, map_inv, hg2_eq]
  have hnotcomm2 : q2' * q2 ≠ q2 * q2' := by
    apply not_commute_of_map_not_commute e2 hq2'K2 hq2K2
    rw [he2_q2']
    change (c2 * x2 * c2⁻¹) * x2 ≠ x2 * (c2 * x2 * c2⁻¹)
    exact hc2
  have hzc1 : q1 * q1' * q1⁻¹ * q1'⁻¹ = z := by
    have hmem := (sec10KS_Qi_elem hP5 hC5 hpsp hctx q1 hq1 q1' hq1'mem).1
    rcases mem_zpowers_eq_one_or_self hzsq hmem with h1 | h1
    · exfalso
      apply hnotcomm1
      have h2 : q1 * q1' = (q1 * q1' * q1⁻¹ * q1'⁻¹) * (q1' * q1) := by group
      rw [h1, one_mul] at h2
      exact h2.symm
    · exact h1
  have hzc2 : q2 * q2' * q2⁻¹ * q2'⁻¹ = z := by
    have hmem := (sec10KS_Qi_elem hP5 hC5 hpsp hctx.swap q2 hq2mem q2' hq2'mem).1
    rcases mem_zpowers_eq_one_or_self hzsq hmem with h1 | h1
    · exfalso
      apply hnotcomm2
      have h2 : q2 * q2' = (q2 * q2' * q2⁻¹ * q2'⁻¹) * (q2' * q2) := by group
      rw [h1, one_mul] at h2
      exact h2.symm
    · exact h1
  have hq1'eq : q1 * q1' = z * (q1' * q1) := by
    have h2 : q1 * q1' = (q1 * q1' * q1⁻¹ * q1'⁻¹) * (q1' * q1) := by group
    rw [hzc1] at h2
    exact h2
  have hq2'eq : q2 * q2' = z * (q2' * q2) := by
    have h2 : q2 * q2' = (q2 * q2' * q2⁻¹ * q2'⁻¹) * (q2' * q2) := by group
    rw [hzc2] at h2
    exact h2
  have hkey : (q1 * q2) * (q1' * q2') = (q1' * q2') * (q1 * q2) := by
    have hc : q2 * q1' = q1' * q2 := (hcommQ q1' hq1'mem q2 hq2mem).symm
    have hc' : q2' * q1 = q1 * q2' := (hcommQ q1 hq1 q2' hq2'mem).symm
    have hzA : z * (q1' * q1) = (q1' * q1) * z :=
      hzcen1 (q1' * q1) (K1.mul_mem hq1'K1 hq1K1)
    calc (q1 * q2) * (q1' * q2') = (q1 * q1') * (q2 * q2') := by
          rw [show (q1 * q2) * (q1' * q2') = q1 * (q2 * q1') * q2' by group, hc]
          group
      _ = (z * (q1' * q1)) * (z * (q2' * q2)) := by rw [hq1'eq, hq2'eq]
      _ = (q1' * q1) * (q2' * q2) := by
          rw [hzA]
          calc ((q1' * q1) * z) * (z * (q2' * q2))
              = (q1' * q1) * (z * z) * (q2' * q2) := by group
            _ = (q1' * q1) * (q2' * q2) := by rw [hzsq]; group
      _ = (q1' * q2') * (q1 * q2) := by
          rw [show (q1' * q1) * (q2' * q2) = q1' * (q1 * q2') * q2 by group,
            show q1 * q2' = q2' * q1 from hc'.symm]
          group
  have hconj : (g1 * g2) * q * (g1 * g2)⁻¹ = q1' * q2' := by
    have hmul : (g1 * g2) * q = (q1' * q2') * (g1 * g2) := by
      have hgq : g2 * q1 = q1 * g2 := (hcomm12 q1 hq1K1 g2 hg2K2).symm
      have hgq1 : g1 * q1 = q1' * g1 := by rw [hq1'def]; group
      have hgq2 : g2 * q2 = q2' * g2 := by rw [hq2'def]; group
      have hcross : g1 * q2' = q2' * g1 := hcomm12 g1 hg1K1 q2' hq2'K2
      calc (g1 * g2) * q = (g1 * g2) * (q1 * q2) := by rw [hqeq]
        _ = g1 * (g2 * q1) * q2 := by group
        _ = g1 * (q1 * g2) * q2 := by rw [hgq]
        _ = (g1 * q1) * (g2 * q2) := by group
        _ = (q1' * g1) * (q2' * g2) := by rw [hgq1, hgq2]
        _ = q1' * (g1 * q2') * g2 := by group
        _ = q1' * (q2' * g1) * g2 := by rw [hcross]
        _ = (q1' * q2') * (g1 * g2) := by group
    rw [hmul]
    group
  have hne : ∀ e ∈ zpowers z, (g1 * g2) * q * (g1 * g2)⁻¹ ≠ q * e := by
    intro e he h
    rw [hconj, hqeq] at h
    have hkey2 : q1⁻¹ * q1' = q2 * e * q2'⁻¹ := by
      have h' : q1⁻¹ * (q1' * q2') * q2'⁻¹ = q1⁻¹ * ((q1 * q2) * e) * q2'⁻¹ := by
        rw [h]
      rw [show q1⁻¹ * (q1' * q2') * q2'⁻¹ = q1⁻¹ * q1' by group,
        show q1⁻¹ * ((q1 * q2) * e) * q2'⁻¹ = q2 * e * q2'⁻¹ by group] at h'
      exact h'
    have he1_or : e = 1 ∨ e = z := mem_zpowers_eq_one_or_self hzsq he
    have heK2 : ∀ a ∈ K2, e * a = a * e := by
      intro a ha
      rcases he1_or with h1 | hz
      · rw [h1, one_mul, mul_one]
      · rw [hz]; exact hzcen2 a ha
    have heQ2 : e ∈ twoCoreIn K2 := (Subgroup.zpowers_le.mpr hzQ2) he
    have hrearr : q2 * e * q2'⁻¹ = q2 * q2'⁻¹ * e := by
      rw [show q2 * e * q2'⁻¹ = q2 * (e * q2'⁻¹) by group,
        heK2 q2'⁻¹ (K2.inv_mem hq2'K2)]
      group
    have hwmem1 : q1⁻¹ * q1' ∈ twoCoreIn K1 :=
      (twoCoreIn K1).mul_mem ((twoCoreIn K1).inv_mem hq1) hq1'mem
    have hwmem2 : q2 * q2'⁻¹ * e ∈ twoCoreIn K2 :=
      (twoCoreIn K2).mul_mem
        ((twoCoreIn K2).mul_mem hq2mem ((twoCoreIn K2).inv_mem hq2'mem)) heQ2
    have hwzp : q1⁻¹ * q1' ∈ zpowers z := by
      have hle : twoCoreIn K1 ⊓ twoCoreIn K2 ≤ K1 ⊓ K2 :=
        inf_le_inf (twoCoreIn_le_X K1) (twoCoreIn_le_X K2)
      rw [(sec10KS_main hP5 hC5 hpsp hctx).2.2] at hle
      exact hle ⟨hwmem1, by rw [hkey2, hrearr]; exact hwmem2⟩
    have hq1'eq2 : q1' = q1 * (q1⁻¹ * q1') := by group
    have hwcomm : (q1⁻¹ * q1') * q1 = q1 * (q1⁻¹ * q1') := by
      rcases mem_zpowers_eq_one_or_self hzsq hwzp with h1 | hz
      · rw [h1, one_mul, mul_one]
      · rw [hz]; exact hzcen1 q1 hq1K1
    have hcomm_q1 : q1' * q1 = q1 * q1' := by
      have h1 : q1' * q1 = (q1 * (q1⁻¹ * q1')) * q1 := by
        conv_lhs => rw [hq1'eq2]
      rw [h1]
      calc (q1 * (q1⁻¹ * q1')) * q1 = q1 * ((q1⁻¹ * q1') * q1) := by group
        _ = q1 * (q1 * (q1⁻¹ * q1')) := by rw [hwcomm]
        _ = q1 * q1' := by rw [← hq1'eq2]
    exact hnotcomm1 hcomm_q1
  refine ⟨g1 * g2, Subgroup.mul_mem_sup hg1K1 hg2K2, ?_, ?_, ?_⟩
  · rw [hconj, hqeq]
    exact hkey.symm
  · simpa using hne 1 (Subgroup.one_mem _)
  · exact hne z (Subgroup.mem_zpowers z)

end CFSG.OddStandard.SmallF3.Omega
