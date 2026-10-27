module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TQ8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem conj_invol_conj {s x : G} (hs2 : s * s = 1) :
    s * (s * x * s⁻¹) * s⁻¹ = x := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
    _ = x := by rw [hs', hs2]; group

private theorem twoCoreIn_le' (X : Subgroup G) : twoCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.pCore 2 ↥X)

private theorem twoCoreIn_conj_mem {X : Subgroup G} {a : G} (ha : a ∈ X) {x : G}
    (hx : x ∈ twoCoreIn X) : a * x * a⁻¹ ∈ twoCoreIn X := by
  unfold twoCoreIn CFSG.inSubgroup at hx ⊢
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  rw [← hyx]
  refine Subgroup.mem_map.mpr ⟨⟨a, ha⟩ * y * ⟨a, ha⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem y hy ⟨a, ha⟩
  · simp

private theorem commutator_prod_of_commute' {P Q : Subgroup G}
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

theorem sec10T_swap_data [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) {s : G} (hs : s ∈ S) (hs2 : s * s = 1)
    (hsw : ∀ x ∈ K1, s * x * s⁻¹ ∈ K2) :
    ∃ g ∈ twoCoreIn K1, g ∉ zpowers z ∧ s * g * s⁻¹ ∈ K2 ∧
      ∃ x1 x2 : G, Odd (orderOf x1) ∧ Odd (orderOf x2) ∧ x1 * s = s * x1 ∧ x2 * s = s * x2 ∧
        x1 * z = z * x1 ∧ x2 * z = z * x2 ∧
        ∃ e ∈ zpowers z, (s * g * s⁻¹)⁻¹ * g = x2 * x1⁻¹ * e := by
  obtain ⟨k, hkK1, hkodd, g0, hg0Q1, hg0nc⟩ := sec10T_exists_comm3 hP5 hC5 hpsp hctx
  have hg0K1 : g0 ∈ K1 := twoCoreIn_le' K1 hg0Q1
  have hcommK : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  set k' : G := s * k * s⁻¹ with hk'def
  set g0' : G := s * g0 * s⁻¹ with hg0'def
  set x1 : G := k * k' with hx1def
  set w : G := g0 * g0' with hwdef
  have hk'K2 : k' ∈ K2 := by rw [hk'def]; exact hsw k hkK1
  have hg0'K2 : g0' ∈ K2 := by rw [hg0'def]; exact hsw g0 hg0K1
  set g : G := g0 * k * g0⁻¹ * k⁻¹ with hgdef
  have hg_eq_inv : g = (k * g0 * k⁻¹ * g0⁻¹)⁻¹ := by rw [hgdef]; group
  have hconj : k * g0 * k⁻¹ ∈ twoCoreIn K1 := twoCoreIn_conj_mem hkK1 hg0Q1
  have hprod : k * g0 * k⁻¹ * g0⁻¹ ∈ twoCoreIn K1 :=
    Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hg0Q1)
  have hgQ1 : g ∈ twoCoreIn K1 := by rw [hg_eq_inv]; exact Subgroup.inv_mem _ hprod
  have hgK1 : g ∈ K1 := twoCoreIn_le' K1 hgQ1
  have hg_inv_eq : g⁻¹ = k * g0 * k⁻¹ * g0⁻¹ := by rw [hg_eq_inv]; group
  have hg_notZ : g ∉ zpowers z := fun hZ => hg0nc (hg_inv_eq ▸ Subgroup.inv_mem _ hZ)
  set g' : G := g0' * k' * g0'⁻¹ * k'⁻¹ with hg'def
  have hg'K2 : g' ∈ K2 := by
    rw [hg'def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg0'K2 hk'K2)
      (Subgroup.inv_mem _ hg0'K2)) (Subgroup.inv_mem _ hk'K2)
  have hg's : s * g * s⁻¹ = g' := by
    rw [hgdef, hg'def, hg0'def, hk'def]
    group
  have hsgK2 : s * g * s⁻¹ ∈ K2 := hg's.symm ▸ hg'K2
  have hzK1 : ∀ a ∈ K1, a * z = z * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.pocket1.2.1 ha).2
  have hzK2 : ∀ a ∈ K2, a * z = z * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.pocket2.2.1 ha).2
  have hkk'_comm : Commute k k' := hcommK k hkK1 k' hk'K2
  have hk'order : orderOf k' = orderOf k := by
    rw [hk'def, ← MulAut.conj_apply]
    exact (MulAut.conj s).orderOf_eq k
  have hk'pow : k' ^ orderOf k = 1 := by
    rw [← hk'order]
    exact pow_orderOf_eq_one k'
  have hx1pow : x1 ^ orderOf k = 1 := by
    rw [hx1def, hkk'_comm.mul_pow, pow_orderOf_eq_one, hk'pow, mul_one]
  have hx1odd : Odd (orderOf x1) :=
    Odd.of_dvd_nat hkodd (orderOf_dvd_of_pow_eq_one hx1pow)
  have hsx1 : s * x1 * s⁻¹ = x1 := by
    rw [hx1def]
    have hmul : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    rw [hmul, ← hk'def]
    have hk'back : s * k' * s⁻¹ = k := by rw [hk'def]; exact conj_invol_conj hs2
    rw [hk'back, hkk'_comm.eq]
  have hx1s : x1 * s = s * x1 := by
    calc x1 * s = (s * x1 * s⁻¹) * s := by rw [hsx1]
      _ = s * x1 := by group
  have hsw : s * w * s⁻¹ = w := by
    rw [hwdef]
    have hmul : s * (g0 * g0') * s⁻¹ = (s * g0 * s⁻¹) * (s * g0' * s⁻¹) := by group
    rw [hmul, ← hg0'def]
    have hg0'back : s * g0' * s⁻¹ = g0 := by rw [hg0'def]; exact conj_invol_conj hs2
    rw [hg0'back]
    exact (hcommK g0 hg0K1 g0' hg0'K2).symm
  set x2 : G := w * x1 * w⁻¹ with hx2def
  have hsx2 : s * x2 * s⁻¹ = x2 := by
    rw [hx2def]
    have hsplit : s * (w * x1 * w⁻¹) * s⁻¹ =
        (s * w * s⁻¹) * (s * x1 * s⁻¹) * (s * w * s⁻¹)⁻¹ := by group
    rw [hsplit, hsw, hsx1]
  have hx2s : x2 * s = s * x2 := by
    calc x2 * s = (s * x2 * s⁻¹) * s := by rw [hsx2]
      _ = s * x2 := by group
  have hx2order : orderOf x2 = orderOf x1 := by
    rw [hx2def, ← MulAut.conj_apply]
    exact (MulAut.conj w).orderOf_eq x1
  have hx2odd : Odd (orderOf x2) := by rw [hx2order]; exact hx1odd
  have hkz : Commute k z := hzK1 k hkK1
  have hk'z : Commute k' z := hzK2 k' hk'K2
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
  have hx1z : x1 * z = z * x1 := hx1zc.eq
  have hx2z : x2 * z = z * x2 := hx2zc.eq
  have hgQ : g ∈ secQ K1 K2 := by
    rw [sec10KS_twoCore_sup hP5 hC5 hpsp hctx]
    exact Subgroup.mem_sup_left hgQ1
  have hg'Q : g' ∈ secQ K1 K2 := hg's ▸ sec10J_Q_normal hP5 hb hctx s hs g hgQ
  have hg'2 : g' * g' ∈ zpowers z :=
    ((sec10KS_Q_elem hP5 hC5 hpsp hctx).2 g' hg'Q g' hg'Q).2
  set e : G := (g' * g')⁻¹ with hedef
  have heZ : e ∈ zpowers z := by rw [hedef]; exact Subgroup.inv_mem _ hg'2
  have hx2x1 : x2 * x1⁻¹ = g * g' := by
    rw [hx2def, hx1def, hwdef]
    rw [← commutatorElement_def,
        commutator_prod_of_commute' hcommK hg0K1 hkK1 hg0'K2 hk'K2,
        commutatorElement_def, commutatorElement_def, hgdef, hg'def]
  have hgg' : Commute g g' := hcommK g hgK1 g' hg'K2
  have hfinal : (s * g * s⁻¹)⁻¹ * g = x2 * x1⁻¹ * e := by
    rw [hg's, hx2x1, hedef]
    have h1 : (g * g') * (g' * g')⁻¹ = g * g'⁻¹ := by group
    rw [h1, hgg'.inv_right.eq]
  exact ⟨g, hgQ1, hg_notZ, hsgK2, x1, x2, hx1odd, hx2odd, hx1s, hx2s, hx1z, hx2z,
    e, heZ, hfinal⟩

end CFSG.OddStandard.SmallF3.Omega
