module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G]

private lemma commutatorElement_mul_left_of_central {z a b : G} (hza : Commute z a)
    (hzb : Commute z b) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, hzb.commutator_eq, mul_one]
  have h2 : Commute z ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  exact h2.mul_inv_cancel

private lemma commutatorElement_mul_right_of_central {a b z : G} (haz : Commute a z) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, haz.commutator_eq, mul_one]
  group

theorem l34g_odd_central_lift {E : Subgroup G} {x e : G} (hx : x * x = 1)
    (hxE : x ∈ normalizer (E : Set G)) (heE : e ∈ E) (hodd : Odd (orderOf e))
    (hc : ∀ g ∈ E, g * (x * e * x⁻¹ * e⁻¹) = (x * e * x⁻¹ * e⁻¹) * g) :
    ∃ z ∈ E, (∀ g ∈ E, g * z = z * g) ∧ (e * z) * x = x * (e * z) := by
  set w : G := x * e * x⁻¹ * e⁻¹ with hw
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hwE : w ∈ E := by
    rw [hw]
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp hxE e).mp heE) (E.inv_mem heE)
  have hwc : ∀ g ∈ E, Commute w g := fun g hg => (hc g hg).symm
  have hxe : x * e * x⁻¹ = w * e := by rw [hw]; group
  have hxw : x * w * x⁻¹ = w⁻¹ := by
    have h3 : x⁻¹ * e⁻¹ * x⁻¹ = (x * e * x⁻¹)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hxinv, mul_assoc]
    have h1 : x * w * x⁻¹ = e * x⁻¹ * e⁻¹ * x⁻¹ := by
      rw [hw]
      rw [show x * (x * e * x⁻¹ * e⁻¹) * x⁻¹ = (x * x) * (e * x⁻¹ * e⁻¹ * x⁻¹) by group]
      rw [hx, one_mul]
    rw [h1, show e * x⁻¹ * e⁻¹ * x⁻¹ = e * (x⁻¹ * e⁻¹ * x⁻¹) by group, h3, hxe]
    group
  have hpow : w ^ orderOf e = 1 := by
    have hconj : x * e ^ orderOf e * x⁻¹ = (x * e * x⁻¹) ^ orderOf e := (conj_pow).symm
    rw [pow_orderOf_eq_one e, mul_one, mul_inv_cancel] at hconj
    rw [hxe, (hwc e heE).mul_pow (orderOf e), pow_orderOf_eq_one e, mul_one] at hconj
    exact hconj.symm
  have hoddw : Odd (orderOf w) := hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  obtain ⟨k, hk⟩ := hoddw
  refine ⟨w ^ (k + 1), E.pow_mem hwE (k + 1), ?_, ?_⟩
  · intro g hg
    exact ((hwc g hg).pow_left (k + 1)).eq.symm
  · have hz2 : w ^ (k + 1) * w ^ (k + 1) = w := by
      rw [← pow_add]
      have h2 : k + 1 + (k + 1) = orderOf w + 1 := by rw [hk]; ring
      rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
    have hxz : x * w ^ (k + 1) * x⁻¹ = (w ^ (k + 1))⁻¹ := by
      rw [← conj_pow, hxw, inv_pow]
    have hmain : x * (e * w ^ (k + 1)) * x⁻¹ = e * w ^ (k + 1) := by
      have h1 : x * (e * w ^ (k + 1)) * x⁻¹
          = (x * e * x⁻¹) * (x * w ^ (k + 1) * x⁻¹) := by group
      rw [h1, hxe, hxz]
      have hwz : w * (w ^ (k + 1))⁻¹ = w ^ (k + 1) := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hz2.symm
      rw [show (w * e) * (w ^ (k + 1))⁻¹ = e * (w * (w ^ (k + 1))⁻¹) by
        rw [(hwc e heE).eq]; group, hwz]
    have hxez : x * (e * w ^ (k + 1)) = (e * w ^ (k + 1)) * x := by
      calc x * (e * w ^ (k + 1)) = x * (e * w ^ (k + 1)) * x⁻¹ * x := by group
        _ = (e * w ^ (k + 1)) * x := by rw [hmain]
    exact hxez.symm

theorem l34g_perfect_le_of_central {E J J' : Subgroup G} (hJE : J ≤ E) (hJ'E : J' ≤ E)
    (hJ : ⁅J, J⁆ = J)
    (h : ∀ g ∈ J, ∃ g' ∈ J', ∀ e ∈ E, (g * g'⁻¹) * e = e * (g * g'⁻¹)) : J ≤ J' := by
  have hcomm_le : ⁅J', J'⁆ ≤ J' := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact J'.mul_mem (J'.mul_mem (J'.mul_mem hx hy) (J'.inv_mem hx)) (J'.inv_mem hy)
  rw [← hJ, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨a', ha', hca⟩ := h a ha
  obtain ⟨b', hb', hcb⟩ := h b hb
  set p : G := a * a'⁻¹ with hp
  set q : G := b * b'⁻¹ with hq
  have hqE : q ∈ E := by rw [hq]; exact E.mul_mem (hJE hb) (E.inv_mem (hJ'E hb'))
  have hpcomm : ∀ e ∈ E, Commute p e := by
    intro e he
    show p * e = e * p
    rw [hp]
    exact hca e he
  have hqcomm : ∀ e ∈ E, Commute q e := by
    intro e he
    show q * e = e * q
    rw [hq]
    exact hcb e he
  have hpa : p * a' = a := by rw [hp]; group
  have hqb : q * b' = b := by rw [hq]; group
  have hpa' : Commute p a' := hpcomm a' (hJ'E ha')
  have hpb' : Commute p b' := hpcomm b' (hJ'E hb')
  have hpq : Commute p q := hpcomm q hqE
  have hqb' : Commute q b' := hqcomm b' (hJ'E hb')
  have ha'q : Commute a' q := (hqcomm a' (hJ'E ha')).symm
  have key : ⁅a, b⁆ = ⁅a', b'⁆ := by
    rw [← hpa, ← hqb, hqb'.eq]
    rw [commutatorElement_mul_left_of_central hpa' (hpb'.mul_right hpq)]
    exact commutatorElement_mul_right_of_central ha'q
  rw [key]
  exact hcomm_le (Subgroup.commutator_mem_commutator ha' hb')

theorem l34g_inn_centralizer_of_perfect {Y : Type} [Group Y] (h : Group.IsPerfect Y) :
    centralizer (((MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)) =
      ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_centralizer_iff] at hσ
  have h1 : ∀ y z : Y, σ (y * z * y⁻¹) = y * σ z * y⁻¹ := by
    intro y z
    have hmem : MulAut.conj y ∈ (MulAut.conj : Y →* MulAut Y).range := ⟨y, rfl⟩
    have hc := DFunLike.congr_fun (hσ (MulAut.conj y) hmem) z
    simpa [MulAut.mul_apply, MulAut.conj_apply] using hc.symm
  have h2 : ∀ y w : Y, w * (y⁻¹ * σ y) = (y⁻¹ * σ y) * w := by
    intro y w
    obtain ⟨z, rfl⟩ := σ.surjective w
    have h3 : σ y * σ z = y * σ z * y⁻¹ * σ y := by
      have h4 := h1 y z
      rw [map_mul, map_mul, map_inv] at h4
      calc σ y * σ z = (σ y * σ z * (σ y)⁻¹) * σ y := by group
        _ = y * σ z * y⁻¹ * σ y := by rw [h4]
    calc σ z * (y⁻¹ * σ y) = y⁻¹ * (y * σ z * y⁻¹ * σ y) := by group
      _ = y⁻¹ * (σ y * σ z) := by rw [h3]
      _ = (y⁻¹ * σ y) * σ z := by group
  let φ : Y →* Subgroup.center Y :=
    { toFun := fun y => ⟨y⁻¹ * σ y, Subgroup.mem_center_iff.mpr (h2 y)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro y y'
        apply Subtype.ext
        change (y * y')⁻¹ * σ (y * y') = (y⁻¹ * σ y) * (y'⁻¹ * σ y')
        have hc := h2 y y'⁻¹
        calc (y * y')⁻¹ * σ (y * y') = y'⁻¹ * (y⁻¹ * σ y) * σ y' := by rw [map_mul]; group
          _ = (y⁻¹ * σ y) * y'⁻¹ * σ y' := by rw [hc]
          _ = (y⁻¹ * σ y) * (y'⁻¹ * σ y') := by group }
  have hker : commutator Y ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (φ b).2 (φ a)
  rw [h.commutator_eq_top] at hker
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun y => ?_
  have hy : y ∈ φ.ker := hker (Subgroup.mem_top y)
  have h6 : y⁻¹ * σ y = 1 := by
    have h := MonoidHom.mem_ker.1 hy
    exact congrArg Subtype.val h
  have h7 : σ y = y := by
    calc σ y = y * (y⁻¹ * σ y) := by group
      _ = y := by rw [h6, mul_one]
  simpa using h7

end CFSG.OddStandard.SmallF3.Omega
