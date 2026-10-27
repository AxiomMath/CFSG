module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

private lemma conjNormal_mul_inv_mem_ker {X P : Type*} [Group X] [Group P] {K : Subgroup X}
    [K.Normal] {t : X} (q : K →* P) (π : P)
    (hq : ∀ k : K, q (MulAut.conjNormal t k) = π * q k * π⁻¹)
    (k : K) (hk : q k ∈ Subgroup.centralizer ({π} : Set P)) :
    MulAut.conjNormal t k * k⁻¹ ∈ q.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hq k]
  have hcomm : π * q k * π⁻¹ = q k := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hk
    rw [← hk]; simp
  rw [hcomm]; simp

private def conjNormalMulInvHom {X P : Type*} [Group X] [Group P] {K : Subgroup X}
    [K.Normal] {t : X} (q : K →* P) (hker : q.ker ≤ Subgroup.center K) (π : P)
    (hq : ∀ k : K, q (MulAut.conjNormal t k) = π * q k * π⁻¹)
    (H : Subgroup K)
    (hH : H ≤ (Subgroup.centralizer ({π} : Set P)).comap q) :
    H →* K where
  toFun k := MulAut.conjNormal t (k : K) * (k : K)⁻¹
  map_one' := by simp
  map_mul' := by
    intro a b
    have hbcenter : MulAut.conjNormal t (b : K) * (b : K)⁻¹ ∈ Subgroup.center K :=
      hker (conjNormal_mul_inv_mem_ker q π hq (b : K) (hH b.2))
    rw [Subgroup.mem_center_iff] at hbcenter
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
    rw [mul_assoc (MulAut.conjNormal t (a : K)) (MulAut.conjNormal t (b : K))
          ((b : K)⁻¹ * (a : K)⁻¹),
        ← mul_assoc (MulAut.conjNormal t (b : K)) (b : K)⁻¹ (a : K)⁻¹,
        ← hbcenter (a : K)⁻¹,
        ← mul_assoc (MulAut.conjNormal t (a : K)) (a : K)⁻¹
          (MulAut.conjNormal t (b : K) * (b : K)⁻¹)]

private lemma conjNormal_mul_inv_mul_comm {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    {t : X} {a b : K}
    (hb : MulAut.conjNormal t b * b⁻¹ ∈ Subgroup.center K) :
    MulAut.conjNormal t (a * b) * (a * b)⁻¹ =
      (MulAut.conjNormal t a * a⁻¹) * (MulAut.conjNormal t b * b⁻¹) := by
  rw [Subgroup.mem_center_iff] at hb
  simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
  rw [mul_assoc (MulAut.conjNormal t a) (MulAut.conjNormal t b) (b⁻¹ * a⁻¹),
      ← mul_assoc (MulAut.conjNormal t b) b⁻¹ a⁻¹,
      ← hb a⁻¹,
      ← mul_assoc (MulAut.conjNormal t a) a⁻¹ (MulAut.conjNormal t b * b⁻¹)]

private lemma conjNormal_mul_inv_mem_center_of {X P : Type*} [Group X] [Group P]
    {K : Subgroup X} [K.Normal] {t : X} (q : K →* P)
    (hker : q.ker ≤ Subgroup.center K)
    (hq : ∀ k : K, q (MulAut.conjNormal t k) = q k) (k : K) :
    MulAut.conjNormal t k * k⁻¹ ∈ Subgroup.center K := by
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, hq k]
  simp

private lemma card_subgroupOf_eq {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  have h := Subgroup.card_map_of_injective (K := H.subgroupOf K) (f := K.subtype)
    K.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype] at h
  exact h.symm

theorem card_range_inf_centralizer_le {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    [K.Normal] {t : X} {P : Type*} [Group P] (q : K →* P) (hker : q.ker ≤ Subgroup.center K)
    (π : P) (hq : ∀ k : K, q (MulAut.conjNormal t k) = π * q k * π⁻¹) :
    Nat.card (q.range ⊓ centralizer ({π} : Set P) : Subgroup P) ≤
      Nat.card (K ⊓ centralizer ({t} : Set X) : Subgroup X) := by
  classical
  haveI : Finite K := Finite.of_injective (Subtype.val : K → X) Subtype.val_injective
  set Kt : Subgroup K := (Subgroup.centralizer ({π} : Set P)).comap q with hKt
  let c : Kt →* K := conjNormalMulInvHom q hker π hq Kt le_rfl
  let q' : Kt →* P := q.comp Kt.subtype
  have hZle : q.ker ≤ Kt := by
    intro k hk
    show q k ∈ Subgroup.centralizer ({π} : Set P)
    rw [MonoidHom.mem_ker] at hk
    rw [hk]
    exact Subgroup.one_mem _
  have hCle : (Subgroup.centralizer ({t} : Set X)).subgroupOf K ≤ Kt := by
    intro x hx
    show q x ∈ Subgroup.centralizer ({π} : Set P)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx' : (x : X) * t = t * (x : X) :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    have hconj : MulAut.conjNormal t x = x := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, ← hx']
      simp
    have hqx : q x = π * q x * π⁻¹ := by
      have h := hq x
      rwa [hconj] at h
    conv_lhs => rw [hqx]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hkerq : MonoidHom.ker q' = (q.ker).subgroupOf Kt := by
    ext k
    exact Iff.rfl
  have hcard_Zsub : Nat.card ((q.ker).subgroupOf Kt) = Nat.card q.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv
  have hrange_le : MonoidHom.range c ≤ q.ker := by
    rintro - ⟨k, rfl⟩
    exact conjNormal_mul_inv_mem_ker q π hq (k : K) (k.2)
  have hcard_c : Nat.card (MonoidHom.ker c) * Nat.card (MonoidHom.range c) = Nat.card Kt :=
    Subgroup.card_ker_mul_card_range c
  have hcard_q : Nat.card (MonoidHom.ker q') * Nat.card (MonoidHom.range q') = Nat.card Kt :=
    Subgroup.card_ker_mul_card_range q'
  have hZpos : 0 < Nat.card q.ker := Nat.card_pos
  have hle : Nat.card (MonoidHom.range q') ≤ Nat.card (MonoidHom.ker c) := by
    have hmain : Nat.card q.ker * Nat.card (MonoidHom.range q') ≤
        Nat.card q.ker * Nat.card (MonoidHom.ker c) := by
      calc Nat.card q.ker * Nat.card (MonoidHom.range q')
          = Nat.card (MonoidHom.ker q') * Nat.card (MonoidHom.range q') := by
            rw [hkerq, hcard_Zsub]
        _ = Nat.card Kt := hcard_q
        _ = Nat.card (MonoidHom.ker c) * Nat.card (MonoidHom.range c) := hcard_c.symm
        _ ≤ Nat.card (MonoidHom.ker c) * Nat.card q.ker :=
            Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hrange_le)
        _ = Nat.card q.ker * Nat.card (MonoidHom.ker c) := by rw [Nat.mul_comm]
    exact Nat.le_of_mul_le_mul_left hmain hZpos
  have hker_c : MonoidHom.ker c =
      ((Subgroup.centralizer ({t} : Set X)).subgroupOf K).subgroupOf Kt := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      change MulAut.conjNormal t (k : K) * (k : K)⁻¹ = 1 at hk
      have hconj : MulAut.conjNormal t (k : K) = (k : K) := mul_inv_eq_one.mp hk
      have hx : t * (k : X) * t⁻¹ = (k : X) := by
        rw [← MulAut.conjNormal_apply]
        exact congrArg Subtype.val hconj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    · intro hk
      rw [Subgroup.mem_centralizer_singleton_iff] at hk
      have hconj : MulAut.conjNormal t (k : K) = (k : K) := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, ← hk]
        simp
      show MulAut.conjNormal t (k : K) * (k : K)⁻¹ = 1
      rw [hconj]; simp
  have hcard_ker_c : Nat.card (MonoidHom.ker c) =
      Nat.card (K ⊓ centralizer ({t} : Set X) : Subgroup X) := by
    calc Nat.card (MonoidHom.ker c)
        = Nat.card (((Subgroup.centralizer ({t} : Set X)).subgroupOf K).subgroupOf Kt) := by
          rw [hker_c]
      _ = Nat.card ((Subgroup.centralizer ({t} : Set X)).subgroupOf K) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv
      _ = Nat.card ((Subgroup.centralizer ({t} : Set X)) ⊓ K : Subgroup X) :=
          card_subgroupOf_eq _ _
      _ = Nat.card (K ⊓ centralizer ({t} : Set X) : Subgroup X) := by rw [inf_comm]
  have hq'range : MonoidHom.range q' = q.range ⊓ Subgroup.centralizer ({π} : Set P) := by
    calc MonoidHom.range q' = Kt.map q := by
          rw [show q' = q.comp Kt.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
      _ = ((Subgroup.centralizer ({π} : Set P)).comap q).map q := by rw [hKt]
      _ = q.range ⊓ Subgroup.centralizer ({π} : Set P) := Subgroup.map_comap_eq q _
  calc Nat.card (q.range ⊓ centralizer ({π} : Set P) : Subgroup P)
      = Nat.card (MonoidHom.range q') := by rw [hq'range]
    _ ≤ Nat.card (MonoidHom.ker c) := hle
    _ = Nat.card (K ⊓ centralizer ({t} : Set X) : Subgroup X) := hcard_ker_c

theorem le_centralizer_of_perfect {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hK : ⁅K, K⁆ = K) {t : X} {P : Type*} [Group P] (q : K →* P)
    (hker : q.ker ≤ Subgroup.center K) (hq : ∀ k : K, q (MulAut.conjNormal t k) = q k) :
    K ≤ centralizer ({t} : Set X) := by
  classical
  let f : K →* K :=
  { toFun := fun k => MulAut.conjNormal t k * k⁻¹
    map_one' := by simp
    map_mul' := fun a b =>
      conjNormal_mul_inv_mul_comm (conjNormal_mul_inv_mem_center_of q hker hq b) }
  have hf_center : ∀ k : K, f k ∈ Subgroup.center K :=
    fun k => conjNormal_mul_inv_mem_center_of q hker hq k
  let c : K →* Subgroup.center K := f.codRestrict (Subgroup.center K) hf_center
  haveI : Group.IsPerfect K := (Subgroup.isPerfect_iff).mpr hK
  have hcomm : commutator K ≤ c.ker := Abelianization.commutator_subset_ker c
  have hker_top : c.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top]
    exact hcomm
  have hc : c = 1 := MonoidHom.ker_eq_top_iff.mp hker_top
  have hc_one : ∀ k : K, c k = 1 := fun k => by rw [hc]; rfl
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj : MulAut.conjNormal t (⟨x, hx⟩ : K) = ⟨x, hx⟩ := by
    have hval : f ⟨x, hx⟩ = 1 := by
      have h := congrArg Subtype.val (hc_one ⟨x, hx⟩)
      change f ⟨x, hx⟩ = 1 at h
      exact h
    exact mul_inv_eq_one.mp hval
  have hx' : t * x * t⁻¹ = x := by
    have h := congrArg Subtype.val hconj
    rw [MulAut.conjNormal_apply] at h
    simpa using h
  exact (mul_inv_eq_iff_eq_mul.mp hx').symm

end CFSG.OddStandard.AltStdSec.SwapPartner
