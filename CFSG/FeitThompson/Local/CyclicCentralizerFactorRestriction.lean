module

public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
public import CFSG.FeitThompson.Representations.PrimeCentralTorsionCharacteristic
import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct
import CFSG.FeitThompson.Local.HighRankCentralTorsionLine
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.Local.MaximalPlaneCentralizerPrimeTorsion

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {G : Type*} [Group G]

namespace IsInternalDirectProduct

variable {W U V : Subgroup G}

theorem mk' (hW : (W : Set G) = (U : Set G) * (V : Set G)) (hinf : U ⊓ V = ⊥)
    (hcomm : ∀ x ∈ U, ∀ y ∈ V, Commute x y) : IsInternalDirectProduct W U V :=
  ⟨fun u hu => show u ∈ (W : Set G) from hW ▸ ⟨u, hu, 1, one_mem _, mul_one u⟩,
    fun v hv => show v ∈ (W : Set G) from hW ▸ ⟨1, one_mem _, v, hv, one_mul v⟩,
    hW, hinf, commutator_eq_bot_iff_le_centralizer.2 fun _ hx =>
      mem_centralizer_iff.2 fun _ hy => (hcomm _ hx _ hy).symm⟩

theorem symm (h : IsInternalDirectProduct W U V) : IsInternalDirectProduct W V U := by
  refine mk' (Set.eq_of_subset_of_subset ?_ ?_) (by rw [inf_comm]; exact h.inf_eq_bot)
    fun x hx y hy => (h.commute hy hx).symm
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := (Set.ext_iff.1 h.coe_eq_mul x).1 hx
    exact ⟨v, hv, u, hu, (h.commute hu hv).symm.eq⟩
  · rintro x ⟨v, hv, u, hu, rfl⟩
    exact h.coe_eq_mul ▸ ⟨u, hu, v, hv, (h.commute hu hv).eq⟩

noncomputable def mulEquivProd (h : IsInternalDirectProduct W U V) : (U × V) ≃* W :=
  mulEquivProdOfCoeEqMul h.coe_eq_mul h.inf_eq_bot fun _ hx _ hy => h.commute hx hy

@[simp]
theorem coe_mulEquivProd_apply (h : IsInternalDirectProduct W U V) (x : U × V) :
    ((h.mulEquivProd x : W) : G) = (x.1 : G) * (x.2 : G) :=
  coe_mulEquivProdOfCoeEqMul_apply _ _ _ x

theorem isMulCommutative (h : IsInternalDirectProduct W U V) [IsMulCommutative U]
    [IsMulCommutative V] : IsMulCommutative W := by
  rw [isMulCommutative_iff_of_setLike]
  intro a ha b hb
  obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := (Set.ext_iff.1 h.coe_eq_mul a).1 ha
  obtain ⟨u₂, hu₂, v₂, hv₂, rfl⟩ := (Set.ext_iff.1 h.coe_eq_mul b).1 hb
  have cuu : Commute u₁ u₂ := setLike_mul_comm hu₁ hu₂
  have cvv : Commute v₁ v₂ := setLike_mul_comm hv₁ hv₂
  have c12 : Commute u₁ v₂ := h.commute hu₁ hv₂
  have c21 : Commute v₁ u₂ := (h.commute hu₂ hv₁).symm
  exact ((cuu.mul_right c12).mul_left (c21.mul_right cvv))

theorem inf_left (h : IsInternalDirectProduct W U V) {P : Subgroup G} (hUP : U ≤ P) :
    IsInternalDirectProduct (P ⊓ W) U (P ⊓ V) := by
  refine ⟨le_inf hUP h.left_le, le_inf inf_le_left (inf_le_right.trans h.right_le),
    Set.eq_of_subset_of_subset ?_ ?_, ?_, ?_⟩
  · rintro x ⟨hxP, hxW⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := (Set.ext_iff.1 h.coe_eq_mul x).1 hxW
    have hvP : v ∈ P := by
      have h' : u⁻¹ * (u * v) ∈ P := mul_mem (inv_mem (hUP hu)) hxP
      simpa using h'
    exact ⟨u, hu, v, ⟨hvP, hv⟩, rfl⟩
  · rintro x ⟨u, hu, v, ⟨hvP, hv⟩, rfl⟩
    exact ⟨mul_mem (hUP hu) hvP, h.coe_eq_mul ▸ ⟨u, hu, v, hv, rfl⟩⟩
  · exact le_bot_iff.1 (h.inf_eq_bot ▸ inf_le_inf_left U inf_le_right)
  · exact le_bot_iff.1 (h.commutator_eq_bot ▸ commutator_mono le_rfl inf_le_right)

end IsInternalDirectProduct

def subgroupCenterTorsionBy (P : Subgroup G) (n : ℕ) : Subgroup G :=
  (centerTorsionBy P n).map P.subtype

theorem mem_subgroupCenterTorsionBy {P : Subgroup G} {n : ℕ} {z : G} :
    z ∈ subgroupCenterTorsionBy P n ↔ z ∈ P ∧ (∀ x ∈ P, x * z = z * x) ∧ z ^ n = 1 := by
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    rw [mem_centerTorsionBy] at hw
    exact ⟨w.2, fun x hx => congrArg Subtype.val (mem_center_iff.1 hw.1 ⟨x, hx⟩),
      congrArg Subtype.val hw.2⟩
  · rintro ⟨hz, hcomm, hzn⟩
    refine Subgroup.mem_map.2 ⟨⟨z, hz⟩, mem_centerTorsionBy.2
      ⟨mem_center_iff.2 fun x => Subtype.ext (hcomm x x.2), Subtype.ext (by simpa using hzn)⟩, rfl⟩

theorem subgroupCenterTorsionBy_le {P : Subgroup G} {n : ℕ} : subgroupCenterTorsionBy P n ≤ P :=
  fun _ hz => (mem_subgroupCenterTorsionBy.1 hz).1

theorem subgroupCenterTorsionBy_le_centralizer {P : Subgroup G} {n : ℕ} :
    subgroupCenterTorsionBy P n ≤ centralizer (P : Set G) := fun _ hz =>
  mem_centralizer_iff.2 fun x hx => (mem_subgroupCenterTorsionBy.1 hz).2.1 x hx

theorem subgroupCenterTorsionBy_le_omega1 {P : Subgroup G} {n : ℕ} :
    subgroupCenterTorsionBy P n ≤ omega1 n G := fun _ hz =>
  mem_omega1_of_pow_eq_one (mem_subgroupCenterTorsionBy.1 hz).2.2

theorem subgroupCenterTorsionBy_top {n : ℕ} :
    subgroupCenterTorsionBy (⊤ : Subgroup G) n = centerTorsionBy G n := by
  ext z
  rw [mem_subgroupCenterTorsionBy, mem_centerTorsionBy, mem_center_iff]
  simp

variable {p d : ℕ}

theorem elementaryAbelianPRank_eq_of_card_eq [Finite G] (hp : p.Prime) {A : Subgroup G}
    [IsMulCommutative A] (hexp : ∀ x ∈ A, x ^ p = 1) (hcard : Nat.card A = p ^ d) :
    elementaryAbelianPRank p A = d := by
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  refine Nat.le_antisymm (elementaryAbelianPRank_le fun e he => ?_)
    (le_elementaryAbelianPRank hp.one_lt ?_)
  · obtain ⟨H, hHcard⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks he
    have hdvd : p ^ e ∣ p ^ d := by
      rw [← hHcard, ← hcard]
      exact H.card_subgroup_dvd_card
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  · obtain ⟨f⟩ := nonempty_mulEquiv_pi_of_exponent (d := d) (G := (A : Subgroup G)) hp
      (fun x => Subtype.ext (hexp x.1 x.2)) hcard
    exact mem_elementaryAbelianRanks.2 ⟨⊤, ⟨(Subgroup.topEquiv).trans f⟩⟩

theorem maximal_isElementaryAbelianSubgroup_iff {E : Subgroup G} :
    Maximal (IsElementaryAbelianSubgroup p) E ↔
      Maximal (fun A : Subgroup G => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E := by
  simp only [Maximal, isElementaryAbelianSubgroup_iff]

variable {R : Type*} [Group R] {E P Y : Subgroup R}

theorem subgroupCenterTorsionBy_le_of_maximal (hE : Maximal (IsElementaryAbelianSubgroup p) E)
    (hEP : E ≤ P) : subgroupCenterTorsionBy P p ≤ E := by
  intro z hz
  obtain ⟨-, hcomm, hzp⟩ := mem_subgroupCenterTorsionBy.1 hz
  exact mem_of_maximal_of_mem_centralizer_of_pow_eq_one
    (maximal_isElementaryAbelianSubgroup_iff.1 hE)
    (mem_centralizer_iff.2 fun e he => hcomm e (hEP he)) hzp

theorem centerTorsionBy_le_subgroupCenterTorsionBy
    (hE : Maximal (IsElementaryAbelianSubgroup p) E) (hEP : E ≤ P) :
    centerTorsionBy R p ≤ subgroupCenterTorsionBy P p := fun _ hz =>
  mem_subgroupCenterTorsionBy.2
    ⟨hEP (centerTorsionBy_le_of_maximal (maximal_isElementaryAbelianSubgroup_iff.1 hE) hz),
      fun x _ => mem_center_iff.1 (mem_center_of_mem_centerTorsionBy hz) x,
      pow_eq_one_of_mem_centerTorsionBy hz⟩

theorem exists_line_ne (hp : p.Prime) (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcard : Nat.card E = p ^ 2)
    (hZ₁E : centerTorsionBy R p ≤ E) (hZ₁card : Nat.card (centerTorsionBy R p) = p) :
    ∃ A₀ : Subgroup R, A₀ ≤ E ∧ Nat.card A₀ = p ∧ A₀ ≠ centerTorsionBy R p := by
  have hp1 := hp.one_lt
  have hlt : centerTorsionBy R p < E := by
    refine lt_of_le_of_ne hZ₁E fun h => ?_
    rw [h, hEcard] at hZ₁card
    nlinarith [hZ₁card, pow_pos hp.pos 2]
  obtain ⟨x, hxE, hxZ⟩ := SetLike.exists_of_lt hlt
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ one_mem _)
  have := Fact.mk hp
  exact ⟨zpowers x, zpowers_le.2 hxE, by rw [Nat.card_zpowers, orderOf_eq_prime (hEexp x hxE) hx1],
    fun h => hxZ (h ▸ mem_zpowers x)⟩

theorem subgroupCenterTorsionBy_eq_centerTorsionBy [Finite R] (hp : p.Prime)
    (hEmax : Maximal (IsElementaryAbelianSubgroup p) E) (hEcard : Nat.card E = p ^ 2)
    (hEP : E ≤ P) (hPnc : ¬ IsMulCommutative P)
    (hZ₁card : Nat.card (centerTorsionBy R p) = p) (hYcyc : IsCyclic Y)
    (hprod : ∀ A₀ : Subgroup R, A₀ ≤ E → Nat.card A₀ = p → A₀ ≠ centerTorsionBy R p →
      IsInternalDirectProduct (centralizer (E : Set R)) A₀ Y) :
    subgroupCenterTorsionBy P p = centerTorsionBy R p := by
  have := hYcyc
  have hZ₁E : centerTorsionBy R p ≤ E :=
    centerTorsionBy_le_of_maximal (maximal_isElementaryAbelianSubgroup_iff.1 hEmax)
  have hZ₀E : subgroupCenterTorsionBy P p ≤ E := subgroupCenterTorsionBy_le_of_maximal hEmax hEP
  have hZ₁Z₀ : centerTorsionBy R p ≤ subgroupCenterTorsionBy P p :=
    centerTorsionBy_le_subgroupCenterTorsionBy hEmax hEP
  obtain ⟨A₀, hA₀E, hA₀card, hA₀ne⟩ :=
    exists_line_ne hp hEmax.prop.pow_eq_one hEcard hZ₁E hZ₁card
  have : IsMulCommutative E := hEmax.prop.isMulCommutative
  have : IsMulCommutative A₀ := isMulCommutative_of_le hA₀E
  have : IsMulCommutative (centralizer (E : Set R)) :=
    (hprod A₀ hA₀E hA₀card hA₀ne).isMulCommutative
  have hne : subgroupCenterTorsionBy P p ≠ E := by
    intro h
    refine hPnc (isMulCommutative_of_le (A := centralizer (E : Set R)) fun x hx => ?_)
    exact mem_centralizer_iff.2 fun e he =>
      ((mem_subgroupCenterTorsionBy.1 (h.ge he)).2.1 x hx).symm
  have hlt : Nat.card (subgroupCenterTorsionBy P p) < Nat.card E := by
    by_contra hcon
    exact hne (eq_of_le_of_card_ge hZ₀E (not_lt.1 hcon))
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).1 (hEcard ▸ card_dvd_of_le hZ₀E)
  have hpdvd : p ∣ Nat.card (subgroupCenterTorsionBy P p) := by
    have h' := card_dvd_of_le hZ₁Z₀
    rwa [hZ₁card] at h'
  have hklt : k < 2 :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).1 (by rw [← hk, ← hEcard]; exact hlt)
  have hkne : k ≠ 0 := by
    rintro rfl
    rw [hk, pow_zero] at hpdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpdvd)
  have hcardZ₀ : Nat.card (subgroupCenterTorsionBy P p) = p := by
    rw [hk, show k = 1 by omega, pow_one]
  exact (eq_of_le_of_card_ge hZ₁Z₀ (by rw [hcardZ₀, hZ₁card])).symm

theorem isInternalDirectProduct_inf_centralizer (hEP : E ≤ P) {A₀ : Subgroup R} (hA₀E : A₀ ≤ E)
    (hprod : IsInternalDirectProduct (centralizer (E : Set R)) A₀ Y) :
    IsInternalDirectProduct (P ⊓ centralizer (E : Set R)) A₀ (P ⊓ Y) :=
  hprod.inf_left (hA₀E.trans hEP)

theorem isCyclic_inf_of_isCyclic_right (P Y : Subgroup R) (hYcyc : IsCyclic Y) :
    IsCyclic (P ⊓ Y : Subgroup R) :=
  have := hYcyc
  isCyclic_of_le inf_le_right

theorem subgroupCenterTorsionBy_le_inf [Finite R] (hp : p.Prime)
    (hEmax : Maximal (IsElementaryAbelianSubgroup p) E) (hEcard : Nat.card E = p ^ 2)
    (hEP : E ≤ P) (hPnc : ¬ IsMulCommutative P)
    (hZ₁card : Nat.card (centerTorsionBy R p) = p) (hYcyc : IsCyclic Y)
    (hZ₁Y : centerTorsionBy R p ≤ Y)
    (hprod : ∀ A₀ : Subgroup R, A₀ ≤ E → Nat.card A₀ = p → A₀ ≠ centerTorsionBy R p →
      IsInternalDirectProduct (centralizer (E : Set R)) A₀ Y) :
    subgroupCenterTorsionBy P p ≤ P ⊓ Y :=
  le_inf subgroupCenterTorsionBy_le
    ((subgroupCenterTorsionBy_eq_centerTorsionBy hp hEmax hEcard hEP hPnc hZ₁card hYcyc
      hprod).le.trans hZ₁Y)

theorem plane_centralizer_restriction [Finite R] (hp : p.Prime)
    (hEmax : Maximal (IsElementaryAbelianSubgroup p) E) (hEcard : Nat.card E = p ^ 2)
    (hEP : E ≤ P) (hPnc : ¬ IsMulCommutative P)
    (hZ₁card : Nat.card (centerTorsionBy R p) = p) (hYcyc : IsCyclic Y)
    (hZ₁Y : centerTorsionBy R p ≤ Y)
    (hprod : ∀ A₀ : Subgroup R, A₀ ≤ E → Nat.card A₀ = p → A₀ ≠ centerTorsionBy R p →
      IsInternalDirectProduct (centralizer (E : Set R)) A₀ Y) :
    subgroupCenterTorsionBy P p = centerTorsionBy R p ∧
      (∀ A₀ : Subgroup R, A₀ ≤ E → Nat.card A₀ = p → A₀ ≠ centerTorsionBy R p →
        IsInternalDirectProduct (P ⊓ centralizer (E : Set R)) A₀ (P ⊓ Y)) ∧
      IsCyclic (P ⊓ Y : Subgroup R) ∧ subgroupCenterTorsionBy P p ≤ P ⊓ Y :=
  ⟨subgroupCenterTorsionBy_eq_centerTorsionBy hp hEmax hEcard hEP hPnc hZ₁card hYcyc hprod,
    fun A₀ hA₀E hA₀card hA₀ne =>
      isInternalDirectProduct_inf_centralizer hEP hA₀E (hprod A₀ hA₀E hA₀card hA₀ne),
    isCyclic_inf_of_isCyclic_right P Y hYcyc,
    subgroupCenterTorsionBy_le_inf hp hEmax hEcard hEP hPnc hZ₁card hYcyc hZ₁Y hprod⟩

end

end CFSG.FeitThompson
