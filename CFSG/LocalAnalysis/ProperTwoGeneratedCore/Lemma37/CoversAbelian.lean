module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverNorm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover
open scoped commutatorElement

namespace CoverExclusion

theorem inCenterOf_mul {G : Type*} [Group G] {Q : Subgroup G} {a b : G} (ha : InCenterOf Q a)
    (hb : InCenterOf Q b) : InCenterOf Q (a * b) :=
  ⟨Q.mul_mem ha.1 hb.1, fun q hq => (ha.2 q hq).mul_right (hb.2 q hq)⟩

theorem mul_self_eq_one_of_transitive {G : Type*} [Group G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {D : Subgroup G}
    (htrans : ∀ w w' : G, InCenterOf Q w → w ≠ 1 → InCenterOf Q w' → w' ≠ 1 →
      ∃ d ∈ D, d⁻¹ * w * d = w')
    {w : G} (hw : InCenterOf Q w) : w * w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hww
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hww (mul_one 1)
  obtain ⟨d, -, hd⟩ := htrans _ _ (inCenterOf_mul hw hw) hww hw hw1
  have hconj : (MulAut.conj d⁻¹).toMonoidHom (w * w) = w := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hd
  have hord : orderOf w = orderOf (w ^ 2) := by
    rw [pow_two, ← orderOf_injective (MulAut.conj d⁻¹).toMonoidHom (MulAut.conj d⁻¹).injective
      (w * w), hconj]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨w, hw.1⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [orderOf_pow' w two_ne_zero, hk] at hord
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hw1 hk
  · rw [pow_succ, Nat.gcd_eq_right (dvd_mul_left 2 _), Nat.mul_div_cancel _ two_pos] at hord
    have : 0 < 2 ^ k := pow_pos two_pos k
    omega

variable {K : Type*} [Group K]

theorem mul_self_eq_one_of_mem_center (hZ2 : Nat.card (Subgroup.center K) = 2) {s : K}
    (hs : s ∈ Subgroup.center K) : s * s = 1 := by
  have h := orderOf_dvd_natCard (⟨s, hs⟩ : Subgroup.center K)
  rw [hZ2, orderOf_dvd_iff_pow_eq_one, pow_two] at h
  exact congrArg Subtype.val h

theorem eq_or_of_mem_center (hZ2 : Nat.card (Subgroup.center K) = 2) {s t : K}
    (hs : s ∈ Subgroup.center K) (ht : t ∈ Subgroup.center K) : s = 1 ∨ t = 1 ∨ s = t := by
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center K)).mp hZ2
  by_cases hs1 : s = 1
  · exact Or.inl hs1
  by_cases ht1 : t = 1
  · exact Or.inr (Or.inl ht1)
  refine Or.inr (Or.inr ?_)
  have h1 := hu ⟨s, hs⟩ (fun h => hs1 (congrArg Subtype.val h))
  have h2 := hu ⟨t, ht⟩ (fun h => ht1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

variable {Q : Subgroup K}

theorem commutatorElement_mem_center {x y : K}
    (hx : (x : K ⧸ Subgroup.center K) ∈ centralImage Q) (hy : y ∈ centerPreimage Q) :
    ⁅x, y⁆ ∈ Subgroup.center K := by
  rw [← QuotientGroup.eq_one_iff]
  have hc := ((mem_centerPreimage_iff.mp hy).2 _ hx).eq
  rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, hc, mul_inv_cancel_right, mul_inv_cancel]

theorem mul_self_eq_of_mk_eq_conj (hZ2 : Nat.card (Subgroup.center K) = 2) {x y : K}
    {g : K ⧸ Subgroup.center K} (h : (x : K ⧸ Subgroup.center K) = g⁻¹ * y * g)
    (hy : y * y ∈ Subgroup.center K) : x * x = y * y := by
  set g' := Quotient.out g
  have hg : ((g'⁻¹ * y * g' : K) : K ⧸ Subgroup.center K) = x := by
    rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.out_eq']
  have hz := QuotientGroup.eq.mp hg
  set z := (g'⁻¹ * y * g')⁻¹ * x
  have hx : x = g'⁻¹ * y * g' * z := (mul_inv_cancel_left _ _).symm
  have hzc := Subgroup.mem_center_iff.mp hz
  have hyc := Subgroup.mem_center_iff.mp hy
  rw [hx, Commute.mul_mul_mul_comm (hzc _).symm, mul_self_eq_one_of_mem_center hZ2 hz, mul_one,
    show g'⁻¹ * y * g' * (g'⁻¹ * y * g') = g'⁻¹ * ((y * y) * g') by group, ← hyc g',
    inv_mul_cancel_left]

theorem mul_mul_self_eq {x y : K} (hc : ⁅y, x⁆ ∈ Subgroup.center K) :
    (x * y) * (x * y) = ⁅y, x⁆ * (x * x) * (y * y) := by
  have h1 : y * x = ⁅y, x⁆ * x * y := by
    rw [commutatorElement_def]
    group
  have h2 : x * ⁅y, x⁆ = ⁅y, x⁆ * x := Subgroup.mem_center_iff.mp hc x
  calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
    _ = x * ⁅y, x⁆ * x * y * y := by rw [h1]; simp only [mul_assoc]
    _ = ⁅y, x⁆ * (x * x) * (y * y) := by rw [h2]; simp only [mul_assoc]

theorem commutatorElement_mul_left_eq {x y y' : K} (hc : ⁅y', x⁆ ∈ Subgroup.center K) :
    ⁅y * y', x⁆ = ⁅y', x⁆ * ⁅y, x⁆ := by
  have h1 : ⁅y * y', x⁆ = y * ⁅y', x⁆ * y⁻¹ * ⁅y, x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [h1, Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right]

theorem exists_notMem_of_card_lt {α : Type*} [Finite α] (s : Finset α) (h : s.card < Nat.card α) :
    ∃ a, a ∉ s := by
  let _ : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ] at h
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨a, ha⟩

theorem mul_ne_one_of_ne {G : Type*} [Group G] {v v' : G} (hv : v * v = 1) (h : v ≠ v') :
    v * v' ≠ 1 := fun h' =>
  h ((inv_eq_of_mul_eq_one_right hv).symm.trans (inv_eq_of_mul_eq_one_right h'))

theorem centerPreimage_comm_of_card (hZ2 : Nat.card (Subgroup.center K) = 2)
    {D : Subgroup (K ⧸ Subgroup.center K)}
    (htrans : ∀ w w' : K ⧸ Subgroup.center K, InCenterOf (centralImage Q) w → w ≠ 1 →
      InCenterOf (centralImage Q) w' → w' ≠ 1 → ∃ d ∈ D, d⁻¹ * w * d = w')
    (hexp : ∀ w, InCenterOf (centralImage Q) w → w * w = 1)
    (hcard : 8 ≤ Nat.card {w : K ⧸ Subgroup.center K // InCenterOf (centralImage Q) w})
    {x y : K} (hx : x ∈ centerPreimage Q) (hy : y ∈ centerPreimage Q) : x * y = y * x := by
  classical
  have : Finite {w : K ⧸ Subgroup.center K // InCenterOf (centralImage Q) w} :=
    Nat.finite_of_card_ne_zero (by omega)
  have hsqZ : ∀ a ∈ centerPreimage Q, a * a ∈ Subgroup.center K := fun a ha => by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hexp _ (mem_centerPreimage_iff.mp ha)
  let one : {w : K ⧸ Subgroup.center K // InCenterOf (centralImage Q) w} := ⟨1, inCenterOf_one _⟩
  obtain ⟨w₁, hw₁⟩ := exists_notMem_of_card_lt {one}
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨w₂, hw₂⟩ := exists_notMem_of_card_lt {one, w₁}
    (lt_of_le_of_lt (Finset.card_le_two) (by omega))
  obtain ⟨w₃, hw₃⟩ := exists_notMem_of_card_lt {one, w₁, w₂, ⟨_, inCenterOf_mul w₁.2 w₂.2⟩}
    (lt_of_le_of_lt (Finset.card_le_four) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw₁ hw₂ hw₃
  have hne : ∀ {v v' : {w : K ⧸ Subgroup.center K // InCenterOf (centralImage Q) w}},
      v ≠ v' → (v : K ⧸ Subgroup.center K) ≠ v' := fun h h' => h (Subtype.ext h')
  have h1 : (w₁ : K ⧸ Subgroup.center K) ≠ 1 := hne hw₁
  have h2 : (w₂ : K ⧸ Subgroup.center K) ≠ 1 := hne hw₂.1
  have h3 : (w₃ : K ⧸ Subgroup.center K) ≠ 1 := hne hw₃.1
  have h12 := mul_ne_one_of_ne (hexp _ w₁.2) (hne hw₂.2).symm
  have h13 := mul_ne_one_of_ne (hexp _ w₁.2) (hne hw₃.2.1).symm
  have h23 := mul_ne_one_of_ne (hexp _ w₂.2) (hne hw₃.2.2.1).symm
  have h123 : (w₁ : K ⧸ Subgroup.center K) * (w₂ * w₃) ≠ 1 := by
    rw [← mul_assoc]
    exact mul_ne_one_of_ne (hexp _ (inCenterOf_mul w₁.2 w₂.2)) (hne hw₃.2.2.2).symm
  have hlift : ∀ v : {w : K ⧸ Subgroup.center K // InCenterOf (centralImage Q) w},
      Quotient.out (v : K ⧸ Subgroup.center K) ∈ centerPreimage Q := fun v =>
    mem_centerPreimage_iff.mpr (by rw [QuotientGroup.out_eq']; exact v.2)
  set x₁ := Quotient.out (w₁ : K ⧸ Subgroup.center K)
  set x₂ := Quotient.out (w₂ : K ⧸ Subgroup.center K)
  set x₃ := Quotient.out (w₃ : K ⧸ Subgroup.center K)
  have hx₁ : (x₁ : K ⧸ Subgroup.center K) = w₁ := QuotientGroup.out_eq' _
  have hx₂ : (x₂ : K ⧸ Subgroup.center K) = w₂ := QuotientGroup.out_eq' _
  have hx₃ : (x₃ : K ⧸ Subgroup.center K) = w₃ := QuotientGroup.out_eq' _
  set e := x₁ * x₁
  have he2 : e * e = 1 := mul_self_eq_one_of_mem_center hZ2 (hsqZ x₁ (hlift w₁))
  have hsq : ∀ a ∈ centerPreimage Q, (a : K ⧸ Subgroup.center K) ≠ 1 → a * a = e := by
    intro a ha ha1
    obtain ⟨d, -, hd⟩ := htrans _ _ w₁.2 h1 (mem_centerPreimage_iff.mp ha) ha1
    exact mul_self_eq_of_mk_eq_conj hZ2 (g := d) (by rw [hx₁, hd]) (hsqZ x₁ (hlift w₁))
  have hcomm : ∀ a ∈ centerPreimage Q, ∀ b ∈ centerPreimage Q,
      (a : K ⧸ Subgroup.center K) ≠ 1 → (b : K ⧸ Subgroup.center K) ≠ 1 →
      (a : K ⧸ Subgroup.center K) * b ≠ 1 → ⁅b, a⁆ = e := by
    intro a ha b hb ha1 hb1 hab1
    have h := mul_mul_self_eq (commutatorElement_mem_center (mem_centerPreimage_iff.mp hb).1 ha)
    rw [hsq _ ((centerPreimage Q).mul_mem ha hb) (by rwa [QuotientGroup.mk_mul]), hsq a ha ha1,
      hsq b hb hb1, mul_assoc, he2, mul_one] at h
    exact h.symm
  have he1 : e = 1 := by
    have k1 := hcomm _ (hlift w₁) _ (hlift w₂) (by rwa [hx₁]) (by rwa [hx₂])
      (by rwa [hx₁, hx₂])
    have k2 := hcomm _ (hlift w₁) _ (hlift w₃) (by rwa [hx₁]) (by rwa [hx₃])
      (by rwa [hx₁, hx₃])
    have k3 := hcomm _ (hlift w₁) _ ((centerPreimage Q).mul_mem (hlift w₂) (hlift w₃))
      (by rwa [hx₁]) (by rwa [QuotientGroup.mk_mul, hx₂, hx₃])
      (by rwa [QuotientGroup.mk_mul, hx₁, hx₂, hx₃])
    rw [commutatorElement_mul_left_eq (commutatorElement_mem_center
      (mem_centerPreimage_iff.mp (hlift w₃)).1 (hlift w₁)), k1, k2] at k3
    exact mul_eq_right.mp k3
  by_cases hx1 : (x : K ⧸ Subgroup.center K) = 1
  · exact (Subgroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff x).mp hx1) y).symm
  by_cases hy1 : (y : K ⧸ Subgroup.center K) = 1
  · exact Subgroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff y).mp hy1) x
  by_cases hxy1 : (x : K ⧸ Subgroup.center K) * y = 1
  · have hz := (QuotientGroup.eq_one_iff (N := Subgroup.center K) (x * y)).mp
      (by rwa [QuotientGroup.mk_mul])
    have h := Subgroup.mem_center_iff.mp hz x
    rw [mul_assoc] at h
    exact mul_left_cancel h
  · exact (commutatorElement_eq_one_iff_mul_comm.mp ((hcomm x hx y hy hx1 hy1 hxy1).trans he1)).symm

theorem centerPreimage_comm_of_commutator
    (hcomm : ∀ w, InCenterOf (centralImage Q) w →
      ∃ a ∈ centralImage Q, ∃ b ∈ centralImage Q, w = a * b * a⁻¹ * b⁻¹)
    {x y : K} (hx : x ∈ centerPreimage Q) (hy : y ∈ centerPreimage Q) : x * y = y * x := by
  obtain ⟨a, ha, b, hb, hab⟩ := hcomm _ (mem_centerPreimage_iff.mp hx)
  let H := (centralImage Q).comap (QuotientGroup.mk' (Subgroup.center K))
  have hmem : ∀ g : H, ⁅(g : K), y⁆ ∈ Subgroup.center K := fun g =>
    commutatorElement_mem_center (Q := Q)
      (show ((g : K) : K ⧸ Subgroup.center K) ∈ centralImage Q from g.2) hy
  let φ : H →* Subgroup.center K :=
    { toFun := fun g => ⟨⁅(g : K), y⁆, hmem g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by
        change ⁅(g : K) * h, y⁆ = ⁅(g : K), y⁆ * ⁅(h : K), y⁆
        rw [commutatorElement_mul_left_eq (hmem h)]
        exact (Subgroup.mem_center_iff.mp (hmem h) _).symm) }
  have ha' : Quotient.out a ∈ H := by
    change QuotientGroup.mk' _ (Quotient.out a) ∈ centralImage Q
    rwa [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
  have hb' : Quotient.out b ∈ H := by
    change QuotientGroup.mk' _ (Quotient.out b) ∈ centralImage Q
    rwa [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
  have h1 : φ ⁅(⟨_, ha'⟩ : H), (⟨_, hb'⟩ : H)⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.mp (φ _).2 _)
  have hcx : ((⁅Quotient.out a, Quotient.out b⁆ : K) : K ⧸ Subgroup.center K) = x := by
    rw [hab, commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.out_eq',
      QuotientGroup.out_eq']
  set c := ⁅Quotient.out a, Quotient.out b⁆
  have hcy : c * y = y * c := commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h1)
  have hz := Subgroup.mem_center_iff.mp (QuotientGroup.eq.mp hcx)
  have hxc : x = c * (c⁻¹ * x) := (mul_inv_cancel_left _ _).symm
  rw [hxc, mul_assoc, ← hz y, ← mul_assoc, hcy, mul_assoc]

end CoverExclusion

end CFSG.ProperTwoGeneratedCore.Lemma37
