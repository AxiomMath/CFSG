module

public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG
open scoped commutatorElement

variable {Q : Type*} [Group Q] [Finite Q]

theorem _root_.CFSG.IsExtraspecialPGroup.commutator_mem_center (hQ : IsExtraspecialPGroup 2 Q)
    (a b : Q) : ⁅a, b⁆ ∈ center Q := by
  rw [← hQ.2.1, _root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)

theorem _root_.CFSG.IsExtraspecialPGroup.sq_mem_center (hQ : IsExtraspecialPGroup 2 Q) (a : Q) :
    a ^ 2 ∈ center Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 Q) := ⟨hQ.1⟩
  rw [← hQ.2.2.1]
  exact pth_power_mem_frattini_of_isPGroup (R := Q) (p := 2) a

section Split

variable (hc : ∀ a b : Q, ⁅a, b⁆ ∈ center Q)

@[expose] def commHom (w : Q) : Q →* center Q where
  toFun x := ⟨⁅x, w⁆, hc x w⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    show ⁅x * y, w⁆ = ⁅x, w⁆ * ⁅y, w⁆
    have h := mem_center_iff.1 (hc y w) x
    have h2 := mem_center_iff.1 (hc x w) ⁅y, w⁆
    simp only [commutatorElement_def] at h h2 ⊢
    calc x * y * w * (x * y)⁻¹ * w⁻¹
        = x * (y * w * y⁻¹ * w⁻¹) * (w * x⁻¹ * w⁻¹) := by group
      _ = (y * w * y⁻¹ * w⁻¹) * x * (w * x⁻¹ * w⁻¹) := by rw [h]
      _ = (y * w * y⁻¹ * w⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group
      _ = (x * w * x⁻¹ * w⁻¹) * (y * w * y⁻¹ * w⁻¹) := h2

theorem _root_.CFSG.IsExtraspecialPGroup.exists_centralizer_eq_prod (hQ : IsExtraspecialPGroup 2 Q)
    (hcard : 2 ^ 5 ≤ Nat.card Q) {t : Q} (ht : orderOf t = 2) (hnc : t ∉ center Q) :
    ∃ E : Subgroup Q, IsExtraspecialPGroup 2 ↥E ∧ Nat.card Q = 4 * Nat.card E ∧
      center Q ≤ E ∧ (center ↥E).map E.subtype = center Q ∧ Disjoint E (zpowers t) ∧
      centralizer ({t} : Set Q) = E ⊔ zpowers t := by
  have hc := hQ.commutator_mem_center
  have hZ : Nat.card (center Q) = 2 := hQ.2.2.2
  obtain ⟨s, hs⟩ : ∃ s : Q, s * t ≠ t * s := by
    by_contra h
    push Not at h
    exact hnc (mem_center_iff.2 h)
  let Φ : Q →* center Q × center Q := (commHom hc s).prod (commHom hc t)
  have hΦ : ∀ x : Q, Φ x = (⟨⁅x, s⁆, hc x s⟩, ⟨⁅x, t⁆, hc x t⟩) := fun x => rfl
  have hker : ∀ x : Q, x ∈ Φ.ker ↔ ⁅x, s⁆ = 1 ∧ ⁅x, t⁆ = 1 := by
    intro x
    rw [MonoidHom.mem_ker, hΦ, Prod.mk_eq_one, Subtype.ext_iff, Subtype.ext_iff]
    rfl
  set a : center Q := ⟨⁅t, s⁆, hc t s⟩ with ha
  have ha1 : a ≠ 1 := by
    intro h
    have h' : ⁅t, s⁆ = 1 := congrArg Subtype.val h
    exact hs (commutatorElement_eq_one_iff_mul_comm.1 h').symm
  have hatop : zpowers a = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, hZ]
    have h2 : orderOf a ∣ 2 := hZ ▸ orderOf_dvd_natCard a
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · exact h
  have hao : orderOf a = 2 := by
    rw [← Nat.card_zpowers, hatop, Subgroup.card_top, hZ]
  have hΦt : Φ t = (a, 1) := by
    rw [hΦ]; ext <;> simp [ha]
  have hΦs : Φ s = (1, a⁻¹) := by
    rw [hΦ]; ext
    · simp
    · simp [ha, commutatorElement_inv]
  have hΦts : ∀ i j : ℤ, Φ (t ^ i * s ^ j) = (a ^ i, a⁻¹ ^ j) := by
    intro i j
    rw [map_mul, map_zpow, map_zpow, hΦt, hΦs]
    ext <;> simp
  have hrep : ∀ y : center Q × center Q, ∃ i j : ℤ, Φ (t ^ i * s ^ j) = y := by
    intro y
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 (hatop ▸ mem_top y.1 : y.1 ∈ zpowers a)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1
      (show y.2 ∈ zpowers a⁻¹ by rw [zpowers_inv, hatop]; exact mem_top _)
    exact ⟨i, j, by rw [hΦts]; exact Prod.ext hi hj⟩
  have hsurj : Function.Surjective Φ := fun y => by
    obtain ⟨i, j, h⟩ := hrep y
    exact ⟨_, h⟩
  have hdec : ∀ q : Q, ∃ i j : ℤ, q * (t ^ i * s ^ j)⁻¹ ∈ Φ.ker := by
    intro q
    obtain ⟨i, j, h⟩ := hrep (Φ q)
    exact ⟨i, j, by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]⟩
  have hcardQ : Nat.card Q = 4 * Nat.card Φ.ker := by
    have h := Subgroup.card_ker_mul_card_range Φ
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_prod, hZ] at h
    omega
  have hcZ : center Q ≤ Φ.ker := by
    intro x hx
    rw [hker]
    exact ⟨commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 hx s).symm,
      commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 hx t).symm⟩
  have hcentral : ∀ x ∈ Φ.ker, (∀ y ∈ Φ.ker, x * y = y * x) → x ∈ center Q := by
    intro x hx hxy
    rw [mem_center_iff]
    intro q
    obtain ⟨i, j, he⟩ := hdec q
    obtain ⟨hxs, hxt⟩ := (hker x).1 hx
    have hxs' : x * s = s * x := commutatorElement_eq_one_iff_mul_comm.1 hxs
    have hxt' : x * t = t * x := commutatorElement_eq_one_iff_mul_comm.1 hxt
    have hxti : x * t ^ i = t ^ i * x := ((Commute.zpow_right hxt' i))
    have hxsj : x * s ^ j = s ^ j * x := ((Commute.zpow_right hxs' j))
    have hxe := hxy _ he
    have key : ∀ e h : Q, x * e = e * x → x * h = h * x → x * (e * h) = (e * h) * x := by
      intro e h he' hh'
      rw [← mul_assoc, he', mul_assoc, hh', ← mul_assoc]
    have hxh : x * (t ^ i * s ^ j) = (t ^ i * s ^ j) * x := key _ _ hxti hxsj
    have := key _ _ hxe hxh
    rw [inv_mul_cancel_right] at this
    exact this.symm
  have h2t : ∀ k : ℤ, a ^ k = 1 → t ^ k = 1 := by
    intro k hk
    have h2 : (2 : ℤ) ∣ k := by
      have := orderOf_dvd_iff_zpow_eq_one.2 hk
      rw [hao] at this
      exact_mod_cast this
    refine orderOf_dvd_iff_zpow_eq_one.1 ?_
    rw [ht]
    exact_mod_cast h2
  have hdisj : Disjoint Φ.ker (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hx hxt
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    have hk : Φ (t ^ k) = 1 := hx
    rw [map_zpow, hΦt] at hk
    have hk1 : a ^ k = 1 := congrArg Prod.fst hk
    exact h2t k hk1
  have hs2 : s ^ (2 : ℤ) ∈ center Q := by
    rw [zpow_two, ← sq]; exact hQ.sq_mem_center s
  have hcentr : centralizer ({t} : Set Q) = Φ.ker ⊔ zpowers t := by
    apply le_antisymm
    · intro x hx
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hx
      obtain ⟨i, j, h⟩ := hrep (Φ x)
      have h' := h
      rw [hΦts] at h'
      have hj : a⁻¹ ^ j = 1 := by
        have h1 := congrArg Prod.snd h'
        have h2 : (Φ x).2 = 1 := Subtype.ext (commutatorElement_eq_one_iff_mul_comm.2 hxt)
        simpa [h2] using h1
      have hj2 : (2 : ℤ) ∣ j := by
        have := orderOf_dvd_iff_zpow_eq_one.2 hj
        rw [orderOf_inv, hao] at this
        exact_mod_cast this
      obtain ⟨m, rfl⟩ := hj2
      have hsj : s ^ (2 * m) ∈ center Q := by
        rw [zpow_mul]; exact zpow_mem hs2 m
      have hde : x * (t ^ i * s ^ (2 * m))⁻¹ ∈ Φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← h, mul_inv_cancel]
      have hx' : x = (x * (t ^ i * s ^ (2 * m))⁻¹ * s ^ (2 * m)) * t ^ i := by
        have hcm : s ^ (2 * m) * t ^ i = t ^ i * s ^ (2 * m) :=
          (mem_center_iff.1 hsj (t ^ i)).symm
        calc x = x * (t ^ i * s ^ (2 * m))⁻¹ * (t ^ i * s ^ (2 * m)) := by group
          _ = x * (t ^ i * s ^ (2 * m))⁻¹ * (s ^ (2 * m) * t ^ i) := by rw [hcm]
          _ = _ := by group
      rw [hx']
      exact Subgroup.mul_mem_sup (Φ.ker.mul_mem hde (hcZ hsj)) (zpow_mem (mem_zpowers t) i)
    · refine sup_le (fun x hx => ?_) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
      exact mem_centralizer_singleton_iff.2
        (commutatorElement_eq_one_iff_mul_comm.1 ((hker x).1 hx).2)
  have hZE : (center Q).subgroupOf Φ.ker = (center Q).subgroupOf Φ.ker := rfl
  have hnab : ∃ x : ↥Φ.ker, x ∉ (center Q).subgroupOf Φ.ker := by
    by_contra hcon
    push Not at hcon
    have hle : Φ.ker ≤ center Q := fun x hx => hcon ⟨x, hx⟩
    have : Nat.card Φ.ker ≤ 2 := hZ ▸ Subgroup.card_le_of_le hle
    omega
  have hext : IsExtraspecialPGroup 2 ↥Φ.ker := by
    refine CFSG.RankThree.PartOne.PlaneCommuting.isExtraspecialPGroup_of_pairing
      (hQ.1.to_subgroup _) (Z := (center Q).subgroupOf Φ.ker) ?_ ?_ ?_ ?_ ?_ hnab
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcZ).toEquiv]; exact hZ
    · intro x hx
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_center_iff.1 hx y)
    · intro x y
      exact hc x y
    · intro x
      exact hQ.sq_mem_center x
    · intro x hx
      exact hcentral x x.2 fun y hy => congrArg Subtype.val (hx ⟨y, hy⟩)
  refine ⟨Φ.ker, hext, hcardQ, hcZ, ?_, hdisj, hcentr⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hcentral x x.2 fun y hy => (congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)).symm
  · intro x hx
    refine ⟨⟨x, hcZ hx⟩, ?_, rfl⟩
    show _ ∈ center ↥Φ.ker
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.1 hx y)

end Split

end CFSG.EvenSporadicStandard.TwoB
