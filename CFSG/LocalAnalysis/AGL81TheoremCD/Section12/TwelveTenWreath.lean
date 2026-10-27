module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Wreath

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

variable {G : Type} [Group G] [Finite G]

private def wCoord : W3 := ⟨fun x => x, 1⟩

private def wSwap : W3 := ⟨1, Multiplicative.ofAdd 1⟩

private theorem ofAdd_one_ne_one : (Multiplicative.ofAdd (1 : ZMod 3) : M3) ≠ 1 := by
  intro h
  exact one_ne_zero (Multiplicative.ofAdd.injective h)

private theorem wSwap_not_mem : wSwap ∉ wBase := by
  rw [mem_wBase]
  exact ofAdd_one_ne_one

private theorem center_le_wBase : Subgroup.center W3 ≤ wBase := by
  intro z hz
  by_contra hzB
  have hzr : z.right ≠ 1 := fun h => hzB (mem_wBase.mpr h)
  have hcomm : wCoord * z = z * wCoord := Subgroup.mem_center_iff.mp hz wCoord
  have hconst := left_const_of_commute hzr rfl hcomm 1 (Multiplicative.ofAdd 1)
  exact ofAdd_one_ne_one (by simpa [wCoord] using hconst.symm)

private theorem mem_center_of_mem_wBase_of_left_const {A : W3} (hA : A ∈ wBase)
    (hc : ∀ x y : M3, A.left x = A.left y) : A ∈ Subgroup.center W3 := by
  rw [Subgroup.mem_center_iff]
  intro w
  apply RegularWreathProduct.ext
  · funext x
    rw [RegularWreathProduct.mul_left, RegularWreathProduct.mul_left]
    simp only [Pi.mul_apply]
    calc w.left x * A.left (w.right⁻¹ * x)
        = w.left x * A.left x :=
          congrArg (fun c => w.left x * c) (hc (w.right⁻¹ * x) x)
      _ = A.left x * w.left x := mul_comm _ _
      _ = A.left x * w.left (A.right⁻¹ * x) := by
          rw [show A.right⁻¹ = 1 from inv_eq_one.mpr (mem_wBase.mp hA), one_mul]
  · simp [RegularWreathProduct.mul_right, mem_wBase.mp hA]

private theorem mem_center_of_mem_wBase_of_commute_not_mem_wBase {A S : W3}
    (hA : A ∈ wBase) (hS : S ∉ wBase) (hc : Commute A S) : A ∈ Subgroup.center W3 := by
  have hSr : S.right ≠ 1 := fun h => hS (mem_wBase.mpr h)
  have hAr : A.right = 1 := mem_wBase.mp hA
  refine mem_center_of_mem_wBase_of_left_const hA fun x y => ?_
  exact left_const_of_commute hSr hAr ((commute_iff_eq A S).mp hc) x y

private def centerEquivM3 : ↥(Subgroup.center W3) ≃ M3 where
  toFun z := (z : W3).left 1
  invFun c :=
    ⟨⟨fun _ => c, 1⟩, mem_center_of_mem_wBase_of_left_const rfl fun _ _ => rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext x
      have hzB : (z : W3) ∈ wBase := center_le_wBase z.2
      have hzr : (z : W3).right = 1 := mem_wBase.mp hzB
      have hSr : wSwap.right ≠ 1 := fun h => wSwap_not_mem (mem_wBase.mpr h)
      have hcomm : (z : W3) * wSwap = wSwap * (z : W3) :=
        (Subgroup.mem_center_iff.mp z.2 wSwap).symm
      have hconst := left_const_of_commute hSr hzr hcomm x 1
      simpa using hconst.symm
    · exact (mem_wBase.mp (center_le_wBase z.2)).symm
  right_inv _ := rfl

private theorem card_center_W3 : Nat.card (Subgroup.center W3) = 3 := by
  rw [Nat.card_congr centerEquivM3, card_M3]

private theorem mem_baseIn_iff {Q : Subgroup G} (e : ↥Q ≃* W3) {x : G} (hx : x ∈ Q) :
    x ∈ baseIn e ↔ e ⟨x, hx⟩ ∈ wBase := by
  constructor
  · intro h
    rw [baseIn, Subgroup.mem_map] at h
    obtain ⟨q, hq, hqx⟩ := h
    rw [Subgroup.mem_map] at hq
    obtain ⟨w, hw, hwq⟩ := hq
    have hq' : q = ⟨x, hx⟩ := Subtype.ext hqx
    have heq : e ⟨x, hx⟩ = w := by
      rw [← hq', ← hwq]
      simp
    rw [heq]
    exact hw
  · intro h
    rw [baseIn, Subgroup.mem_map]
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_map]
    exact ⟨e ⟨x, hx⟩, h, by simp⟩

theorem card_centerIn_of_mulEquiv_W3 {Q : Subgroup G} (e : ↥Q ≃* W3) :
    Nat.card (CFSG.centerIn Q) = 3 := by
  rw [CFSG.centerIn_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective,
    Nat.card_congr (Subgroup.centerCongr e).toEquiv, card_center_W3]

theorem centerIn_le_baseIn {Q : Subgroup G} (e : ↥Q ≃* W3) : CFSG.centerIn Q ≤ baseIn e := by
  intro x hx
  have hxQ : x ∈ Q := hx.1
  have hcenterQ : (⟨x, hxQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (y : G) y.2)
  have hinW : e ⟨x, hxQ⟩ ∈ Subgroup.center W3 := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hcenterQ
  exact (mem_baseIn_iff e hxQ).mpr (center_le_wBase hinW)

theorem mem_centerIn_of_commute_of_not_mem_baseIn {Q : Subgroup G} (e : ↥Q ≃* W3) {s a : G}
    (hs : s ∈ Q) (hsA : s ∉ baseIn e) (ha : a ∈ baseIn e) (hc : Commute a s) :
    a ∈ CFSG.centerIn Q := by
  have haQ : a ∈ Q := baseIn_le e ha
  have hA : e ⟨a, haQ⟩ ∈ wBase := (mem_baseIn_iff e haQ).mp ha
  have hS : e ⟨s, hs⟩ ∉ wBase := fun h => hsA ((mem_baseIn_iff e hs).mpr h)
  have hcQ : (⟨a, haQ⟩ : ↥Q) * ⟨s, hs⟩ = ⟨s, hs⟩ * ⟨a, haQ⟩ :=
    Subtype.ext ((commute_iff_eq a s).mp hc)
  have hcW : Commute (e ⟨a, haQ⟩) (e ⟨s, hs⟩) := by
    apply (commute_iff_eq _ _).mpr
    rw [← map_mul, ← map_mul]
    exact congrArg e hcQ
  have hAc : e ⟨a, haQ⟩ ∈ Subgroup.center W3 :=
    mem_center_of_mem_wBase_of_commute_not_mem_wBase hA hS hcW
  refine ⟨haQ, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro y hy
  have hAY : Commute (e ⟨y, hy⟩) (e ⟨a, haQ⟩) :=
    (commute_iff_eq _ _).mpr (Subgroup.mem_center_iff.mp hAc (e ⟨y, hy⟩))
  have hcommQ : (⟨y, hy⟩ : ↥Q) * ⟨a, haQ⟩ = ⟨a, haQ⟩ * ⟨y, hy⟩ := by
    apply e.injective
    rw [map_mul, map_mul]
    exact (commute_iff_eq _ _).mp hAY
  exact congrArg Subtype.val hcommQ

private theorem center_le_subgroupOf_of_index_three {Q D : Subgroup G} (hDQ : D ≤ Q)
    (hQcard : Nat.card ↥Q = 81) (hDcard : Nat.card ↥D = 27)
    (hcenterQcard : Nat.card (Subgroup.center ↥Q) = 3) :
    Subgroup.center ↥Q ≤ D.subgroupOf Q := by
  set N : Subgroup ↥Q := D.subgroupOf Q with hNdef
  have hNcard : Nat.card N = 27 := by
    rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv]
    exact hDcard
  have hNindex : N.index = 3 := by
    have h := N.card_mul_index
    rw [hNcard, hQcard] at h
    omega
  have hNnormal : N.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hNindex, hQcard]
    norm_num
  haveI : N.Normal := hNnormal
  have hNne : N ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hNcard
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 ↥Q := IsPGroup.of_card (n := 4) (by rw [hQcard]; norm_num)
  haveI : Group.IsNilpotent ↥Q := hQp.isNilpotent
  have hmeet : N ⊓ Subgroup.center ↥Q ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥Q) (H := N) hNne
  have hHcard : Nat.card (N ⊓ Subgroup.center ↥Q : Subgroup ↥Q) = 3 := by
    have hdvd : Nat.card (N ⊓ Subgroup.center ↥Q : Subgroup ↥Q) ∣ 3 := by
      rw [← hcenterQcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq (N ⊓ Subgroup.center ↥Q : Subgroup ↥Q) h) hmeet
    · exact h
  have hEq : N ⊓ Subgroup.center ↥Q = Subgroup.center ↥Q :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcenterQcard, hHcard])
  exact inf_eq_right.mp hEq

theorem centerIn_eq_of_isThreeOnePlusTwo {Q D : Subgroup G} (e : ↥Q ≃* W3) (hDQ : D ≤ Q)
    (hD : IsThreeOnePlusTwo ↥D) : CFSG.centerIn D = CFSG.centerIn Q := by
  have hQcard : Nat.card ↥Q = 81 := card_of_equiv e
  have hDcard : Nat.card ↥D = 27 := hD.2.1
  have hZQcard : Nat.card (CFSG.centerIn Q) = 3 := card_centerIn_of_mulEquiv_W3 e
  have hcenterQcard : Nat.card (Subgroup.center ↥Q) = 3 := by
    rw [← Subgroup.card_map_of_injective (K := Subgroup.center ↥Q) Q.subtype_injective,
      ← CFSG.centerIn_eq_map_center]
    exact hZQcard
  have hcenterLeN : Subgroup.center ↥Q ≤ D.subgroupOf Q :=
    center_le_subgroupOf_of_index_three hDQ hQcard hDcard hcenterQcard
  have hZQleD : CFSG.centerIn Q ≤ D := by
    rw [CFSG.centerIn_eq_map_center]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact hcenterLeN hz
  have hZle : CFSG.centerIn Q ≤ CFSG.centerIn D := by
    intro x hx
    exact ⟨hZQleD hx,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hDQ) hx.2⟩
  have hZDcard : Nat.card (CFSG.centerIn D) = 3 := by
    rw [CFSG.centerIn_eq_map_center, Subgroup.card_map_of_injective D.subtype_injective]
    exact hD.1.2.2.2
  exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [hZDcard, hZQcard])).symm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
