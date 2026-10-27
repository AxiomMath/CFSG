module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.ThreeCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.ThreePair
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInv_three {G : Type} [Group G] [Finite G] {a z x : G} (h : IsF5Type a z)
    (hCls : GzClassFacts a z) (hY4a : Y4aFacts a z) (hSGz : StructGzFacts a z)
    (hx : IsConj a x) (haz : a ∈ Gx z) (hxz : x ∈ Gx z) (haz2 : IsConj z (a * z))
    (hnc : ¬ IsConj a (a * z)) (h3 : orderOf (a * x) = 3)
    (hcard : Nat.card ↥(CbarCent z ⟨a * x, Subgroup.mul_mem _ haz hxz⟩) = 18) :
    ∃ t : G, IsConj a t ∧ t ∈ Gxyz a z x := by
  have hplus : IsPlusExtraspecial 2 (Qz z ⊓ Gx (a * x)) :=
    oddInv_three_plus hSGz ⟨a * x, Subgroup.mul_mem _ haz hxz⟩ (by
      rw [Subgroup.orderOf_mk]
      exact h3) hcard
  have hC8 : 8 ≤ Nat.card ↥((Qz z ⊓ Gx (a * x)) ⊓ Gx a) :=
    oddInv_three_card h hx haz hnc hplus
  have hY : Y4aStruct a z a := hY4a.y4a a haz (IsConj.refl a) haz2
  let A : Subgroup G := Gxy a z ⊓ Qz z
  let W : Subgroup G := CFSG.Open.pCoreOf 2 (derivedOf (Gxy a z))
  let C : Subgroup G := (Qz z ⊓ Gx (a * x)) ⊓ Gx a
  have hQz_le : Qz z ≤ Gx z := Subgroup.map_subtype_le _
  have hA : IsElemTwo 5 A := hY.card_Q
  have hW : IsElemTwo 4 W := hY.orth.1
  have hCA : C ≤ A := by
    intro c hc
    obtain ⟨hc1, hca⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨hcQ, -⟩ := Subgroup.mem_inf.mp hc1
    exact Subgroup.mem_inf.mpr ⟨mem_Gxy.mpr ⟨hca, hQz_le hcQ⟩, hcQ⟩
  have hWA : W ≤ A := by
    intro c hc
    have hc' : c ∈ derivedOf (Gxy a z) ⊓ Qz z ⊓ Qz (a * z) := by
      rw [← hY.pCore]
      exact hc
    obtain ⟨hc1, -⟩ := Subgroup.mem_inf.mp hc'
    obtain ⟨hcD, hcQ⟩ := Subgroup.mem_inf.mp hc1
    exact Subgroup.mem_inf.mpr ⟨derivedOf_le (Gxy a z) hcD, hcQ⟩
  obtain ⟨E, hE_le, hE⟩ :=
    oddInv_three_exists_pair hCA hWA hA hW (show 8 ≤ Nat.card ↥C from hC8)
  have hY4b : Y4bStruct a z a := hSGz.y4b a haz (IsConj.refl a) haz2
  have hEW : E ≤ W := hE_le.trans inf_le_right
  have hnotall : ¬ (∀ t ∈ E, t ≠ 1 → IsConj z t) := fun hall =>
    hY4b.no_2B_pair ⟨E, hEW, hE, hall⟩
  push_neg at hnotall
  obtain ⟨t, htE, htne, htz⟩ := hnotall
  have ht2 : t ^ 2 = 1 := hE.1.2 t htE
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 htne
  have hconj : IsConj a t := (hCls.inv_two t htord).resolve_right htz
  have htC : t ∈ C := (hE_le.trans inf_le_left) htE
  obtain ⟨htC1, hta⟩ := Subgroup.mem_inf.mp htC
  obtain ⟨htQ, htax⟩ := Subgroup.mem_inf.mp htC1
  have htaz : t ∈ Gx z := hQz_le htQ
  have ha2 : a ^ 2 = 1 := by
    rw [← h.orderOf_a]
    exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by
    rw [← pow_two]
    exact ha2
  have hxeq : x = a * (a * x) := by
    rw [← mul_assoc, haa, one_mul]
  have hat : a * t = t * a := mem_Gx.mp hta
  have haxt : (a * x) * t = t * (a * x) := mem_Gx.mp htax
  have hxt : x * t = t * x := by
    rw [hxeq, mul_assoc, haxt, ← mul_assoc, hat, mul_assoc]
  exact ⟨t, hconj, mem_Gxyz.mpr ⟨hta, htaz, mem_Gx.mpr hxt⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
