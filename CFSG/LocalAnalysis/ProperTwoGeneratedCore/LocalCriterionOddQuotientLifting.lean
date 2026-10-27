module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G Q : Type*} [Group G] [Finite G] [Group Q]

omit [Finite G] in
theorem odd_kernel_subgroup_restriction (f : G →* Q)
    (hodd : Odd (Nat.card f.ker)) (A : Subgroup G) :
    Odd (Nat.card (f.comp A.subtype).ker) := by
  have hker : (f.comp A.subtype).ker = f.ker.comap A.subtype := by
    ext a
    rfl
  rw [hker]
  exact hodd.of_dvd_nat
    (Subgroup.card_comap_dvd_of_injective f.ker A.subtype A.subtype_injective)

theorem involution_image_of_odd_kernel (f : G →* Q)
    (hodd : Odd (Nat.card f.ker)) {z : G} (hz : IsInvolution z) :
    IsInvolution (f z) := by
  constructor
  · intro h
    exact not_isInvolution_of_mem_odd_subgroup f.ker hodd
      (show z ∈ f.ker from h) hz
  · simpa only [map_pow, map_one] using congrArg f hz.sq_eq_one

theorem involution_lift_of_odd_kernel (f : G →* Q)
    (hodd : Odd (Nat.card f.ker)) {y : Q} (hy : IsInvolution y)
    (hpreimage : ∃ x : G, f x = y) :
    ∃ x : G, IsInvolution x ∧ f x = y := by
  let W : Subgroup Q := Subgroup.zpowers y
  let P : Subgroup G := W.comap f
  obtain ⟨x, hx⟩ := hpreimage
  have hxP : x ∈ P := by
    change f x ∈ W
    rw [hx]
    exact Subgroup.mem_zpowers y
  let xP : P := ⟨x, hxP⟩
  have hyorder : orderOf y = 2 := orderOf_eq_prime hy.sq_eq_one hy.ne_one
  have htwoOrder : 2 ∣ orderOf x := by
    rw [← hyorder, ← hx]
    exact orderOf_map_dvd f x
  have htwoCard : 2 ∣ Nat.card P := by
    apply htwoOrder.trans
    change orderOf (xP : G) ∣ Nat.card P
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard xP
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 htwoCard
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have htI : IsInvolution (t : G) :=
    ⟨(orderOf_eq_prime_iff.mp htG).2, (orderOf_eq_prime_iff.mp htG).1⟩
  have hftI := involution_image_of_odd_kernel f hodd htI
  have hftW : f (t : G) ∈ W := t.property
  have hcard : Nat.card W = 2 := by
    dsimp only [W]
    simpa only [Nat.card_zpowers] using hyorder
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hcard
  have hftne : (⟨f (t : G), hftW⟩ : W) ≠ 1 :=
    fun h => hftI.ne_one (congrArg Subtype.val h)
  have hyne : (⟨y, Subgroup.mem_zpowers y⟩ : W) ≠ 1 :=
    fun h => hy.ne_one (congrArg Subtype.val h)
  have heq : f (t : G) = y :=
    congrArg Subtype.val ((hw _ hftne).trans (hw _ hyne).symm)
  exact ⟨t, htI, heq⟩

theorem involution_lift_in_subgroup_of_odd_kernel (f : G →* Q)
    (hodd : Odd (Nat.card f.ker)) (A : Subgroup G)
    {y : Q} (hy : IsInvolution y) (hyA : y ∈ A.map f) :
    ∃ x : G, x ∈ A ∧ IsInvolution x ∧ f x = y := by
  obtain ⟨a, haA, ha⟩ := hyA
  obtain ⟨x, hx, hfx⟩ := involution_lift_of_odd_kernel (f.comp A.subtype)
    (odd_kernel_subgroup_restriction f hodd A) hy ⟨⟨a, haA⟩, ha⟩
  exact ⟨x, x.property,
    CFSG.BenderSuzuki.IsInvolution.map_of_injective hx A.subtype A.subtype_injective, hfx⟩

omit [Finite G] in
theorem involutions_kernel_conjugate (f : G →* Q)
    (hodd : Odd (Nat.card f.ker)) {s t : G}
    (hs : IsInvolution s) (ht : IsInvolution t) (heq : f s = f t) :
    ∃ n : G, n ∈ f.ker ∧ rightConjugateElem s n = t := by
  have hst : s * t ∈ f.ker := by
    change f (s * t) = 1
    rw [map_mul, heq]
    simpa only [map_pow, map_one, pow_two, map_mul] using congrArg f ht.sq_eq_one
  have horder : Odd (orderOf (s * t)) := by
    let r : f.ker := ⟨s * t, hst⟩
    have hr := hodd.of_dvd_nat (orderOf_dvd_natCard r)
    change Odd (orderOf (r : G))
    rw [Subgroup.orderOf_coe]
    exact hr
  obtain ⟨n, hn, hconj⟩ := exists_zpowers_conjugator_of_odd_product hs ht horder
  exact ⟨n, (Subgroup.zpowers_le.mpr hst) hn, hconj⟩

omit [Finite G] in
theorem involution_point_class_image_iff (f : G →* Q)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {z w : G} (hz : IsInvolution z) (hw : IsInvolution w) :
    f w ∈ involutionPointClass (f z) ↔ w ∈ involutionPointClass z := by
  constructor
  · rintro ⟨qg, hqg⟩
    obtain ⟨g, hg⟩ := hf qg
    have hmap : f (rightConjugateElem z g) = f w := by
      simpa only [rightConjugateElem, map_mul, map_inv, hg] using hqg
    obtain ⟨n, _, hn⟩ := involutions_kernel_conjugate f hodd
      (isInvolution_rightConjugateElem hz) hw hmap
    exact ⟨g * n, (rightConjugateElem_comp z g n).symm.trans hn⟩
  · rintro ⟨g, rfl⟩
    exact ⟨f g, by simp only [rightConjugateElem, map_mul, map_inv]⟩

omit [Finite G] in
theorem involution_centralizer_image (f : G →* Q)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {z : G} (hz : IsInvolution z) :
    (Subgroup.centralizer ({z} : Set G)).map f =
      Subgroup.centralizer ({f z} : Set Q) := by
  apply le_antisymm
  · rintro y ⟨g, hg, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((show Commute g z from Subgroup.mem_centralizer_singleton_iff.mp hg).map f)
  · intro y hy
    obtain ⟨g, hg⟩ := hf y
    have hycomm := Subgroup.mem_centralizer_singleton_iff.mp hy
    have heq : f (rightConjugateElem z g) = f z := by
      simp only [rightConjugateElem, map_mul, map_inv, hg]
      rw [mul_assoc, ← hycomm, inv_mul_cancel_left]
    obtain ⟨n, hn, hconj⟩ := involutions_kernel_conjugate f hodd
      (isInvolution_rightConjugateElem hz) hz heq
    have hfix : rightConjugateElem z (g * n) = z :=
      (rightConjugateElem_comp z g n).symm.trans hconj
    refine ⟨g * n, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have h := congrArg (fun a : G => (g * n) * a) hfix
      simp only [rightConjugateElem, ← mul_assoc, mul_inv_cancel, one_mul] at h
      simpa only [mul_assoc] using h.symm
    · rw [map_mul, show f n = 1 from hn, mul_one, hg]

theorem commuting_involution_lift_of_odd_kernel (f : G →* Q)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {z : G} {y : Q} (hz : IsInvolution z) (hy : IsInvolution y)
    (hcomm : Commute y (f z)) :
    ∃ u : G, IsInvolution u ∧ f u = y ∧ Commute u z := by
  have hymem : y ∈ (Subgroup.centralizer ({z} : Set G)).map f := by
    rw [involution_centralizer_image f hf hodd hz]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  obtain ⟨u, huC, hu, hfu⟩ := involution_lift_in_subgroup_of_odd_kernel f hodd
    (Subgroup.centralizer ({z} : Set G)) hy hymem
  exact ⟨u, hu, hfu, Subgroup.mem_centralizer_singleton_iff.mp huC⟩

theorem central_sylow_two_image (f : G →* Q) (hf : Function.Surjective f)
    (S : Sylow 2 G) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hcentral : ∀ s ∈ (S : Subgroup G), Commute z s) :
    ∃ T : Sylow 2 Q, (T : Subgroup Q) = (S : Subgroup G).map f ∧
      f z ∈ (T : Subgroup Q) ∧ ∀ t ∈ (T : Subgroup Q), Commute (f z) t := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨S.mapSurjective hf, Sylow.coe_mapSurjective hf S, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem f hzS
  · rw [Sylow.coe_mapSurjective]
    rintro t ⟨s, hs, rfl⟩
    exact (hcentral s hs).map f

end CFSG.ProperTwoGeneratedCore
