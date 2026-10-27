module

public import CFSG.Fischer.Classification.Basic.WidthOne
public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.Uniq.MuSets
public import CFSG.Fischer.Uniq.Connected

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

section Affine

variable (hP : Pair X E) {d e z : X} (hd : d ∈ E) (he : e ∈ E) (hz : z ∈ E)
  (hde : d * e ≠ e * d) (hdz : d * z ≠ z * d) (hez : e * z ≠ z * e)
  (hzl : z * (d * e * d) ≠ d * e * d * z)

include hP hd he hz in
theorem Pair.conj_mem_closure_affine {n : X}
    (hn : n ∈ Subgroup.closure ({d * e, d * z} : Set X)) :
    d * n * d ∈ Subgroup.closure ({d * e, d * z} : Set X) := by
  set N := Subgroup.closure ({d * e, d * z} : Set X)
  induction hn using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with hs | hs <;> rw [hs]
    · rw [Pair.conj_mul_eq_inv hP hd he]
      exact N.inv_mem (Subgroup.subset_closure (Set.mem_insert _ _))
    · rw [Pair.conj_mul_eq_inv hP hd hz]
      exact N.inv_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  | one => rw [mul_one, Pair.mul_self hP hd]; exact N.one_mem
  | mul a b _ _ ha hb =>
    rw [show d * (a * b) * d = d * a * d * (d * b * d) by
      simp only [← mul_assoc, mul_assoc (d * a) d d, Pair.mul_self hP hd, mul_one]]
    exact N.mul_mem ha hb
  | inv a _ ha =>
    rw [show d * a⁻¹ * d = (d * a * d)⁻¹ by
      rw [mul_inv_rev, mul_inv_rev, Pair.inv_eq hP hd, mul_assoc]]
    exact N.inv_mem ha

include hP hd he hz hde hdz hez hzl in
theorem Pair.not_commute_of_mem_inter_closure_affine {s t : X}
    (hs : s ∈ E ∩ (Subgroup.closure ({d, e, z} : Set X) : Set X))
    (ht : t ∈ E ∩ (Subgroup.closure ({d, e, z} : Set X) : Set X)) (hst : s ≠ t) :
    s * t ≠ t * s := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  set N := Subgroup.closure ({d * e, d * z} : Set X)
  have hnot : ∀ w ∈ E, w ∉ N := by
    intro w hw hwN
    have h3 := hR.pow_three_eq_one hwN
    rw [pow_three', Pair.mul_self hP hw, one_mul] at h3
    exact Pair.ne_one hP hw h3
  obtain ⟨n, hn, hsn | hsn⟩ := Pair.exists_eq_or_eq_mul_of_mem_closure hP hd he hz hs.2
  · exact absurd (hsn ▸ hn) (hnot s hs.1)
  obtain ⟨m, hm, htm | htm⟩ := Pair.exists_eq_or_eq_mul_of_mem_closure hP hd he hz ht.2
  · exact absurd (htm ▸ hm) (hnot t ht.1)
  have hstN : s * t ∈ N := by
    rw [hsn, htm, show d * n * (d * m) = d * n * d * m by simp only [mul_assoc]]
    exact N.mul_mem (Pair.conj_mem_closure_affine hP hd he hz hn) hm
  intro hc
  have h3 := hR.pow_three_eq_one hstN
  have h2 : (s * t) ^ 2 = 1 := by
    rw [sq]
    calc s * t * (s * t) = s * (t * s) * t := by simp only [mul_assoc]
      _ = s * s * (t * t) := by rw [← hc]; simp only [mul_assoc]
      _ = 1 := by rw [Pair.mul_self hP hs.1, Pair.mul_self hP ht.1, one_mul]
  have h1 : s * t = 1 := by
    calc s * t = (s * t) ^ 3 * ((s * t) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  apply hst
  rw [← Pair.inv_eq hP hs.1]
  exact inv_eq_of_mul_eq_one_right h1

end Affine

section Small

theorem Pair.isSymplecticType_of_forall_ncard_le_three (hP : Pair X E)
    (hconn : (commGraph E).Connected) (hk : ∀ e ∈ E, (LocalClass E e).ncard ≤ 3) :
    IsSymplecticType E := by
  classical
  have := Pair.finite hP
  intro d hd e he z hz hde
  by_contra hcon
  push Not at hcon
  obtain ⟨hzd, hze, hzl⟩ := hcon
  have hdz : d * z ≠ z * d := fun h => hzd h.symm
  have hez : e * z ≠ z * e := fun h => hze h.symm
  set P := E ∩ (Subgroup.closure ({d, e, z} : Set X) : Set X) with hPdef
  have hP9 : P.ncard = 9 := Pair.ncard_inter_closure_affine hP hd he hz hde hdz hez hzl
  have hdP : d ∈ P := ⟨hd, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  set S := P \ {d}
  have hS8 : S.ncard = 8 := by rw [Set.ncard_sdiff_singleton_of_mem hdP, hP9]
  have hmu : ∀ q ∈ S, (muSet E d q).Nonempty := fun q hq =>
    Pair.muSet_nonempty hP hconn hd hq.1.1
      (Pair.not_commute_of_mem_inter_closure_affine hP hd he hz hde hdz hez hzl hq.1 hdP
        fun h => hq.2 h)
  let F : X → Finset X := fun b => (Set.toFinite (LocalClass E b \ {d})).toFinset
  let t : Finset X := (Set.toFinite (LocalClass E d)).toFinset
  have hsub : (Set.toFinite S).toFinset ⊆ t.biUnion F := by
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨b, hb⟩ := hmu q hq
    rw [Finset.mem_biUnion]
    refine ⟨b, (Set.Finite.mem_toFinset _).2 hb.1, (Set.Finite.mem_toFinset _).2 ⟨?_, hq.2⟩⟩
    exact ⟨hq.1.1, fun h => hb.2.2.1 h.symm, hb.2.2.2.symm⟩
  have hF : ∀ b ∈ t, (F b).card ≤ 2 := by
    intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    have hdb : d ∈ LocalClass E b := ⟨hd, fun h => hb.2.1 h.symm, hb.2.2.symm⟩
    rw [← Set.ncard_eq_toFinset_card, Set.ncard_sdiff_singleton_of_mem hdb]
    have := hk b hb.1
    omega
  have ht : t.card ≤ 3 := by
    rw [← Set.ncard_eq_toFinset_card]
    exact hk d hd
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le_card_mul t F 2 hF
  rw [← Set.ncard_eq_toFinset_card, hS8] at h1
  omega

end Small

section O3

theorem o3Input_of_ncard_le_three
    (hC : ∀ (G : Type) [Group G] (D : Set G), Hyp G D → NonabelianCommutator G → ∀ d ∈ D,
      (LocalClass D d).Nonempty → HasNormalPSubgroup 3 (LocalQuotient D d) →
      (LocalClass D d).ncard ≤ 3) :
    O3Input := by
  intro G _ D hH hnab hsymp d hd hne h3
  exfalso
  apply hsymp
  have hk0 := hC G D hH hnab d hd hne h3
  have hk : ∀ e ∈ D, (LocalClass D e).ncard ≤ 3 := by
    intro e he
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hH.pair hd he)
    rw [← Pair.image_conj_localClass hH.pair g d,
      Set.ncard_image_of_injective _ (conj_injective g)]
    exact hk0
  have hna : ¬ ∀ a b : commutator G, a * b = b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact fun h => hab (h a b)
  obtain ⟨d', hd', e', he', hne', hc⟩ := Pair.exists_ne_commute hH.pair hH.simple hna
  have hconn := Pair.connected_of_simple hH.pair hH.simple ⟨d', e', hd', he', hne', hc⟩
  exact Pair.isSymplecticType_of_forall_ncard_le_three hH.pair hconn hk

end O3

end CFSG.Fischer.Classification
