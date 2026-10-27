module

public import CFSG.LargeExtraspecial.S97RWC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75

theorem eq_one_of_mul_self_of_odd {K : Type*} [Group K] [Finite K] {Z : Subgroup K}
    (hZ : Odd (Nat.card Z)) {z : K} (hz : z ∈ Z) (hzz : z * z = 1) : z = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : Z) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [pow_two, hzz]))
  have h2 := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
  have h3 : orderOf (⟨z, hz⟩ : Z) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hZ) h1 h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)

theorem mem_of_mk_mem_map {K : Type*} [Group K] [Finite K] {T Z : Subgroup K} [Z.Normal]
    (hZc : Z ≤ center K) (hZ : Odd (Nat.card Z)) (hT : ∀ t ∈ T, t * t = 1) {w : K}
    (hw : w * w = 1) (h : QuotientGroup.mk' Z w ∈ T.map (QuotientGroup.mk' Z)) : w ∈ T := by
  obtain ⟨t, ht, he⟩ := h
  have hz : t⁻¹ * w ∈ Z := QuotientGroup.eq.mp he
  have hzc := mem_center_iff.mp (hZc hz)
  have hw' : w = t * (t⁻¹ * w) := by group
  have hzz : (t⁻¹ * w) * (t⁻¹ * w) = 1 := by
    have h1 : w * w = t * t * ((t⁻¹ * w) * (t⁻¹ * w)) := by
      conv_lhs => rw [hw']
      rw [mul_assoc t, ← mul_assoc (t⁻¹ * w) t, ← hzc t]
      group
    rw [hw, hT t ht, one_mul] at h1
    exact h1.symm
  rw [hw', eq_one_of_mul_self_of_odd hZ hz hzz, mul_one]
  exact ht

variable {G : Type} [Group G] [Finite G] {S : Setting G} {k : G} {m : S.M} {O : Subgroup S.O}

variable (S k m) in
noncomputable abbrev Lam97 : Type := S9.Q97 S k m ⧸ center (S9.Q97 S k m)

variable (S k m) in
@[expose] noncomputable def pi97 : ↥(S9.X97 S k m) →* Lam97 S k m :=
  (QuotientGroup.mk' (center (S9.Q97 S k m))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(S9.X97 S k m)))

variable (S k m) in
@[expose] noncomputable def T97 (j : G) : Subgroup (Lam97 S k m) :=
  (S9.Tj97 S k m j).map (QuotientGroup.mk' (center (S9.Q97 S k m)))

theorem pi97_surjective : Function.Surjective (pi97 S k m) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem pi97_mem_T97 {j : G} {x : ↥(S9.X97 S k m)} (hx : (x : S.O) ∈ S.Lbar j) :
    pi97 S k m x ∈ T97 S k m j :=
  ⟨_, ⟨x, mem_subgroupOf.mpr hx, rfl⟩, rfl⟩

theorem exists_of_mem_T97 {j : G} {t : Lam97 S k m} (ht : t ∈ T97 S k m j) :
    ∃ x : ↥(S9.X97 S k m), (x : S.O) ∈ S.Lbar j ∧ pi97 S k m x = t := by
  obtain ⟨u, ⟨x, hx, rfl⟩, rfl⟩ := ht
  exact ⟨x, mem_subgroupOf.mp hx, rfl⟩

theorem isElemAbelian_T97 {j : G} (Hj : Hyp4 S j) : CFSG.Open.IsElemAbelian 2 (T97 S k m j) :=
  isElemAbelian_map_of_hom (S9.Tj97_isElemAbelian Hj) _

theorem mul_self_of_mem_T97 {j : G} (Hj : Hyp4 S j) {t : Lam97 S k m} (ht : t ∈ T97 S k m j) :
    t * t = 1 := by
  rw [← pow_two]
  exact (isElemAbelian_T97 Hj).2 t ht

namespace H97

variable (X : S9.Hyp97 S k m O) (hodd : Odd (Nat.card (center (S9.Q97 S k m))))
include X hodd

omit X hodd in
theorem pi97_conj (x : ↥(S9.X97 S k m)) (t : S9.Q97 S k m) :
    pi97 S k m x * QuotientGroup.mk' (center (S9.Q97 S k m)) t * (pi97 S k m x)⁻¹ =
      QuotientGroup.mk' (center (S9.Q97 S k m))
        ((x : S9.Q97 S k m) * t * (x : S9.Q97 S k m)⁻¹) :=
  rfl

omit X in
theorem mk_mem_normalizer_of_pi97 {j : G} (Hj : Hyp4 S j) {x : ↥(S9.X97 S k m)}
    (hx : pi97 S k m x ∈ normalizer (T97 S k m j : Set (Lam97 S k m))) :
    (x : S9.Q97 S k m) ∈ normalizer (S9.Tj97 S k m j : Set (S9.Q97 S k m)) := by
  refine mem_normalizer_of_map_conj_eq (S9.map_conj_eq_of_forall_conj fun t ht => ?_)
  have hsq : ∀ t' ∈ S9.Tj97 S k m j, t' * t' = 1 := fun t' ht' => by
    rw [← pow_two]; exact (S9.Tj97_isElemAbelian Hj).2 t' ht'
  refine mem_of_mk_mem_map le_rfl hodd hsq ?_ ?_
  · calc (x : S9.Q97 S k m) * t * (x : S9.Q97 S k m)⁻¹ *
          ((x : S9.Q97 S k m) * t * (x : S9.Q97 S k m)⁻¹) =
          (x : S9.Q97 S k m) * (t * t) * (x : S9.Q97 S k m)⁻¹ := by group
      _ = 1 := by rw [hsq t ht]; group
  · have h1 : QuotientGroup.mk' (center (S9.Q97 S k m)) t ∈ T97 S k m j := mem_map_of_mem _ ht
    exact (congrArg (· ∈ T97 S k m j) (pi97_conj x t)).mp ((mem_normalizer_iff.mp hx _).mp h1)

theorem pi97_mem_normalizer_iff {j : G} (hj : S.Lbar j ≤ S9.X97 S k m) (Hj : Hyp4 S j)
    (Cj : Cons311 S j) (x : ↥(S9.X97 S k m)) :
    pi97 S k m x ∈ normalizer (T97 S k m j : Set (Lam97 S k m)) ↔
      (x : S.O) ∈ normalizer (S.Lbar j : Set S.O) := by
  constructor
  · intro hx
    have hxLO := X.mem_normalizer_of_mk hj (mk_mem_normalizer_of_pi97 hodd Hj hx)
    have hle : (S.Lbar j).map (MulAut.conj (x : S.O)).toMonoidHom ≤
        normalizer ((S.Lbar j ⊔ O : Subgroup S.O) : Set S.O) := by
      rintro _ ⟨l, hl, rfl⟩
      exact le_normalizer ((mem_normalizer_iff.mp hxLO l).mp (mem_sup_left hl))
    exact mem_normalizer_of_map_conj_eq (S9.map_conj_eq_of_le_normalizer Hj Cj S9.X97_le_Mbar hj
      X.le X.normal X.isPGroup x.2 hle)
  · intro hx
    refine mem_normalizer_of_map_conj_eq (S9.map_conj_eq_of_forall_conj fun t ht => ?_)
    obtain ⟨u, hu, rfl⟩ := exists_of_mem_T97 ht
    have hxu : ((x * u * x⁻¹ : ↥(S9.X97 S k m)) : S.O) ∈ S.Lbar j := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mem_normalizer_iff.mp hx _).mp hu
    have h1 := pi97_mem_T97 (S := S) (k := k) (m := m) hxu
    simpa only [map_mul, map_inv] using h1

theorem pi97_eq_one_iff {j : G} (Hj : Hyp4 S j) {x : ↥(S9.X97 S k m)}
    (hx : (x : S.O) ∈ S.Lbar j) : pi97 S k m x = 1 ↔ (x : S.O) ∈ O := by
  rw [← X.mk_eq_one_iff]
  constructor
  · intro h1
    have hT : (x : S9.Q97 S k m) ∈ S9.Tj97 S k m j := ⟨x, mem_subgroupOf.mpr hx, rfl⟩
    have hZ : (x : S9.Q97 S k m) ∈ center (S9.Q97 S k m) :=
      (QuotientGroup.eq_one_iff (x : S9.Q97 S k m)).mp h1
    refine eq_one_of_mul_self_of_odd hodd hZ ?_
    rw [← pow_two]
    exact (S9.Tj97_isElemAbelian Hj).2 _ hT
  · intro h1
    exact (congrArg (QuotientGroup.mk' (center (S9.Q97 S k m))) h1).trans (map_one _)

omit X in
theorem card_T97 {j : G} (Hj : Hyp4 S j) :
    Nat.card (T97 S k m j) = Nat.card (S9.Tj97 S k m j) := by
  refine (Nat.card_congr (Equiv.ofBijective (fun t : S9.Tj97 S k m j =>
    (⟨QuotientGroup.mk' _ (t : S9.Q97 S k m), mem_map_of_mem _ t.2⟩ : T97 S k m j)) ⟨?_, ?_⟩)).symm
  · intro a b hab
    have h1 : QuotientGroup.mk' (center (S9.Q97 S k m)) (a : S9.Q97 S k m) =
        QuotientGroup.mk' _ (b : S9.Q97 S k m) := congrArg Subtype.val hab
    have h2 : (a : S9.Q97 S k m)⁻¹ * b ∈ center (S9.Q97 S k m) := QuotientGroup.eq.mp h1
    have h3 : (a : S9.Q97 S k m)⁻¹ * b ∈ S9.Tj97 S k m j := mul_mem (inv_mem a.2) b.2
    have h4 := eq_one_of_mul_self_of_odd hodd h2 (by
      rw [← pow_two]; exact (S9.Tj97_isElemAbelian Hj).2 _ h3)
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  · rintro ⟨_, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

end H97

end CFSG.LargeExtraspecial.S11
