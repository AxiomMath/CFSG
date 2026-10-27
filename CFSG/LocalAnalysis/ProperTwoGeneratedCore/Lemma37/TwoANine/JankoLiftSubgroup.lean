module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoLift

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

variable {J : Type*} [Group J]

@[expose] noncomputable def liftOddSubgroup (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
    (Y : Subgroup (alternatingGroup (Fin 9))) : Subgroup J :=
  closure {x | proj e x ∈ Y ∧ Odd (orderOf x)}

private theorem orderOf_conj' {X : Type*} [Group X] (g a : X) :
    orderOf (g * a * g⁻¹) = orderOf a := by
  simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq a

namespace IsTwoANine

variable (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem card_map_proj_of_odd {X : Subgroup J} (hX : Odd (Nat.card X)) :
    Nat.card (X.map (proj e)) = Nat.card X := by
  have hinj : Function.Injective ((proj e).comp X.subtype) := fun x y h =>
    Subtype.ext (hJ.eq_of_proj_eq_of_odd e (hX.of_dvd_nat (X.orderOf_dvd_natCard x.2))
      (hX.of_dvd_nat (X.orderOf_dvd_natCard y.2)) h)
  have hrange : X.map (proj e) = ((proj e).comp X.subtype).range := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem exists_le_comap_card_eq {Y : Subgroup (alternatingGroup (Fin 9))}
    (hY : Odd (Nat.card Y)) :
    ∃ Y₁ : Subgroup J, Y₁ ≤ Y.comap (proj e) ∧ Nat.card Y₁ = Nat.card Y := by
  have := hJ.finite
  set W := Y.comap (proj e)
  have hZW : center J ≤ W := fun c hc => by
    rw [mem_comap, (proj_eq_one_iff e).mpr hc]
    exact Y.one_mem
  have hN : Nat.card ((center J).subgroupOf W) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv, hJ.card_center]
  have hW : Nat.card W = 2 * Nat.card Y := hJ.card_comap_proj e Y
  have hNi : ((center J).subgroupOf W).index = Nat.card Y := by
    have h := ((center J).subgroupOf W).card_mul_index
    rw [hN, hW] at h
    omega
  obtain ⟨Y₀, hY₀⟩ := exists_right_complement'_of_coprime (N := (center J).subgroupOf W)
    (by rw [hN, hNi]; exact Nat.coprime_two_left.mpr hY)
  refine ⟨Y₀.map W.subtype, map_subtype_le _, ?_⟩
  have h := hY₀.card_mul_card
  rw [card_map_of_injective W.subtype_injective]
  rw [hN, hW] at h
  omega

variable {Y : Subgroup (alternatingGroup (Fin 9))} (hY : Odd (Nat.card Y))
include hY

private theorem liftOddSubgroup_spec : Nat.card (liftOddSubgroup e Y) = Nat.card Y ∧
    ∀ x : J, x ∈ liftOddSubgroup e Y ↔ proj e x ∈ Y ∧ Odd (orderOf x) := by
  obtain ⟨Y₁, hY₁, hcard⟩ := hJ.exists_le_comap_card_eq e hY
  have hodd : Odd (Nat.card Y₁) := hcard ▸ hY
  have hmap : Y₁.map (proj e) = Y := Subgroup.eq_of_le_of_card_ge (map_le_iff_le_comap.mpr hY₁)
    (by rw [hJ.card_map_proj_of_odd e hodd, hcard])
  have hS : {x : J | proj e x ∈ Y ∧ Odd (orderOf x)} = Y₁ := by
    ext x
    refine ⟨fun ⟨hxY, hxo⟩ => ?_, fun hx => ⟨hY₁ hx, hodd.of_dvd_nat (Y₁.orderOf_dvd_natCard hx)⟩⟩
    rw [← hmap] at hxY
    obtain ⟨y, hy, hyx⟩ := hxY
    rw [SetLike.mem_coe, ← hJ.eq_of_proj_eq_of_odd e
      (hodd.of_dvd_nat (Y₁.orderOf_dvd_natCard hy)) hxo hyx]
    exact hy
  have hL : liftOddSubgroup e Y = Y₁ := by rw [liftOddSubgroup, hS, closure_eq]
  refine ⟨by rw [hL, hcard], fun x => ?_⟩
  rw [hL, ← SetLike.mem_coe, ← hS]
  rfl

theorem mem_liftOddSubgroup_iff {x : J} :
    x ∈ liftOddSubgroup e Y ↔ proj e x ∈ Y ∧ Odd (orderOf x) :=
  (hJ.liftOddSubgroup_spec e hY).2 x

theorem card_liftOddSubgroup : Nat.card (liftOddSubgroup e Y) = Nat.card Y :=
  (hJ.liftOddSubgroup_spec e hY).1

theorem odd_card_liftOddSubgroup : Odd (Nat.card (liftOddSubgroup e Y)) := by
  rw [hJ.card_liftOddSubgroup e hY]
  exact hY

theorem liftOdd_mem_liftOddSubgroup {g : alternatingGroup (Fin 9)} (hg : g ∈ Y) :
    liftOdd e g ∈ liftOddSubgroup e Y := by
  have hgo : Odd (orderOf g) := hY.of_dvd_nat (Y.orderOf_dvd_natCard hg)
  exact (hJ.mem_liftOddSubgroup_iff e hY).mpr ⟨by rw [hJ.proj_liftOdd e hgo]; exact hg,
    hJ.odd_orderOf_liftOdd e hgo⟩

theorem map_liftOddSubgroup : (liftOddSubgroup e Y).map (proj e) = Y := by
  refine le_antisymm ?_ fun g hg => ⟨liftOdd e g, hJ.liftOdd_mem_liftOddSubgroup e hY hg,
    hJ.proj_liftOdd e (hY.of_dvd_nat (Y.orderOf_dvd_natCard hg))⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ((hJ.mem_liftOddSubgroup_iff e hY).mp hx).1

theorem liftOddSubgroup_le_comap : liftOddSubgroup e Y ≤ Y.comap (proj e) :=
  fun _ hx => ((hJ.mem_liftOddSubgroup_iff e hY).mp hx).1

@[expose] noncomputable def liftOddSubgroupEquiv : liftOddSubgroup e Y ≃* Y :=
  (MulEquiv.ofBijective ((proj e).subgroupMap (liftOddSubgroup e Y))
    ⟨fun x y h => Subtype.ext (hJ.eq_of_proj_eq_of_odd e
      ((hJ.mem_liftOddSubgroup_iff e hY).mp x.2).2 ((hJ.mem_liftOddSubgroup_iff e hY).mp y.2).2
      (congrArg Subtype.val h)), (proj e).subgroupMap_surjective _⟩).trans
    (MulEquiv.subgroupCongr (hJ.map_liftOddSubgroup e hY))

@[simp] theorem coe_liftOddSubgroupEquiv_apply (x : liftOddSubgroup e Y) :
    ((hJ.liftOddSubgroupEquiv e hY x : Y) : alternatingGroup (Fin 9)) = proj e x :=
  rfl

theorem le_liftOddSubgroup {X : Subgroup J} (hX : Odd (Nat.card X)) (h : X.map (proj e) ≤ Y) :
    X ≤ liftOddSubgroup e Y := fun x hx => (hJ.mem_liftOddSubgroup_iff e hY).mpr
  ⟨h ⟨x, hx, rfl⟩, hX.of_dvd_nat (X.orderOf_dvd_natCard hx)⟩

theorem centralizer_liftOddSubgroup : centralizer (liftOddSubgroup e Y : Set J) =
    (centralizer (Y : Set (alternatingGroup (Fin 9)))).comap (proj e) := by
  ext u
  rw [mem_comap, mem_centralizer_iff, mem_centralizer_iff]
  refine ⟨fun h g hg => ?_, fun h x hx => ?_⟩
  · rw [← hJ.proj_liftOdd e (hY.of_dvd_nat (Y.orderOf_dvd_natCard hg)), ← map_mul,
      h _ (hJ.liftOdd_mem_liftOddSubgroup e hY hg), map_mul]
  · obtain ⟨hxY, hxo⟩ := (hJ.mem_liftOddSubgroup_iff e hY).mp hx
    exact (hJ.commute_of_odd_orderOf e hxo (h _ hxY).symm).symm

theorem normalizer_liftOddSubgroup : normalizer (liftOddSubgroup e Y : Set J) =
    (normalizer (Y : Set (alternatingGroup (Fin 9)))).comap (proj e) := by
  refine le_antisymm (fun u hu => ?_) fun u hu => ?_
  · rw [mem_comap, ← hJ.map_liftOddSubgroup e hY]
    exact le_normalizer_map (proj e) ⟨u, hu, rfl⟩
  · rw [mem_comap, mem_normalizer_iff] at hu
    rw [mem_normalizer_iff]
    intro x
    rw [hJ.mem_liftOddSubgroup_iff e hY, hJ.mem_liftOddSubgroup_iff e hY, orderOf_conj', map_mul,
      map_mul, map_inv, ← hu]

omit hY in
theorem eq_liftOddSubgroup {X : Subgroup J} (hX : Odd (Nat.card X)) :
    X = liftOddSubgroup e (X.map (proj e)) := by
  have hXo : Odd (Nat.card (X.map (proj e))) := by rw [hJ.card_map_proj_of_odd e hX]; exact hX
  have := hJ.finite
  exact Subgroup.eq_of_le_of_card_ge (hJ.le_liftOddSubgroup e hXo hX le_rfl)
    (by rw [hJ.card_liftOddSubgroup e hXo, hJ.card_map_proj_of_odd e hX])

omit hY

theorem odd_card_map_proj {X : Subgroup J} (hX : Odd (Nat.card X)) :
    Odd (Nat.card (X.map (proj e))) := by
  rw [hJ.card_map_proj_of_odd e hX]
  exact hX

theorem zpowers_liftOdd {g : alternatingGroup (Fin 9)} (hg : Odd (orderOf g)) :
    zpowers (liftOdd e g) = liftOddSubgroup e (zpowers g) := by
  have h := hJ.eq_liftOddSubgroup e (X := zpowers (liftOdd e g))
    (by rw [Nat.card_zpowers]; exact hJ.odd_orderOf_liftOdd e hg)
  rwa [MonoidHom.map_zpowers, hJ.proj_liftOdd e hg] at h

end IsTwoANine

section Transport

variable {G : Type*} [Group G] (H : Subgroup G)

theorem centralizer_inf_eq_map_subtype (x : H) :
    centralizer ({(x : G)} : Set G) ⊓ H = (centralizer ({x} : Set H)).map H.subtype := by
  ext g
  constructor
  · rintro ⟨hg, hgH⟩
    exact ⟨⟨g, hgH⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hg)), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)), y.2⟩

theorem card_centralizer_inf_eq (x : H) :
    Nat.card (centralizer ({(x : G)} : Set G) ⊓ H : Subgroup G) =
      Nat.card (centralizer ({x} : Set H)) := by
  rw [centralizer_inf_eq_map_subtype, card_map_of_injective H.subtype_injective]

theorem centralizer_map_inf_eq_map_subtype (X : Subgroup H) :
    centralizer ((X.map H.subtype : Subgroup G) : Set G) ⊓ H =
      (centralizer (X : Set H)).map H.subtype := by
  ext g
  constructor
  · rintro ⟨hg, hgH⟩
    exact ⟨⟨g, hgH⟩, mem_centralizer_iff.mpr fun x hx =>
      Subtype.ext (mem_centralizer_iff.mp hg x ⟨x, hx, rfl⟩), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨mem_centralizer_iff.mpr ?_, y.2⟩
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hy x hx)

theorem normalizer_map_inf_eq_map_subtype (X : Subgroup H) :
    normalizer ((X.map H.subtype : Subgroup G) : Set G) ⊓ H =
      (normalizer (X : Set H)).map H.subtype := by
  have hmem : ∀ x : H, (x : G) ∈ X.map H.subtype ↔ x ∈ X := fun x =>
    mem_map_iff_mem H.subtype_injective
  ext g
  constructor
  · rintro ⟨hg, hgH⟩
    refine ⟨⟨g, hgH⟩, mem_normalizer_iff.mpr fun x => ?_, rfl⟩
    rw [← hmem, ← hmem]
    exact mem_normalizer_iff.mp hg x
  · rintro ⟨y, hy, rfl⟩
    refine ⟨mem_normalizer_iff.mpr fun x => ?_, y.2⟩
    by_cases hx : x ∈ H
    · change ((⟨x, hx⟩ : H) : G) ∈ X.map H.subtype ↔
        ((y * ⟨x, hx⟩ * y⁻¹ : H) : G) ∈ X.map H.subtype
      rw [hmem, hmem]
      exact mem_normalizer_iff.mp hy _
    · have hyx : (y : G) * x * (y : G)⁻¹ ∉ H := fun h => hx (by
        simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem y.2) h) y.2)
      exact iff_of_false (fun h => hx (map_subtype_le X h)) fun h => hyx (map_subtype_le X h)

end Transport

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
