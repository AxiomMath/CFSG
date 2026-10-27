module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12Good
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.ARS.Defs

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld
open scoped commutatorElement

structure S12TranspositionData {Y : Type*} [Group Y] (X : Subgroup Y) (E : Set Y) (t : Y) :
    Prop where
  subset : E ⊆ X
  gen : X = closure E
  mem : t ∈ E
  cls : ∀ τ ∈ E, ∃ x ∈ X, τ = x * t * x⁻¹
  conj : ∀ x ∈ X, ∀ τ ∈ E, x * τ * x⁻¹ ∈ E
  invol : ∀ τ ∈ E, τ * τ = 1
  ne_one : ∀ τ ∈ E, τ ≠ 1
  ord : ∀ d ∈ E, ∀ e ∈ E, orderOf (d * e) ≤ 4
  sq : ∀ d ∈ E, ∀ e ∈ E, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ E

theorem s12_mem_zpowers_invol {Y : Type*} [Group Y] {x y : Y} (hx : x * x = 1)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, hx2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]

theorem s12_center_eq_bot {Y : Type*} [Group Y] {X : Subgroup Y}
    (h : ∀ y ∈ X, (∀ x ∈ X, x * y = y * x) → y = 1) : center X = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  refine Subtype.ext (h y y.2 fun x hx => ?_)
  have := mem_center_iff.mp hy ⟨x, hx⟩
  exact congrArg Subtype.val this

theorem s12_normal_pGroup_eq_bot {Y : Type*} [Group Y] {X : Subgroup Y} {p : ℕ}
    (h : ∀ P : Subgroup Y, P ≤ X → IsPGroup p P → X ≤ normalizer (P : Set Y) → P = ⊥)
    (N : Subgroup X) (hN : N.Normal) (hp : IsPGroup p N) : N = ⊥ := by
  have hmap : N.map X.subtype = ⊥ := by
    refine h _ (map_subtype_le N) (hp.map _) fun x hx => ?_
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, hN.conj_mem n hn _, rfl⟩
    · rintro ⟨n, hn, hny⟩
      have hyX : y ∈ X := by
        have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ X :=
          X.mul_mem (X.mul_mem (X.inv_mem hx) (hny ▸ n.2)) hx
        simpa [mul_assoc] using h1
      refine ⟨⟨y, hyX⟩, ?_, rfl⟩
      have h1 := hN.conj_mem n hn (⟨x, hx⟩⁻¹)
      have e : (⟨x, hx⟩ : X)⁻¹ * n * (⟨x, hx⟩⁻¹)⁻¹ = ⟨y, hyX⟩ := by
        apply Subtype.ext
        simp only [InvMemClass.coe_inv, MulMemClass.coe_mul, inv_inv]
        have hny' : (n : Y) = x * y * x⁻¹ := hny
        rw [hny']
        group
      rwa [e] at h1
  rw [eq_bot_iff]
  intro n hn
  have h1 : (n : Y) ∈ N.map X.subtype := ⟨n, hn, rfl⟩
  rw [hmap, mem_bot] at h1
  rw [mem_bot]
  exact Subtype.ext h1

theorem s12_closure_preimage_eq_top {Y : Type*} [Group Y] {X : Subgroup Y} {E : Set Y}
    (h : X = closure E) : closure (Subtype.val ⁻¹' E : Set X) = ⊤ := by
  subst h
  exact closure_closure_coe_preimage

theorem s12_orderOf_mul_coe {Y : Type*} [Group Y] {X : Subgroup Y} {d e : X} :
    orderOf (d * e) = orderOf ((d : Y) * e) := by
  rw [← Subgroup.orderOf_coe]
  rfl

namespace S12TranspositionData

variable {Y : Type*} [Group Y] {X : Subgroup Y} {E : Set Y} {t : Y}
  (hD : S12TranspositionData X E t)

@[expose] def t' : X := ⟨t, hD.subset hD.mem⟩

@[expose] def rootSet : Set (Subgroup X) := Set.range (ARS.conjSub (zpowers hD.t'))

include hD

theorem conjSub_zpowers (x : X) :
    ARS.conjSub (zpowers hD.t') x = zpowers (x * hD.t' * x⁻¹) := by
  rw [ARS.conjSub, MonoidHom.map_zpowers]
  rfl

theorem mem_rootSet {A : Subgroup X} :
    A ∈ hD.rootSet ↔ ∃ e : X, (e : Y) ∈ E ∧ A = zpowers e := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x * hD.t' * x⁻¹, ?_, hD.conjSub_zpowers x⟩
    exact hD.conj x x.2 t hD.mem
  · rintro ⟨e, he, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hD.cls e he
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hD.conjSub_zpowers]
    congr 1
    exact Subtype.ext hxe.symm

theorem invol' {e : X} (he : (e : Y) ∈ E) : e * e = 1 :=
  Subtype.ext (hD.invol _ he)

omit hD in
theorem commuting_of_commute {d e : X} (h : d * e = e * d) :
    ARS.Commuting (zpowers d) (zpowers e) := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  exact Commute.zpow_zpow (show Commute d e from h) i j

omit hD in
theorem conjSub_zpowers' (d x : X) :
    ARS.conjSub (zpowers d) x = zpowers (x * d * x⁻¹) := by
  rw [ARS.conjSub, MonoidHom.map_zpowers]
  rfl

theorem opposite_of_three {d e : X} (hd : (d : Y) ∈ E) (he : (e : Y) ∈ E)
    (hne : zpowers d ≠ zpowers e) (h3 : orderOf (d * e) = 3) :
    ARS.Opposite (zpowers d) (zpowers e) := by
  have hdd := hD.invol' hd
  have hee := hD.invol' he
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hp3 : (d * e) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have key : e * d * e⁻¹ = d * e * d⁻¹ := by
    have h1 : e * d * e = d⁻¹ * e⁻¹ * d⁻¹ := by
      calc e * d * e = d⁻¹ * ((d * e) * (d * e) * (d * e)) * e⁻¹ * d⁻¹ := by group
        _ = d⁻¹ * e⁻¹ * d⁻¹ := by rw [← pow_three', hp3]; group
    rw [hei, hdi, h1, hdi, hei]
  refine ⟨hne, fun a ha ha1 => ?_, fun b hb hb1 => ?_⟩
  · rcases s12_mem_zpowers_invol hdd ha with rfl | rfl
    · exact absurd rfl ha1
    refine ⟨e, mem_zpowers e, fun h => hD.ne_one _ he (congrArg Subtype.val h), ?_⟩
    rw [conjSub_zpowers', conjSub_zpowers', key]
  · rcases s12_mem_zpowers_invol hee hb with rfl | rfl
    · exact absurd rfl hb1
    refine ⟨d, mem_zpowers d, fun h => hD.ne_one _ hd (congrArg Subtype.val h), ?_⟩
    rw [conjSub_zpowers', conjSub_zpowers', key]

omit hD in
theorem commutator_zpowers_of_invol {d e : X} (hdd : d * d = 1) (hee : e * e = 1) :
    ⁅zpowers d, zpowers e⁆ = zpowers ((d * e) ^ 2) := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hc : ⁅d, e⁆ = (d * e) ^ 2 := by
    rw [commutatorElement_def, hdi, hei, pow_two]
    group
  apply le_antisymm
  · rw [commutator_le]
    intro a ha b hb
    rcases s12_mem_zpowers_invol hdd ha with rfl | rfl
    · rw [commutatorElement_one_left]
      exact one_mem _
    rcases s12_mem_zpowers_invol hee hb with rfl | rfl
    · rw [commutatorElement_one_right]
      exact one_mem _
    rw [hc]
    exact mem_zpowers _
  · rw [zpowers_le, ← hc]
    exact commutator_mem_commutator (mem_zpowers d) (mem_zpowers e)

omit hD in
theorem commute_sq_of_invol {d e : X} (hdd : d * d = 1) (hee : e * e = 1)
    (hf : (d * e) ^ 2 * (d * e) ^ 2 = 1) :
    (d * e) ^ 2 * d = d * (d * e) ^ 2 ∧ (d * e) ^ 2 * e = e * (d * e) ^ 2 := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hfi : ((d * e) ^ 2)⁻¹ = (d * e) ^ 2 := inv_eq_of_mul_eq_one_right hf
  have h1 : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
    rw [hdi, mul_inv_rev, hdi, hei]
    calc d * (d * e) * d = (d * d) * (e * d) := by group
      _ = e * d := by rw [hdd, one_mul]
  have h2 : e * (d * e) * e⁻¹ = (d * e)⁻¹ := by
    rw [mul_inv_rev, hdi, hei]
    calc e * (d * e) * e = e * d * (e * e) := by group
      _ = e * d := by rw [hee, mul_one]
  have h1' : d * (d * e) ^ 2 * d⁻¹ = (d * e) ^ 2 := by rw [← conj_pow, h1, inv_pow, hfi]
  have h2' : e * (d * e) ^ 2 * e⁻¹ = (d * e) ^ 2 := by rw [← conj_pow, h2, inv_pow, hfi]
  constructor
  · calc (d * e) ^ 2 * d = d * (d * e) ^ 2 * d⁻¹ * d := by rw [h1']
      _ = d * (d * e) ^ 2 := by group
  · calc (d * e) ^ 2 * e = e * (d * e) ^ 2 * e⁻¹ * e := by rw [h2']
      _ = e * (d * e) ^ 2 := by group

theorem special_of_four {d e : X} (hd : (d : Y) ∈ E) (he : (e : Y) ∈ E)
    (h4 : orderOf (d * e) = 4) : ARS.Special hD.rootSet (zpowers d) (zpowers e) := by
  have hdd := hD.invol' hd
  have hee := hD.invol' he
  have h4' : orderOf ((d : Y) * e) = 4 := by rwa [← s12_orderOf_mul_coe]
  have hfE : (((d * e) ^ 2 : X) : Y) ∈ E := by
    have := hD.sq _ hd _ he h4'
    simpa using this
  have hf := hD.invol' hfE
  obtain ⟨hfd, hfe⟩ := commute_sq_of_invol hdd hee hf
  rw [ARS.Special, commutator_zpowers_of_invol hdd hee]
  exact ⟨hD.mem_rootSet.mpr ⟨_, hfE, rfl⟩, commuting_of_commute hfd, commuting_of_commute hfe⟩

variable [Finite Y]

theorem isRootClass : ARS.IsRootClass hD.rootSet where
  conj_class := ⟨_, rfl⟩
  ne_bot := by
    intro A hA
    obtain ⟨e, he, rfl⟩ := hD.mem_rootSet.mp hA
    intro h
    have h1 := mem_zpowers e
    rw [h, mem_bot] at h1
    exact hD.ne_one _ he (congrArg Subtype.val h1)
  mul_self := by
    intro A hA a ha
    obtain ⟨e, he, rfl⟩ := hD.mem_rootSet.mp hA
    rcases s12_mem_zpowers_invol (hD.invol' he) ha with rfl | rfl
    · exact mul_one 1
    · exact hD.invol' he
  rel := by
    intro A hA B hB hAB
    obtain ⟨d, hd, rfl⟩ := hD.mem_rootSet.mp hA
    obtain ⟨e, he, rfl⟩ := hD.mem_rootSet.mp hB
    have hdd := hD.invol' hd
    have hee := hD.invol' he
    have hle : orderOf (d * e) ≤ 4 := by
      rw [s12_orderOf_mul_coe]
      exact hD.ord _ hd _ he
    have hpos : 0 < orderOf (d * e) := orderOf_pos _
    interval_cases h : orderOf (d * e)
    · exfalso
      apply hAB
      have h1 : d * e = 1 := orderOf_eq_one_iff.mp h
      have h2 : e = d := by
        calc e = d⁻¹ * (d * e) := by group
          _ = d := by rw [h1, mul_one]; exact inv_eq_of_mul_eq_one_right hdd
      rw [h2]
    · left
      apply commuting_of_commute
      have h1 : (d * e) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
      have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
      have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
      calc d * e = (d * e)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_two, h1])).symm
        _ = e * d := by rw [mul_inv_rev, hdi, hei]
    · right; left
      exact hD.opposite_of_three hd he hAB h
    · right; right
      exact hD.special_of_four hd he h
  gen := by
    rw [eq_top_iff, ← s12_closure_preimage_eq_top hD.gen, closure_le]
    intro e he
    exact (le_iSup₂ (f := fun A (_ : A ∈ hD.rootSet) => A) (zpowers e)
      (hD.mem_rootSet.mpr ⟨e, he, rfl⟩)) (mem_zpowers e)

theorem arsHyp (hcen : ∀ y ∈ X, (∀ x ∈ X, x * y = y * x) → y = 1) (hO2 : S12NoNormalTwo X)
    (hnd : ∃ d ∈ E, ∃ e ∈ E, orderOf (d * e) = 4) : ARS.Hyp X hD.rootSet where
  finite := inferInstance
  root := hD.isRootClass
  nondeg := by
    obtain ⟨d, hd, e, he, h4⟩ := hnd
    refine ⟨zpowers ⟨d, hD.subset hd⟩, hD.mem_rootSet.mpr ⟨_, hd, rfl⟩,
      zpowers ⟨e, hD.subset he⟩, hD.mem_rootSet.mpr ⟨_, he, rfl⟩, ?_⟩
    exact hD.special_of_four hd he (by rw [s12_orderOf_mul_coe]; exact h4)
  center := s12_center_eq_bot hcen
  twoCore := fun N hN hp => s12_normal_pGroup_eq_bot (fun P h1 h2 h3 => hO2 P h1 h2 h3) N hN hp

end S12TranspositionData


end CFSG.LargeExtraspecial
