module

public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace OrthoF2

theorem linearIndependent_pair_iff {x y : V} :
    LinearIndependent (ZMod 2) ![x, y] ↔ x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y := by
  by_cases hx : x = 0
  · subst hx
    simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    exact fun h => h.ne_zero 0 rfl
  · rw [LinearIndependent.pair_iff' hx]
    constructor
    · intro h
      exact ⟨hx, fun hy => h 0 (by rw [zero_smul, hy]), fun hxy => h 1 (by rw [one_smul, hxy])⟩
    · rintro ⟨-, hy, hxy⟩ a
      rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
      · rw [zero_smul]
        exact Ne.symm hy
      · rw [one_smul]
        exact hxy

theorem linearIndependent_pair_symm {x y : V} (h : LinearIndependent (ZMod 2) ![x, y]) :
    LinearIndependent (ZMod 2) ![y, x] := by
  obtain ⟨hx, hy, hxy⟩ := linearIndependent_pair_iff.mp h
  exact linearIndependent_pair_iff.mpr ⟨hy, hx, Ne.symm hxy⟩

theorem finrank_span_pair {x y : V} (h : LinearIndependent (ZMod 2) ![x, y]) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {x, y}) = 2 := by
  have := finrank_span_eq_card h
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at this

theorem not_mem_span_singleton_of_pair {x y : V} (h : LinearIndependent (ZMod 2) ![x, y]) :
    y ∉ (ZMod 2) ∙ x := by
  obtain ⟨hx, hy, hxy⟩ := linearIndependent_pair_iff.mp h
  intro hmem
  rcases mem_span_singleton_iff.mp hmem with h' | h'
  · exact hy h'
  · exact hxy h'.symm

theorem mem_orthogonal_span_singleton_iff {v x : V} :
    x ∈ LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ v) ↔ polar q v x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    simpa using h v (Submodule.mem_span_singleton_self v)
  · intro h n hn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
    rw [polarBilin_apply_apply, polar_smul_left, h, smul_zero]

theorem mem_orthogonal_span_pair_iff {v w x : V} :
    x ∈ LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {v, w}) ↔
      polar q v x = 0 ∧ polar q w x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨by simpa using h v (Submodule.subset_span (by simp)),
      by simpa using h w (Submodule.subset_span (by simp))⟩
  · rintro ⟨hv, hw⟩ n hn
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hn
    rw [polarBilin_apply_apply, polar_add_left, polar_smul_left, polar_smul_left, hv, hw,
      smul_zero, smul_zero, add_zero]

theorem map_eq_zero_of_mem_span_pair {v w x : V} (hv : q v = 0) (hw : q w = 0)
    (hvw : polar q v w = 0) (hx : x ∈ Submodule.span (ZMod 2) {v, w}) : q x = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [map_add_eq, map_smul_zmod2, map_smul_zmod2, polar_smul_left, polar_smul_right, hv, hw,
    hvw]
  simp

theorem commSpace_one : commSpace (1 : V ≃ₗ[ZMod 2] V) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  rw [Submodule.mem_bot, LinearEquiv.coe_one, id, sub_self]

theorem exists_polar_eq_one_polar_eq_zero [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {v w : V} (h : LinearIndependent (ZMod 2) ![v, w]) :
    ∃ x, polar q x v = 1 ∧ polar q x w = 0 := by
  have hv : v ∉ (ZMod 2) ∙ w := not_mem_span_singleton_of_pair (linearIndependent_pair_symm h)
  obtain ⟨z, hz, hvz⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_polar_ne_zero hq hv
  refine ⟨z, ?_, ?_⟩
  · rw [polar_comm]
    exact zmod2_eq_one_of_ne_zero hvz
  · rw [polar_comm]
    exact hz w (Submodule.mem_span_singleton_self w)

end OrthoF2

theorem eichler_apply_zmod2 {a u : V} (ha : q a = 0) (hau : polar q a u = 0) (x : V) :
    eichler q a u x = x + polar q x a • u + (polar q x u + q u * polar q x a) • a := by
  rw [eichler_apply ha hau, sub_eq_add_neg, ← neg_smul, zmod2_neg]

theorem eichler_mul_self {a u : V} (hau : polar q a u = 0) :
    eichler q a u * eichler q a u = 1 := by
  rw [eichler_mul hau hau, vec_add_self, eichler_zero_right]

theorem commSpace_eichler_le (a u : V) :
    commSpace (eichler q a u) ≤ Submodule.span (ZMod 2) {a, u} := by
  intro y hy
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  obtain ⟨s, t, h⟩ := CFSG.ClassicalGroups.Orthogonal.eichler_apply_eq_add (Q := q) a u x
  rw [h, add_assoc, add_sub_cancel_left, add_comm]
  exact Submodule.mem_span_pair.mpr ⟨t, s, rfl⟩

theorem commSpace_eichler [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {a u : V} (ha : q a = 0) (hau : polar q a u = 0) (hli : LinearIndependent (ZMod 2) ![a, u]) :
    commSpace (eichler q a u) = Submodule.span (ZMod 2) {a, u} := by
  refine le_antisymm (commSpace_eichler_le a u) ?_
  obtain ⟨x₁, hx₁a, hx₁u⟩ := exists_polar_eq_one_polar_eq_zero hq hli
  obtain ⟨x₂, hx₂u, hx₂a⟩ := exists_polar_eq_one_polar_eq_zero hq (linearIndependent_pair_symm hli)
  have hamem : a ∈ commSpace (eichler q a u) := by
    have h := sub_mem_commSpace (eichler q a u) x₂
    have e : eichler q a u x₂ - x₂ = a := by
      rw [eichler_apply_zmod2 ha hau, hx₂a, hx₂u]
      simp
    rwa [e] at h
  have humem : u ∈ commSpace (eichler q a u) := by
    have h := sub_mem_commSpace (eichler q a u) x₁
    have e : eichler q a u x₁ - x₁ = u + q u • a := by
      rw [eichler_apply_zmod2 ha hau, hx₁a, hx₁u]
      simp only [one_smul, zero_add, mul_one]
      abel
    rw [e] at h
    have h2 := sub_mem h (Submodule.smul_mem _ (q u) hamem)
    rwa [add_sub_cancel_right] at h2
  rw [Submodule.span_le]
  rintro y (rfl | rfl)
  · exact hamem
  · exact humem

theorem eichler_ne_one [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {a u : V} (ha : q a = 0) (hau : polar q a u = 0) (hli : LinearIndependent (ZMod 2) ![a, u]) :
    eichler q a u ≠ 1 := by
  intro h1
  have h := commSpace_eichler hq ha hau hli
  rw [h1, commSpace_one] at h
  have h2 := finrank_span_pair hli
  rw [← h, finrank_bot] at h2
  exact absurd h2 (by norm_num)

theorem eichler_isTypeA [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {a u : V} (ha : q a = 0) (hau : polar q a u = 0) (hli : LinearIndependent (ZMod 2) ![a, u])
    (hu : q u = 0) :
    IsTypeA q (eichler q a u) 2 ∧
      commSpace (eichler q a u) = Submodule.span (ZMod 2) {a, u} := by
  have hc := commSpace_eichler hq ha hau hli
  refine ⟨⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (eichler_mem_orthogonalGroup q a u),
    eichler_ne_one hq ha hau hli, eichler_mul_self hau, by rw [hc, finrank_span_pair hli],
    fun x hx => ?_⟩, hc⟩
  rw [hc] at hx
  exact map_eq_zero_of_mem_span_pair ha hu hau hx

theorem eichler_isTypeC [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {a u : V} (ha0 : a ≠ 0) (ha : q a = 0) (hau : polar q a u = 0) (hu : q u = 1) :
    IsTypeC q (eichler q a u) 2 ∧
      commSpace (eichler q a u) = Submodule.span (ZMod 2) {a, u} := by
  have hli : LinearIndependent (ZMod 2) ![a, u] := by
    refine linearIndependent_pair_iff.mpr ⟨ha0, ?_, ?_⟩
    · rintro rfl
      rw [map_zero] at hu
      exact zero_ne_one hu
    · rintro rfl
      rw [ha] at hu
      exact zero_ne_one hu
  have hc := commSpace_eichler hq ha hau hli
  refine ⟨⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (eichler_mem_orthogonalGroup q a u),
    eichler_ne_one hq ha hau hli, eichler_mul_self hau, by rw [hc, finrank_span_pair hli],
    even_two, u, by rw [hc]; exact Submodule.subset_span (by simp), by rw [hu]; exact one_ne_zero⟩,
    hc⟩

theorem eq_one_or_eq_eichler_of_totallySingular [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {v w : V} (hli : LinearIndependent (ZMod 2) ![v, w])
    (hv : q v = 0) (hw : q w = 0) (hvw : polar q v w = 0) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ orthogonalGroup q) (hcomm : commSpace t ≤ Submodule.span (ZMod 2) {v, w})
    (hfix : ∀ x, polar q v x = 0 → polar q w x = 0 → t x = x) :
    t = 1 ∨ t = eichler q v w := by
  obtain ⟨xv, hxvv, hxvw⟩ := exists_polar_eq_one_polar_eq_zero hq hli
  obtain ⟨xw, hxww, hxwv⟩ :=
    exists_polar_eq_one_polar_eq_zero hq (linearIndependent_pair_symm hli)
  have hcoord : ∀ d ∈ Submodule.span (ZMod 2) {v, w},
      d = polar q d xv • v + polar q d xw • w := by
    intro d hd
    obtain ⟨s, r, rfl⟩ := Submodule.mem_span_pair.mp hd
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_comm q v xv, hxvv,
      polar_comm q w xv, hxvw, polar_comm q v xw, hxwv, polar_comm q w xw, hxww, mul_one,
      mul_zero, add_zero, zero_add]
  have hself : ∀ y, polar q (t y - y) y = 0 := by
    intro y
    have h0 : q (t y - y) = 0 :=
      map_eq_zero_of_mem_span_pair hv hw hvw (hcomm (sub_mem_commSpace t y))
    rw [map_sub_eq_polar ht] at h0
    rw [QuadraticMap.polar_sub_left, h0, polar_self_eq_zero, sub_zero]
  set β := polar q (t xv - xv) xw with hβ
  set γ := polar q (t xw - xw) xv with hγ
  have htxv : t xv = xv + β • w := by
    have h := hcoord _ (hcomm (sub_mem_commSpace t xv))
    rw [hself, zero_smul, zero_add] at h
    rw [← h]
    abel
  have htxw : t xw = xw + γ • v := by
    have h := hcoord _ (hcomm (sub_mem_commSpace t xw))
    rw [hself, zero_smul, add_zero] at h
    rw [← h]
    abel
  have hβγ : γ = β := by
    have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ht xv xw
    rw [htxv, htxw] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
      hxvv, polar_comm q w xw, hxww, polar_comm q w v, hvw, mul_one, mul_zero, add_zero] at h
    exact zmod2_eq_of_add_eq_zero (by linear_combination h)
  have hgen : ∀ y, t y = y + β • (polar q y v • w + polar q y w • v) := by
    intro y
    set c := polar q y v with hc
    set d := polar q y w with hd
    set y' := y - c • xv - d • xw with hy'
    have hy'v : polar q v y' = 0 := by
      rw [hy', polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right,
        polar_comm q v xv, hxvv, polar_comm q v xw, hxwv, hc, polar_comm q y v]
      simp
    have hy'w : polar q w y' = 0 := by
      rw [hy', polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right,
        polar_comm q w xv, hxvw, polar_comm q w xw, hxww, hd, polar_comm q y w]
      simp
    have hty' := hfix y' hy'v hy'w
    have hy : y = y' + c • xv + d • xw := by
      rw [hy']
      abel
    conv_lhs => rw [hy]
    rw [map_add, map_add, map_smul, map_smul, hty', htxv, htxw, hβγ]
    conv_rhs => rw [hy]
    module
  rcases zmod2_eq_zero_or_eq_one β with h0 | h1
  · left
    ext y
    rw [hgen, h0, zero_smul, add_zero]
    rfl
  · right
    ext y
    rw [hgen, h1, one_smul, eichler_apply_zmod2 hv hvw, hw, zero_mul, add_zero, add_assoc]

theorem eichler_of_totallySingular [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {v w : V} (hli : LinearIndependent (ZMod 2) ![v, w])
    (hv : q v = 0) (hw : q w = 0) (hvw : polar q v w = 0) :
    IsTypeA q (eichler q v w) 2 ∧ commSpace (eichler q v w) = Submodule.span (ZMod 2) {v, w} ∧
      ∀ x, polar q v x = 0 → polar q w x = 0 → eichler q v w x = x := by
  obtain ⟨hA, hc⟩ := eichler_isTypeA hq hv hvw hli hw
  refine ⟨hA, hc, fun x hxv hxw => ?_⟩
  rw [polar_comm] at hxv hxw
  exact CFSG.ClassicalGroups.Orthogonal.eichler_apply_of_polar_eq_zero hxv hxw

namespace OrthoF2

theorem exists_pair_of_finrank_eq_two [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V}
    (hU2 : finrank (ZMod 2) U = 2) :
    ∃ v w : V, LinearIndependent (ZMod 2) ![v, w] ∧ Submodule.span (ZMod 2) {v, w} = U := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) U hU2
  have hli : LinearIndependent (ZMod 2) ![(b 0 : V), (b 1 : V)] := by
    refine linearIndependent_pair_iff.mpr ⟨fun h => b.ne_zero 0 (Subtype.ext h),
      fun h => b.ne_zero 1 (Subtype.ext h), fun h => ?_⟩
    exact absurd (b.injective (Subtype.ext h)) (by decide)
  refine ⟨b 0, b 1, hli, ?_⟩
  have hle : Submodule.span (ZMod 2) {(b 0 : V), (b 1 : V)} ≤ U := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact (b 0).2
    · exact (b 1).2
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_pair hli, hU2])

end OrthoF2

theorem existsUnique_of_totallySingular_finrank_two [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, q u = 0)
    (hU2 : finrank (ZMod 2) U = 2) :
    ∃! t : V ≃ₗ[ZMod 2] V, t ∈ orthogonalGroup q ∧ t ≠ 1 ∧ commSpace t ≤ U ∧
      ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin U, t x = x := by
  obtain ⟨v, w, hli, rfl⟩ := exists_pair_of_finrank_eq_two hU2
  have hv : q v = 0 := hU v (Submodule.subset_span (by simp))
  have hw : q w = 0 := hU w (Submodule.subset_span (by simp))
  have hvw : polar q v w = 0 := by
    have h := hU (v + w) (Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)))
    rwa [map_add_eq, hv, hw, zero_add, zero_add] at h
  obtain ⟨hA, hc, hfix⟩ := eichler_of_totallySingular hq hli hv hw hvw
  refine ⟨eichler q v w, ⟨eichler_mem_orthogonalGroup q v w, hA.2.1, hc.le, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨hxv, hxw⟩ := mem_orthogonal_span_pair_iff.mp hx
    exact hfix x hxv hxw
  · rintro s ⟨hs, hs1, hscomm, hsfix⟩
    rcases eq_one_or_eq_eichler_of_totallySingular hq hli hv hw hvw hs hscomm
      (fun x hxv hxw => hsfix x (mem_orthogonal_span_pair_iff.mpr ⟨hxv, hxw⟩)) with h | h
    · exact absurd h hs1
    · exact h

theorem isTypeA_of_totallySingular_finrank_two [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, q u = 0)
    (hU2 : finrank (ZMod 2) U = 2) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ orthogonalGroup q)
    (ht1 : t ≠ 1) (hcomm : commSpace t ≤ U)
    (hfix : ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin U, t x = x) :
    IsTypeA q t 2 ∧ commSpace t = U := by
  obtain ⟨v, w, hli, rfl⟩ := exists_pair_of_finrank_eq_two hU2
  have hv : q v = 0 := hU v (Submodule.subset_span (by simp))
  have hw : q w = 0 := hU w (Submodule.subset_span (by simp))
  have hvw : polar q v w = 0 := by
    have h := hU (v + w) (Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)))
    rwa [map_add_eq, hv, hw, zero_add, zero_add] at h
  rcases eq_one_or_eq_eichler_of_totallySingular hq hli hv hw hvw ht hcomm
    (fun x hxv hxw => hfix x (mem_orthogonal_span_pair_iff.mpr ⟨hxv, hxw⟩)) with h | h
  · exact absurd h ht1
  · subst h
    obtain ⟨hA, hc, -⟩ := eichler_of_totallySingular hq hli hv hw hvw
    exact ⟨hA, hc⟩

end CFSG.LargeExtraspecial
