module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ5
public import CFSG.LieType.Chevalley.SylowOpposition

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Layer

variable {τ : Tag} {K : Type} [Field K] {J : Set (Fin τ.rank)}

theorem pinnedX_mem_degSeries {d : ℤ} {α : Fin τ.rank → ℤ} (hα : α ∈ degSet τ J d) (c : K) :
    pinnedX τ K α c ∈ degSeries τ K J d :=
  pinnedX_mem_rootSpan hα c

theorem isAbLayer_degSeries {d : ℤ} (hd : 1 ≤ d) :
    IsAbLayer (degSeries τ K J d) (degSeries τ K J (d + 1)) where
  le := degSeries_anti (show d ≤ d + 1 by omega)
  conj_mem x hx n hn := (Subgroup.mem_normalizer_iff.1
    (posUnipotent_le_normalizer_degSeries (d + 1) (degSeries_le_posUnipotent hx)) n).1 hn
  comm_mem x hx y hy := by
    have h1 := commutator_degSeries_le (K := K) (J := J) hd hd
      (Subgroup.commutator_mem_commutator hx hy)
    exact degSeries_anti (show d + 1 ≤ d + d by omega) (by simpa [commutatorElement_def] using h1)

theorem pinnedX_pow_three [CharP K 3] (α : Fin τ.rank → ℤ) (c : K) :
    pinnedX τ K α c ^ 3 = 1 := by
  have h := (pinnedHom τ K α).map_pow (Multiplicative.ofAdd c) 3
  have h3 : (3 : ℕ) • c = 0 := by
    rw [nsmul_eq_mul, CharP.cast_eq_zero K 3, zero_mul]
  have e : pinnedHom τ K α ((Multiplicative.ofAdd c) ^ 3) = 1 := by
    rw [← ofAdd_nsmul, h3, ofAdd_zero, map_one]
  rw [map_pow] at e
  simpa [pinnedHom_apply] using e

theorem isLayer_degSeries [CharP K 3] {d : ℤ} (hd : 1 ≤ d) :
    IsLayer (degSeries τ K J d) (degSeries τ K J (d + 1)) where
  toIsAbLayer := isAbLayer_degSeries hd
  cube_mem := by
    refine (isAbLayer_degSeries (K := K) (J := J) hd).cube_mem_of_gens
      (S := {g | ∃ α ∈ degSet τ J d, ∃ c : K, pinnedX τ K α c = g})
      (rootSpan_eq_closure K (degSet τ J d)) ?_
    rintro _ ⟨α, hα, c, rfl⟩
    rw [pinnedX_pow_three α c]
    exact one_mem _

end Layer

section Coord

variable {τ : Tag} {K : Type} [Field K] {J : Set (Fin τ.rank)}

@[expose] def degLayerRoots (τ : Tag) (J : Set (Fin τ.rank)) (d : ℤ) : Set (Fin τ.rank → ℤ) :=
  degSet τ J d \ degSet τ J (d + 1)

theorem mem_degLayerRoots {d : ℤ} {α : Fin τ.rank → ℤ} :
    α ∈ degLayerRoots τ J d ↔ α ∈ parabolicRadicalRoots τ J ∧ parabolicDegree τ J α = d := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    by_contra hne
    exact h3 ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.ge⟩, fun h => by have := h.2; omega⟩

theorem degLayerRoots_finite (d : ℤ) : (degLayerRoots τ J d).Finite :=
  (finite_setOf_isRoot τ).subset fun _ h => (degSet_pos h.1).1

instance (d : ℤ) : Fintype (degLayerRoots τ J d) := (degLayerRoots_finite d).fintype

variable [CharP K 3]

@[expose] def coordMk {d : ℤ} (hd : 1 ≤ d) (i : degLayerRoots τ J d) (c : K) :
    Lyr (isLayer_degSeries (K := K) (J := J) hd) :=
  Lyr.mk _ ⟨pinnedX τ K i.1 c, pinnedX_mem_degSeries i.2.1 c⟩

theorem coordMk_add {d : ℤ} (hd : 1 ≤ d) (i : degLayerRoots τ J d) (c c' : K) :
    coordMk hd i (c + c') = coordMk hd i c + coordMk hd i c' := by
  unfold coordMk
  rw [← Lyr.mk_add]
  congr 1
  exact Subtype.ext (pinnedX_add τ K i.1 c c')

theorem coordMk_zero {d : ℤ} (hd : 1 ≤ d) (i : degLayerRoots τ J d) :
    coordMk hd i (0 : K) = 0 := by
  unfold coordMk
  rw [← Lyr.mk_zero]
  congr 1
  exact Subtype.ext (pinnedX_zero τ K i.1)

@[expose] def coordMap {d : ℤ} (hd : 1 ≤ d) :
    (degLayerRoots τ J d → K) →+ Lyr (isLayer_degSeries (K := K) (J := J) hd) where
  toFun c := ∑ i, coordMk hd i (c i)
  map_zero' := by simp [coordMk_zero]
  map_add' c c' := by simp [coordMk_add, Finset.sum_add_distrib]

theorem coordMap_single {d : ℤ} (hd : 1 ≤ d) (i : degLayerRoots τ J d) (c : K) :
    coordMap hd (Pi.single i c) = coordMk hd i c := by
  classical
  unfold coordMap
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj, coordMk_zero]
  · simp

theorem coordMap_surjective {d : ℤ} (hd : 1 ≤ d) : Function.Surjective (coordMap (τ := τ) (K := K) (J := J) hd) := by
  classical
  intro z
  obtain ⟨⟨x, hx⟩, rfl⟩ := Lyr.mk_surjective _ z
  have hS : degSeries τ K J d = Subgroup.closure {g | ∃ α ∈ degSet τ J d, ∃ c : K, pinnedX τ K α c = g} :=
    rootSpan_eq_closure K (degSet τ J d)
  have key : ∀ x ∈ Subgroup.closure {g | ∃ α ∈ degSet τ J d, ∃ c : K, pinnedX τ K α c = g},
      ∃ c, ∀ hx : x ∈ degSeries τ K J d, coordMap hd c = Lyr.mk _ ⟨x, hx⟩ := by
    intro x hxc
    induction hxc using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, c, rfl⟩ := hy
      by_cases hαd : α ∈ degSet τ J (d + 1)
      · refine ⟨0, fun hx => ?_⟩
        rw [map_zero]
        exact ((Lyr.mk_eq_zero _).2 (pinnedX_mem_degSeries hαd c)).symm
      · exact ⟨Pi.single ⟨α, hα, hαd⟩ c, fun hx => coordMap_single hd _ _⟩
    | one => exact ⟨0, fun hx => by rw [map_zero]; exact (Lyr.mk_zero _).symm⟩
    | mul y y' hy hy' ihy ihy' =>
      obtain ⟨c, hc⟩ := ihy
      obtain ⟨c', hc'⟩ := ihy'
      have hyH : y ∈ degSeries τ K J d := hS ▸ hy
      have hy'H : y' ∈ degSeries τ K J d := hS ▸ hy'
      exact ⟨c + c', fun hx => by
        rw [map_add, hc hyH, hc' hy'H]
        exact (Lyr.mk_add _ ⟨y, hyH⟩ ⟨y', hy'H⟩).symm⟩
    | inv y hy ih =>
      obtain ⟨c, hc⟩ := ih
      have hyH : y ∈ degSeries τ K J d := hS ▸ hy
      exact ⟨-c, fun hx => by
        rw [map_neg, hc hyH]
        exact (Lyr.mk_neg _ ⟨y, hyH⟩).symm⟩
  obtain ⟨c, hc⟩ := key x (hS ▸ hx)
  exact ⟨c, hc hx⟩

end Coord

section Card

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem degSet_eq_union (d : ℤ) :
    degSet τ J d = degLayerRoots τ J d ∪ degSet τ J (d + 1) := by
  classical
  ext α
  constructor
  · intro h
    by_cases h' : α ∈ degSet τ J (d + 1)
    · exact Or.inr h'
    · exact Or.inl ⟨h, h'⟩
  · rintro (h | h)
    · exact h.1
    · exact degSet_anti (show d ≤ d + 1 by omega) h

theorem degSet_finite (d : ℤ) : (degSet τ J d).Finite :=
  (finite_setOf_isRoot τ).subset fun _ h => (degSet_pos h).1

theorem ncard_degSet_eq (d : ℤ) : (degSet τ J d).ncard =
    (degLayerRoots τ J d).ncard + (degSet τ J (d + 1)).ncard := by
  conv_lhs => rw [degSet_eq_union d]
  exact Set.ncard_union_eq (Set.disjoint_left.2 fun _ h h' => h.2 h')
    (degLayerRoots_finite d) (degSet_finite _)

theorem card_layer {d : ℤ} (hd : 1 ≤ d) :
    Nat.card (Lyr (isLayer_degSeries (K := K) (J := J) hd)) =
      Nat.card K ^ (degLayerRoots τ J d).ncard := by
  haveI := finite_modGL (τ := τ) (K := K)
  have h1 := Lyr.card_mul (isLayer_degSeries (K := K) (J := J) hd)
  rw [card_degSeries hd, card_degSeries (show 1 ≤ d + 1 by omega)] at h1
  rw [ncard_degSet_eq d, pow_add] at h1
  have hq : 0 < Nat.card K ^ (degSet τ J (d + 1)).ncard := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  exact Nat.eq_of_mul_eq_mul_right hq h1

theorem coordMap_bijective {d : ℤ} (hd : 1 ≤ d) :
    Function.Bijective (coordMap (τ := τ) (K := K) (J := J) hd) := by
  refine (coordMap_surjective hd).bijective_of_nat_card_le ?_
  rw [card_layer hd, Nat.card_fun, Nat.card_coe_set_eq]

end Card

section Torus

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem conj_rootDiagUnit_mem {a : Fin τ.rank → Kˣ} {d : ℤ} {x : ModGL τ K}
    (hx : x ∈ degSeries τ K J d) :
    (MulAut.conj (rootDiagUnit τ a)).toMonoidHom x ∈ degSeries τ K J d :=
  (Subgroup.mem_normalizer_iff.1 (rootDiagUnit_mem_normalizer_degSeries a d) x).1 hx

@[expose] def conjL (a : Fin τ.rank → Kˣ) {d : ℤ} (hd : 1 ≤ d) :
    Lyr (isLayer_degSeries (K := K) (J := J) hd) →ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd) :=
  Lyr.mapL _ (MulAut.conj (rootDiagUnit τ a)).toMonoidHom (fun _ hx => conj_rootDiagUnit_mem hx)
    (fun _ hx => conj_rootDiagUnit_mem hx)

theorem conjL_coordMk (a : Fin τ.rank → Kˣ) {d : ℤ} (hd : 1 ≤ d) (i : degLayerRoots τ J d) (c : K) :
    conjL a hd (coordMk hd i c) = coordMk hd i ((rootChar a i.1 : K) * c) := by
  unfold conjL coordMk
  rw [Lyr.mapL_mk]
  congr 1
  exact Subtype.ext (rootDiagUnit_conj_pinnedX a (degSet_pos i.2.1).1 c)

theorem conjL_coordMap (a : Fin τ.rank → Kˣ) {d : ℤ} (hd : 1 ≤ d) (c : degLayerRoots τ J d → K) :
    conjL a hd (coordMap hd c) = coordMap hd (fun i => (rootChar a i.1 : K) * c i) := by
  unfold coordMap
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, conjL_coordMk]

@[expose] def zetaDiag (J : Set (Fin τ.rank)) : Fin τ.rank → Kˣ :=
  open Classical in fun i => if i ∈ J then 1 else -1

theorem rootChar_zetaDiag (γ : Fin τ.rank → ℤ) :
    rootChar (zetaDiag (K := K) J) γ = (-1) ^ parabolicDegree τ J γ := by
  classical
  have key : ∀ s : Finset (Fin τ.rank), ∏ i ∈ s, (zetaDiag (K := K) J i) ^ γ i =
      (-1 : Kˣ) ^ (∑ i ∈ s, if i ∈ J then 0 else γ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add, ih]
      congr 1
      by_cases hiJ : i ∈ J <;> simp [zetaDiag, hiJ]
  exact key Finset.univ

end Torus

section Zeta

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem rootChar_zetaDiag_of_degree {d : ℤ} (i : degLayerRoots τ J d) :
    (rootChar (zetaDiag (K := K) J) i.1 : Kˣ) = (-1) ^ d := by
  rw [rootChar_zetaDiag, (mem_degLayerRoots.1 i.2).2]

theorem conjL_zeta_odd {d : ℤ} (hd : 1 ≤ d) (hodd : Odd d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) : conjL (zetaDiag J) hd z = -z := by
  obtain ⟨c, rfl⟩ := (coordMap_bijective hd).2 z
  rw [conjL_coordMap, ← map_neg]
  congr 1
  funext i
  rw [rootChar_zetaDiag_of_degree, hodd.neg_one_zpow]
  simp

end Zeta

end CFSG.LocalAnalysis.GLTheoremA
