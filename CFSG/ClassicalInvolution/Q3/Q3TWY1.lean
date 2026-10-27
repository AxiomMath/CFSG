module

public import CFSG.ClassicalInvolution.Q3.Q3ZLiftCover
public import CFSG.ClassicalInvolution.Q3.Q3VF4CNodes
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair
  SymplecticBlockStandardPair longBlock shortBlock eq_one_of_mem_center_of_mem_suppGroup
  isSupp_longBlock coords longBlock_injective)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (exists_lift_of_noCover)
open CFSG.LieType.Steinberg (nonempty_commOrder_ofCartan)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

section Pair

theorem symplecticBlockPair_map_central3 {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : SymplecticBlockStandardPair (GaloisField 3 1) W U V) (φ : X →* Y)
    (hφ : φ.ker ≤ Subgroup.center X) :
    SymplecticBlockPair (GaloisField 3 1) (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, hinjL, -, hU, hV⟩ := h
  have : Group.IsPerfect (StatedSp 2 (GaloisField 3 1)) := Q3Z.isPerfect_sp4_three
  have hcen : ∀ s : StatedSp 2 (GaloisField 3 1), φ (θ s) = 1 →
      s ∈ Subgroup.center (StatedSp 2 (GaloisField 3 1)) := by
    intro s hs
    have hc : θ s ∈ Subgroup.center X := hφ (MonoidHom.mem_ker.mpr hs)
    refine mem_center_of_comm_mem_center fun t => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
      ← Subgroup.mem_center_iff.mp hc (θ t)]
    group
  set C : StatedSp 2 (GaloisField 3 1) →* StatedSp 2 (GaloisField 3 1) :=
    (MulAut.conj c⁻¹).toMonoidHom with hC
  refine ⟨φ.comp θ, c, ?_, fun s hs => hcen s hs, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · intro l₁ l₂ hl
    simp only [MonoidHom.comp_apply] at hl
    have h1 : φ (θ (C (longBlock (GaloisField 3 1) 2 1 (l₁⁻¹ * l₂)))) = 1 := by
      simp only [map_mul, map_inv]
      rw [hl, inv_mul_cancel]
    have h2 := hcen _ h1
    have h3 : longBlock (GaloisField 3 1) 2 1 (l₁⁻¹ * l₂) ∈
        Subgroup.center (StatedSp 2 (GaloisField 3 1)) := by
      have h4 := (inferInstance : (Subgroup.center (StatedSp 2 (GaloisField 3 1))).Normal).conj_mem
        _ h2 c
      have e : c * C (longBlock (GaloisField 3 1) 2 1 (l₁⁻¹ * l₂)) * c⁻¹ =
          longBlock (GaloisField 3 1) 2 1 (l₁⁻¹ * l₂) := by
        simp only [hC, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [e] at h4
    have h5' := eq_one_of_mem_center_of_mem_suppGroup h3 (isSupp_longBlock (1 : Fin 2) _)
      (t := Sum.inl (0 : Fin 2)) (by
        simp only [coords, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        decide)
    have h6 : l₁⁻¹ * l₂ = 1 := by
      apply longBlock_injective (1 : Fin 2)
      rw [h5', map_one]
    exact inv_mul_eq_one.mp h6
  · show ((longBlock (GaloisField 3 1) 2 1).range.map C).map (φ.comp θ) = U.map φ
    rw [← hU]
    simp only [Subgroup.map_map, MonoidHom.comp_assoc]
  · show ((shortBlock (GaloisField 3 1) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map C).map
      (φ.comp θ) = V.map φ
    rw [← hV]
    simp only [Subgroup.map_map, MonoidHom.comp_assoc]

theorem exists_hom_lift_sp4_three {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]
    (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) (hO3 : ¬ 3 ∣ Nat.card O)
    (θb : StatedSp 2 (GaloisField 3 1) →* Y ⧸ O) :
    ∃ θ : StatedSp 2 (GaloisField 3 1) →* Y, (QuotientGroup.mk' O).comp θ = θb := by
  have : Group.IsPerfect (StatedSp 2 (GaloisField 3 1)) := Q3Z.isPerfect_sp4_three
  have hdiv : ∀ m n : ℕ, m ∣ n → (Odd n ∧ ¬ 3 ∣ n) → (Odd m ∧ ¬ 3 ∣ m) :=
    fun m n hmn ⟨ho, hn⟩ => ⟨ho.of_dvd_nat hmn, fun h => hn (h.trans hmn)⟩
  refine exists_lift_of_noCover (Q := fun n => Odd n ∧ ¬ 3 ∣ n) hdiv Q3Z.sp4_three_noCover
    (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O) ?_ ?_ θb
  · rw [QuotientGroup.ker_mk']
    exact hOc
  · rw [QuotientGroup.ker_mk']
    exact ⟨hOodd, hO3⟩

theorem symplecticBlockPair_lift3 {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]
    (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) (hO3 : ¬ 3 ∣ Nat.card O)
    {A : Subgroup Y} (hA : Pow3 A) {V W : Subgroup (Y ⧸ O)}
    (h : SymplecticBlockPair (GaloisField 3 1) W (A.map (QuotientGroup.mk' O)) V) :
    ∃ B : Subgroup Y, B.map (QuotientGroup.mk' O) = V ∧ Pow3 B ∧
      ∃ W' : Subgroup Y, SymplecticBlockPair (GaloisField 3 1) W' A B := by
  obtain ⟨θb, c, -, hker, hinjL, hU, hV⟩ := h
  obtain ⟨θ, hθ⟩ := exists_hom_lift_sp4_three hOc hOodd hO3 θb
  have hπθ : ∀ x, QuotientGroup.mk' O (θ x) = θb x := fun x => DFunLike.congr_fun hθ x
  have hker0 : (QuotientGroup.mk' O).ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  have hcop : ∀ n ∈ (QuotientGroup.mk' O).ker, ¬ 3 ∣ orderOf n := by
    intro n hn h3
    rw [QuotientGroup.ker_mk'] at hn
    have h1 : orderOf (⟨n, hn⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hO3 (h3.trans h1)
  let C : StatedSp 2 (GaloisField 3 1) →* StatedSp 2 (GaloisField 3 1) :=
    (MulAut.conj c⁻¹).toMonoidHom
  let φL : SL(2, GaloisField 3 1) →* Y := θ.comp (C.comp (longBlock (GaloisField 3 1) 2 1))
  let φS : SL(2, GaloisField 3 1) →* Y := θ.comp (C.comp
    (shortBlock (GaloisField 3 1) (zero_ne_one : (0 : Fin 2) ≠ 1)))
  have hLr : ((longBlock (GaloisField 3 1) 2 1).range.map C).map θ = φL.range := by
    show _ = (θ.comp (C.comp (longBlock (GaloisField 3 1) 2 1))).range
    rw [MonoidHom.range_comp, MonoidHom.range_comp]
  have hSr : ((shortBlock (GaloisField 3 1) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map C).map θ =
      φS.range := by
    show _ = (θ.comp (C.comp (shortBlock (GaloisField 3 1)
      (zero_ne_one : (0 : Fin 2) ≠ 1)))).range
    rw [MonoidHom.range_comp, MonoidHom.range_comp]
  have hmapL : φL.range.map (QuotientGroup.mk' O) = A.map (QuotientGroup.mk' O) := by
    rw [← hLr, Subgroup.map_map, show (QuotientGroup.mk' O).comp θ = θb from hθ]
    exact hU
  have hmapS : φS.range.map (QuotientGroup.mk' O) = V := by
    rw [← hSr, Subgroup.map_map, show (QuotientGroup.mk' O).comp θ = θb from hθ]
    exact hV
  have hLA : φL.range = A :=
    eq_of_map_eq_of_pow3 (QuotientGroup.mk' O) hker0 hcop (pow3_range_sl2 card_gf3 φL) hA hmapL
  refine ⟨φS.range, hmapS, pow3_range_sl2 card_gf3 φS, θ.range, θ, c, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker, ← hπθ, MonoidHom.mem_ker.mp hx, map_one]
  · intro a b hab
    apply hinjL
    simp only [MonoidHom.comp_apply] at hab ⊢
    rw [← hπθ, ← hπθ]
    exact congrArg (QuotientGroup.mk' O) hab
  · rw [hLr, hLA]
  · rw [hSr]

end Pair

section Odd


theorem symplecticPair_oddDatum3 {n : ℕ} (hn : 3 ≤ n) :
    ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W
      (CFSG.LieType.CurtisTits.rankOne (oddDatum n (GaloisField 3 1)).rootGroup
        (⟨n - 2, by show n - 2 < n; omega⟩ : Fin (oddDatum n (GaloisField 3 1)).rank))
      (CFSG.LieType.CurtisTits.rankOne (oddDatum n (GaloisField 3 1)).rootGroup
        (⟨n - 1, by show n - 1 < n; omega⟩ : Fin (oddDatum n (GaloisField 3 1)).rank)) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (oddDatum n (GaloisField 3 1)).isFiniteType
    (Dv := (oddDatum n (GaloisField 3 1)).divisible) rfl
  have hE := CFSG.LieType.Steinberg.SpinOdd.chevalleyExtras (by omega : 2 ≤ n) O
    CFSG.LieType.Steinberg.SpinOdd.commC (CFSG.LieType.Steinberg.SpinOdd.commutatorFormula O)
  exact Q3V.exists_symplecticBlockStandardPair_rankOne_three hE rfl
    (i := ⟨n - 1, by show n - 1 < n; omega⟩) (j := ⟨n - 2, by show n - 2 < n; omega⟩)
    (by show cartanB n ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ = -2
        simp [cartanB, Fin.ext_iff]
        omega)
    (by show cartanB n ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = -1
        simp [cartanB, Fin.ext_iff]
        omega)

theorem centralQuot3_odd {m : ℕ} (hm : 3 ≤ m) :
    CentralQuot3 (spinAction (quadOdd m (GaloisField 3 1)))
      (fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField 3 1)))
      (fundSet (quadOdd m (GaloisField 3 1)))
      (scalars (GaloisField 3 1) (Fin m ⊕ Fin m ⊕ Unit → GaloisField 3 1)) := by
  have hadm : StatedLieAdmissible .POmegaOdd m 3 1 := ⟨Nat.prime_three, le_rfl, hm, by norm_num⟩
  have hY := yData3_odd hm hadm
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hker := ker_spinAction_le_center (quadOdd m (GaloisField 3 1))
  exact
    { ker_le := hker
      cop := fun z hz h3 => by
        have h2' : z ^ 2 = 1 := by
          rw [pow_two]
          exact ModelFacts.OrthAut.odd_hker2 h2 m z hz
        have := h3.trans (orderOf_dvd_of_pow_eq_one h2')
        omega
      center_le := fun z hz => Gaps.spinAction_center_mem_scalars_odd h2 hm hz
      pow3 := hY.pow3
      inj := fun R hR r hr h1 => hY.central R hR r hr (hker h1)
      map_mem := fun R hR => Gaps.map_mem_fundSet_odd hm hY.sc hR
      surj := fun L hL => Gaps.exists_map_eq_odd hm odd_gf3 hL }

end Odd

end CFSG.ClassicalInvolution.Q3.Q3TWY
