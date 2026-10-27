module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.CoverLiftsKer
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestJ3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.SectionRank.Native CFSG.Blueprint
open scoped commutatorElement

theorem j3_cover_setup
    {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (hZ3 : Nat.card (center X) = 3) (e : X ⧸ center X ≃* NativeSporadic.J3) :
    ∃ k : Fin 6 → X, (∀ w ∈ j3GammaWords, evalW k w = 1) ∧
      center X ≤ closure (Set.range k) ∧ Nat.card (closure (Set.range k)) = 5832 ∧
      (closure (Set.range k)).map (QuotientGroup.mk' (center X)) =
        closure (Set.range fun i => QuotientGroup.mk' (center X) (k i)) ∧
      Nat.card (closure (Set.range fun i => QuotientGroup.mk' (center X) (k i))) = 1944 ∧
      (∀ w ∈ j3CoverRels, evalW k w ∈ center X) ∧
      ∃ φ : PG 6 j3GammaWords →* X, Function.Injective φ ∧
        ∀ i, φ (PresentedGroup.of i) = k i := by
  classical
  have hperf : Group.IsPerfect X := hX.1
  have hπk := QuotientGroup.ker_mk' (center X)
  have hZp : IsPGroup 3 (center X) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.of_card (n := 1) (by rw [hZ3]; norm_num)
  obtain ⟨g, he, hc, hrels, hN⟩ := J3_cover_witness
  have hev : ∀ w, e.symm (evalW g w) = evalW (fun i => e.symm (g i)) w := fun w =>
    map_evalW e.symm g w
  set g' : Fin 6 → X ⧸ center X := fun i => e.symm (g i) with hg'
  have hcard : Nat.card (X ⧸ center X) = 50232960 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3
  have he' : ∀ i, j3CoverE i ≠ 0 → g' i ^ j3CoverE i = 1 ∧ Nat.Coprime 3 (j3CoverE i) := by
    intro i hi
    refine ⟨by rw [hg', ← map_pow, he i hi, map_one], ?_⟩
    have : j3CoverE i = 8 := by
      unfold j3CoverE at hi ⊢
      split_ifs at hi ⊢ <;> simp_all
    rw [this]
    decide
  have hc' : ∀ i, j3CoverE i = 0 → g' i = ⁅evalW g' (j3CoverCWf i).1, evalW g' (j3CoverCWf i).2⁆ := by
    intro i hi
    simp only [hg']
    rw [← hev, ← hev, ← map_commutatorElement, ← hc i hi]
  have hrels' : ∀ w ∈ j3CoverRels, evalW g' w = 1 := by
    intro w hw
    simp only [hg']
    rw [← hev, hrels w hw, map_one]
  have hN' : Nat.card (Subgroup.closure ({g' 0, g' 1} : Set (X ⧸ center X))) = 1944 := by
    have h := Subgroup.card_map_of_injective (f := (e.symm : NativeSporadic.J3 →* X ⧸ center X))
      (K := Subgroup.closure ({g 0, g 1} : Set NativeSporadic.J3)) e.symm.injective
    rw [MonoidHom.map_closure, Set.image_pair] at h
    exact h.trans hN
  have hΓ := j3_gamma_card
  set H := closure (Set.range g')
  have hle : Subgroup.closure ({g' 0, g' 1} : Set (X ⧸ center X)) ≤ H := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact subset_closure ⟨0, rfl⟩
    · exact subset_closure ⟨1, rfl⟩
  have hNidx : (Subgroup.closure ({g' 0, g' 1} : Set (X ⧸ center X))).index = 25840 := by
    have h1 := (Subgroup.closure ({g' 0, g' 1} : Set (X ⧸ center X))).index_mul_card
    rw [hN', hcard] at h1
    omega
  have hidx : ¬ 3 ∣ H.index := by
    intro h3
    have := h3.trans (Subgroup.index_dvd_of_le hle)
    rw [hNidx] at this
    omega
  have hcardH : 1944 ≤ Nat.card H := by
    rw [← hN']
    exact Subgroup.card_le_of_le hle
  obtain ⟨k, hk, hkrel, hkerk, hmapk, hcardk, hΓk⟩ := exists_lifts_closure
    (QuotientGroup.mk'_surjective (center X)) hπk.le (by rw [hπk]; exact hZp) g' j3CoverE
    j3CoverCWf he' hc' j3CoverRels hrels' hidx hΓ.1
  rw [hπk] at hkerk hcardk
  have hk' : (fun i => QuotientGroup.mk' (center X) (k i)) = g' := funext hk
  have hHcard : Nat.card H = 1944 := by
    have h1 : Nat.card H * 3 ≤ 5832 := by
      have := hcardk.symm.le.trans hΓk
      rw [hZ3] at this
      exact this.trans hΓ.2
    omega
  refine ⟨k, hkrel, hkerk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcardk, hHcard, hZ3]
  · rw [hmapk, hk']
  · rw [hk']; exact hHcard
  · intro w hw
    rw [← hπk, MonoidHom.mem_ker]
    have h1 := map_evalW (QuotientGroup.mk' (center X)) k w
    rw [h1]
    change evalW (fun i => QuotientGroup.mk' (center X) (k i)) w = 1
    rw [hk']
    exact hrels' w hw
  ·
    have hrelk : ∀ r ∈ ({r | r ∈ (gammaWords j3CoverE j3CoverCWf j3CoverRels).map FreeGroup.mk} :
        Set (FreeGroup (Fin 6))), FreeGroup.lift k r = 1 := by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      rw [lift_mk_eq_evalW]
      exact hkrel w hw
    let φ : PG 6 (gammaWords j3CoverE j3CoverCWf j3CoverRels) →* X :=
      PresentedGroup.toGroup hrelk
    have hφ : φ.range = closure (Set.range k) := by
      rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
        ← Set.range_comp]
      congr 2
      funext i
      exact PresentedGroup.toGroup.of _
    have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
    have hcrk : Nat.card φ.range = 5832 := by
      rw [hφ, hcardk, hHcard, hZ3]
    have hfinΓ : Finite (PG 6 (gammaWords j3CoverE j3CoverCWf j3CoverRels)) := hΓ.1
    have hbij : Function.Bijective φ.rangeRestrict :=
      hsurj.bijective_of_nat_card_le (by rw [hcrk]; exact hΓ.2)
    refine ⟨φ, ?_, fun i => PresentedGroup.toGroup.of _⟩
    intro a b hab
    exact hbij.1 (Subtype.ext hab)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
