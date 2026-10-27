module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzHyp31A

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp Cover


theorem oddCover_top_suz {Y : Type} [Group Y] (hY : IsSporadic Y .Suz) :
    OddCover .Suz (⊤ : Subgroup Y) := by
  obtain ⟨hfin, hs, hnc⟩ := suz_simple_data hY
  have hZ : center Y = ⊥ := center_eq_bot_of_isSimpleGroup_nonabelian hnc
  obtain ⟨e⟩ := hY
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := Y)).symm
    (isQuasisimple_of_simple_nonabelian hs hnc), ?_, ?_⟩
  · rw [card_center_of_mulEquiv' (Subgroup.topEquiv (G := Y)), hZ, Subgroup.card_bot]
    exact odd_one
  · exact ⟨(quotientCenterEquiv' (Subgroup.topEquiv (G := Y))).trans
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e)⟩

theorem suzQ_of_pair_top {Y : Type} [Group Y] (hY : IsSporadic Y .Suz) {K : Subgroup Y} {u : Y}
    (hP : SuzPair Y ⊤ K u) : SuzQ Y ⊤ K u := by
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hP
  refine ⟨hu, hu2, hKL, hKu, hKperf, ?_⟩
  obtain ⟨hfin, hs, hnc⟩ := suz_simple_data hY
  have hZ : center Y = ⊥ := center_eq_bot_of_isSimpleGroup_nonabelian hnc
  have hZ' : center ↥(⊤ : Subgroup Y) = ⊥ := by
    apply Subgroup.card_eq_one.1
    rw [card_center_of_mulEquiv' (Subgroup.topEquiv (G := Y)), hZ, Subgroup.card_bot]
  have hqinj : Function.Injective (q ↥(⊤ : Subgroup Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    unfold q
    rw [QuotientGroup.ker_mk', hZ']
  rw [Subgroup.card_map_of_injective hqinj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
  exact hcard

theorem suzAutFix_of_autCentralizerN0 (h : SuzAutCentralizerN0) : SuzAutFix := by
  intro Y _ hY K u hP
  obtain ⟨hfin, hs, hnc⟩ := suz_simple_data hY
  have hcov := oddCover_top_suz hY
  have hQ := suzQ_of_pair_top hY hP
  obtain ⟨N₀, hcan⟩ := exists_canLoc K (by rw [hP.2.2.2.2.2]; decide)
  obtain ⟨hsolv, h2, hinner⟩ := h Y ⊤ K u N₀ hcov hQ hcan
  let e : MulAut Y ≃* MulAut ↥(⊤ : Subgroup Y) :=
    MulAut.congr (Subgroup.topEquiv (G := Y)).symm
  have happ : ∀ (β : MulAut Y) (k : ↥(⊤ : Subgroup Y)),
      ((e β k : ↥(⊤ : Subgroup Y)) : Y) = β k := fun β k => rfl
  have hmem : ∀ β ∈ autFixing K, e β ∈ autCentralizer (⊤ : Subgroup Y) N₀ := by
    intro β hβ k hk
    apply Subtype.ext
    rw [happ]
    exact hβ k (hcan.le hk)
  let f : ↥(autFixing K) →* ↥(autCentralizer (⊤ : Subgroup Y) N₀) :=
    (e.toMonoidHom.comp (autFixing K).subtype).codRestrict (autCentralizer (⊤ : Subgroup Y) N₀)
      (fun β => hmem β β.2)
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (e.injective (congrArg Subtype.val hab))
  have hsq : ∀ A : Subgroup ↥(autFixing K), IsPGroup 2 A → ∀ x ∈ A, x * x = 1 := by
    intro A hA x hx
    have hmapp : IsPGroup 2 ↥(A.map f) :=
      hA.of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A)
    have := (h2 (A.map f) hmapp).1 (f x) (Subgroup.mem_map_of_mem f hx)
    apply hf
    rw [map_mul, map_one]
    exact this
  refine ⟨⟨Group.isSolvable_of_isSolvable_injective hf, fun E hE _ => ?_, fun β hβ => ?_⟩, hsq⟩
  · have hpE : IsPGroup 2 ↥(E.map f) := by
      intro g
      obtain ⟨x, hx, hg⟩ := g.2
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have h1 : (g : ↥(autCentralizer (⊤ : Subgroup Y) N₀)) = f x := hg.symm
      show (g : ↥(autCentralizer (⊤ : Subgroup Y) N₀)) ^ 2 ^ 1 = 1
      rw [h1, pow_one, pow_two, ← map_mul, hE x hx, map_one]
    have := (h2 (E.map f) hpE).2
    rwa [Subgroup.card_map_of_injective hf] at this
  · obtain ⟨g, hg⟩ := hinner _ (hmem β hβ)
    refine ⟨(g : Y), e.injective ?_⟩
    rw [hg]
    ext z
    rw [happ]
    simp [MulAut.conj_apply]

end CFSG.EvenSporadicStandard.Induction
