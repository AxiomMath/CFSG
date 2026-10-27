module

public import CFSG.RankThree.PartOne.CTP.SpinMinusEven

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.WeakCT
  CFSG.RankThree.PartOne.CTP
open scoped MatrixGroups

namespace CompsPTwoDFrameE


theorem weakCT_spinMinus_even_of_frame_pinned {n f : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n 2 f)
    (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f) {b c : F}
    [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type}
    [Group X] (U : Fin (n - 1) → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (θ : spinGroup (quadMinus 3 F b c) →* X)
    (hθV : (shortBlock hirr 3 finOne).range.map θ = U ⟨n - 2, by omega⟩)
    (ρ' : Fin (n - 2) → (SL(2, F) →* X))
    (hρ'₀ : ρ' ⟨n - 2 - 1, by omega⟩ = θ.comp (minusLongBlock b c))
    (hρ'U : ∀ k : Fin (n - 2),
      Function.Injective (ρ' k) ∧ (ρ' k).range = U ⟨k.val, by omega⟩)
    (hρ'ψ : ∀ i j : Fin (n - 2), i.val + 1 = j.val →
      ∃ ψ : SL(3, F) →* X, ψ.comp (blk F 0) = ρ' i ∧ ψ.comp (blk F 1) = ρ' j) :
    ∃ Ψ : spinGroup (quadMinus n F b c) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (quadMinus n F b c))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaMinus n 2 f ∧
      (∀ k, (CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map Ψ = U k) ∧
      (∀ (k : Fin (n - 1)) (hk : k.val + 1 < n - 1),
        Ψ.comp (rLong n b c hk) = ρ' ⟨k.val, by omega⟩) ∧
      ∀ (k : Fin (n - 1)), ¬ k.val + 1 < n - 1 →
        Ψ.comp (shortBlock hirr n k) = θ.comp (shortBlock hirr 3 finOne) := by
  classical
  have hn4 : 4 ≤ n := hn
  have hn3 : 3 ≤ n := by omega
  let P := spinMinusModel hirr
  let ρL : Fin (n - 1) → SL(2, F) →* X := fun k => if h : k.val < n - 2 then ρ' ⟨k.val, h⟩ else 1
  let ρS : SL(2, ShortField b c) →* X := θ.comp P.sb
  have hρL : ∀ k : Fin (n - 1), (h : k.val < n - 2) → ρL k = ρ' ⟨k.val, h⟩ := fun k h =>
    dite_eq_left h
  have hρLU : ∀ k : Fin (n - 1), k.val + 1 < n - 1 → (ρL k).range = U k := fun k hk => by
    rw [hρL k (by omega)]
    exact (hρ'U ⟨k.val, by omega⟩).2
  have hρLinj : ∀ k : Fin (n - 1), (h : k.val + 1 < n - 1) → Function.Injective (ρL k) :=
    fun k hk => by
      rw [hρL k (by omega)]
      exact (hρ'U ⟨k.val, by omega⟩).1
  have hρSU : ∀ k : Fin (n - 1), ¬ k.val + 1 < n - 1 → ρS.range = U k := fun k hk => by
    have hkb : k = ⟨n - 2, by omega⟩ := Fin.ext (by have := k.2; simp only; omega)
    rw [hkb, MonoidHom.range_comp]
    exact hθV
  have hCT : CurtisTits.CurtisTitsConclusion.{0} (minusDatum n hirr) .POmegaMinus n 2 f :=
    CurtisTits.curtisTitsConclusion_spinMinus hirr hadm hF
  have hCTG := minusDatum_isCTGroupDatum n hirr hn4
  have hL := leviConePresented_spinMinus hirr hn4
  have hdiv : (minusDatum n hirr).divisible = ∅ := rfl
  let nd : ∀ k, NodeData (minusDatum n hirr) X k (U k) := fun k =>
    if hk : k.val + 1 < n - 1 then nodeDataLong hirr (ρL k) (hρLU k hk) hk
    else nodeDataShortEven hirr ρS (hρSU k hk) hk
  have ndL : ∀ (k : Fin (n - 1)) (hk : k.val + 1 < n - 1),
      (nd k).IsParam (rLong n b c hk) (ρL k) := fun k hk => by
    have e : nd k = nodeDataLong hirr (ρL k) (hρLU k hk) hk := dite_eq_left hk
    rw [e]
    exact nodeDataLong_isParam hirr _ _ hk
  have ndS : ∀ (k : Fin (n - 1)) (hk : ¬ k.val + 1 < n - 1),
      (nd k).IsParam (shortBlock hirr n k) ρS := fun k hk => by
    have e : nd k = nodeDataShortEven hirr ρS (hρSU k hk) hk := dite_eq_right hk
    rw [e]
    exact nodeDataShortEven_isParam hirr _ _ hk
  have hnt : ∃ k, ∃ g, (nd k).ψp g ≠ 1 := by
    let k₁ : Fin (n - 1) := ⟨0, by omega⟩
    have hk₁ : k₁.val + 1 < n - 1 := by simp only [k₁]; omega
    refine ⟨k₁, ⟨rLong n b c hk₁ (tv 0 1 1), rLong_upper hirr hk₁ 1⟩, ?_⟩
    rw [(ndL k₁ hk₁).ψp_eq 1]
    intro h
    exact tv_zero_one_one_ne_one (hρLinj k₁ hk₁ (h.trans (map_one _).symm))
  have hloc : ∀ i j : Fin (minusDatum n hirr).rank, i ≤ j →
      ∃ (E : LeviEmbedding (minusDatum n hirr) i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : (minusDatum n hirr).rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : (minusDatum n hirr).rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · by_cases hi : i.val + 1 < n - 1
      · exact exists_levi_node hdiv hCTG nd (ndL i hi) (rLong_injective hi)
      · exact exists_levi_node hdiv hCTG nd (ndS i hi) (shortBlock_injective_even hirr n i)
    · have hlt' : i.val < j.val := hlt
      have hi2 : i.val < n - 1 := i.2
      have hj2 : j.val < n - 1 := j.2
      by_cases hadj : i.val + 1 = j.val
      · by_cases hj : j.val + 1 < n - 1
        ·
          have hi : i.val + 1 < n - 1 := by omega
          obtain ⟨emb, hinj, hemb0, hemb1⟩ := exists_sl3_minus_even b c hadj hi hj
          obtain ⟨ψ, hψ0, hψ1⟩ := hρ'ψ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
            (by simpa [edgeUp] using hadj)
          exact exists_levi_of_model hdiv hCTG nd (ndL i hi) (ndL j hj) emb hinj (blk F 0)
            (blk F 1) hemb0 hemb1 ψ (hψ0.trans (hρL i (by omega)).symm)
            (hψ1.trans (hρL j (by omega)).symm)
        ·
          have hia : i.val + 3 = n := by omega
          have hjb : j.val + 2 = n := by omega
          have hi : i.val + 1 < n - 1 := by omega
          have hi' : ρL i = θ.comp P.lb := by
            have hk : (⟨i.val, by omega⟩ : Fin (n - 2)) = ⟨n - 2 - 1, by omega⟩ :=
              Fin.ext (by simp only; omega)
            rw [hρL i (by omega), hk, hρ'₀]
            rfl
          exact exists_levi_of_model hdiv hCTG nd (ndL i hi) (ndS j hj)
            (minusShift n hn3 b c).spinGroupMap (spinGroupMap_minusShift_injective_even n hn3 hirr)
            (minusLongBlock b c) (shortBlock hirr 3 finOne) (minusShift_comp_longBlock hn3 hia hi)
            (minusShift_comp_shortBlock hn3 hirr hjb) θ hi'.symm rfl
      ·
        have hlt2 : i.val + 1 < j.val := by omega
        have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
        have hi : i.val + 1 < n - 1 := by omega
        have hcU : ∀ (A : SL(2, F)) (B : SL(2, F)), ∀ (hj : j.val + 1 < n - 1),
            Commute (ρL i A) (ρL j B) := fun A B hj =>
          hcomm i j hlt2 _ (hρLU i hi ▸ ⟨A, rfl⟩) _ (hρLU j hj ▸ ⟨B, rfl⟩)
        by_cases hj : j.val + 1 < n - 1
        · exact exists_levi_orth hdiv hCTG nd (ndL i hi) (ndL j hj) (rLong_injective hi)
            (rLong_injective hj) (commute_rLong_rLong hi hj hlt2)
            (hZ_of_torus (minusDatum_torus_iSupIndep n hirr) hne _ _
              (rLong_center_mem_torus hirr hi) (rLong_center_mem_torus hirr hj))
            (fun A B => hcU A B hj)
        · exact exists_levi_orth hdiv hCTG nd (ndL i hi) (ndS j hj) (rLong_injective hi)
            (shortBlock_injective_even hirr n j) (commute_rLong_shortBlock hirr hi hlt2)
            (hZ_of_torus (minusDatum_torus_iSupIndep n hirr) hne _ _
              (rLong_center_mem_torus hirr hi) (shortBlock_center_mem_torus hirr hj))
            (fun A B => hcomm i j hlt2 _ (hρLU i hi ▸ ⟨A, rfl⟩) _ (hρSU j hj ▸ ⟨B, rfl⟩))
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, hpin⟩ :=
    weakCT_of_twisted_nodes_pinned hCT hL hdiv hgen nd hnt hloc
  refine ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => (hpin k).1, ?_, ?_⟩
  · intro k hk
    rw [← hρL k (by omega)]
    exact (ndL k hk).comp_eq_of_rootGroup Ψ (hpin k).2.1 (hpin k).2.2
  · intro k hk
    change Ψ.comp (shortBlock hirr n k) = ρS
    exact (ndS k hk).comp_eq_of_rootGroup Ψ (hpin k).2.1 (hpin k).2.2

theorem weakCT_spinMinus_even_of_frame {n f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 2 f)
    (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f) {b c : F}
    [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type}
    [Group X] (U : Fin (n - 1) → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (θ : spinGroup (quadMinus 3 F b c) →* X)
    (hθV : (shortBlock hirr 3 finOne).range.map θ = U ⟨n - 2, by omega⟩)
    (ρ' : Fin (n - 2) → (SL(2, F) →* X))
    (hρ'₀ : ρ' ⟨n - 2 - 1, by omega⟩ = θ.comp (minusLongBlock b c))
    (hρ'U : ∀ k : Fin (n - 2),
      Function.Injective (ρ' k) ∧ (ρ' k).range = U ⟨k.val, by omega⟩)
    (hρ'ψ : ∀ i j : Fin (n - 2), i.val + 1 = j.val →
      ∃ ψ : SL(3, F) →* X, ψ.comp (blk F 0) = ρ' i ∧ ψ.comp (blk F 1) = ρ' j) :
    ∃ Ψ : spinGroup (quadMinus n F b c) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (quadMinus n F b c))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaMinus n 2 f ∧
      ∀ k, (CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map Ψ = U k := by
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, hnodes, -, -⟩ :=
    weakCT_spinMinus_even_of_frame_pinned hadm hn hF hirr U hgen hcomm θ hθV ρ' hρ'₀ hρ'U hρ'ψ
  exact ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, hnodes⟩

end CompsPTwoDFrameE

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
