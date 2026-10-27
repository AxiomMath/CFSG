module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus

public section

namespace CFSG.ClassicalInvolution.Models.TwistedPairs

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

@[expose] def TwistedB2BlockPair {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type} [Group X] (W U V : Subgroup X) : Prop :=
  haveI := fact_shortField hirr
  ∃ θ : spinGroup (quadMinus 3 F b c) →* X, θ.range = W ∧
    θ.ker ≤ Subgroup.center (spinGroup (quadMinus 3 F b c)) ∧
    Function.Injective (θ.comp (spinMinusModel hirr).lb) ∧
    (spinMinusModel hirr).lb.range.map θ = U ∧ (spinMinusModel hirr).sb.range.map θ = V

theorem TwistedB2BlockStandardPair.pair {F : Type} [Field F] [Finite F] {b c : F}
    {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {X : Type} [Group X] {W U V : Subgroup X}
    (h : TwistedB2BlockStandardPair hirr W U V) : TwistedB2BlockPair hirr W U V := by
  have := fact_shortField hirr
  obtain ⟨θ, hrange, hker, hl, -, hU, hV⟩ := h
  exact ⟨θ, hrange, hker, hl, hU, hV⟩

end CFSG.ClassicalInvolution.Models.TwistedPairs

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

theorem weakCT_spinMinus_of_pair {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p f)
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ Nat.card F) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type} [Group X] (U : Fin (n - 1) → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hpair : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (htw : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockPair hirr W (U i) (U j)) :
    ∃ Ψ : spinGroup (quadMinus n F b c) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (quadMinus n F b c))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaMinus n p f ∧
      ∀ k, (CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map Ψ = U k := by
  classical
  have hn4 : 4 ≤ n := hadm.2.2
  have h2 : (2 : F) ≠ 0 := by
    have hp := hadm.1
    have hf := hadm.2.1
    have hqc : (ringChar F).Prime := by
      rw [ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
      exact hp
    rw [Ne, ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hqc,
      ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
    exact hp2
  have := fact_shortField hirr
  have hn3 : 3 ≤ n := by omega
  obtain ⟨W, θ, hθW, -, hθl, hθU, hθV⟩ :=
    htw ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ (by simp only; omega) (by simp only; omega)
  let P := spinMinusModel hirr
  have hν : ∃ t, P.nu t ≠ 1 := exists_spinNu_ne hq
  let U' : Fin (n - 2) → Subgroup X := fun k => U ⟨k.val, by omega⟩
  have hcomm' : ∀ i j : Fin (n - 2), i ≠ j → ¬ edgeUp (n - 2) i j → ¬ edgeUp (n - 2) j i →
      ∀ u ∈ U' i, ∀ v ∈ U' j, u * v = v * u := by
    intro i j hne h1 h2' u hu v hv
    simp only [edgeUp] at h1 h2'
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm _ _ (by simp only; omega) u hu v hv
    · exact (hcomm _ _ (by simp only; omega) v hv u hu).symm
  have hpair' : ∀ i j : Fin (n - 2), edgeUp (n - 2) i j →
      ∃ W, LinearBlockStandardPair F W (U' i) (U' j) := by
    intro i j hij
    simp only [edgeUp] at hij
    have hj := j.isLt
    exact hpair ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij (by dsimp only; omega)
  have hU' : (θ.comp P.lb).range = U' ⟨n - 2 - 1, by omega⟩ := by
    rw [MonoidHom.range_comp]
    exact hθU
  have hV' : ∀ q : Fin (n - 2), (edgeUp (n - 2) ⟨n - 2 - 1, by omega⟩ q ∨
      edgeUp (n - 2) q ⟨n - 2 - 1, by omega⟩) → ∀ x ∈ (θ.comp P.sb).range, ∀ y ∈ U' q,
      x * y = y * x := by
    intro q hq' x hx y hy
    have hq'' : q.val + 1 = n - 2 - 1 := by
      rcases hq' with h | h
      · simp only [edgeUp] at h
        have := q.2
        omega
      · simpa only [edgeUp] using h
    rw [MonoidHom.range_comp] at hx
    have hx' : x ∈ U ⟨n - 2, by omega⟩ := hθV ▸ hx
    exact (hcomm ⟨q.val, by omega⟩ ⟨n - 2, by omega⟩ (by simp only; omega) y hy x hx').symm
  obtain ⟨ρ', hρ'₀, hρ'U, hρ'ψ⟩ := exists_frame_of_tree_long P hν hq
    (rootedTree_edgeUp_last (m := n - 2) (by omega))
    ⟨⟨n - 4, by omega⟩, Or.inr (by simp only [edgeUp]; omega)⟩ hcomm' hpair' hθl hU' hV'
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
  have hCT : CurtisTits.CurtisTitsConclusion.{0} (minusDatum n hirr) .POmegaMinus n p f :=
    CurtisTits.curtisTitsConclusion_spinMinus hirr hadm hF
  have hCTG := minusDatum_isCTGroupDatum n hirr hn4
  have hL := leviConePresented_spinMinus hirr hn4
  have hdiv : (minusDatum n hirr).divisible = ∅ := rfl
  let nd : ∀ k, NodeData (minusDatum n hirr) X k (U k) := fun k =>
    if hk : k.val + 1 < n - 1 then nodeDataLong hirr (ρL k) (hρLU k hk) hk
    else nodeDataShort hirr h2 ρS (hρSU k hk) hk
  have ndL : ∀ (k : Fin (n - 1)) (hk : k.val + 1 < n - 1),
      (nd k).IsParam (rLong n b c hk) (ρL k) := fun k hk => by
    have e : nd k = nodeDataLong hirr (ρL k) (hρLU k hk) hk := dite_eq_left hk
    rw [e]
    exact nodeDataLong_isParam hirr _ _ hk
  have ndS : ∀ (k : Fin (n - 1)) (hk : ¬ k.val + 1 < n - 1),
      (nd k).IsParam (shortBlock hirr n k) ρS := fun k hk => by
    have e : nd k = nodeDataShort hirr h2 ρS (hρSU k hk) hk := dite_eq_right hk
    rw [e]
    exact nodeDataShort_isParam hirr h2 _ _ hk
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
      · exact exists_levi_node hdiv hCTG nd (ndS i hi) (shortBlock_injective hirr h2 n i)
    · have hlt' : i.val < j.val := hlt
      have hi2 : i.val < n - 1 := i.2
      have hj2 : j.val < n - 1 := j.2
      by_cases hadj : i.val + 1 = j.val
      · by_cases hj : j.val + 1 < n - 1
        ·
          have hi : i.val + 1 < n - 1 := by omega
          obtain ⟨emb, hinj, hemb0, hemb1⟩ := exists_sl3_minus h2 hn4 b c hadj hi hj
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
          exact exists_levi_of_model hdiv hCTG nd (ndL i hi) (ndS j hj)
            (minusShift n hn3 b c).spinGroupMap (spinGroupMap_minusShift_injective h2 n hn3 hirr)
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
            (shortBlock_injective hirr h2 n j) (commute_rLong_shortBlock hirr hi hlt2)
            (hZ_of_torus (minusDatum_torus_iSupIndep n hirr) hne _ _
              (rLong_center_mem_torus hirr hi) (shortBlock_center_mem_torus hirr hj))
            (fun A B => hcomm i j hlt2 _ (hρLU i hi ▸ ⟨A, rfl⟩) _ (hρSU j hj ▸ ⟨B, rfl⟩))
  exact weakCT_of_twisted_nodes hCT hL hdiv hgen nd hnt hloc

end CFSG.ClassicalInvolution.WeakCT
