module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightBHeis
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightBUnitaryCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTAlignMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignFour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightBSecondClass

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Commute

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp 4 K}

theorem disjoint_compl_ctuPlanes_blkShort_two {R : Finset (Fin 4)} (h2R : 2 ∈ R) (h3R : 3 ∈ R)
    (h2 : 2 + 1 < (2 * 4 + 1) / 2) :
    Disjoint ((ctuPlanes 1 R)ᶜ) (Finset.univ.filter fun a : Fin (2 * 4 + 1) =>
      blkShort (n := 2 * 4 + 1) ⟨2, by omega⟩ h2 a ≠ 0) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [Finset.mem_compl] at ha
  apply ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  rw [blkShort_ne_zero_iff] at hb
  obtain ⟨w, rfl⟩ := (ctuCoord 4 1).surjective a
  rw [ctuCoord_mem_ctuPlanes]
  rcases w with (p | p) | i
  · simp only [ctuCoord_inl_inl] at hb
    rw [inPlanes_inl]
    have hp := p.2
    rcases (by omega : p.val = 2 ∨ p.val = 3) with h | h
    · rw [show p = 2 from Fin.ext h]
      exact h2R
    · rw [show p = 3 from Fin.ext h]
      exact h3R
  · simp only [ctuCoord_inl_inr] at hb
    rw [inPlanes_inl]
    have hp := p.2
    rcases (by omega : p.val = 2 ∨ p.val = 3) with h | h
    · rw [show p = 2 from Fin.ext h]
      exact h2R
    · rw [show p = 3 from Fin.ext h]
      exact h3R
  · simp only [ctuCoord_inr] at hb
    have hi := i.2
    omega

theorem commute_productPiece_odd {G : Type*} [Group G] {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) (htr : ∀ c, σ c = c → ∃ d, d + σ d = c)
    (Φ : ∀ k : Fin 4, ctuBlock σ 1 ({k} : Finset (Fin 4)) →* G)
    (hagree : ∀ (k l : Fin 4) (x : SU σ (2 * 4 + 1)) (hx : x ∈ ctuBlock σ 1 ({k} : Finset (Fin 4)))
      (hx' : x ∈ ctuBlock σ 1 ({l} : Finset (Fin 4))), Φ k ⟨x, hx⟩ = Φ l ⟨x, hx'⟩)
    {x : SU σ (2 * 4 + 1)} (hx : x ∈ rankOne (rootGroup σ hσ (2 * 4 + 1)) ⟨0, by norm_num⟩)
    (hx2 : x ∈ ctuBlock σ 1 ({2} : Finset (Fin 4))) {y : SU σ (2 * 4 + 1)}
    (hy : y ∈ rankOne (rootGroup σ hσ (2 * 4 + 1)) ⟨2, by norm_num⟩)
    (hy0 : y ∈ ctuBlock σ 1 ({0} : Finset (Fin 4))) :
    Commute (Φ 2 ⟨x, hx2⟩) (Φ 0 ⟨y, hy0⟩) := by
  have h0 : 0 + 1 < (2 * 4 + 1) / 2 := by norm_num
  have h2 : 2 + 1 < (2 * 4 + 1) / 2 := by norm_num
  set m : Fin (2 * 4 + 1) := ctuCoord 4 1 (Sum.inr 0) with hmdef
  have hm : Fin.rev m = m := ctuCoord_inr_rev le_rfl 0
  have hmR : ∀ R : Finset (Fin 4), m ∉ ctuPlanes 1 R := fun R h =>
    not_inPlanes_inr R 0 (ctuCoord_mem_ctuPlanes.1 h)
  have hyS := ctuToSL_mem_blockSpecialLinear_of_mem_rankOne h2 hy
  have hy1 : y ∈ ctuBlock σ 1 ({1} : Finset (Fin 4)) :=
    rankOne_le_ctuBlock le_rfl (⟨2, by norm_num⟩ : Fin ((2 * 4 + 1) / 2)) (by decide)
      (by decide) hy
  set C : Subgroup G := centralizer ({Φ 0 ⟨y, hy0⟩} : Set G) with hC
  set M : Subgroup (SU σ (2 * 4 + 1)) :=
    (C.comap (Φ 2)).map (ctuBlock σ 1 ({2} : Finset (Fin 4))).subtype with hM
  have hmemM : ∀ (z : SU σ (2 * 4 + 1)) (hz : z ∈ ctuBlock σ 1 ({2} : Finset (Fin 4))),
      Φ 2 ⟨z, hz⟩ ∈ C → z ∈ M := fun z hz h => ⟨⟨z, hz⟩, h, rfl⟩
  have hcommz : ∀ {R : Finset (Fin 4)}, 2 ∈ R → 3 ∈ R → ∀ z ∈ ctuBlock σ 1 R, z * y = y * z := by
    intro R h2R h3R z hz
    apply ctuToSL_injective
    rw [map_mul, map_mul]
    exact (LinearPilot.commute_blockSpecialLinear_of_disjoint
      (disjoint_compl_ctuPlanes_blkShort_two h2R h3R h2) hz hyS).eq
  have hheis0 : ∀ (i : Fin (2 * 4 + 1)) (hi : i ≠ Fin.rev i) (him : i ≠ m),
      i ∉ ctuPlanes 1 ({1, 2, 3} : Finset (Fin 4)) → heisenbergSubgroup σ hσ hi him hm ≤ M := by
    intro i hi him hiR z hz
    have hz123 := heisenbergSubgroup_le_ctuBlock hi him hm hiR (hmR _) hz
    have hz2 : z ∈ ctuBlock σ 1 ({2} : Finset (Fin 4)) := ctuBlock_anti (by decide) hz123
    have hz1 : z ∈ ctuBlock σ 1 ({1} : Finset (Fin 4)) := ctuBlock_anti (by decide) hz123
    refine hmemM z hz2 ?_
    have h1 : Φ 2 ⟨z, hz2⟩ = Φ 1 ⟨z, hz1⟩ := hagree 2 1 z hz2 hz1
    have h1' : Φ 0 ⟨y, hy0⟩ = Φ 1 ⟨y, hy1⟩ := hagree 0 1 y hy0 hy1
    have h2 : (⟨z, hz1⟩ : ctuBlock σ 1 ({1} : Finset (Fin 4))) * ⟨y, hy1⟩ = ⟨y, hy1⟩ * ⟨z, hz1⟩ :=
      Subtype.ext (hcommz (by decide) (by decide) z hz123)
    rw [hC, mem_centralizer_singleton_iff, h1, h1', ← map_mul, h2, map_mul]
  have hheis1 : ∀ (i : Fin (2 * 4 + 1)) (hi : i ≠ Fin.rev i) (him : i ≠ m),
      i ∉ ctuPlanes 1 ({0, 2, 3} : Finset (Fin 4)) → heisenbergSubgroup σ hσ hi him hm ≤ M := by
    intro i hi him hiR z hz
    have hz023 := heisenbergSubgroup_le_ctuBlock hi him hm hiR (hmR _) hz
    have hz2 : z ∈ ctuBlock σ 1 ({2} : Finset (Fin 4)) := ctuBlock_anti (by decide) hz023
    have hz0 : z ∈ ctuBlock σ 1 ({0} : Finset (Fin 4)) := ctuBlock_anti (by decide) hz023
    refine hmemM z hz2 ?_
    have h1 : Φ 2 ⟨z, hz2⟩ = Φ 0 ⟨z, hz0⟩ := hagree 2 0 z hz2 hz0
    have h2 : (⟨z, hz0⟩ : ctuBlock σ 1 ({0} : Finset (Fin 4))) * ⟨y, hy0⟩ = ⟨y, hy0⟩ * ⟨z, hz0⟩ :=
      Subtype.ext (hcommz (by decide) (by decide) z hz023)
    rw [hC, mem_centralizer_singleton_iff, h1, ← map_mul, h2, map_mul]
  have hL₀ : rankOne (rootGroup σ hσ (2 * 4 + 1)) ⟨0, by norm_num⟩ ≤ M := by
    refine rankOne_short_le_of_heisenberg htr h0 hm fun i hi him hcase => ?_
    rcases hcase with rfl | rfl | rfl | rfl
    · refine hheis0 _ hi him ?_
      rw [lowIdx_eq_ctuCoord (by norm_num), ctuCoord_mem_ctuPlanes, inPlanes_inl]
      decide
    · refine hheis1 _ hi him ?_
      rw [lowIdx_eq_ctuCoord (by norm_num), ctuCoord_mem_ctuPlanes, inPlanes_inl]
      simp [planeOf, Fin.ext_iff]
    · refine hheis0 _ hi him ?_
      rw [rev_lowIdx_eq_ctuCoord le_rfl (by norm_num), ctuCoord_mem_ctuPlanes, inPlanes_inl]
      decide
    · refine hheis1 _ hi him ?_
      rw [rev_lowIdx_eq_ctuCoord le_rfl (by norm_num), ctuCoord_mem_ctuPlanes, inPlanes_inl]
      simp [planeOf, Fin.ext_iff]
  obtain ⟨⟨x', hx'⟩, hx'C, hxx⟩ := hL₀ hx
  have hxx' : (⟨x', hx'⟩ : ctuBlock σ 1 ({2} : Finset (Fin 4))) = ⟨x, hx2⟩ := Subtype.ext hxx
  rw [hxx'] at hx'C
  exact mem_centralizer_singleton_iff.1 hx'C

theorem nsUniProductCommute_odd (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam 1 le_rfl (unitaryInvolution F 2 1) ι hι e k)
    (hagree : NsUniParamAgree P) : NsUniProductCommute hF P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hx2 y hy hy0
  exact commute_productPiece_odd (unitaryInvolution_involutive hF)
    (fun c hc => CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq hF hc)
    (fun k => (P k).Φ) hagree hx hx2 hy hy0

end Commute

section Align

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem exists_nsUniParamAgree_odd (hKc : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 1 ≤ f) (hN : 4 ≤ N)
    (P : ∀ k : Fin N, NsUniParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k) :
    ∃ Q : ∀ k : Fin N, NsUniParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k,
      NsUniParamAgree Q := by
  classical
  obtain ⟨o⟩ : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hex : ∀ k : Fin N, ∃ R : NsUniParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k,
      ∀ (x : SU (unitaryInvolution F 2 f) (2 * N + 1))
        (hx : x ∈ ctuBlock (unitaryInvolution F 2 f) 1 ({k, o} : Finset (Fin N))),
        R.Φ ⟨x, ctuBlock_pair_le_left _ k o hx⟩ = (P o).Φ ⟨x, ctuBlock_pair_le_right _ k o hx⟩ := by
    intro k
    by_cases hko : k = o
    · subst hko
      exact ⟨P k, fun x hx => rfl⟩
    · obtain ⟨ν, hν, b, h1⟩ := (P k).exists_twist_of_overlap hKc hF hf hN hko (P o)
      have hT := ctuaTwist_admissible (N := N) (hε := le_rfl) (ι := ι) (hι := hι)
        (hσ := unitaryInvolution_involutive hF) hν b
      refine ⟨(P k).twistBy hT.inv, fun x hx => ?_⟩
      rw [NsUniParam.twistBy_Φ_apply]
      have hx' : (ctuaTwist le_rfl (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν
          b)⁻¹ x ∈ ctuBlock (unitaryInvolution F 2 f) 1 ({k, o} : Finset (Fin N)) :=
        (hT.inv.mem_iff _ x).2 hx
      refine (h1 _ hx').trans (congrArg (P o).Φ (Subtype.ext ?_))
      change (ctuaTwist le_rfl (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b)
        ((ctuaTwist le_rfl (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b)⁻¹
          x) = x
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  choose Q hQ using hex
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl := mem_ctuBlock_pair hx hx'
  have hagreeo : ∀ {m : Fin N} (y : SU (unitaryInvolution F 2 f) (2 * N + 1))
      (hy : y ∈ ctuBlock (unitaryInvolution F 2 f) 1 ({m} : Finset (Fin N)))
      (hy' : y ∈ ctuBlock (unitaryInvolution F 2 f) 1 ({o} : Finset (Fin N))),
      (Q m).Φ ⟨y, hy⟩ = (P o).Φ ⟨y, hy'⟩ :=
    fun y hy hy' => hQ _ y (mem_ctuBlock_pair hy hy')
  by_cases hko : k = o
  · subst hko
    exact (hagreeo x hx hx).trans (hagreeo x hx' hx).symm
  by_cases hlo : l = o
  · subst hlo
    exact (hagreeo x hx hx').trans (hagreeo x hx' hx').symm
  obtain ⟨ν, hν, b, h1⟩ := (Q k).exists_twist_of_overlap hKc hF hf hN hkl (Q l)
  have hT := ctuaTwist_admissible (N := N) (hε := le_rfl) (ι := ι) (hι := hι)
    (hσ := unitaryInvolution_involutive hF) hν b
  set T := ctuaTwist le_rfl (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b
    with hTdef
  have hsub : ∀ m ∈ ({o, k, l} : Finset (Fin N)),
      ctuBlock (unitaryInvolution F 2 f) 1 ({o, k, l} : Finset (Fin N)) ≤
        ctuBlock (unitaryInvolution F 2 f) 1 ({m} : Finset (Fin N)) :=
    fun m hm => ctuBlock_anti (Finset.singleton_subset_iff.2 hm)
  have hfix : ∀ y ∈ ctuBlock (unitaryInvolution F 2 f) 1 ({o, k, l} : Finset (Fin N)),
      T y = y := by
    intro y hy
    have hTy : T y ∈ ctuBlock (unitaryInvolution F 2 f) 1 ({o, k, l} : Finset (Fin N)) :=
      (hT.mem_iff _ y).2 hy
    have hyk := hsub k (by simp) hy
    have hyl := hsub l (by simp) hy
    have hyo := hsub o (by simp) hy
    have h2 := h1 y (mem_ctuBlock_pair hyk hyl)
    rw [hagreeo y hyk hyo, hagreeo (T y) (hsub l (by simp) hTy) (hsub o (by simp) hTy)] at h2
    have h3 := (P o).injOn_ctuBlock hF (by omega) (Ne.symm hko) (x := ⟨y, hyo⟩)
      (y := ⟨T y, hsub o (by simp) hTy⟩) hyk (hsub k (by simp) hTy) h2
    exact (congrArg (fun w : ctuBlock (unitaryInvolution F 2 f) 1 ({o} : Finset (Fin N)) =>
      (w : SU (unitaryInvolution F 2 f) (2 * N + 1))) h3).symm
  have hcard : 1 ≤ ({o, k, l} : Finset (Fin N))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_three (a := o) (b := k) (c := l)
    omega
  have hT1 : T = 1 :=
    ctuaTwist_eq_one_of_fix_odd hν b (exists_add_unitaryInvolution_add_one_ctua hF) hcard hfix
  have hTx : T x = x := by rw [hT1, MulAut.one_apply]
  exact (h1 x hxkl).trans (congrArg (Q l).Φ (Subtype.ext hTx))

end Align

section Param

theorem exists_nsUniParam_odd_of_three_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) (n : ℕ) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin (n + 1), NsKindSp e t k .unitaryOdd) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (_ : Nat.card F = (2 ^ 1) ^ 2)
      (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
      ∀ k : Fin (n + 1), Nonempty (NsUniParam 1 le_rfl (unitaryInvolution F 2 1) ι hι e k) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hP := fun k => exists_nsGramParam_odd hset hK hn e htC ht k (hroot k)
  obtain ⟨K₀', _, h₀, _, C₀, hC, hC₀, hβ₀⟩ := hP 0
  have : Finite K₀' := h₀.finite
  have : CharP K₀' 2 := h₀.charP
  have : Finite h₀.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h₀
  obtain ⟨P₀, hP₀⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h₀.fixedField)
    (n := 2 * n + 1) (i₀ := ⟨n, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]; omega))
  obtain ⟨ι₀, -⟩ := hβ₀ (oddBeta P₀ hP₀)
  have hF : Nat.card K₀' = (2 ^ 1) ^ 2 := by rw [h₀.card]; norm_num
  set ι : K →+* K₀' := h₀.fixedField.subtype.comp (ι₀ : K →+* h₀.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K₀' 2 1 (ι c) = ι c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h₀.bar_apply]
    exact (h₀.mem_fixedField.1 (ι₀ c).2)
  refine ⟨K₀', inferInstance, inferInstance, inferInstance, hF, ι, hι, fun k => ?_⟩
  obtain ⟨K', _, h, _, C, hCk, hCk₀, hβ⟩ := hP k
  have : Finite K' := h.finite
  have : Finite h.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  obtain ⟨P, hPk⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h.fixedField)
    (n := 2 * n + 1) (i₀ := ⟨n, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]; omega))
  obtain ⟨ι', Φ, hrange, hker, hN1⟩ := hβ (oddBeta P hPk)
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq ι
    (h.fixedField.subtype.comp (ι' : K →+* h.fixedField)) (by rw [hF, h.card]; norm_num)
  exact ⟨nsUniParamOfGramOdd hCk₀ θ hθ P hPk Φ hrange hker hN1⟩

theorem exists_nsUniParam_even_of_three_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) (n : ℕ) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin (n + 1), NsKindSp e t k .unitaryEven) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (_ : Nat.card F = (2 ^ 1) ^ 2)
      (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
      ∀ k : Fin (n + 1),
        Nonempty (NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hP := fun k => exists_nsGramParam_even hset hK hn e htC ht k (hroot k)
  obtain ⟨K₀', _, h₀, _, -, -, -, ι₀, -⟩ := hP 0
  have : Finite K₀' := h₀.finite
  have : CharP K₀' 2 := h₀.charP
  have hF : Nat.card K₀' = (2 ^ 1) ^ 2 := by rw [h₀.card]; norm_num
  set ι : K →+* K₀' := h₀.fixedField.subtype.comp (ι₀ : K →+* h₀.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K₀' 2 1 (ι c) = ι c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h₀.bar_apply]
    exact (h₀.mem_fixedField.1 (ι₀ c).2)
  refine ⟨K₀', inferInstance, inferInstance, inferInstance, hF, ι, hι, fun k => ?_⟩
  obtain ⟨K', _, h, _, C₀, hC, hC₀, ι', Φ, hrange, hker, hN1⟩ := hP k
  have : Finite K' := h.finite
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq ι
    (h.fixedField.subtype.comp (ι' : K →+* h.fixedField)) (by rw [hF, h.card]; norm_num)
  exact ⟨nsUniParamOfGram hC₀ θ hθ Φ hrange hker hN1⟩

end Param

section Cover

theorem spTwoUnitaryCoverEightInput_unitaryOdd_holds :
    SpTwoUnitaryCoverEightInput .unitaryOdd 1 := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  obtain ⟨F, _, _, _, hF, ι, hι, hpar⟩ :=
    exists_nsUniParam_odd_of_three_le hset 3 hK le_rfl e ht hKt hroot
  obtain ⟨P, hagree⟩ := exists_nsUniParamAgree_odd (by rw [hK, pow_one]) hF le_rfl le_rfl
    fun k => (hpar k).some
  exact nsUnitaryCover_four_of_nsUniParamAgree hF P hagree (nsUniProductCommute_odd hF P hagree)

@[expose] def SpTwoUnitaryEvenEightAgreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k .unitaryEven) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (hF : Nat.card F = (2 ^ 1) ^ 2)
        (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)
        (P : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k),
        NsUniParamAgree P ∧ NsUniProductCommute hF P

theorem spTwoUnitaryCoverEightInput_unitaryEven_of_agree (h : SpTwoUnitaryEvenEightAgreeInput) :
    SpTwoUnitaryCoverEightInput .unitaryEven 0 := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  obtain ⟨F, _, _, _, hF, ι, hι, P, hagree, hcomm⟩ := h G L hset K hK e t ht hKt hroot
  exact nsUnitaryCover_four_of_nsUniParamAgree hF P hagree hcomm

end Cover

section Rows

theorem spTwoRowInput_unitaryOdd_holds : SpTwoRowInput .unitaryOdd :=
  spTwoRowInput_unitaryOdd_of_covers spTwoUnitaryCoverEightInput_unitaryOdd_holds
    spTwoUnitaryCoverInput_unitaryOdd_holds

theorem spTwoRowInput_unitaryEven_of_agree (h : SpTwoUnitaryEvenEightAgreeInput) :
    SpTwoRowInput .unitaryEven :=
  spTwoRowInput_unitaryEven_of_covers (spTwoUnitaryCoverEightInput_unitaryEven_of_agree h)
    spTwoUnitaryEvenSecondClassQuotEightInput_holds spTwoUnitaryCoverInput_unitaryEven_holds
    spTwoUnitaryEvenSecondClassQuotInput_holds

end Rows

end CFSG.SeitzReduction.SymplecticPilot
