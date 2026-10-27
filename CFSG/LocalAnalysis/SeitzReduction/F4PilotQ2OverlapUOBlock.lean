module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOUnitary

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp nsElt complSp complSpEquiv ctuEmbed ctuBlock
  ctuEmbed_mem_ctuBlock_iff ctuBlockEquiv ctuCoord ctuPlanes mem_ctuBlock ctuCoord_mem_ctuPlanes
  ctuBlockIdx ctuBlockIdx_ctuCoord mat_ctuBlockEquiv ctuBlockIdx_injective
  mem_range_ctuBlockIdx_iff)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)

section Corr

variable {F : Type} [Field F] {σ : F ≃+* F} {m ε : ℕ}

theorem ctuBlockIdx_mem_ctuPlanes_pair_iff (k : Fin (m + 1)) (l : Fin m) (a : Fin (2 * m + ε)) :
    ctuBlockIdx m ε k a ∈ ctuPlanes ε ({k, k.succAbove l} : Finset (Fin (m + 1))) ↔
      a ∈ ctuPlanes ε ({l} : Finset (Fin m)) := by
  obtain ⟨w, rfl⟩ := (ctuCoord m ε).surjective a
  rw [ctuBlockIdx_ctuCoord, ctuCoord_mem_ctuPlanes, ctuCoord_mem_ctuPlanes]
  rcases w with u | i
  · change CFSG.SeitzReduction.SymplecticPilot.planeOf (Sum.map k.succAbove k.succAbove u) ∈
        ({k, k.succAbove l} : Finset (Fin (m + 1))) ↔
      CFSG.SeitzReduction.SymplecticPilot.planeOf u ∈ ({l} : Finset (Fin m))
    rw [planeOf_sumMap, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton,
      Fin.succAbove_right_inj]
    constructor
    · rintro (h | h)
      · exact absurd h (Fin.succAbove_ne _ _)
      · exact h
    · exact Or.inr
  · exact iff_of_false (CFSG.SeitzReduction.SymplecticPilot.not_inPlanes_inr _ i)
      (CFSG.SeitzReduction.SymplecticPilot.not_inPlanes_inr _ i)

theorem mem_ctuBlock_pair_iff_ctuBlockEquiv (hε : ε ≤ 1) (k : Fin (m + 1)) (l : Fin m)
    (x : ctuBlock σ ε ({k} : Finset (Fin (m + 1)))) :
    (x : SU σ (2 * (m + 1) + ε)) ∈ ctuBlock σ ε ({k, k.succAbove l} : Finset (Fin (m + 1))) ↔
      ctuBlockEquiv σ hε k x ∈ ctuBlock σ ε ({l} : Finset (Fin m)) := by
  have hmat : ∀ a b, (((ctuBlockEquiv σ hε k x : SU σ (2 * m + ε)) : GL (Fin (2 * m + ε)) F) :
      Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) F) a b =
      (((x : SU σ (2 * (m + 1) + ε)) : GL (Fin (2 * (m + 1) + ε)) F) :
        Matrix (Fin (2 * (m + 1) + ε)) (Fin (2 * (m + 1) + ε)) F)
          (ctuBlockIdx m ε k a) (ctuBlockIdx m ε k b) := fun a b =>
    congrFun (congrFun (mat_ctuBlockEquiv hε k x) a) b
  constructor
  · intro hx
    rw [mem_ctuBlock]
    intro a b hab
    rw [hmat, mem_ctuBlock.1 hx _ _ (hab.imp (ctuBlockIdx_mem_ctuPlanes_pair_iff k l a).2
      (ctuBlockIdx_mem_ctuPlanes_pair_iff k l b).2), Matrix.one_apply, Matrix.one_apply]
    simp only [(ctuBlockIdx_injective (ε := ε) k).eq_iff]
  · intro hβ
    rw [mem_ctuBlock]
    intro a b hab
    by_cases ha : a ∈ ctuPlanes ε ({k} : Finset (Fin (m + 1)))
    · exact mem_ctuBlock.1 x.2 a b (Or.inl ha)
    by_cases hb : b ∈ ctuPlanes ε ({k} : Finset (Fin (m + 1)))
    · exact mem_ctuBlock.1 x.2 a b (Or.inr hb)
    obtain ⟨a', rfl⟩ := (mem_range_ctuBlockIdx_iff k a).2 ha
    obtain ⟨b', rfl⟩ := (mem_range_ctuBlockIdx_iff k b).2 hb
    rw [← hmat, mem_ctuBlock.1 hβ a' b' (hab.imp (ctuBlockIdx_mem_ctuPlanes_pair_iff k l a').1
      (ctuBlockIdx_mem_ctuPlanes_pair_iff k l b').1), Matrix.one_apply, Matrix.one_apply]
    simp only [(ctuBlockIdx_injective (ε := ε) k).eq_iff]

theorem ctuBlock_pair_le_singleton (k : Fin (m + 1)) (l : Fin m) :
    ctuBlock σ ε ({k, k.succAbove l} : Finset (Fin (m + 1))) ≤
      ctuBlock σ ε ({k} : Finset (Fin (m + 1))) :=
  CFSG.SeitzReduction.SymplecticPilot.ctuBlock_anti (by simp)

theorem map_ctuBlockEquiv_pair (hε : ε ≤ 1) (k : Fin (m + 1)) (l : Fin m) :
    ((ctuBlock σ ε ({k, k.succAbove l} : Finset (Fin (m + 1)))).subgroupOf
        (ctuBlock σ ε ({k} : Finset (Fin (m + 1))))).map
          (ctuBlockEquiv σ hε k).toMonoidHom = ctuBlock σ ε ({l} : Finset (Fin m)) := by
  ext y
  obtain ⟨x, rfl⟩ := (ctuBlockEquiv σ hε k).surjective y
  rw [← mem_ctuBlock_pair_iff_ctuBlockEquiv]
  constructor
  · rintro ⟨x', hx', hxx'⟩
    rw [← (ctuBlockEquiv σ hε k).injective hxx']
    exact hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

@[expose] noncomputable def ctuBlockPairEquiv (hε : ε ≤ 1) (k : Fin (m + 1)) (l : Fin m) :
    ctuBlock σ ε ({k, k.succAbove l} : Finset (Fin (m + 1))) ≃*
      ctuBlock σ ε ({l} : Finset (Fin m)) :=
  (Subgroup.subgroupOfEquivOfLe (ctuBlock_pair_le_singleton k l)).symm.trans
    (((ctuBlockEquiv σ hε k).subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_ctuBlockEquiv_pair hε k l)))

theorem coe_ctuBlockPairEquiv (hε : ε ≤ 1) (k : Fin (m + 1)) (l : Fin m)
    (x : ctuBlock σ ε ({k, k.succAbove l} : Finset (Fin (m + 1)))) :
    ((ctuBlockPairEquiv hε k l x : ctuBlock σ ε ({l} : Finset (Fin m))) : SU σ (2 * m + ε)) =
      ctuBlockEquiv σ hε k ⟨x, ctuBlock_pair_le_singleton k l x.2⟩ :=
  rfl

end Corr


section Piece

variable {F : Type} [Field F] {σ : F ≃+* F} {ε : ℕ}

theorem finset_three_zero_eq : ({3, 0} : Finset (Fin 4)) = {3, (3 : Fin 4).succAbove 0} := by
  decide

@[expose] noncomputable def twoUniPieceEquiv (hε : ε ≤ 1) :
    ctuBlock σ ε ({3, 0} : Finset (Fin 4)) ≃* SU σ (2 * 2 + ε) :=
  (MulEquiv.subgroupCongr (congrArg (ctuBlock σ ε) finset_three_zero_eq)).trans
    ((ctuBlockPairEquiv hε (3 : Fin (3 + 1)) (0 : Fin 3)).trans
      (ctuBlockEquiv σ hε (0 : Fin (2 + 1))))

variable {K : Type} [Field K] [CharP K 2] {ι : K →+* F}

theorem twoUniPieceEquiv_ctuEmbed (hε : ε ≤ 1) (hι : ∀ c, σ (ι c) = ι c) (y : StatedSp 2 K)
    (hy : ctuEmbed ε hε σ ι hι (spEmbed (3 : Fin 4).succAbove Fin.succAbove_right_injective
      (spEmbed (0 : Fin 3).succAbove Fin.succAbove_right_injective y)) ∈
        ctuBlock σ ε ({3, 0} : Finset (Fin 4))) :
    twoUniPieceEquiv hε ⟨_, hy⟩ = ctuEmbed ε hε σ ι hι y := by
  have hy' : ctuEmbed ε hε σ ι hι (spEmbed (3 : Fin 4).succAbove Fin.succAbove_right_injective
      (spEmbed (0 : Fin 3).succAbove Fin.succAbove_right_injective y)) ∈
        ctuBlock σ ε ({3, (3 : Fin 4).succAbove 0} : Finset (Fin (3 + 1))) := by
    rw [← finset_three_zero_eq]
    exact hy
  have h1 : ((ctuBlockPairEquiv hε (3 : Fin (3 + 1)) (0 : Fin 3) ⟨_, hy'⟩ :
      ctuBlock σ ε ({0} : Finset (Fin 3))) : SU σ (2 * 3 + ε)) =
        ctuEmbed ε hε σ ι hι (spEmbed (0 : Fin 3).succAbove Fin.succAbove_right_injective y) := by
    rw [coe_ctuBlockPairEquiv]
    exact CFSG.SeitzReduction.SymplecticPilot.ctuBlockEquiv_ctuEmbed hε hι (3 : Fin (3 + 1)) _
      _
  have hz0 : ctuEmbed ε hε σ ι hι (spEmbed (0 : Fin 3).succAbove Fin.succAbove_right_injective y)
      ∈ ctuBlock σ ε ({0} : Finset (Fin (2 + 1))) :=
    h1 ▸ (ctuBlockPairEquiv hε (3 : Fin (3 + 1)) (0 : Fin 3) ⟨_, hy'⟩).2
  have h2 : twoUniPieceEquiv hε ⟨_, hy⟩ = ctuBlockEquiv σ hε (0 : Fin (2 + 1)) ⟨_, hz0⟩ := by
    change ctuBlockEquiv σ hε (0 : Fin (2 + 1))
      (ctuBlockPairEquiv hε (3 : Fin (3 + 1)) (0 : Fin 3) ⟨_, hy'⟩) = _
    congr 1
    exact Subtype.ext h1
  rw [h2]
  exact CFSG.SeitzReduction.SymplecticPilot.ctuBlockEquiv_ctuEmbed hε hι (0 : Fin (2 + 1)) y hz0

theorem spEmbed_spEmbed_elt_positiveLong (c : K) :
    spEmbed (3 : Fin 4).succAbove Fin.succAbove_right_injective
      (spEmbed (0 : Fin 3).succAbove Fin.succAbove_right_injective
        (elt (.positiveLong (0 : Fin 2)) c)) = elt (.positiveLong (1 : Fin 4)) c := by
  rw [CFSG.SeitzReduction.SymplecticPilot.spEmbed_elt_positiveLong,
    CFSG.SeitzReduction.SymplecticPilot.spEmbed_elt_positiveLong]
  rfl

theorem spEmbed_spEmbed_elt_positiveSum (c : K) :
    spEmbed (3 : Fin 4).succAbove Fin.succAbove_right_injective
      (spEmbed (0 : Fin 3).succAbove Fin.succAbove_right_injective
        (elt (.positiveSum (0 : Fin 2) 1 (by decide)) c)) =
      elt (.positiveSum (1 : Fin 4) 2 (by decide)) c := by
  rw [spEmbed_elt_positiveSum_of_lt _ (by decide) (by decide),
    spEmbed_elt_positiveSum_of_lt _ (by decide) (by decide)]
  rfl

end Piece

section Cent

variable {G H : Type*} [Group G] [Group H]

theorem card_centralizer_inf_eq_of_mulEquiv (A : Subgroup G) (ψ : A ≃* H) {u : G} (hu : u ∈ A) :
    Nat.card (centralizer ({u} : Set G) ⊓ A : Subgroup G) =
      Nat.card (centralizer ({ψ ⟨u, hu⟩} : Set H)) := by
  have e1 : (centralizer ({⟨u, hu⟩} : Set A)).map A.subtype = centralizer ({u} : Set G) ⊓ A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)), y.2⟩
    · rintro ⟨hx, hxA⟩
      exact ⟨⟨x, hxA⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 hx)), rfl⟩
  have e2 : (centralizer ({⟨u, hu⟩} : Set A)).map ψ.toMonoidHom =
      centralizer ({ψ ⟨u, hu⟩} : Set H) := by
    ext y
    obtain ⟨x, rfl⟩ := ψ.surjective y
    constructor
    · rintro ⟨x', hx', hxx'⟩
      rw [← hxx']
      exact mem_centralizer_singleton_iff.2 (by
        change ψ x' * ψ ⟨u, hu⟩ = ψ ⟨u, hu⟩ * ψ x'
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hx'])
    · intro hx
      refine ⟨x, mem_centralizer_singleton_iff.2 (ψ.injective ?_), rfl⟩
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.1 hx
  rw [← e1, Subgroup.card_map_of_injective A.subtype_injective, ← e2,
    Subgroup.card_map_of_injective ψ.injective]

end Cent


section Orders

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_SU_unitaryInvolution_two (hF : Nat.card F = (2 ^ 1) ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.card (SU (unitaryInvolution F 2 1) k) : ℤ) = ((2 ^ 1 : ℕ) : ℤ) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  rw [Nat.card_congr (CFSG.LieType.Universal.Unitary.equivStatedSU hF k).toEquiv]
  exact CFSG.RankThree.PartOne.KFU.card_statedSU_eq
    (CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hF le_rfl) hk

theorem card_SU_four_two (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Nat.card (SU (unitaryInvolution F 2 1) (2 * 2 + 0)) = 25920 := by
  have h := card_SU_unitaryInvolution_two hF (k := 2 * 2 + 0) (by norm_num)
  have h' : (Nat.card (SU (unitaryInvolution F 2 1) (2 * 2 + 0)) : ℤ) = 25920 := by
    rw [h]
    decide
  exact_mod_cast h'

theorem card_SU_five_two (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Nat.card (SU (unitaryInvolution F 2 1) (2 * 2 + 1)) = 13685760 := by
  have h := card_SU_unitaryInvolution_two hF (k := 2 * 2 + 1) (by norm_num)
  have h' : (Nat.card (SU (unitaryInvolution F 2 1) (2 * 2 + 1)) : ℤ) = 13685760 := by
    rw [h]
    decide
  exact_mod_cast h'

end Orders

section Final

variable {K F : Type} [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2]

noncomputable abbrev twoSUTransvection {ε : ℕ} (hε : ε ≤ 1) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) : SU (unitaryInvolution F 2 1) (2 * 2 + ε) :=
  ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι (elt (.positiveLong (0 : Fin 2)) 1)

noncomputable abbrev twoSURankTwo {ε : ℕ} (hε : ε ≤ 1) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) : SU (unitaryInvolution F 2 1) (2 * 2 + ε) :=
  ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι (elt (.positiveSum (0 : Fin 2) 1 (by decide)) 1)

@[expose] def TwoSUCentValues (κ : Sp6Kind) {ε : ℕ} (hε : ε ≤ 1) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) : Prop :=
  Nat.card (centralizer ({twoSUTransvection hε ι hι} :
      Set (SU (unitaryInvolution F 2 1) (2 * 2 + ε)))) = twoOverlapInvOrderL κ ∧
    Nat.card (centralizer ({twoSURankTwo hε ι hι} :
      Set (SU (unitaryInvolution F 2 1) (2 * 2 + ε)))) = twoOverlapInvOrderS κ

theorem twoUniBlockValues_of_suCentValues {κ : Sp6Kind} {ε : ℕ} (hε : ε ≤ 1) {ι : K →+* F}
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)
    (h0 : Nat.card (SU (unitaryInvolution F 2 1) (2 * 2 + ε)) = twoDiagPieceOrder κ)
    (hC : TwoSUCentValues κ hε ι hι) : TwoUniBlockValues κ hε ι hι := by
  obtain ⟨hL, hS⟩ := hC
  have huL : twoUniTransvection hε ι hι ∈
      ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4)) :=
    (ctuEmbed_mem_ctuBlock_iff (hε := hε) (hι := hι)).2
      (CFSG.SeitzReduction.SymplecticPilot.elt_positiveLong_mem_spBlock (by decide) 1)
  have huS : twoUniRankTwo hε ι hι ∈
      ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4)) :=
    (ctuEmbed_mem_ctuBlock_iff (hε := hε) (hι := hι)).2
      (CFSG.SeitzReduction.SymplecticPilot.elt_positiveSum_mem_spBlock (by decide) (by decide)
        (by decide) 1)
  have hyL : ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι
      (spEmbed (3 : Fin 4).succAbove Fin.succAbove_right_injective
        (spEmbed (0 : Fin 3).succAbove Fin.succAbove_right_injective
          (elt (.positiveLong (0 : Fin 2)) (1 : K)))) ∈
        ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4)) := by
    rw [spEmbed_spEmbed_elt_positiveLong]
    exact huL
  have hyS : ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι
      (spEmbed (3 : Fin 4).succAbove Fin.succAbove_right_injective
        (spEmbed (0 : Fin 3).succAbove Fin.succAbove_right_injective
          (elt (.positiveSum (0 : Fin 2) 1 (by decide)) (1 : K)))) ∈
        ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4)) := by
    rw [spEmbed_spEmbed_elt_positiveSum]
    exact huS
  have eL : (⟨twoUniTransvection hε ι hι, huL⟩ :
      ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4))) = ⟨_, hyL⟩ :=
    Subtype.ext (congrArg (ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι)
      (spEmbed_spEmbed_elt_positiveLong 1).symm)
  have eS : (⟨twoUniRankTwo hε ι hι, huS⟩ :
      ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4))) = ⟨_, hyS⟩ :=
    Subtype.ext (congrArg (ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι)
      (spEmbed_spEmbed_elt_positiveSum 1).symm)
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr (twoUniPieceEquiv hε).toEquiv, h0]
  · rw [card_centralizer_inf_eq_of_mulEquiv _ (twoUniPieceEquiv hε) huL, eL,
      twoUniPieceEquiv_ctuEmbed hε hι _ hyL]
    exact hL
  · rw [card_centralizer_inf_eq_of_mulEquiv _ (twoUniPieceEquiv hε) huS, eS,
      twoUniPieceEquiv_ctuEmbed hε hι _ hyS]
    exact hS

theorem twoUniBlockValues_unitary6 (hF : Nat.card F = (2 ^ 1) ^ 2) {ι : K →+* F}
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)
    (hC : TwoSUCentValues .unitary6 (Nat.zero_le 1) ι hι) :
    TwoUniBlockValues .unitary6 (Nat.zero_le 1) ι hι :=
  twoUniBlockValues_of_suCentValues (Nat.zero_le 1) hι (card_SU_four_two hF) hC

theorem twoUniBlockValues_unitary7 (hF : Nat.card F = (2 ^ 1) ^ 2) {ι : K →+* F}
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)
    (hC : TwoSUCentValues .unitary7 le_rfl ι hι) :
    TwoUniBlockValues .unitary7 le_rfl ι hι :=
  twoUniBlockValues_of_suCentValues le_rfl hι (card_SU_five_two hF) hC

end Final

end CFSG.SeitzReduction.F4Pilot
