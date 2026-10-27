module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParam
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E ne_succ')
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (mem_closure_sl2)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Blocks

variable {F : Type} [Field F] {n : ℕ}

theorem simpleRootSL2_le_spBlock_compl {j k : Fin n} (hkj : k ≠ j)
    (hk1 : j.val + 1 < n → k.val ≠ j.val + 1) :
    simpleRootSL2 F j ≤ spBlock F ({k}ᶜ : Finset (Fin n)) := by
  by_cases h : j.val + 1 < n
  · rw [simpleRootSL2_of_lt h]
    rintro _ ⟨A, rfl⟩
    intro r s hrs
    refine isSupp_shortBlock (ne_succ' h) A r s fun hrs' => hrs ⟨?_, ?_⟩
    · rcases hrs'.1 with hr | hr <;> rw [mem_coords] at hr <;>
        rcases hr with rfl | rfl <;> simp [mem_planeCoords, Ne.symm hkj]
      all_goals exact fun e => hk1 h (by rw [← e])
    · rcases hrs'.2 with hr | hr <;> rw [mem_coords] at hr <;>
        rcases hr with rfl | rfl <;> simp [mem_planeCoords, Ne.symm hkj]
      all_goals exact fun e => hk1 h (by rw [← e])
  · rw [simpleRootSL2_of_not_lt h, ← spBlock_singleton]
    exact spBlock_mono (by simpa using hkj)

theorem elt_difference_mem_siegelBlock {B : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hi : i ∈ B) (hj : j ∈ B) (c : F) : elt (.difference i j hij) c ∈ siegelBlock F B := by
  rw [siegelBlock, Subgroup.mem_map]
  refine ⟨Matrix.SpecialLinearGroup.transvection hij c, ?_, ?_⟩
  · intro a b hab
    change (1 + Matrix.single i j c : Matrix (Fin n) (Fin n) F) a b = _
    rw [Matrix.add_apply, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rcases hab with hab | hab <;> contradiction
    · rw [add_zero]
  · rw [CFSG.LieType.Universal.Symplectic.SpExtras.elt_difference_eq_leviHom,
      ← TauCeti.toGL_transvection_eq_transvectionUnit]
    rfl

theorem filter_pair_eq {j : Fin n} (h : j.val + 1 < n) :
    (Finset.univ.filter fun i : Fin n => j.val ≤ i.val ∧ i.val ≤ j.val + 1) =
      {j, ⟨j.val + 1, h⟩} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Fin.ext_iff]
  omega

theorem filter_string_eq {j : Fin n} :
    (Finset.univ.filter fun i : Fin n => j.val ≤ i.val ∧ i.val < j.val + 1) = {j} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem filter_tail_eq {j : Fin n} (h : ¬j.val + 1 < n) :
    (Finset.univ.filter fun i : Fin n => j.val ≤ i.val) = {j} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem simpleRootSL2_le_siegelBlock {j : Fin n} (h : j.val + 1 < n) :
    simpleRootSL2 F j ≤
      siegelBlock F (Finset.univ.filter fun i : Fin n => j.val ≤ i.val ∧ i.val ≤ j.val + 1) := by
  rw [simpleRootSL2_of_lt h, filter_pair_eq h]
  rintro _ ⟨A, rfl⟩
  have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
      (siegelBlock F {j, ⟨j.val + 1, h⟩}).comap (shortBlock F (ne_succ' h)) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change shortBlock F (ne_succ' h) (sl2Upper c) ∈ siegelBlock F {j, ⟨j.val + 1, h⟩}
      rw [shortBlock_sl2Upper]
      exact elt_difference_mem_siegelBlock _ (by simp) (by simp) c
    · change shortBlock F (ne_succ' h) (sl2Lower c) ∈ siegelBlock F {j, ⟨j.val + 1, h⟩}
      rw [shortBlock_sl2Lower]
      exact elt_difference_mem_siegelBlock _ (by simp) (by simp) c
  exact hle (mem_closure_sl2 A)

theorem siegelBlock_pair_eq_simpleRootSL2 [Finite F] {j : Fin n} (h : j.val + 1 < n) :
    siegelBlock F (Finset.univ.filter fun i : Fin n => j.val ≤ i.val ∧ i.val ≤ j.val + 1) =
      simpleRootSL2 F j := by
  have : Finite (StatedSp n F) := inferInstance
  refine (Subgroup.eq_of_le_of_card_ge (simpleRootSL2_le_siegelBlock h) ?_).symm
  have hcard2 : (Finset.univ.filter fun i : Fin n =>
      j.val ≤ i.val ∧ i.val ≤ j.val + 1).card = 2 := by
    rw [filter_pair_eq h, Finset.card_pair]
    intro e
    have := congrArg Fin.val e
    simp at this
  rw [siegelBlock, card_map_of_injective (leviEmbedSL_injective (K := F) (n := n)),
    ← Nat.card_congr (LinearPilot.blockSpecialLinearEquivOfCardTwo (K := F) hcard2).toEquiv,
    simpleRootSL2, MonoidHom.range_eq_map,
    card_map_of_injective (simpleRootHom_injective (K := F) j), Subgroup.card_top]

end Blocks

section Simple

variable {F : Type} [Field F] {n : ℕ}

theorem isQuasisimple_simpleRootSL2' [Finite F] (hF : 4 ≤ Nat.card F) (j : Fin n) :
    CFSG.IsQuasisimple (simpleRootSL2 F j) := by
  have e : simpleRootSL2 F j ≃* StatedSp 1 F :=
    (MonoidHom.ofInjective (simpleRootHom_injective (K := F) j)).symm.trans
      (longBlockEquivOne F)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 1 F le_rfl (Or.inl (Or.inr hF)))

theorem isQuasisimple_simpleRootSL2 [Finite F] (hF : 4 ≤ Nat.card F) (j : Fin n) :
    CFSG.Open.IsQuasisimple (simpleRootSL2 F j) := by
  have hq := isQuasisimple_simpleRootSL2' hF j
  have := hq.1
  exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩

theorem isQuasisimple_simpleRootSL2_subgroupOf [Finite F] (hF : 4 ≤ Nat.card F) {j : Fin n}
    {S : Subgroup (StatedSp n F)} (hS : simpleRootSL2 F j ≤ S) :
    CFSG.Open.IsQuasisimple ((simpleRootSL2 F j).subgroupOf S) := by
  have hq : CFSG.IsQuasisimple ((simpleRootSL2 F j).subgroupOf S) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hS).symm
      (isQuasisimple_simpleRootSL2' hF j)
  have := hq.1
  exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩

theorem iSup_simpleRootSL2_eq_top (hn : 1 ≤ n) : ⨆ j : Fin n, simpleRootSL2 F j = ⊤ := by
  refine eq_top_of_adjacent_of_long_statedSp _ ⟨n - 1, by omega⟩ (fun i j hij c hadj => ?_)
    (fun c => ?_) (fun c => ?_)
  · rcases hadj with hadj | hadj
    · have h : i.val + 1 < n := hadj ▸ j.isLt
      obtain rfl : j = ⟨i.val + 1, h⟩ := Fin.ext hadj.symm
      refine mem_iSup_of_mem i ?_
      rw [simpleRootSL2_of_lt h, ← shortBlock_sl2Upper]
      exact ⟨_, rfl⟩
    · have h : j.val + 1 < n := hadj ▸ i.isLt
      obtain rfl : i = ⟨j.val + 1, h⟩ := Fin.ext hadj.symm
      refine mem_iSup_of_mem j ?_
      rw [simpleRootSL2_of_lt h, ← shortBlock_sl2Lower (ne_succ' h)]
      exact ⟨_, rfl⟩
  · refine mem_iSup_of_mem ⟨n - 1, by omega⟩ ?_
    rw [simpleRootSL2_of_not_lt (by simp; omega), longRootSp2, ← longBlock_sl2Upper]
    exact ⟨_, rfl⟩
  · refine mem_iSup_of_mem ⟨n - 1, by omega⟩ ?_
    rw [simpleRootSL2_of_not_lt (by simp; omega), longRootSp2, ← longBlock_sl2Lower]
    exact ⟨_, rfl⟩

end Simple

section Pieces

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {k : Fin n}

theorem notMem_filter_pair {j k : Fin n} (hkj : k ≠ j) (hk1 : j.val + 1 < n → k.val ≠ j.val + 1)
    (h : j.val + 1 < n) :
    k ∉ Finset.univ.filter fun i : Fin n => j.val ≤ i.val ∧ i.val ≤ j.val + 1 := by
  rw [filter_pair_eq h]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hkj, fun e => hk1 h (by rw [e])⟩

theorem FieldNeighbourParam.pieceCore_singleton_eq_map (P : FieldNeighbourParam e t ι σ k)
    (hK : 4 ≤ Nat.card K) {j : Fin n} (hkj : k ≠ j) (hk1 : j.val + 1 < n → k.val ≠ j.val + 1) :
    pieceCore e ({j} : Finset (Fin n)) =
      ((simpleRootSL2 F j).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).map P.Φ := by
  by_cases h : j.val + 1 < n
  · rw [← filter_string_eq (j := j), P.pieceCore_string_eq_map hK (a := j.val) (b := j.val + 1)
      (by omega) h (notMem_filter_pair hkj hk1 h), siegelBlock_pair_eq_simpleRootSL2 h]
  · rw [← filter_tail_eq h, pieceCore_tail_eq, filter_tail_eq h,
      P.planeCore_eq_map hK (by simpa using hkj), spBlock_singleton, simpleRootSL2_of_not_lt h]

omit [Finite F] in
theorem SwapNeighbourParam.pieceCore_singleton_eq_map [Finite K] (P : SwapNeighbourParam e t k)
    (hK : 4 ≤ Nat.card K) {j : Fin n} (hkj : k ≠ j) (hk1 : j.val + 1 < n → k.val ≠ j.val + 1) :
    pieceCore e ({j} : Finset (Fin n)) =
      (((simpleRootSL2 K j).subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))).prod
        ((simpleRootSL2 K j).subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n))))).map P.Ψ := by
  by_cases h : j.val + 1 < n
  · rw [← filter_string_eq (j := j), P.pieceCore_string_eq_map hK (a := j.val) (b := j.val + 1)
      (by omega) h (notMem_filter_pair hkj hk1 h), siegelBlock_pair_eq_simpleRootSL2 h]
  · rw [← filter_tail_eq h, pieceCore_tail_eq, filter_tail_eq h,
      P.planeCore_eq_map hK (by simpa using hkj), spBlock_singleton, simpleRootSL2_of_not_lt h]

end Pieces

section Global

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

theorem mem_normalizer_iSup_of_forall {M : Type*} [Group M] {ι' : Sort*} {H : ι' → Subgroup M}
    {g : M} (hg : ∀ i, g ∈ normalizer (H i : Set M)) :
    g ∈ normalizer ((⨆ i, H i : Subgroup M) : Set M) := by
  have hmap : ∀ i, (H i).map (MulAut.conj g).toMonoidHom = H i := fun i => by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 (hg i) x).1 hx
    · intro hy
      refine ⟨g⁻¹ * y * g, (mem_normalizer_iff.1 (hg i) _).2 ?_, ?_⟩
      · rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hsup : (⨆ i, H i).map (MulAut.conj g).toMonoidHom = ⨆ i, H i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hmap
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hsup]
    exact ⟨x, hx, rfl⟩
  · rw [← hsup] at hx
    obtain ⟨x', hx', hxx'⟩ := hx
    have : x' = x := by
      change g * x' * g⁻¹ = g * x * g⁻¹ at hxx'
      simpa using hxx'
    exact this ▸ hx'

@[expose] noncomputable def spGlobal (e : L ≃* StatedSp n K) : Subgroup G :=
  ⨆ j : Fin n, pieceCore e ({j} : Finset (Fin n))

theorem spGlobal_def (e : L ≃* StatedSp n K) :
    spGlobal e = ⨆ j : Fin n, pieceCore e ({j} : Finset (Fin n)) :=
  rfl

theorem mem_normalizer_spGlobal (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) : t ∈ normalizer (spGlobal e : Set G) :=
  mem_normalizer_iSup_of_forall fun _ => le_normalizer_pieceCore e htC _

theorem le_spGlobal (hK : 4 ≤ Nat.card K) (hn : 1 ≤ n) (e : L ≃* StatedSp n K) :
    L ≤ spGlobal e := by
  refine (UnitaryPilot.modelToG_top e).symm.le.trans ?_
  rw [← iSup_simpleRootSL2_eq_top hn, UnitaryPilot.modelToG_iSup]
  exact iSup_mono fun j => modelToG_simpleRootSL2_le_pieceCore e hK (Finset.mem_singleton_self j)

end Global

end CFSG.SeitzReduction.SymplecticPilot
