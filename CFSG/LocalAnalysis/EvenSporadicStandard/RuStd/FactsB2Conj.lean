module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs
public import CFSG.Sporadic.Schreier.RuConj

public section

namespace CFSG.EvenSporadicStandard.RuStd

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HypOne CFSG.Sporadic.RuSchreier

variable {n : ℕ}

namespace B2

theorem conj_mem_of_mem_closure {G : Type*} [Group G] {S Y : Set G}
    (hS : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y ∧ s⁻¹ * y * s ∈ Y) {c : G}
    (hc : c ∈ Subgroup.closure S) : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := by
  let H : Subgroup G :=
    { carrier := {c | ∀ y ∈ Y, c * y * c⁻¹ ∈ Y ∧ c⁻¹ * y * c ∈ Y}
      mul_mem' := by
        intro a b ha hb y hy
        obtain ⟨hb1, -⟩ := hb y hy
        obtain ⟨ha1, -⟩ := ha _ hb1
        obtain ⟨-, ha2⟩ := ha y hy
        obtain ⟨-, hb2⟩ := hb _ ha2
        refine ⟨?_, ?_⟩
        · simpa [mul_assoc] using ha1
        · simpa [mul_assoc] using hb2
      one_mem' := by
        intro y hy
        simp only [one_mul, inv_one, mul_one]
        exact ⟨hy, hy⟩
      inv_mem' := by
        intro a ha y hy
        obtain ⟨h1, h2⟩ := ha y hy
        exact ⟨by simpa using h2, by simpa using h1⟩ }
  have hle : Subgroup.closure S ≤ H := (Subgroup.closure_le H).2 fun s hs y hy => hS s hs y hy
  exact fun y hy => (hle hc y hy).1

theorem tblEq_symm {S T : Table} (h : tblEq n S T = true) : tblEq n T S = true :=
  tblEq_iff.2 fun i hi => ((tblEq_iff.1 h) i hi).symm

theorem classCheckOf_spec (K : Subgroup (Equiv.Perm (Fin n))) {gens gensInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ K)
    (hK : K ≤ Subgroup.closure (gg '' {l | l < gens.size})) {r : Table}
    {rg : Equiv.Perm (Fin n)} (hr : Rep n r rg) {q : Array Table × Array ℕ × Array ℕ} {N : ℕ}
    (h : classCheckOf n gens gensInv r q N = true) :
    (conjSet K rg).ncard = N ∧
      ∀ T ∈ q.1.toList, ∀ g : Equiv.Perm (Fin n), Rep n T g → g ∈ conjSet K rg := by
  classical
  simp only [classCheckOf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨htree, hclosed⟩, hdist⟩, hsize⟩ := h
  have hspec := conjTreeOK_spec K hg hr htree
  have hmem : ∀ T ∈ q.1.toList, ∀ g : Equiv.Perm (Fin n), Rep n T g → g ∈ conjSet K rg := by
    intro T hT g hTg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    obtain ⟨c, hc, hrepc⟩ := hspec k hk
    rw [getElem!_pos q.1 k hk] at hrepc
    rw [Array.getElem_toList] at hTg
    exact ⟨c, hc, rep_unique hrepc hTg⟩
  refine ⟨?_, hmem⟩
  have hrep : ∀ k < q.1.size, Rep n q.1[k]! (tablePerm n q.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrepc⟩ := hspec k hk
    rw [tablePerm_eq hrepc]
    exact hrepc
  have hnodup : (q.1.toList.map (tablePerm n)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm hrep) hdist
  set Y : Set (Equiv.Perm (Fin n)) := {y | ∃ T ∈ q.1.toList, Rep n T y} with hY
  have hY1 : ∀ l < gens.size, ∀ y ∈ Y,
      gg l * y * (gg l)⁻¹ ∈ Y ∧ (gg l)⁻¹ * y * gg l ∈ Y := by
    rintro l hl y ⟨T, hT, hTy⟩
    obtain ⟨hgl, hgil, -⟩ := hg l hl
    have hTa : T ∈ q.1 := Array.mem_toList_iff.1 hT
    simp only [conjClosedH, Array.all_eq_true' ] at hclosed
    have h1 := List.all_eq_true.1 (hclosed T hTa) l (List.mem_range.2 hl)
    rw [Bool.and_eq_true] at h1
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨T1, hT1, hT1e⟩ := Array.any_eq_true'.1 (memT_of_memTH h1a)
    obtain ⟨T2, hT2, hT2e⟩ := Array.any_eq_true'.1 (memT_of_memTH h1b)
    refine ⟨⟨T1, Array.mem_toList_iff.2 hT1, ?_⟩, ⟨T2, Array.mem_toList_iff.2 hT2, ?_⟩⟩
    · exact rep_of_tblEq (rep_conjT hgl hgil hTy) (tblEq_symm hT1e)
    · have hgl' : Rep n gens[l]! ((gg l)⁻¹)⁻¹ := by rwa [inv_inv]
      have := rep_conjT hgil hgl' hTy
      rw [inv_inv] at this
      exact rep_of_tblEq this (tblEq_symm hT2e)
  have hYS : ∀ s ∈ gg '' {l | l < gens.size}, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y ∧ s⁻¹ * y * s ∈ Y := by
    rintro _ ⟨l, hl, rfl⟩ y hy
    exact hY1 l hl y hy
  have hrgY : rg ∈ Y := by
    simp only [conjTreeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
    obtain ⟨⟨hpos, h0⟩, -⟩ := htree
    refine ⟨q.1[0]!, ?_, rep_of_tblEq hr h0⟩
    rw [getElem!_pos q.1 0 hpos]
    exact Array.mem_toList_iff.2 (Array.getElem_mem hpos)
  have hYeq : conjSet K rg = Y := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact conj_mem_of_mem_closure hYS (hK hc) rg hrgY
    · rintro ⟨T, hT, hTy⟩
      exact hmem T hT y hTy
  have hYE : Y = ↑(q.1.toList.map (tablePerm n)).toFinset := by
    ext y
    simp only [hY, Set.mem_ofPred_eq, List.coe_toFinset]
    constructor
    · rintro ⟨T, hT, hTy⟩
      exact List.mem_map.2 ⟨T, hT, tablePerm_eq hTy⟩
    · intro hy
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm (e := fun k => tablePerm n q.1[k]!) hrep hy
      refine ⟨q.1[k]!, ?_, hrep k hk⟩
      rw [getElem!_pos q.1 k hk]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hk)
  rw [hYeq, hYE, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup, List.length_map,
    Array.length_toList, hsize]

end B2

end CFSG.EvenSporadicStandard.RuStd
