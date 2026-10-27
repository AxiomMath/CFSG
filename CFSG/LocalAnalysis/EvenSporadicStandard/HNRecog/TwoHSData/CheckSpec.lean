module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.TwoHS

theorem rep_elemW_of_gensOK (h : gensOK = true) {w : List ℕ} (hw : wordOK w = true) :
    Rep 1408 (tabW w) (elemW w) := by
  have hperm : ∀ g ∈ h1408Gens, permOK 1408 g = true := by
    rw [gensOK, List.all_eq_true] at h
    intro g hg
    exact (Bool.and_eq_true_iff.mp (h g hg)).1
  have hw' : ∀ l ∈ w, 1 ≤ l ∧ l ≤ h1408Gens.length := by
    rw [wordOK, List.all_eq_true] at hw
    intro l hl
    have := hw l hl
    rw [h1408Gens_length]
    exact of_decide_eq_true this
  have h' := rep_wordTbl'' (n := 1408) (by norm_num) hperm w hw'
  rw [h1408Gens_map_tp] at h'
  exact h'

structure IsEnumSet (n : ℕ) (E : Array Table) (S : Set (Equiv.Perm (Fin n))) : Prop where
  rep : ∀ k < E.size, ∃ g ∈ S, Rep n E[k]! g
  cov : ∀ g ∈ S, ∃ k < E.size, Rep n E[k]! g

theorem IsEnumSet.memT_iff {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) {x : Table} {g : Equiv.Perm (Fin n)} (hx : Rep n x g) :
    memT n E x = true ↔ g ∈ S := by
  constructor
  · intro hm
    rw [memT, Array.any_eq_true'] at hm
    obtain ⟨T, hT, hTx⟩ := hm
    obtain ⟨k, hk, hkT⟩ := Array.getElem_of_mem hT
    have hkT' : E[k]! = T := by rw [getElem!_pos E k hk, hkT]
    have hTx' : tblEq n x E[k]! = true := by rw [hkT']; exact hTx
    obtain ⟨g', hg'S, hrep⟩ := h.rep k hk
    rw [rep_unique hx (rep_of_tblEq hrep hTx')]
    exact hg'S
  · intro hg
    obtain ⟨k, hk, hrep⟩ := h.cov g hg
    rw [memT, Array.any_eq_true']
    exact ⟨E[k]!, getElem!_mem_array hk, (tblEq_iff_eq hx hrep).2 rfl⟩

theorem IsEnumSet.forall_iff {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → (b x = true ↔ Q g)) :
    E.all b = true ↔ ∀ g ∈ S, Q g := by
  constructor
  · intro hm g hg
    rw [Array.all_eq_true'] at hm
    obtain ⟨k, hk, hrep⟩ := h.cov g hg
    exact (hb (E[k]!) g hrep).1 (hm (E[k]!) (getElem!_mem_array hk))
  · intro hQ
    rw [Array.all_eq_true']
    intro x hx
    obtain ⟨k, hk, hkT⟩ := Array.getElem_of_mem hx
    obtain ⟨g, hgS, hrep⟩ := h.rep k hk
    have hbk : b (E[k]!) = true := (hb (E[k]!) g hrep).2 (hQ g hgS)
    have hxE : x = E[k]! := hkT.symm.trans (getElem!_pos E k hk).symm
    rw [hxE]
    exact hbk

theorem IsEnumSet.exists_iff {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → (b x = true ↔ Q g)) :
    E.any b = true ↔ ∃ g ∈ S, Q g := by
  constructor
  · intro hm
    rw [Array.any_eq_true'] at hm
    obtain ⟨x, hx, hbx⟩ := hm
    obtain ⟨k, hk, hkT⟩ := Array.getElem_of_mem hx
    obtain ⟨g, hgS, hrep⟩ := h.rep k hk
    have hxE : x = E[k]! := hkT.symm.trans (getElem!_pos E k hk).symm
    have hrep' : Rep n x g := by rw [hxE]; exact hrep
    exact ⟨g, hgS, (hb x g hrep').1 hbx⟩
  · rintro ⟨g, hgS, hQg⟩
    obtain ⟨k, hk, hrep⟩ := h.cov g hgS
    rw [Array.any_eq_true']
    exact ⟨E[k]!, getElem!_mem_array hk, (hb (E[k]!) g hrep).2 hQg⟩

private theorem memT_of_match_some {n : ℕ} {L : Array Table} {y : Table} {o : Option ℕ}
    (h : (match o with
          | some i => (L[i]?.map (tblEq n y)).getD false
          | none => false) = true) : memT n L y = true := by
  cases o with
  | none => exact absurd h Bool.false_ne_true
  | some i =>
    have h' : (L[i]?.map (tblEq n y)).getD false = true := h
    cases hL : L[i]? with
    | none =>
      rw [hL] at h'
      simp only [Option.map_none, Option.getD_none] at h'
      exact absurd h' Bool.false_ne_true
    | some e =>
      rw [hL] at h'
      simp only [Option.map_some, Option.getD_some] at h'
      exact Array.any_eq_true'.2 ⟨e, Array.mem_of_getElem? hL, h'⟩

private theorem closedOKH_closedOK {n : ℕ} {gens L : Array Table}
    (h : closedOKH n gens L = true) : closedOK n gens L = true := by
  simp only [closedOKH, Array.all_eq_true] at h
  rw [closedOK]
  simp only [Array.all_eq_true]
  intro i hi j hj
  exact memT_of_match_some (h i hi j hj)

private theorem enumOKH_enumOK {n cap m : ℕ} {gs : List Table}
    (h : enumOKH n cap m gs = true) :
    enumOK n cap m gs = true ∧ ∀ g ∈ gs, permOK n g = true := by
  simp only [enumOKH, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hgi, htree⟩, hclosed⟩, hdist⟩, hsize⟩ := h
  have hperm : ∀ g ∈ gs, permOK n g = true := by
    intro g hg
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.1 hgi g hg)).1
  have hinv : ∀ g ∈ gs, invOK n g (invT n g) = true := by
    intro g hg
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.1 hgi g hg)).2
  refine ⟨?_, hperm⟩
  simp only [enumOK, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, htree⟩, ?_⟩, hdist⟩, hsize⟩
  · rw [List.all_eq_true]
    exact hinv
  · exact closedOKH_closedOK hclosed

theorem enumW_spec {cap m : ℕ} {ws : List (List ℕ)} (h : enumW cap m ws = true) :
    Nat.card ↥(closure (elemW '' {w | w ∈ ws})) = m ∧
      IsEnumSet 1408 (subgroupList cap ws) (closure (elemW '' {w | w ∈ ws}) : Set _) := by
  simp only [enumW, Bool.and_eq_true] at h
  obtain ⟨⟨hgens, hws⟩, hEH⟩ := h
  obtain ⟨henum, hperm⟩ := enumOKH_enumOK hEH
  obtain ⟨hcard, hrep, hcov, -⟩ := enumOK_spec (n := 1408) (by norm_num) hperm henum
  have htp : ∀ w ∈ ws, tp 1408 (tabW w) = elemW w := by
    intro w hw
    have hwok : wordOK w = true := List.all_eq_true.1 hws w hw
    have hrepw := rep_elemW_of_gensOK hgens hwok
    have hpermtab : permOK 1408 (tabW w) = true :=
      hperm (tabW w) (by simp only [tabsW, List.mem_map]; exact ⟨w, hw, rfl⟩)
    exact rep_unique (rep_tp hpermtab) hrepw
  have hgen : genOf 1408 (tabsW ws) = closure (elemW '' {w | w ∈ ws}) := by
    apply le_antisymm
    · rw [genOf, closure_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_setOf_eq, Array.mem_toArray, tabsW] at hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      rw [htp w hw]
      exact subset_closure ⟨w, hw, rfl⟩
    · rw [closure_le]
      rintro _ ⟨w, hw, rfl⟩
      refine subset_closure ⟨tabW w, ?_, htp w hw⟩
      simp only [Set.mem_setOf_eq, Array.mem_toArray, tabsW]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← hgen]
    exact hcard
  · refine ⟨?_, ?_⟩
    · intro k hk
      obtain ⟨hrepk, hmemk⟩ := hrep k hk
      exact ⟨tablePerm 1408 (subgroupList cap ws)[k]!, by rw [← hgen]; exact hmemk, hrepk⟩
    · intro g hg
      obtain ⟨k, hk, hrepk⟩ := hcov g (by rwa [hgen])
      exact ⟨k, hk, hrepk⟩

theorem closure_elemW_le (ws : List (List ℕ)) : closure (elemW '' {w | w ∈ ws}) ≤ P1408 := by
  rw [closure_le]
  rintro _ ⟨w, -, rfl⟩
  exact elemW_mem w

end CFSG.EvenSporadicStandard.HNRecog
