module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.TwoHS

private theorem mem_of_nodup_of_ncard_le {n : ℕ} {S : Set (Equiv.Perm (Fin n))}
    {L : List (Equiv.Perm (Fin n))} (hL : L.Nodup) (hS : ∀ x ∈ L, x ∈ S)
    (hlen : S.ncard ≤ L.length) : ∀ y ∈ S, y ∈ L := by
  classical
  have hsub : (L.toFinset : Set (Equiv.Perm (Fin n))) ⊆ S := fun x hx =>
    hS x (List.mem_toFinset.mp hx)
  have hcard : S.ncard ≤ (L.toFinset : Set (Equiv.Perm (Fin n))).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]
    exact hlen
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  intro y hy
  have : y ∈ (L.toFinset : Set (Equiv.Perm (Fin n))) := by rw [heq]; exact hy
  exact List.mem_toFinset.mp this

theorem wclassOK_spec (hP : Nat.card P1408 = 177408000) {cap : ℕ} {r : WClass}
    (h : wclassOK cap r = true) :
    (CFSG.Sporadic.SmallOddCore.conjClass P1408 (elemW r.rep)).ncard = r.classSize ∧
      IsEnumSet 1408 (classList cap r.rep) (CFSG.Sporadic.SmallOddCore.conjClass P1408 (elemW r.rep)) ∧
      Nat.card ↥(P1408 ⊓ centralizer ({elemW r.rep} : Set (Equiv.Perm (Fin 1408)))) =
        r.centOrder ∧
      closure (elemW '' {w | w ∈ r.centGens}) =
        P1408 ⊓ centralizer ({elemW r.rep} : Set (Equiv.Perm (Fin 1408))) ∧
      IsEnumSet 1408 (subgroupList cap r.centGens)
        ((P1408 ⊓ centralizer ({elemW r.rep} : Set (Equiv.Perm (Fin 1408))) :
          Subgroup (Equiv.Perm (Fin 1408))) : Set _) := by
  simp only [wclassOK, Bool.and_eq_true] at h
  set pg : Array Table := h1408Gens.toArray
  set pgInv : Array Table := pg.map (invT 1408)
  set o : Array Table × Array Nat × Array Nat :=
    conjClosureH 1408 pg pgInv (tabW r.rep) cap
  set cg : Array Table := (tabsW r.centGens).toArray
  set C : Array Table × Array Nat × Array Nat := mulClosureH 1408 cg cap
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgens, hrepOK⟩, hcentOK⟩, htree⟩, hodist⟩, hosize⟩, hcomm⟩, hCtree⟩,
    hCdist⟩, hCsize⟩, hprod⟩ := h
  set t : Equiv.Perm (Fin 1408) := elemW r.rep with ht
  set Kc : Subgroup (Equiv.Perm (Fin 1408)) :=
    closure (elemW '' {w | w ∈ r.centGens}) with hKc
  have hosize' : o.1.size = r.classSize := by simpa using hosize
  have hCsize' : C.1.size = r.centOrder := by simpa using hCsize
  have hprod' : r.classSize * r.centOrder = 177408000 := by simpa using hprod
  have hT : Rep 1408 (tabW r.rep) t := by
    rw [ht]
    exact rep_elemW_of_gensOK hgens hrepOK
  have hgenPerm : ∀ g ∈ h1408Gens, permOK 1408 g = true ∧ invOK 1408 g (invT 1408 g) = true := by
    rw [gensOK, List.all_eq_true] at hgens
    intro g hg
    exact Bool.and_eq_true_iff.mp (hgens g hg)
  have hgP : ∀ l < pg.size, Rep 1408 pg[l]! (tp 1408 pg[l]!) ∧
      Rep 1408 pgInv[l]! (tp 1408 pg[l]!)⁻¹ ∧ tp 1408 pg[l]! ∈ P1408 := by
    intro l hl
    have hmemGen : pg[l]! ∈ h1408Gens := by
      have := getElem!_mem_array hl
      simpa [pg] using this
    have hpi := hgenPerm (pg[l]!) hmemGen
    have hrep : Rep 1408 pg[l]! (tp 1408 pg[l]!) := rep_tp hpi.1
    have hinv : Rep 1408 (invT 1408 (pg[l]!)) (tp 1408 pg[l]!)⁻¹ := rep_invT hrep hpi.2
    have hmemP : tp 1408 pg[l]! ∈ P1408 := by
      rw [← genOf_h1408Gens]
      exact tp_mem_genOf hmemGen
    have hInvEntry : pgInv[l]! = invT 1408 (pg[l]!) := by
      rw [getElem!_pos pgInv l (by simpa [pgInv] using hl), Array.getElem_map,
        ← getElem!_pos pg l hl]
    exact ⟨hrep, by rw [hInvEntry]; exact hinv, hmemP⟩
  have hconj : ∀ k < o.1.size, ∃ c ∈ P1408, Rep 1408 o.1[k]! (c * t * c⁻¹) :=
    conjTreeOK_spec P1408 hgP hT htree
  have horep : ∀ k < o.1.size, Rep 1408 o.1[k]! (tablePerm 1408 o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := hconj k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup : (o.1.toList.map (tablePerm 1408)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm horep) hodist
  have hclass : r.classSize ≤ (CFSG.Sporadic.SmallOddCore.conjClass P1408 t).ncard := by
    have := length_le_ncard_of_nodup honodup (S := CFSG.Sporadic.SmallOddCore.conjClass P1408 t) fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hx
      obtain ⟨c, hc, hrep⟩ := hconj k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩
    rwa [List.length_map, Array.length_toList, hosize'] at this
  have hcommw : ∀ w ∈ r.centGens, commTT 1408 (tabW w) (tabW r.rep) = true := by
    intro w hw
    have hmem : tabW w ∈ cg := by
      simp only [cg, tabsW, Array.mem_toArray, List.mem_map]
      exact ⟨w, hw, rfl⟩
    exact Array.all_eq_true'.1 hcomm (tabW w) hmem
  have hHle : Kc ≤ P1408 ⊓ centralizer ({t} : Set _) := by
    rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    refine mem_inf.mpr ⟨elemW_mem w, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hwok : wordOK w = true := List.all_eq_true.1 hcentOK w hw
    have hrepw : Rep 1408 (tabW w) (elemW w) := rep_elemW_of_gensOK hgens hwok
    exact (commTT_iff hrepw hT).1 (hcommw w hw)
  have hga : ∀ l < cg.size, Rep 1408 cg[l]! (tablePerm 1408 cg[l]!) ∧
      tablePerm 1408 cg[l]! ∈ Kc := by
    intro l hl
    have hmemcg : cg[l]! ∈ r.centGens.map tabW := by
      have := getElem!_mem_array hl
      simpa [cg, tabsW] using this
    obtain ⟨w, hw, hcw⟩ := List.mem_map.1 hmemcg
    have hwok : wordOK w = true := List.all_eq_true.1 hcentOK w hw
    have hrepw : Rep 1408 (tabW w) (elemW w) := rep_elemW_of_gensOK hgens hwok
    have hrep : Rep 1408 (cg[l]!) (elemW w) := by
      rw [hcw] at hrepw
      exact hrepw
    have htpw : tablePerm 1408 (cg[l]!) = elemW w := tablePerm_eq hrep
    refine ⟨by rw [htpw]; exact hrep, ?_⟩
    rw [htpw]
    exact subset_closure ⟨w, hw, rfl⟩
  have hCK := mulTreeOK_spec (n := 1408) (by norm_num) Kc
    (gg := fun l => tablePerm 1408 cg[l]!) hga hCtree
  have hCrep : ∀ k < C.1.size, Rep 1408 C.1[k]! (tablePerm 1408 C.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hCmem : ∀ k < C.1.size, tablePerm 1408 C.1[k]! ∈ Kc := by
    intro k hk
    obtain ⟨c, hc, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hc
  have hCnodup : (C.1.toList.map (tablePerm 1408)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm hCrep) hCdist
  have hKcard : r.centOrder ≤ Nat.card Kc := by
    have := length_le_card_of_nodup hCnodup fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
      exact hCmem k hk
    rwa [List.length_map, Array.length_toList, hCsize'] at this
  have hCle : Nat.card Kc ≤ Nat.card ↥(P1408 ⊓ centralizer ({t} : Set _)) :=
    card_le_of_le hHle
  have hos := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card P1408 t
  rw [hP, ← hprod'] at hos
  have hpos1 : 0 < r.classSize := by
    rcases Nat.eq_zero_or_pos r.classSize with h0 | h0
    · have hp0 := hprod'
      rw [h0, zero_mul] at hp0
      rw [← hp0] at hP
      exact absurd hP (Nat.card_pos (α := P1408)).ne'
    · exact h0
  have hpos2 : 0 < r.centOrder := by
    rcases Nat.eq_zero_or_pos r.centOrder with h0 | h0
    · have hp0 := hprod'
      rw [h0, mul_zero] at hp0
      rw [← hp0] at hP
      exact absurd hP (Nat.card_pos (α := P1408)).ne'
    · exact h0
  have hcent : Nat.card ↥(P1408 ⊓ centralizer ({t} : Set _)) = r.centOrder := by
    by_contra hne
    have hlt : r.centOrder < Nat.card ↥(P1408 ⊓ centralizer ({t} : Set _)) := by omega
    have hlt2 : r.classSize * r.centOrder < (CFSG.Sporadic.SmallOddCore.conjClass P1408 t).ncard *
        Nat.card ↥(P1408 ⊓ centralizer ({t} : Set _)) :=
      Nat.mul_lt_mul_of_le_of_lt hclass hlt (hpos1.trans_le hclass)
    omega
  have hcls : (CFSG.Sporadic.SmallOddCore.conjClass P1408 t).ncard = r.classSize := by
    rw [hcent] at hos
    exact Nat.eq_of_mul_eq_mul_right hpos2 hos
  have hKeq : Kc = P1408 ⊓ centralizer ({t} : Set _) :=
    Subgroup.eq_of_le_of_card_ge hHle (by rw [hcent]; exact hKcard)
  have hclassCov : ∀ y ∈ CFSG.Sporadic.SmallOddCore.conjClass P1408 t, ∃ k < (classList cap r.rep).size,
      Rep 1408 (classList cap r.rep)[k]! y := by
    intro y hy
    have hmem := mem_of_nodup_of_ncard_le honodup (S := CFSG.Sporadic.SmallOddCore.conjClass P1408 t)
      (fun x hx => by
        obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hx
        obtain ⟨c, hc, hrep⟩ := hconj k hk
        rw [tablePerm_eq hrep]
        exact ⟨c, hc, rfl⟩)
      (by rw [List.length_map, Array.length_toList, hosize']; exact le_of_eq hcls) y hy
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hmem
    exact ⟨k, hk, horep k hk⟩
  have hCcov : ∀ y ∈ Kc, ∃ k < (subgroupList cap r.centGens).size,
      Rep 1408 (subgroupList cap r.centGens)[k]! y := by
    intro y hy
    have hmem := mem_of_nodup_of_card_le hCnodup (K := Kc)
      (fun x hx => by
        obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
        exact hCmem k hk)
      (by rw [List.length_map, Array.length_toList, hCsize']; exact le_of_eq (by rw [hKeq, hcent])) y hy
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hmem
    exact ⟨k, hk, hCrep k hk⟩
  have hclassEnum : IsEnumSet 1408 (classList cap r.rep)
      (CFSG.Sporadic.SmallOddCore.conjClass P1408 t) :=
    ⟨fun k hk => by
      obtain ⟨c, hc, hrep⟩ := hconj k hk
      exact ⟨c * t * c⁻¹, ⟨c, hc, rfl⟩, hrep⟩,
     fun y hy => by
      obtain ⟨k, hk, hrep⟩ := hclassCov y hy
      exact ⟨k, hk, hrep⟩⟩
  have hCenum : IsEnumSet 1408 (subgroupList cap r.centGens) (Kc : Set _) :=
    ⟨fun k hk => ⟨tablePerm 1408 (C.1[k]!), hCmem k hk, hCrep k hk⟩,
     fun y hy => by
      obtain ⟨k, hk, hrep⟩ := hCcov y hy
      exact ⟨k, hk, hrep⟩⟩
  exact ⟨hcls, hclassEnum, hcent, hKeq, by rw [← hKeq]; exact hCenum⟩

end CFSG.EvenSporadicStandard.HNRecog
