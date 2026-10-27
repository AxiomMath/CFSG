module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WTransport
public import Mathlib

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def enumOK (n m : ℕ) (gens : Array Table) (E : Array Table × Array ℕ × Array ℕ)
    (size : ℕ) : Bool :=
  gens.all (fun x => permOK n x) && mulTreeOK n gens E.1 E.2.1 E.2.2 &&
    hkeysDistinct n E.1.toList && closedOKS n m gens E.1 && E.1.size == size

structure EnumSpec (n : ℕ) (gens L : Array Table) : Prop where
  perm : ∀ x ∈ gens, permOK n x = true
  rep : ∀ k < L.size, Rep n L[k]! (tablePerm n L[k]!)
  mem : ∀ k < L.size, tablePerm n L[k]! ∈ closure (tp n '' {x | x ∈ gens})
  cover : ∀ x ∈ closure (tp n '' {x | x ∈ gens}), ∃ k < L.size, Rep n L[k]! x
  nodup : (L.toList.map (tablePerm n)).Nodup
  card : Nat.card ↥(closure (tp n '' {x | x ∈ gens})) = L.size

theorem enumOK_spec {n m : ℕ} (hn : n < 2 ^ 32) {gens : Array Table}
    {E : Array Table × Array ℕ × Array ℕ} {size : ℕ}
    (h : enumOK n m gens E size = true) : EnumSpec n gens E.1 ∧ E.1.size = size := by
  simp only [enumOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [Array.all_eq_true'] at h1
  obtain ⟨hrep, hcov, hcard⟩ := enumS_spec hn h1 h2 (closedOK_of_closedOKS h4) h3
  exact ⟨⟨h1, fun k hk => (hrep k hk).1, fun k hk => (hrep k hk).2, hcov,
    nodup_of_hkeysDistinct (forall₂_tablePerm (fun k hk => (hrep k hk).1)) h3, hcard⟩, h5⟩

namespace EnumSpec

variable {n : ℕ} {gens L : Array Table}

theorem rep_mem (h : EnumSpec n gens L) {T : Table} (hT : T ∈ L) :
    Rep n T (tablePerm n T) ∧ tablePerm n T ∈ closure (tp n '' {x | x ∈ gens}) := by
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hT
  have h1 := h.rep k hk
  have h2 := h.mem k hk
  rw [getElem!_pos L k hk] at h1 h2
  exact ⟨h1, h2⟩

theorem cover_mem (h : EnumSpec n gens L) {x : Equiv.Perm (Fin n)}
    (hx : x ∈ closure (tp n '' {x | x ∈ gens})) : ∃ T ∈ L, Rep n T x := by
  obtain ⟨k, hk, hrep⟩ := h.cover x hx
  exact ⟨L[k]!, getElem!_mem_array hk, hrep⟩

theorem card_inf_centralizer (h : EnumSpec n gens L) {w : Table} {β : Equiv.Perm (Fin n)}
    (hw : Rep n w β) :
    Nat.card ↥(closure (tp n '' {x | x ∈ gens}) ⊓ centralizer ({β} : Set (Equiv.Perm (Fin n)))) =
      (L.toList.filter (commTT n w)).length := by
  have hnodup : ((L.toList.filter (commTT n w)).map (tablePerm n)).Nodup :=
    h.nodup.sublist ((List.filter_sublist (p := commTT n w)).map (tablePerm n))
  rw [← List.length_map (f := tablePerm n)]
  refine card_eq_length (fun g => g ∈ closure (tp n '' {x | x ∈ gens}) ⊓
    centralizer ({β} : Set (Equiv.Perm (Fin n)))) id Function.injective_id _ hnodup fun b => ?_
  constructor
  · intro hb
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hTL, hTc⟩ := List.mem_filter.1 hT
    obtain ⟨hrep, hmem⟩ := h.rep_mem (Array.mem_toList_iff.1 hTL)
    exact ⟨tablePerm n T, ⟨hmem, mem_centralizer_singleton_iff.2
      ((commTT_iff hw hrep).1 hTc).symm⟩, rfl⟩
  · rintro ⟨g, ⟨hgK, hgc⟩, rfl⟩
    obtain ⟨T, hT, hrep⟩ := h.cover_mem hgK
    refine List.mem_map.2 ⟨T, List.mem_filter.2 ⟨Array.mem_toList_iff.2 hT,
      (commTT_iff hw hrep).2 (mem_centralizer_singleton_iff.1 hgc).symm⟩, tablePerm_eq hrep⟩

theorem mem_inf_of_filter (h : EnumSpec n gens L) {w : Table} {β : Equiv.Perm (Fin n)}
    (hw : Rep n w β) {a : Table} (ha : a ∈ L.toList.filter (commTT n w)) :
    Rep n a (tablePerm n a) ∧ tablePerm n a ∈ closure (tp n '' {x | x ∈ gens}) ⊓
      centralizer ({β} : Set (Equiv.Perm (Fin n))) := by
  obtain ⟨haL, hac⟩ := List.mem_filter.1 ha
  obtain ⟨hrep, hmem⟩ := h.rep_mem (Array.mem_toList_iff.1 haL)
  exact ⟨hrep, hmem, mem_centralizer_singleton_iff.2 ((commTT_iff hw hrep).1 hac).symm⟩

end EnumSpec

@[expose] def wRoots (n : ℕ) (tT : Table) (W : Array Table) : Array Table :=
  W.filter fun w => tblEq n (compT n w w) tT

@[expose] def centEOK (n : ℕ) (tT : Table) (rts W : Array Table) : Bool :=
  W.all fun w => !(rts.all fun r => commTT n w r) || tblEq n w (idT n) || tblEq n w tT

@[expose] def betaAux (n : ℕ) (C : List Table) : Bool :=
  C.length == 8 && C.any fun a => C.any fun b => !commTT n a b

@[expose] def betaOK (n : ℕ) (E : Array Table) (w : Table) : Bool :=
  ordTest n 3 w && betaAux n (E.toList.filter (commTT n w))

@[expose] def wCheck (n m capW : ℕ) (tT : Table) (cg : Array Table) : Bool :=
  let WE := mulClosureS n m cg capW
  let rts := wRoots n tT WE.1
  let EE := mulClosureS n m rts 40
  permOK n tT && enumOK n m cg WE 1920 && rts.size == 20 && enumOK n m rts EE 32 &&
    centEOK n tT rts WE.1 && WE.1.any (betaOK n EE.1)

theorem rootFactsFor_of_wCheck {n m capW : ℕ} (hn : n < 2 ^ 32)
    {X : Subgroup (Equiv.Perm (Fin n))} {tT : Table} {cg : Array Table}
    (htX : tp n tT ∈ X)
    (hcg : closure (tp n '' {x | x ∈ cg}) =
      X ⊓ centralizer ({tp n tT} : Set (Equiv.Perm (Fin n))))
    (hchk : wCheck n m capW tT cg = true) : RootFactsFor ↥X ⟨tp n tT, htX⟩ := by
  classical
  simp only [wCheck, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hperm, hWchk⟩, hrs⟩, hEchk⟩, hcent⟩, hbeta⟩ := hchk
  obtain ⟨hWs, hWsize⟩ := enumOK_spec hn hWchk
  obtain ⟨hEs, hEsize⟩ := enumOK_spec hn hEchk
  set W := (mulClosureS n m cg capW).1 with hWdef
  set rts := wRoots n tT W with hrtsdef
  set El := (mulClosureS n m rts 40).1 with hEldef
  have ht : Rep n tT (tp n tT) := rep_tp hperm
  have hrts_mem : ∀ r ∈ rts, r ∈ W ∧ tblEq n (compT n r r) tT = true := fun r hr => by
    obtain ⟨h1, h2⟩ := Array.mem_filter.1 hr
    exact ⟨h1, h2⟩
  have hrts_root : ∀ r ∈ rts, Rep n r (tp n r) ∧ tp n r ∈ rootSet X (tp n tT) := by
    intro r hr
    obtain ⟨hrW, hsq⟩ := hrts_mem r hr
    have hrr := rep_tp (hEs.perm r hr)
    obtain ⟨hrep, hmem⟩ := hWs.rep_mem hrW
    rw [hcg] at hmem
    have hpe : tablePerm n r = tp n r := tablePerm_eq hrr
    rw [hpe] at hmem
    exact ⟨hrr, hmem.1, (tblEq_iff_eq (Rep.compT hrr hrr) ht).1 hsq⟩
  have hRs : rootSet X (tp n tT) = tp n '' {x | x ∈ rts} := by
    ext x
    constructor
    · rintro ⟨hxX, hxx⟩
      have hcomm : x * tp n tT = tp n tT * x := by
        rw [← hxx, ← mul_assoc]
      have hxK : x ∈ closure (tp n '' {x | x ∈ cg}) := by
        rw [hcg]
        exact ⟨hxX, mem_centralizer_singleton_iff.2 hcomm⟩
      obtain ⟨T, hTW, hT⟩ := hWs.cover_mem hxK
      have hTr : T ∈ rts := by
        refine Array.mem_filter.2 ⟨hTW, ?_⟩
        exact (tblEq_iff_eq (Rep.compT hT hT) ht).2 hxx
      exact ⟨T, hTr, rep_unique (rep_tp (hEs.perm T hTr)) hT⟩
    · rintro ⟨r, hr, rfl⟩
      exact (hrts_root r hr).2
  refine RootFactsFor.of_ambient htX ?_ ?_ ?_ ?_ ?_
  · rw [← hcg, hWs.card, hWsize]
  · rw [hRs]
    calc (tp n '' {x | x ∈ rts}).ncard
        ≤ ((rts.toList.map (tp n)).toFinset : Set (Equiv.Perm (Fin n))).ncard :=
          Set.ncard_le_ncard (by
            rintro _ ⟨T, hT, rfl⟩
            simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map, Array.mem_toList_iff]
            exact ⟨T, hT, rfl⟩) (Finset.finite_toSet _)
      _ = (rts.toList.map (tp n)).toFinset.card := Set.ncard_coe_finset _
      _ ≤ (rts.toList.map (tp n)).length := List.toFinset_card_le _
      _ = 20 := by simp [hrs]
  · rw [hRs, hEs.card, hEsize]
  ·
    intro l hlX hl
    have hr0 : 0 < rts.size := by omega
    have hr0m : rts[0] ∈ rts := Array.getElem_mem hr0
    obtain ⟨-, hr0X, hr0sq⟩ := hrts_root _ hr0m
    have hlt : l * tp n tT = tp n tT * l := by
      have h := hl _ hr0X hr0sq
      rw [← hr0sq]
      calc l * (tp n rts[0] * tp n rts[0]) = (l * tp n rts[0]) * tp n rts[0] := by rw [mul_assoc]
        _ = (tp n rts[0] * l) * tp n rts[0] := by rw [h]
        _ = tp n rts[0] * (l * tp n rts[0]) := by rw [mul_assoc]
        _ = tp n rts[0] * (tp n rts[0] * l) := by rw [h]
        _ = tp n rts[0] * tp n rts[0] * l := by rw [mul_assoc]
    have hlK : l ∈ closure (tp n '' {x | x ∈ cg}) := by
      rw [hcg]
      exact ⟨hlX, mem_centralizer_singleton_iff.2 hlt⟩
    obtain ⟨T, hTW, hT⟩ := hWs.cover_mem hlK
    have hall : (rts.all fun r => commTT n T r) = true := by
      rw [Array.all_eq_true']
      intro r hr
      obtain ⟨hrr, hrX, hrsq⟩ := hrts_root r hr
      exact (commTT_iff hT hrr).2 (hl _ hrX hrsq)
    rw [centEOK, Array.all_eq_true'] at hcent
    have hc := hcent T hTW
    rw [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · exact Or.inl ((tblEq_idT_iff hn hT).1 hc)
    · exact Or.inr ((tblEq_iff_eq hT ht).1 hc)
  ·
    rw [Array.any_eq_true] at hbeta
    obtain ⟨k, hk, hk3⟩ := hbeta
    have hwW : W[k] ∈ W := Array.getElem_mem hk
    obtain ⟨hwrep, hwmem⟩ := hWs.rep_mem hwW
    rw [hcg] at hwmem
    simp only [betaOK, Bool.and_eq_true, betaAux, beq_iff_eq, List.any_eq_true] at hk3
    obtain ⟨hord, hlen, a, ha, b, hb, hab⟩ := (by simpa [and_assoc] using hk3 :
      ordTest n 3 W[k] = true ∧ (El.toList.filter (commTT n W[k])).length = 8 ∧
        ∃ a ∈ El.toList.filter (commTT n W[k]), ∃ b ∈ El.toList.filter (commTT n W[k]),
          commTT n a b = false)
    obtain ⟨hra, hamem⟩ := hEs.mem_inf_of_filter hwrep ha
    obtain ⟨hrb, hbmem⟩ := hEs.mem_inf_of_filter hwrep hb
    refine ⟨tablePerm n W[k], hwmem.1, mem_centralizer_singleton_iff.1 hwmem.2,
      (ordTest_iff_perm hwrep (by norm_num)).1 hord, ?_, tablePerm n a, ?_, tablePerm n b, ?_, ?_⟩
    · rw [hRs, hEs.card_inf_centralizer hwrep, hlen]
    · rw [hRs]
      exact hamem
    · rw [hRs]
      exact hbmem
    · intro hc
      have := (commTT_iff hra hrb).2 hc
      rw [hab] at this
      exact Bool.false_ne_true this

end CFSG.EvenSporadicStandard.Fin76b
