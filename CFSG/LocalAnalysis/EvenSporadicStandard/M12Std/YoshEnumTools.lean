module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

@[expose] def conjT (n : ℕ) (m t : Table) : Table := compT n (compT n m t) (invT n m)

@[expose] def commutatorT (n : ℕ) (a b : Table) : Table :=
  compT n (compT n a b) (compT n (invT n a) (invT n b))

@[expose] def memTab (n : ℕ) (L : List Table) (t : Table) : Bool := L.any fun s => tblEq n s t

@[expose] def commIn (n : ℕ) (cT a b : Table) : Bool :=
  tblEq n (commutatorT n a b) (idT n) || tblEq n (commutatorT n a b) cT

@[expose] def sqIn (n : ℕ) (cT a : Table) : Bool :=
  tblEq n (compT n a a) (idT n) || tblEq n (compT n a a) cT

section Rep

variable {n : ℕ}

theorem rep_conjT (hn : n < 2 ^ 32) {m t : Table} {g h : Equiv.Perm (Fin n)} (hm : Rep n m g)
    (ht : Rep n t h) : Rep n (conjT n m t) (g * h * g⁻¹) :=
  (hm.compT ht).compT (rep_invT_of_rep hn hm)

theorem rep_commutatorT (hn : n < 2 ^ 32) {a b : Table} {g h : Equiv.Perm (Fin n)}
    (ha : Rep n a g) (hb : Rep n b h) : Rep n (commutatorT n a b) ⁅g, h⁆ := by
  have := (ha.compT hb).compT ((rep_invT_of_rep hn ha).compT (rep_invT_of_rep hn hb))
  rwa [← mul_assoc] at this

theorem memTab_iff {L : List Table} {T : Table} {g : Equiv.Perm (Fin n)}
    (hT : Rep n T g) (hL : ∀ S ∈ L, ∃ s : Equiv.Perm (Fin n), Rep n S s) :
    memTab n L T = true ↔ ∃ S ∈ L, ∃ s : Equiv.Perm (Fin n), Rep n S s ∧ s = g := by
  unfold memTab
  rw [List.any_eq_true]
  constructor
  · rintro ⟨S, hS, he⟩
    obtain ⟨s, hs⟩ := hL S hS
    exact ⟨S, hS, s, hs, (tblEq_iff_eq hs hT).1 he⟩
  · rintro ⟨S, hS, s, hs, rfl⟩
    exact ⟨S, hS, (tblEq_iff_eq hs hT).2 rfl⟩

theorem commIn_iff (hn : n < 2 ^ 32) {cT a b : Table} {c x y : Equiv.Perm (Fin n)}
    (hc : Rep n cT c) (ha : Rep n a x) (hb : Rep n b y) :
    commIn n cT a b = true ↔ ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c := by
  have h := rep_commutatorT hn ha hb
  unfold commIn
  rw [Bool.or_eq_true, tblEq_iff_eq h (Rep.idT hn), tblEq_iff_eq h hc]

theorem sqIn_iff (hn : n < 2 ^ 32) {cT a : Table} {c x : Equiv.Perm (Fin n)}
    (hc : Rep n cT c) (ha : Rep n a x) : sqIn n cT a = true ↔ x * x = 1 ∨ x * x = c := by
  have h := ha.compT ha
  unfold sqIn
  rw [Bool.or_eq_true, tblEq_iff_eq h (Rep.idT hn), tblEq_iff_eq h hc]

end Rep

end CFSG.EvenSporadicStandard.M12Std.Yosh

namespace CFSG.EvenSporadicStandard.Fin76b.EnumSpec

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M12Std.Yosh

variable {n : ℕ} {gens L : Array Table}

theorem mem_iff (h : EnumSpec n gens L) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    g ∈ closure (tp n '' {x | x ∈ gens}) ↔ ∃ T' ∈ L, tblEq n T' T = true := by
  constructor
  · intro hg
    obtain ⟨T', hT', hrep⟩ := h.cover_mem hg
    exact ⟨T', hT', (tblEq_iff_eq hrep hT).2 rfl⟩
  · rintro ⟨T', hT', he⟩
    obtain ⟨hrep, hmem⟩ := h.rep_mem hT'
    have := (tblEq_iff_eq hrep hT).1 he
    rw [← this]
    exact hmem

theorem forall_mem (h : EnumSpec n gens L) {Q : Equiv.Perm (Fin n) → Prop}
    (H : ∀ T ∈ L, Q (tablePerm n T)) : ∀ g ∈ closure (tp n '' {x | x ∈ gens}), Q g := by
  intro g hg
  obtain ⟨T, hT, hrep⟩ := h.cover_mem hg
  rw [← tablePerm_eq hrep]
  exact H T hT

theorem exists_entry (h : EnumSpec n gens L) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ closure (tp n '' {x | x ∈ gens})) : ∃ T ∈ L, Rep n T g := h.cover_mem hg

theorem card_filter (h : EnumSpec n gens L) (Q : Equiv.Perm (Fin n) → Prop) (P : Table → Bool)
    (hP : ∀ T ∈ L, P T = true ↔ Q (tablePerm n T)) :
    Nat.card {g : Equiv.Perm (Fin n) // g ∈ closure (tp n '' {x | x ∈ gens}) ∧ Q g} =
      (L.toList.filter P).length := by
  classical
  have hnodup : ((L.toList.filter P).map (tablePerm n)).Nodup :=
    h.nodup.sublist ((List.filter_sublist (p := P)).map (tablePerm n))
  rw [← List.length_map (f := tablePerm n)]
  refine card_eq_length (fun g => g ∈ closure (tp n '' {x | x ∈ gens}) ∧ Q g) id
    Function.injective_id _ hnodup fun b => ?_
  constructor
  · intro hb
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hTL, hTP⟩ := List.mem_filter.1 hT
    obtain ⟨-, hmem⟩ := h.rep_mem (Array.mem_toList_iff.1 hTL)
    exact ⟨tablePerm n T, ⟨hmem, (hP T (Array.mem_toList_iff.1 hTL)).1 hTP⟩, rfl⟩
  · rintro ⟨g, ⟨hgK, hgQ⟩, rfl⟩
    obtain ⟨T, hT, hrep⟩ := h.cover_mem hgK
    refine List.mem_map.2 ⟨T, List.mem_filter.2 ⟨Array.mem_toList_iff.2 hT, ?_⟩,
      tablePerm_eq hrep⟩
    exact (hP T hT).2 (by rw [tablePerm_eq hrep]; exact hgQ)

theorem memTab_iff' (h : EnumSpec n gens L) {T : Table} {g : Equiv.Perm (Fin n)}
    (hT : Rep n T g) : memTab n L.toList T = true ↔ g ∈ closure (tp n '' {x | x ∈ gens}) := by
  rw [h.mem_iff hT]
  unfold memTab
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s, Array.mem_toList_iff.1 hs, he⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨s, Array.mem_toList_iff.2 hs, he⟩

theorem forall_toList (h : EnumSpec n gens L) {Q : Equiv.Perm (Fin n) → Prop}
    (H : ∀ T ∈ L.toList, ∀ g : Equiv.Perm (Fin n), Rep n T g → Q g) :
    ∀ g ∈ closure (tp n '' {x | x ∈ gens}), Q g :=
  h.forall_mem fun T hT => H T (Array.mem_toList_iff.2 hT) _ (h.rep_mem hT).1

theorem forall_forall_mem {gA LA gB LB : Array Table} (hA : EnumSpec n gA LA)
    (hB : EnumSpec n gB LB) {Q : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop}
    (H : ∀ a ∈ LA, ∀ b ∈ LB, Q (tablePerm n a) (tablePerm n b)) :
    ∀ x ∈ closure (tp n '' {x | x ∈ gA}), ∀ y ∈ closure (tp n '' {x | x ∈ gB}), Q x y :=
  hA.forall_mem (Q := fun x => ∀ y ∈ closure (tp n '' {x | x ∈ gB}), Q x y)
    fun a ha => hB.forall_mem (Q := fun y => Q (tablePerm n a) y) fun b hb => H a ha b hb

theorem exists_mem_iff (h : EnumSpec n gens L) {Q : Equiv.Perm (Fin n) → Prop} :
    (∃ g ∈ closure (tp n '' {x | x ∈ gens}), Q g) ↔ ∃ T ∈ L, Q (tablePerm n T) := by
  constructor
  · rintro ⟨g, hg, hQ⟩
    obtain ⟨T, hT, hrep⟩ := h.cover_mem hg
    exact ⟨T, hT, by rw [tablePerm_eq hrep]; exact hQ⟩
  · rintro ⟨T, hT, hQ⟩
    exact ⟨tablePerm n T, (h.rep_mem hT).2, hQ⟩

end CFSG.EvenSporadicStandard.Fin76b.EnumSpec
