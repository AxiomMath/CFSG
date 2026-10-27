module

public import CFSG.GF2Type.SmithTypeE.LMod.Points
public import CFSG.LargeExtraspecial.SMod20Basic
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import Certificates.Data.SmithL6Tr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup Module CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
  CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor decode_zero bit)
open scoped MatrixGroups

attribute [local irreducible] tvIdxTab tvTab tvImg tvList

@[expose] def IsTab (ct : Array ℕ) (π : Equiv.Perm (Fin 1953)) : Prop :=
  ∀ x : Fin 1953, ct[x.val]! = (π x).val

theorem mem_trFixL {ct : Array ℕ} {π : Equiv.Perm (Fin 1953)} (hc : IsTab ct π) {q : ℕ} :
    q ∈ trFixL ct ↔ ∃ hq : q < 1953, π ⟨q, hq⟩ = ⟨q, hq⟩ := by
  rw [trFixL, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨hq, he⟩
    exact ⟨hq, Fin.ext (by rw [← hc ⟨q, hq⟩]; exact he)⟩
  · rintro ⟨hq, he⟩
    exact ⟨hq, by rw [hc ⟨q, hq⟩, he]⟩

theorem nodup_trFixL (ct : Array ℕ) : (trFixL ct).Nodup := by
  unfold trFixL
  exact List.nodup_range.filter _

theorem lt_of_mem_trFixL {ct : Array ℕ} {q : ℕ} (h : q ∈ trFixL ct) : q < 1953 := by
  rw [trFixL, List.mem_filter, List.mem_range] at h
  exact h.1

theorem card_setOf_mem_list {l : List ℕ} (hl : l.Nodup) (hlt : ∀ i ∈ l, i < 1953) :
    Nat.card {x : Fin 1953 // x.val ∈ l} = l.length := by
  classical
  have e : Nat.card {x : Fin 1953 // x.val ∈ l} = (Finset.univ.filter fun x : Fin 1953 =>
      x.val ∈ l).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [e, ← List.toFinset_card_of_nodup hl]
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    simpa using hx
  · intro x _ y _ h
    exact Fin.ext h
  · intro b hb
    have hb' : b ∈ l := by simpa using hb
    exact ⟨⟨b, hlt b hb'⟩, by simp [hb'], rfl⟩

theorem card_fixedPoints_eq {ct : Array ℕ} {π : Equiv.Perm (Fin 1953)} (hc : IsTab ct π) :
    Nat.card {x : Fin 1953 // π x = x} = (trFixL ct).length := by
  have e : {x : Fin 1953 // π x = x} = {x : Fin 1953 // x.val ∈ trFixL ct} := by
    congr
    ext x
    rw [mem_trFixL hc]
    exact ⟨fun h => ⟨x.2, h⟩, fun ⟨_, h⟩ => h⟩
  rw [e]
  exact card_setOf_mem_list (nodup_trFixL ct) (fun i hi => lt_of_mem_trFixL hi)

section Main

theorem sub_eq_add_V (x y : V) : x - y = x + y := by
  funext m
  simp only [Pi.sub_apply, Pi.add_apply]
  generalize x m = a
  generalize y m = b
  revert a b
  decide

variable {A : V ≃ₗ[ZMod 2] V} {π : Equiv.Perm (Fin 1953)}

end Main

end CFSG.GF2Type.SmithTypeE.L6
