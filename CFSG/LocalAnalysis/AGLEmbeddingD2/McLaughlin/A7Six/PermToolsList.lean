module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.PermTools
public import CFSG.Permutation.FinPack

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six.PermTools

open Equiv Equiv.Perm
open CFSG.Permutation.FinPack (memK allK anyK memK_iff allK_iff anyK_iff)

@[expose] noncomputable def reachL (gs L seen : List ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
    (fun c _ r seen =>
      (memK c seen || anyK (fun a => anyK (fun g => Nat.beq (mulC a g) c) gs) seen) && r (c :: seen))
    L seen

@[expose] noncomputable def closedL (gs L : List ℕ) : Bool :=
  allK (fun a => allK (fun g => memK (mulC a g) L) gs) L

@[expose] noncomputable def nodupL (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c t r => !memK c t && r) L

theorem nodup_of_nodupL : ∀ {L : List ℕ}, nodupL L = true → L.Nodup
  | [], _ => List.nodup_nil
  | c :: t, h => by
    change (!memK c t && nodupL t) = true at h
    have h1 : memK c t = false := by
      revert h
      cases memK c t <;> simp
    have h2 : nodupL t = true := by
      revert h
      cases nodupL t <;> simp
    refine List.nodup_cons.2 ⟨fun hc => ?_, nodup_of_nodupL h2⟩
    rw [memK_iff.2 hc] at h1
    exact Bool.noConfusion h1

theorem reachL_sound {gs : List ℕ} {P : ℕ → Prop}
    (hmul : ∀ a, P a → ∀ g ∈ gs, P (mulC a g)) :
    ∀ (L seen : List ℕ), reachL gs L seen = true → (∀ a ∈ seen, P a) → ∀ c ∈ L, P c
  | [], _, _, _ => fun _ hc => absurd hc List.not_mem_nil
  | c :: t, seen, h, hseen => by
    change ((memK c seen || anyK (fun a => anyK (fun g => Nat.beq (mulC a g) c) gs) seen) &&
      reachL gs t (c :: seen)) = true at h
    rw [Bool.and_eq_true, Bool.or_eq_true, memK_iff, anyK_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hc : P c := by
      rcases h1 with h1 | ⟨a, ha, h1⟩
      · exact hseen c h1
      · obtain ⟨g, hg, he⟩ := anyK_iff.1 h1
        rw [← Nat.eq_of_beq_eq_true he]
        exact hmul a (hseen a ha) g hg
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hc
    · exact reachL_sound hmul t (c :: seen) h2 (List.forall_mem_cons.2 ⟨hc, hseen⟩) x hx

theorem exists_of_mem_reachL {S : Set (Perm (Fin 7))} {gs : List ℕ}
    (hgs : ∀ g ∈ gs, ∃ s ∈ S, enc s = g) {L : List ℕ} (h : reachL gs L [idC] = true) :
    ∀ c ∈ L, ∃ x ∈ Subgroup.closure S, enc x = c := by
  refine reachL_sound (P := fun c => ∃ x ∈ Subgroup.closure S, enc x = c) ?_ L [idC] h ?_
  · rintro a ⟨x, hx, rfl⟩ g hg
    obtain ⟨s, hs, rfl⟩ := hgs g hg
    exact ⟨x * s, Subgroup.mul_mem _ hx (Subgroup.subset_closure hs), enc_mul x s⟩
  · intro a ha
    rw [List.mem_singleton] at ha
    rw [ha]
    exact ⟨1, Subgroup.one_mem _, enc_one⟩

theorem mem_closure_iff_reachL (gens : List (Perm (Fin 7))) {S : Set (Perm (Fin 7))}
    (hS : ∀ s, s ∈ S ↔ s ∈ gens) (gs : List ℕ) (hgs : gens.map enc = gs) (L : List ℕ)
    (hid : memK idC L = true) (hcl : closedL gs L = true) (hr : reachL gs L [idC] = true)
    (x : Perm (Fin 7)) : x ∈ Subgroup.closure S ↔ enc x ∈ L := by
  subst hgs
  constructor
  · intro hx
    refine enc_mem_of_closed (fun s hs => List.mem_map_of_mem ((hS s).1 hs)) (memK_iff.1 hid)
      (fun a ha g hg => memK_iff.1 ((allK_iff.1 ((allK_iff.1 hcl) a ha)) g hg)) hx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_of_mem_reachL (S := S) (fun g hg => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      exact ⟨s, (hS s).2 hs, rfl⟩) hr _ hx
    rwa [← enc_injective hyx]

theorem card_closure_reachL (gens : List (Perm (Fin 7))) {S : Set (Perm (Fin 7))}
    (hS : ∀ s, s ∈ S ↔ s ∈ gens) (gs : List ℕ) (hgs : gens.map enc = gs) (L : List ℕ)
    (hid : memK idC L = true) (hcl : closedL gs L = true) (hr : reachL gs L [idC] = true)
    (hnd : nodupL L = true) : Nat.card (Subgroup.closure S) = L.length := by
  classical
  have hmem := mem_closure_iff_reachL gens hS gs hgs L hid hcl hr
  have hreal := exists_of_mem_reachL (S := S) (gs := gs) (fun g hg => by
    rw [← hgs] at hg
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
    exact ⟨s, (hS s).2 hs, rfl⟩) hr
  let f : Subgroup.closure S → {c // c ∈ L.toFinset} :=
    fun x => ⟨enc x, List.mem_toFinset.2 ((hmem x).1 x.2)⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      have h0 : enc (x : Perm (Fin 7)) = enc (y : Perm (Fin 7)) := congrArg Subtype.val h
      exact Subtype.ext (enc_injective h0)
    · intro c
      obtain ⟨x, hx, hxc⟩ := hreal c (List.mem_toFinset.1 c.2)
      exact ⟨⟨x, hx⟩, Subtype.ext hxc⟩
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (nodup_of_nodupL hnd)]

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six.PermTools
