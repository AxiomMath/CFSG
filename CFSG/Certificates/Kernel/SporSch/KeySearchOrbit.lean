
module

public import CFSG.Certificates.Kernel.SporSch.KeySearch
public import CFSG.Certificates.NativeSetOrbit

public section

namespace CFSG.KS.SporSch.KeySearch

open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Certificates
open scoped Pointwise

@[expose] noncomputable def toL {n : Nat} (U : Set (Fin n)) : List Nat :=
  open Classical in ((List.finRange n).filter fun x => decide (x ∈ U)).map Fin.val

theorem mem_toL {n : Nat} {U : Set (Fin n)} {p : Nat} : p ∈ toL U ↔ ∃ h : p < n, ⟨p, h⟩ ∈ U := by
  classical
  simp only [toL, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.isLt, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨p, h⟩, hx, rfl⟩

theorem toL_good {n : Nat} (U : Set (Fin n)) : Good n (toL U) := by
  classical
  refine ⟨?_, fun x hx => (mem_toL.1 hx).1⟩
  unfold toL
  refine List.Pairwise.map _ (fun a b h => h) ?_
  exact (List.pairwise_lt_finRange n).filter _

theorem eq_of_mem_iff {n : Nat} {a b : List Nat} (ha : Good n a) (hb : Good n b)
    (h : ∀ q, q ∈ a ↔ q ∈ b) : a = b := by
  have hp : a.Perm b := (List.perm_ext_iff_of_nodup ha.1.nodup hb.1.nodup).2 h
  exact hp.eq_of_pairwise' (r := (· ≤ ·)) (ha.1.imp le_of_lt) (hb.1.imp le_of_lt)

theorem toL_injective {n : Nat} : Function.Injective (toL (n := n)) := by
  intro U V h
  ext x
  have := congrArg (fun l => x.val ∈ l) h
  simp only [mem_toL, eq_iff_iff] at this
  constructor
  · intro hx
    obtain ⟨_, hx'⟩ := this.1 ⟨x.isLt, hx⟩
    exact hx'
  · intro hx
    obtain ⟨_, hx'⟩ := this.2 ⟨x.isLt, hx⟩
    exact hx'

theorem toL_finSet {n : Nat} {l : List Nat} (hl : Good n l) : toL (finSet n l) = l := by
  refine eq_of_mem_iff (toL_good _) hl fun q => ?_
  rw [mem_toL]
  constructor
  · rintro ⟨_, hq⟩
    exact hq
  · intro hq
    exact ⟨hl.2 q hq, hq⟩

theorem permOfArr_val {n : Nat} {t : Array Nat} (ht : PermA n t) (x : Fin n) :
    (permOfArr n t x).val = t[x.val]! := by
  unfold permOfArr
  rw [dif_pos ⟨ht.1, ht.2⟩]
  rfl

theorem img_toL {n : Nat} {t : Array Nat} (ht : PermA n t) (U : Set (Fin n)) :
    imgSorted t (toL U) = toL (permOfArr n t • U) := by
  refine eq_of_mem_iff (imgSorted_good ht (toL_good U)) (toL_good _) fun q => ?_
  have hp : (imgSorted t (toL U)).Perm ((toL U).map fun p => t[p]!) := List.mergeSort_perm _ _
  rw [hp.mem_iff, List.mem_map, mem_toL]
  constructor
  · rintro ⟨p, hp', rfl⟩
    obtain ⟨hpn, hpU⟩ := mem_toL.1 hp'
    refine ⟨ht.1 p hpn, ⟨⟨p, hpn⟩, hpU, ?_⟩⟩
    exact Fin.ext (permOfArr_val ht _)
  · rintro ⟨hq, ⟨y, hy, e⟩⟩
    refine ⟨y.val, mem_toL.2 ⟨y.isLt, hy⟩, ?_⟩
    have := congrArg Fin.val e
    simp only [Equiv.Perm.smul_def] at this
    rw [permOfArr_val ht] at this
    exact this

theorem orbit_le_card {n : Nat} {gens : Array (Array Nat)} {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : G = Subgroup.closure (Set.range fun j : Fin gens.size => permOfArr n gens[j.val]!))
    (hg : ∀ k < gens.size, PermA n gens[k]!) {start : List Nat} (hs : Good n start)
    (F : Finset (List Nat)) (h0 : start ∈ F)
    (hF : ∀ s ∈ F, ∀ k < gens.size, imgSorted gens[k]! s ∈ F) :
    (Set.range fun g : G => g • finSet n start).ncard ≤ F.card := by
  have key : ∀ g ∈ G, toL ((g : Equiv.Perm (Fin n)) • finSet n start) ∈ F := by
    intro g hg'
    rw [hG] at hg'
    have hstep : ∀ k < gens.size, ∀ y : Equiv.Perm (Fin n),
        toL (y • finSet n start) ∈ F → toL ((permOfArr n gens[k]! * y) • finSet n start) ∈ F := by
      intro k hk y hy
      rw [mul_smul, ← img_toL (hg k hk)]
      exact hF _ hy k hk
    refine Subgroup.closure_induction_left (p := fun g _ => toL (g • finSet n start) ∈ F)
      ?_ ?_ ?_ hg'
    · rw [one_smul, toL_finSet hs]
      exact h0
    · rintro _ ⟨⟨k, hk⟩, rfl⟩ y _ hy
      exact hstep k hk y hy
    · rintro _ ⟨⟨k, hk⟩, rfl⟩ y _ hy
      set x := permOfArr n gens[k]!
      have hpow : ∀ m, toL ((x ^ m * y) • finSet n start) ∈ F := by
        intro m
        induction m with
        | zero => simpa using hy
        | succ m ih =>
          rw [pow_succ', mul_assoc]
          exact hstep k hk _ ih
      have e : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
          Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      rw [e]
      exact hpow _
  have hsub : toL '' (Set.range fun g : G => g • finSet n start) ⊆ (F : Set (List Nat)) := by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact key g g.2
  calc (Set.range fun g : G => g • finSet n start).ncard
      = (toL '' (Set.range fun g : G => g • finSet n start)).ncard :=
        (Set.ncard_image_of_injective _ toL_injective).symm
    _ ≤ (F : Set (List Nat)).ncard := Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F

end CFSG.KS.SporSch.KeySearch

end
