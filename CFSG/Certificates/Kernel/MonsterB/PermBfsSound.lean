module

public import CFSG.Certificates.Kernel.MonsterB.BfsCore
public import CFSG.Monster.B.TwoA.Census.PermBFS

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census

theorem bfsLoop_eq (act : Array ℕ → Array ℕ → Array ℕ) (gens : Array (Array ℕ)) :
    ∀ (f i : ℕ) (pts : Array (Array ℕ)) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), bfsLoop act gens f i pts edges par lab idx =
        ⟨(gLoop (fun k x => act gens[k]! x) gens.size akey f i pts edges par lab idx).1,
          (gLoop (fun k x => act gens[k]! x) gens.size akey f i pts edges par lab idx).2.1,
          (gLoop (fun k x => act gens[k]! x) gens.size akey f i pts edges par lab idx).2.2.1,
          (gLoop (fun k x => act gens[k]! x) gens.size akey f i pts edges par lab idx).2.2.2⟩
  | 0, _, _, _, _, _, _ => rfl
  | f + 1, i, pts, edges, par, lab, idx => by
    rw [bfsLoop, gLoop]
    split
    · have e : bfsStep act gens i (pts, par, lab, idx) =
          gStep (fun k x => act gens[k]! x) gens.size akey i (pts, par, lab, idx) := rfl
      rw [e]
      generalize gStep (fun k x => act gens[k]! x) gens.size akey i (pts, par, lab, idx) = s
      obtain ⟨a, b, c, d, r⟩ := s
      exact bfsLoop_eq act gens f _ _ _ _ _ _
    · rfl

theorem bfsCert_eq (act : Array ℕ → Array ℕ → Array ℕ) (gens : Array (Array ℕ))
    (root : Array ℕ) (fuel : ℕ) :
    bfsCert act gens root fuel =
      ⟨(gBfs (fun k x => act gens[k]! x) gens.size akey root fuel).1,
        (gBfs (fun k x => act gens[k]! x) gens.size akey root fuel).2.1,
        (gBfs (fun k x => act gens[k]! x) gens.size akey root fuel).2.2.1,
        (gBfs (fun k x => act gens[k]! x) gens.size akey root fuel).2.2.2⟩ :=
  bfsLoop_eq act gens fuel 0 _ _ _ _ _

theorem bfsCert_spec {act : Array ℕ → Array ℕ → Array ℕ} {gens : Array (Array ℕ)}
    {root : Array ℕ} {fuel : ℕ} (S : Finset (Array ℕ))
    (hS : ∀ x, Reach (fun k x => act gens[k]! x) gens.size root x ↔ x ∈ S)
    (hv : ∀ x ∈ S, PermArr x = true) (hfuel : S.card ≤ fuel) :
    certOK act gens root (bfsCert act gens root fuel) = true ∧
      (∀ x, x ∈ (bfsCert act gens root fuel).pts ↔ x ∈ S) ∧
      (bfsCert act gens root fuel).pts.size = S.card ∧
      ((bfsCert act gens root fuel).pts.toList.map akey).Nodup := by
  have hroot : root ∈ S := (hS root).1 Reach.root
  have hT : ∀ x ∈ S, ∀ k < gens.size, act gens[k]! x ∈ S := fun x hx k hk =>
    (hS _).1 (Reach.step k hk ((hS x).2 hx))
  have hkey : ∀ x ∈ S, ∀ y ∈ S, akey x = akey y → x = y := fun x hx y hy e =>
    akey_inj (hv x hx) (hv y hy) e
  obtain ⟨hpos, h0, hmem, -, -, hr, htree⟩ :=
    gBfs_spec (act := fun k x => act gens[k]! x) (fuel := fuel) hroot hT hkey hfuel
  obtain ⟨hmem', hsize, hnd⟩ := gBfs_listing (fuel := fuel) S hS hkey hfuel
  rw [bfsCert_eq]
  refine ⟨?_, hmem', hsize, hnd⟩
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨hpos, h0⟩, fun i hi => ?_⟩, pairwise_lt_mergeSort hnd⟩
  simp only [pointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hv _ (hmem i hi), (hr i hi).1⟩, fun k hk => (hr i hi).2 k hk⟩, ?_⟩
  rcases Nat.eq_zero_or_pos i with h | h
  · exact Or.inl h
  · obtain ⟨hp, hl, e⟩ := htree i h hi
    exact Or.inr ⟨⟨hp, hl⟩, e⟩

end CFSG.KC.Bfs
