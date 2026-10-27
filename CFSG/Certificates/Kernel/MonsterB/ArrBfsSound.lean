module

public import CFSG.Certificates.Kernel.MonsterB.BfsCore
public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.Fischer

theorem arrBfsLoop_eq (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (key : Array ℕ → ℕ) :
    ∀ (f i : ℕ) (pts : Array (Array ℕ)) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), arrBfsLoop act ngen key f i pts edges par lab idx =
        ⟨(gLoop act ngen key f i pts edges par lab idx).1,
          (gLoop act ngen key f i pts edges par lab idx).2.1,
          (gLoop act ngen key f i pts edges par lab idx).2.2.1,
          (gLoop act ngen key f i pts edges par lab idx).2.2.2⟩
  | 0, _, _, _, _, _, _ => rfl
  | f + 1, i, pts, edges, par, lab, idx => by
    rw [arrBfsLoop, gLoop]
    split
    · have e : arrBfsStep act ngen key i (pts, par, lab, idx) =
          gStep act ngen key i (pts, par, lab, idx) := rfl
      rw [e]
      generalize gStep act ngen key i (pts, par, lab, idx) = s
      obtain ⟨a, b, c, d, r⟩ := s
      exact arrBfsLoop_eq act ngen key f _ _ _ _ _ _
    · rfl

theorem arrBfs_eq (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (key : Array ℕ → ℕ)
    (root : Array ℕ) (fuel : ℕ) :
    arrBfs act ngen key root fuel =
      ⟨(gBfs act ngen key root fuel).1, (gBfs act ngen key root fuel).2.1,
        (gBfs act ngen key root fuel).2.2.1, (gBfs act ngen key root fuel).2.2.2⟩ :=
  arrBfsLoop_eq act ngen key fuel 0 _ _ _ _ _

theorem arrBfs_spec {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ} {valid : Array ℕ → Bool}
    {key : Array ℕ → ℕ} {root : Array ℕ} {fuel : ℕ} (S : Finset (Array ℕ))
    (hS : ∀ x, Reach act ngen root x ↔ x ∈ S) (hv : ∀ x ∈ S, valid x = true)
    (hkey : ∀ x ∈ S, ∀ y ∈ S, key x = key y → x = y) (hfuel : S.card ≤ fuel) :
    arrCertOK act ngen valid key root (arrBfs act ngen key root fuel) = true ∧
      (∀ x, x ∈ (arrBfs act ngen key root fuel).pts ↔ x ∈ S) ∧
      (arrBfs act ngen key root fuel).pts.size = S.card ∧
      ((arrBfs act ngen key root fuel).pts.toList.map key).Nodup := by
  have hroot : root ∈ S := (hS root).1 Reach.root
  have hT : ∀ x ∈ S, ∀ k < ngen, act k x ∈ S := fun x hx k hk =>
    (hS _).1 (Reach.step k hk ((hS x).2 hx))
  obtain ⟨hpos, h0, hmem, -, -, hr, htree⟩ := gBfs_spec (fuel := fuel) hroot hT hkey hfuel
  obtain ⟨hmem', hsize, hnd⟩ := gBfs_listing (fuel := fuel) S hS hkey hfuel
  rw [arrBfs_eq]
  refine ⟨?_, hmem', hsize, hnd⟩
  simp only [arrCertOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨hpos, h0⟩, fun i hi => ?_⟩, pairwise_lt_mergeSort hnd⟩
  simp only [arrPointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hv _ (hmem i hi), (hr i hi).1⟩, fun k hk => (hr i hi).2 k hk⟩, ?_⟩
  rcases Nat.eq_zero_or_pos i with h | h
  · exact Or.inl h
  · obtain ⟨hp, hl, e⟩ := htree i h hi
    exact Or.inr ⟨⟨hp, hl⟩, e⟩

end CFSG.KC.Bfs
