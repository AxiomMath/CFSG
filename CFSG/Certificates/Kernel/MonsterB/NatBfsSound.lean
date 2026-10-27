module

public import CFSG.Certificates.Kernel.MonsterB.BfsCore
public import CFSG.Monster.B.TwoA.Census.NatCert

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census

theorem natBfsLoop_eq (act : ℕ → ℕ → ℕ) (ngen : ℕ) :
    ∀ (f i : ℕ) (pts : Array ℕ) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), natBfsLoop act ngen f i pts edges par lab idx =
        ⟨(gLoop act ngen id f i pts edges par lab idx).1,
          (gLoop act ngen id f i pts edges par lab idx).2.1,
          (gLoop act ngen id f i pts edges par lab idx).2.2.1,
          (gLoop act ngen id f i pts edges par lab idx).2.2.2⟩
  | 0, _, _, _, _, _, _ => rfl
  | f + 1, i, pts, edges, par, lab, idx => by
    rw [natBfsLoop, gLoop]
    split
    · have e : natBfsStep act ngen i (pts, par, lab, idx) = gStep act ngen id i (pts, par, lab, idx) :=
        rfl
      rw [e]
      generalize gStep act ngen id i (pts, par, lab, idx) = s
      obtain ⟨a, b, c, d, r⟩ := s
      exact natBfsLoop_eq act ngen f _ _ _ _ _ _
    · rfl

theorem natBfs_eq (act : ℕ → ℕ → ℕ) (ngen root fuel : ℕ) :
    natBfs act ngen root fuel =
      ⟨(gBfs act ngen id root fuel).1, (gBfs act ngen id root fuel).2.1,
        (gBfs act ngen id root fuel).2.2.1, (gBfs act ngen id root fuel).2.2.2⟩ :=
  natBfsLoop_eq act ngen fuel 0 _ _ _ _ _

theorem natCertOK_gBfs {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root fuel : ℕ}
    {T : Finset ℕ} (hroot : root ∈ T) (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hv : ∀ x ∈ T, valid x = true) (hfuel : T.card ≤ fuel) :
    natCertOK act ngen valid root (natBfs act ngen root fuel) = true := by
  obtain ⟨hpos, h0, hmem, hinj, -, hr, htree⟩ :=
    gBfs_spec (key := id) (fuel := fuel) hroot hT (fun _ _ _ _ e => e) hfuel
  rw [natBfs_eq]
  simp only [natCertOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨hpos, h0⟩, fun i hi => ?_⟩, pairwise_lt_mergeSort ?_⟩
  · simp only [natPointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨hv _ (hmem i hi), (hr i hi).1⟩, fun k hk => (hr i hi).2 k hk⟩, ?_⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inl h
    · obtain ⟨hp, hl, e⟩ := htree i h hi
      exact Or.inr ⟨⟨hp, hl⟩, e⟩
  · simpa using nodup_map_of_inj id hinj

theorem natBfs_spec {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root fuel : ℕ}
    (S : Finset ℕ) (hS : ∀ x, Reach act ngen root x ↔ x ∈ S) (hv : ∀ x ∈ S, valid x = true)
    (hfuel : S.card ≤ fuel) :
    natCertOK act ngen valid root (natBfs act ngen root fuel) = true ∧
      (∀ x, x ∈ (natBfs act ngen root fuel).pts ↔ x ∈ S) ∧
      (natBfs act ngen root fuel).pts.size = S.card ∧
      (natBfs act ngen root fuel).pts.toList.Nodup := by
  have hroot : root ∈ S := (hS root).1 Reach.root
  have hT : ∀ x ∈ S, ∀ k < ngen, act k x ∈ S := fun x hx k hk =>
    (hS _).1 (Reach.step k hk ((hS x).2 hx))
  obtain ⟨hmem, hsize, hnd⟩ := gBfs_listing (key := id) (fuel := fuel) S hS
    (fun _ _ _ _ e => e) hfuel
  refine ⟨natCertOK_gBfs hroot hT hv hfuel, ?_⟩
  rw [natBfs_eq]
  exact ⟨hmem, hsize, by simpa using hnd⟩

end CFSG.KC.Bfs
