module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

set_option maxRecDepth 100000

@[expose] def e6d4t2IsSingle (b : Fin Tag.E6.rank → ℤ) (s : Fin Tag.E6.rank) : Bool :=
  (List.finRange Tag.E6.rank).all fun t => b t == (Pi.single s 1 : Fin Tag.E6.rank → ℤ) t

@[expose] def e6d4t2FixPair (b₀ b₅ : Fin Tag.E6.rank → ℤ) : Bool :=
  d4t2outGram 1 b₀ 0 && d4t2outGram 1 b₅ 5 && iform b₀ b₅ == 0 &&
    (List.finRange Tag.E6.rank).all fun t =>
      (d4t2outVec 1 b₀ b₅ t - d4t2outZeta t) % 3 == 0

@[expose] def e6d4t2FixCheck : Bool :=
  (List.range e6Certificate.roots.length).all fun k =>
    (List.range e6Certificate.roots.length).all fun m =>
      !e6d4t2FixPair (e6Certificate.root k) (e6Certificate.root m) ||
        (e6d4t2IsSingle (e6Certificate.root k) 0 && e6d4t2IsSingle (e6Certificate.root m) 5)

theorem e6d4t2FixCheck_eq : e6d4t2FixCheck = true := by decide +kernel

theorem e6d4t2_isSingle_eq {b : Fin Tag.E6.rank → ℤ} {s : Fin Tag.E6.rank}
    (h : e6d4t2IsSingle b s = true) : b = Pi.single s 1 := by
  funext t
  have := (List.all_eq_true.1 h) t (List.mem_finRange t)
  simpa using this

section Centralizer

theorem e6d4t2_centralizer_trivial {x : WeylGroup Tag.E6}
    (hx : ∀ j ∈ d4Set Tag.E6, x • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1) :
    x = 1 := by
  obtain ⟨k, hk, hkb⟩ := RootCertificate.exists_root_eq e6Certificate_check
    (IsRoot.smul (IsRoot.basis (0 : Fin Tag.E6.rank)) x)
  obtain ⟨m, hm, hmb⟩ := RootCertificate.exists_root_eq e6Certificate_check
    (IsRoot.smul (IsRoot.basis (5 : Fin Tag.E6.rank)) x)
  have hJ : ∀ j ∈ ([1, 2, 3, 4] : List (Fin Tag.E6.rank)), j ∈ d4Set Tag.E6 := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hgram : ∀ i : Fin Tag.E6.rank, d4t2outGram 1 (x • Pi.single i 1) i = true := fun i =>
    List.all_eq_true.2 fun j hj => beq_iff_eq.2 (by
      have h1 : iform (x • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) (Pi.single j 1) =
          iform (Pi.single i 1) (Pi.single j 1) := by
        calc iform (x • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) (Pi.single j 1) =
            iform (x • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
              (x • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by rw [hx j (hJ j hj)]
          _ = _ := iform_smul _ _ _
      simpa using h1)
  have hvec : x • d4t2outZeta =
      d4t2outVec 1 (x • Pi.single 0 1) (x • Pi.single 5 1) := by
    rw [d4t2outZeta_eq]
    simp only [smul_add, smul_comm x (_ : ℤ)]
    rw [hx 1 ⟨by decide, by decide⟩, hx 2 ⟨by decide, by decide⟩, hx 3 ⟨by decide, by decide⟩,
      hx 4 ⟨by decide, by decide⟩]
    rfl
  have hpair : e6d4t2FixPair (x • Pi.single 0 1) (x • Pi.single 5 1) = true := by
    simp only [e6d4t2FixPair, Bool.and_eq_true]
    refine ⟨⟨⟨hgram 0, hgram 5⟩, beq_iff_eq.2 ?_⟩, List.all_eq_true.2 fun t _ => ?_⟩
    · rw [iform_smul]
      decide +kernel
    · refine beq_iff_eq.2 (Int.emod_eq_zero_of_dvd ?_)
      have := d4t2out_smul_zeta x t
      rwa [hvec] at this
  have hc := e6d4t2FixCheck_eq
  rw [e6d4t2FixCheck, List.all_eq_true] at hc
  have hc1 := hc k (List.mem_range.2 hk)
  rw [List.all_eq_true] at hc1
  have hc2 := hc1 m (List.mem_range.2 hm)
  rw [hkb, hmb, hpair] at hc2
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hc2
  have h0 : x • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 :=
    e6d4t2_isSingle_eq hc2.1
  have h5 : x • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = Pi.single 5 1 :=
    e6d4t2_isSingle_eq hc2.2
  refine CFSG.RankThree.E6.eq_of_smul_single_eq fun j => ?_
  rw [one_smul]
  by_cases hj0 : j = 0
  · rw [hj0]; exact h0
  by_cases hj5 : j = 5
  · rw [hj5]; exact h5
  exact hx j ⟨by
    have : j ≠ 0 := hj0
    have h6 : j.val < 6 := j.2
    have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    omega, by
    have h6 : j.val < 6 := j.2
    have : j.val ≠ 5 := fun h => hj5 (Fin.ext h)
    omega⟩

end Centralizer

end CFSG.LocalAnalysis.GLTheoremA.T158

end
