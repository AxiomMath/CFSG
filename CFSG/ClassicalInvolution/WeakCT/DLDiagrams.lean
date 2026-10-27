module

public import CFSG.ClassicalInvolution.WeakCT.Tree

public section

namespace CFSG.ClassicalInvolution.WeakCT

theorem LinearBlockStandardPair.symm {K : Type} [Field K] {X : Type} [Group X]
    {W U V : Subgroup X} (h : LinearBlockStandardPair K W U V) :
    LinearBlockStandardPair K W V U := by
  obtain ⟨θ, c, h1, h2, h3⟩ := h
  exact ⟨θ, c, h1, h2, h3.symm⟩

abbrev edgeUp (n : ℕ) (i j : Fin n) : Prop := i.val + 1 = j.val

abbrev edgeDown (n : ℕ) (i j : Fin n) : Prop := j.val + 1 = i.val

@[expose] def parentUp (n : ℕ) (k : Fin n) : Fin n := ⟨k.val - 1, by have := k.2; omega⟩

@[expose] def parentDown (n : ℕ) (k : Fin n) : Fin n :=
  ⟨min (k.val + 1) (n - 1), by have := k.2; omega⟩

@[expose] def depthDown (n : ℕ) (k : Fin n) : ℕ := n - 1 - k.val

theorem rootedTree_edgeUp {n : ℕ} (hn : 0 < n) :
    RootedTree (edgeUp n) (parentUp n) (fun k => k.val) ⟨0, hn⟩ := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun i j hij hji => ?_, fun i j hij => ?_⟩
  · have h1 : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp only [parentUp]
    omega
  · have h1 : k.val ≠ 0 := fun h => hk (Fin.ext h)
    left
    simp only [edgeUp, parentUp]
    omega
  · simp only [edgeUp] at hij hji
    omega
  · simp only [edgeUp] at hij
    left
    refine ⟨fun h => ?_, Fin.ext ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · simp only [parentUp]
      omega

theorem rootedTree_edgeDown {n : ℕ} (hn : 0 < n) :
    RootedTree (edgeDown n) (parentDown n) (depthDown n) ⟨n - 1, by omega⟩ := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun i j hij hji => ?_, fun i j hij => ?_⟩
  · have h1 : k.val ≠ n - 1 := fun h => hk (Fin.ext h)
    have h2 := k.2
    simp only [parentDown, depthDown]
    omega
  · have h1 : k.val ≠ n - 1 := fun h => hk (Fin.ext h)
    have h2 := k.2
    left
    simp only [edgeDown, parentDown]
    omega
  · simp only [edgeDown] at hij hji
    omega
  · simp only [edgeDown] at hij
    have h2 := i.2
    left
    refine ⟨fun h => ?_, Fin.ext ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · simp only [parentDown]
      omega

end CFSG.ClassicalInvolution.WeakCT
