module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

section Blocks

variable {n : ℕ} {I : Set ℕ}

theorem exists_other_block (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty) (j : Fin n) :
    ∃ a : Fin n, a ≠ j ∧ 1 ≤ linBlockLen n I a := by
  obtain ⟨i, hi⟩ := hne
  obtain ⟨hi1, hin⟩ := hI i hi
  have h0 : (0 : ℕ) < n := by omega
  have hz := (linBlockLen_spec (I := I) (a := ⟨0, h0⟩) (Or.inl rfl)).2.1
  have hs := (linBlockLen_spec (I := I) (a := ⟨i, hin⟩) (Or.inr hi)).2.1
  by_cases hj : j = ⟨0, h0⟩
  · exact ⟨⟨i, hin⟩, fun h => by
      have := congrArg Fin.val (h.trans hj)
      simp at this
      omega, hs⟩
  · exact ⟨⟨0, h0⟩, fun h => hj h.symm, hz⟩

end Blocks

theorem eq_one_of_scalar_of_single_block {K : Type} [Field K] {n : ℕ} {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty) {j : Fin n}
    (x : ↥(flagStabilizer n K I))
    (hx : (x : SpecialLinearGroup (Fin n) K) ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hj : ∀ a : Fin n, a ≠ j → linLeviHom K n I x a = 1) : x = 1 := by
  obtain ⟨a, haj, ha1⟩ := exists_other_block hI hne j
  have hn : 0 < n := by omega
  have hsc := SpecialLinearGroup.scalar_eq_self_of_mem_center hx ⟨0, hn⟩
  set c : K := ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩
    with hc
  have hblk := congrArg (fun g : GL (Fin (linBlockLen n I a)) K =>
    (g : Matrix (Fin (linBlockLen n I a)) (Fin (linBlockLen n I a)) K) ⟨0, by omega⟩ ⟨0, by omega⟩)
    (hj a haj)
  simp only [coe_linLeviHom_apply, blkAt_apply, Units.val_one, Matrix.one_apply_eq] at hblk
  have hentry : ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ⟨(a : ℕ) + 0, by have := linBlockLen_le (I := I) a; omega⟩
      ⟨(a : ℕ) + 0, by have := linBlockLen_le (I := I) a; omega⟩ = c := by
    have := congrArg (fun A : Matrix (Fin n) (Fin n) K =>
      A ⟨(a : ℕ) + 0, by have := linBlockLen_le (I := I) a; omega⟩
        ⟨(a : ℕ) + 0, by have := linBlockLen_le (I := I) a; omega⟩) hsc
    simp only [scalar_apply, diagonal_apply_eq] at this
    exact this.symm
  have hc1 : c = 1 := hentry.symm.trans hblk
  have hx1 : (x : SpecialLinearGroup (Fin n) K) = 1 := by
    apply Subtype.ext
    rw [← hsc, hc1]
    ext i j
    simp [scalar_apply, diagonal_apply, Matrix.one_apply]
  exact Subtype.ext hx1

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
