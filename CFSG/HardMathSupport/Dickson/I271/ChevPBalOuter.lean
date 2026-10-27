module

public import CFSG.HardMathSupport.Dickson.I271.Support.OuterCoreFree
public import CFSG.HardMathSupport.Dickson.I271.ChevPBal
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterKData

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

theorem lieType_of_catalogIs {S : Type} [Group S] {p : ℕ}
    (h : catalogIs S (onLie fun d => d.characteristic = p)) :
    ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧ idx.1.characteristic = p := by
  obtain ⟨i, hi, he⟩ := h
  cases i <;> first | exact ⟨_, he, hi⟩ | exact absurd hi (by simp [onLie])

theorem chev204_induction {p : ℕ} (hDC : DefCharInnerCoreFree) (hOut : DefCharOuterCoreFree)
    (hK65 : KD65 p) (hKD : KDChevInner p) (hCent : ChevCentralizerStep) (hCyc : ChevCyclicCase)
    (hAmb : ChevAmbCase) :
    ∀ (n : ℕ) (X : Type) [Group X] [Finite X], Nat.card X = n →
      ∀ K B : Subgroup X, Chev204Hyp p K B → ¬ ChevExc p K B → IsStronglyBalancedIn p B K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ hn K B hH hne
    have ih' : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card X →
        ∀ K' B' : Subgroup Y, Chev204Hyp p K' B' → ¬ ChevExc p K' B' →
          IsStronglyBalancedIn p B' K' :=
      fun Y _ _ hlt K' B' h1 h2 => ih (Nat.card Y) (hn ▸ hlt) Y rfl K' B' h1 h2
    have hp := hH.prime
    rcases hH.chev with hL | hA
    · have hLie : I271LieType (· = p) K := lieType_of_catalogIs hL
      obtain ⟨r, hr⟩ := exists_pow_autOrderIn hp hH.elem hH.norm
      by_cases hr1 : r ≤ 1
      · have hle : autOrderIn B K ≤ p := by
          rw [hr]
          calc p ^ r ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hr1
            _ = p := pow_one p
        rcases hCyc X p K B hH hLie hle with h | h
        · exact h
        · exact absurd h hne
      · have h2 : p ^ 2 ≤ autOrderIn B K := by
          rw [hr]
          exact Nat.pow_le_pow_right hp.pos (by omega)
        obtain ⟨A, hAB, hAnc, hAf⟩ := exists_faithful_noncyclic hp hH.elem hH.norm h2
        by_cases hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)
        · exact chev204_inner hDC hKD hH hLie hAB hAnc hAf hin
        · obtain ⟨a₁, ha₁, hout₁⟩ : ∃ a ∈ A,
              ¬ ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := by
            by_contra hcon
            exact hin fun a ha => by_contra fun h => hcon ⟨a, ha, h⟩
          exact chev204_outer hDC hOut hK65 hKD hCent ih' hH hLie hne hAB hAnc hAf ha₁ hout₁
    · exact hAmb X p K B hH hA hne

theorem i271ChevPBal_of_residuals (hDC : DefCharInnerCoreFree) (hOut : DefCharOuterCoreFree)
    (hK65 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD65 p) (hKD : ∀ p : ℕ, p.Prime → p ≠ 2 → KDChevInner p)
    (hCent : ChevCentralizerStep) (hCyc : ChevCyclicCase) (hAmb : ChevAmbCase) : I271ChevPBal := by
  intro X _ _ _ p K B hH hN _ hLie hExc
  obtain ⟨idx, he, hch⟩ := hLie
  refine chev204_induction hDC hOut (hK65 p hH.prime hH.odd) (hKD p hH.prime hH.odd) hCent hCyc
    hAmb (Nat.card X) X rfl K B
    ⟨hH.prime, hH.odd, hH.core, hH.comp, hH.scp, hN.1, Or.inl ⟨TauCeti.CFSGIndex.lie idx, hch, he⟩⟩
    ?_
  rintro ⟨hp3, hb | hc⟩
  · exact hExc ⟨hp3, hb.1, hb.2⟩
  · subst hp3
    have h9 := hN.2
    rw [hc.2] at h9
    norm_num at h9

theorem i271ChevPBal_of_kdata (hDC : DefCharInnerCoreFree) (hOC : KDOutCoreFree)
    (hOI : KDOutCentInner) (hK65 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD65 p)
    (hKD : ∀ p : ℕ, p.Prime → p ≠ 2 → KDChevInner p)
    (hU : ∀ p : ℕ, p.Prime → p ≠ 2 → KDChevUnique p)
    (hT : ∀ p : ℕ, p.Prime → p ≠ 2 → KDOutChev p) (hE : KDOutExc)
    (hCyc : ChevCyclicCase) (hAmb : ChevAmbCase) : I271ChevPBal :=
  i271ChevPBal_of_residuals hDC (defCharOuterCoreFree_of_kdata hOC hOI) hK65 hKD
    (chevCentralizerStep_of_kdata hU hT hE) hCyc hAmb

end CFSG.HardMathSupport.Dickson.I271
