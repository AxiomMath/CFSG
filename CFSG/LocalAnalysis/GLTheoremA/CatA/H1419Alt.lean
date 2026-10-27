module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419Lie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419AltArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.K1419 (PQ I1419UpAltFact)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (IsL3Kind)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char (isL3Kind_quot isL3Kind_finite card_alt)

@[expose] def I1419L3Order20160NotA8 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsL3Kind 2 H → Nat.card (H ⧸ Subgroup.center H) = 20160 →
    Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 8)) → False

theorem alt_of_L3Order4NotA8 (hA8 : I1419L3Order20160NotA8) : I1419UpAltFact := by
  intro Q _ _ β J hQ hCat _ hβ3 _ hJ hcat
  obtain ⟨β', J', hβ'3, hJ', ⟨eJ⟩⟩ := transfer_pSimple β hβ3 hJ
  obtain ⟨i, hi, ⟨eS⟩⟩ := hCat
  cases i with
  | cyclic _ _ => simp [isAltIndex] at hi
  | alternating n hn =>
    have hS : IsSimpleGroup (PQ Q ⧸ Subgroup.center (PQ Q)) := hQ.2
    have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian (PQ Q) hQ
    obtain ⟨hI, ⟨eI⟩⟩ := chevQ_transport Nat.prime_three eS hJ'
    have hα3 : (MulAut.congr eS β') ^ 3 = 1 := by rw [← map_pow, hβ'3, map_one]
    have key : ∃ m : ℕ, 5 ≤ m ∧ Nonempty (PSimple 3 J ≃* alternatingGroup (Fin m)) := by
      by_cases hα1 : MulAut.congr eS β' = 1
      ·
        have htop : fixSubgroup (1 : MulAut (alternatingGroup (Fin n))) = ⊤ := by
          ext h
          simp [mem_fixSubgroup]
        rw [hα1, htop] at hI
        have hna' : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
          obtain ⟨a, b, hab⟩ := hna
          exact ⟨eS a, eS b, fun h => hab (eS.injective (by rw [map_mul, map_mul]; exact h))⟩
        haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
          alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
        obtain ⟨e1⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna' hI
        exact ⟨n, hn, ⟨eJ.trans (eI.trans e1)⟩⟩
      ·
        obtain ⟨m, hm, -, ⟨f⟩⟩ :=
          kdAltDown_holds n 3 hn Nat.prime_three (by norm_num) _ hα3 hα1 _ hI
        exact ⟨m, (le_max_left 5 3).trans hm, ⟨eJ.trans (eI.trans f)⟩⟩
    obtain ⟨m, hm, ⟨f⟩⟩ := key
    obtain ⟨H, hH, hL3, ⟨eH⟩⟩ := l3u3_exists_L3Kind hcat
    haveI : Finite H := isL3Kind_finite 2 H hL3
    have hcard : Nat.card (H ⧸ Subgroup.center H) = m.factorial / 2 := by
      rw [Nat.card_congr eH.toEquiv, Nat.card_congr f.toEquiv, card_alt m (by omega)]
    have h2n : 2 * Nat.card (H ⧸ Subgroup.center H) = m.factorial := by
      rw [hcard]
      exact Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) (by omega))
    rcases isL3Kind_quot 2 Nat.prime_two H hL3 with h1 | ⟨s, hs⟩
    · exfalso
      have h120 : Nat.factorial 5 ≤ Nat.factorial m := Nat.factorial_le hm
      rw [hcard] at h1
      norm_num [Nat.factorial] at h120
      omega
    · obtain ⟨-, hm8, hn20160⟩ := l3Order_factorial hm h2n hs
      subst hm8
      exact hA8 H hL3 hn20160 ⟨eH.trans f⟩
  | sporadic _ => simp [isAltIndex] at hi
  | lie _ => simp [isAltIndex] at hi

end CFSG.LocalAnalysis.GLTheoremA.H1419
