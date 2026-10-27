module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F2G
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCanon
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCyc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InnRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Assembly CFSG.StandardType

@[expose] def OutRankP (lab : GLALabel) (p : ℕ) : CFSG.Assembly.LargeEvenRawCont := fun R _ I _ =>
  IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → ∀ E : Subgroup (MulAut R), IsElemAbelian p E →
    Nat.card E ≤
      Nat.card ↥(E ⊓ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R))) *
        p ^ outBonus107 lab p

theorem coprime_fieldDeg_of_outBonus {lab : GLALabel} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hb : outBonus107 lab p = 0) : Nat.Coprime p (FP.fieldDeg lab) := by
  have hn : ¬ p ∣ lab.n := by
    intro h
    simp [outBonus107, h] at hb
  have h3 : ¬ (p = 3 ∧ lab.tag = LargeEvenLieTag.triD4) := by
    rintro ⟨rfl, ht⟩
    simp [outBonus107, ht] at hb
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  unfold FP.fieldDeg
  split
  all_goals first
    | exact hn
    | exact fun h => ((Nat.Prime.dvd_mul hp).mp h).elim h2 hn
    | (rename_i ht; exact fun h => ((Nat.Prime.dvd_mul hp).mp h).elim
        (fun h' => h3 ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h', ht⟩) hn)

theorem outRankP_of_notD4
    {lab : GLALabel} (hlab : GLAInLambda2 lab) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hD : ¬ (lab.tag = LargeEvenLieTag.D ∧ lab.rank = 4 ∧ p = 3)) :
    Rk2LabelAll lab (OutRankP lab p) := by
  have h := ((((FP.canonOddAut hp hp2 hlab hD).and (FP.canonRawPCyclic hp hp2 hlab hD)).and
    (FP.canonFieldDeg hlab)).and (FP.canonFieldCyc hlab)).and
    (rk2_rawDatum_finite hlab : MI.CAll lab fun R _ _ _ => Finite R)
  refine MI.CAll.mono ?_ h
  rintro R _ I F ⟨⟨⟨⟨hOdd, hCyc⟩, hDeg⟩, ⟨f₀, hf₀⟩⟩, hfin⟩ hs hna E hE
  haveI := hfin
  haveI : Finite (MulAut R) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨J, S, hJI, hJS, hN, hcycS, hpS⟩ := hCyc hs hna
  have hE1 : ∀ e ∈ E, e ^ p = 1 := hE.2
  have hES : E ≤ S := fun e he => hpS e ⟨1, by rw [pow_one]; exact hE1 e he⟩
  have hJcl : J ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) := by
    intro x hx
    apply Subgroup.subset_closure
    left
    rw [← hJI]
    exact hx
  by_cases hb : outBonus107 lab p = 0
  · have hdec : ∀ e ∈ E, ∃ u ∈ J, ∃ f : MulAut R, f ^ FP.fieldDeg lab = 1 ∧ e = u * f := by
      intro e he
      obtain ⟨u, hu, f, hf, rfl⟩ := hOdd hs hna e (hE1 e he)
      refine ⟨u, by rw [← SetLike.mem_coe, hJI]; exact hu, f, ?_, rfl⟩
      exact OR107.pow_eq_one_of_mem_closure hf₀
        (fun g hg => orderOf_dvd_iff_pow_eq_one.mp (hDeg g hg)) hf
    have hEJ : E ≤ J := OR107.le_of_forall_eq_mul (coprime_fieldDeg_of_outBonus hp hp2 hb) hJS hN
      (OR107.commutator_mem_of_cyclic hN hcycS) hES hE1 hdec
    rw [hb, pow_zero, mul_one, inf_eq_left.mpr (hEJ.trans hJcl)]
  · have hb1 : 1 ≤ outBonus107 lab p := Nat.one_le_iff_ne_zero.mpr hb
    calc Nat.card E ≤ Nat.card ↥(E ⊓ J) * p :=
          OR107.card_le_card_inf_mul_of_cyclic hp hN hcycS hES hE1
      _ ≤ Nat.card ↥(E ⊓ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R))) *
          p ^ outBonus107 lab p := by
        apply Nat.mul_le_mul (Subgroup.card_le_of_le (inf_le_inf_left _ hJcl))
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ outBonus107 lab p := Nat.pow_le_pow_right hp.pos hb1

end CFSG.LocalAnalysis.GLTheoremA
