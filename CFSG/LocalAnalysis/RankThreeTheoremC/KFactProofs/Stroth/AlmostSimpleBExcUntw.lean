module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcAbs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcVal
public import CFSG.LieType.SeitzGeneration.ExcParabolicCard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.KFU

section


theorem noSylowNormalizesTwo_adjoint_of_parabolic (τ : Tag) {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ}
    (hpar : ∀ J : Set (Fin τ.rank), J ≠ Set.univ →
      ¬ p ^ (Nat.card (adjointGroup τ K)).factorization p ∣ Nat.card (parabolicSubgroup τ K J)) :
    NoSylowNormalizesTwo p (adjointGroup τ K) := by
  intro R E hR hR2 hE hdvd
  obtain ⟨J, hJ, hdvdJ⟩ := card_dvd_parabolic_of_normalizes τ hR hR2 hE
  exact hpar J hJ (hdvd.trans hdvdJ)

theorem card_parabolicSubgroup_eq (τ : Tag) {K : Type} [Field K] [Finite K]
    [Fintype (WeylGroup τ)] (J : Set (Fin τ.rank)) :
    Nat.card (parabolicSubgroup τ K J) = Nat.card (torusGroup τ K) *
      Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard *
        parabolicSum τ J (Nat.card K) := by
  obtain ⟨-, -, -, -, -, -, hcell⟩ := standard_parabolic_cells τ K
  rw [hcell J, finsum_parabolicWeylGroup_eq]

theorem factorization_card_parabolicSubgroup (τ : Tag) {K : Type} [Field K] [Finite K]
    [Fintype (WeylGroup τ)] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (J : Set (Fin τ.rank)) :
    (Nat.card (parabolicSubgroup τ K J)).factorization p =
      (Nat.card (torusGroup τ K)).factorization p + (parabolicSum τ J (Nat.card K)).factorization p := by
  have hfin : Finite (ModGL τ K) := finite_modGL
  have hH : Nat.card (torusGroup τ K) ≠ 0 := Nat.card_pos.ne'
  have hq : Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard ≠ 0 :=
    pow_ne_zero _ Nat.card_pos.ne'
  have hS : parabolicSum τ J (Nat.card K) ≠ 0 := (parabolicSum_pos J Nat.card_pos).ne'
  rw [card_parabolicSubgroup_eq, Nat.factorization_mul (mul_ne_zero hH hq) hS,
    Nat.factorization_mul hH hq, Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd hpK]
  simp

theorem noSylowNormalizesTwo_adjoint_of_chains (τ : Tag) {K : Type} [Field K] [Finite K]
    [CharP K 2] [Fintype (WeylGroup τ)] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (fsI : List (ℕ × ℕ))
    (hfull : ∀ q, parabolicSum τ Set.univ q = (fsI.map fun f => geomSum f.1 f.2 q).prod)
    (coat : Fin τ.rank → ℕ) (fsC : Fin τ.rank → List (ℕ × ℕ))
    (hcov : ∀ i k : Fin τ.rank, k ≠ i → k ∈ maskSet τ (coat i))
    (hC : ∀ i q, parabolicSum τ (maskSet τ (coat i)) q =
      ((fsC i).map fun f => geomSum f.1 f.2 q).prod)
    (hGI : GoodFactors p e fsI) (hGC : ∀ i, GoodFactors p e (fsC i))
    (hcnt : ∀ i, cntFactors e (fsC i) < cntFactors e fsI) :
    NoSylowNormalizesTwo p (adjointGroup τ K) := by
  classical
  haveI hfin : Finite (ModGL τ K) := finite_modGL
  refine noSylowNormalizesTwo_adjoint_of_parabolic τ fun J hJ hdvd => ?_
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hsub : J ⊆ ((maskSet τ (coat i) : Finset (Fin τ.rank)) : Set (Fin τ.rank)) := fun k hk => by
    exact_mod_cast hcov i k (fun h => hi (h ▸ hk))
  have hle : parabolicSubgroup τ K J ≤ parabolicSubgroup τ K ((maskSet τ (coat i) : Finset (Fin τ.rank)) : Set (Fin τ.rank)) :=
    ((standard_parabolic_cells τ K).2.2.2.1 J _).2 hsub
  have hdvd' : p ^ (Nat.card (adjointGroup τ K)).factorization p ∣
      Nat.card (parabolicSubgroup τ K ((maskSet τ (coat i) : Finset (Fin τ.rank)) : Set (Fin τ.rank))) :=
    hdvd.trans (Subgroup.card_dvd_of_le hle)
  have hval := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd'
  have hAdj : adjointGroup τ K = parabolicSubgroup τ K Set.univ :=
    ((standard_parabolic_cells τ K).2.2.2.2.2.1).symm
  rw [hAdj, factorization_card_parabolicSubgroup τ hp hpK,
    factorization_card_parabolicSubgroup τ hp hpK] at hval
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hlt := factorization_prod_lt_of_cnt_lt hp hp2 hpK hq2 he (hGC i) hGI (hcnt i)
  rw [← hC i, ← hfull] at hlt
  omega

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
