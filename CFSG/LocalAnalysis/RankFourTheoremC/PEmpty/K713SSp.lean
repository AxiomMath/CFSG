module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SCatalog
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem outLift_statedProj_sp {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {p f r : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    [Finite (StatedProj (StatedSp r K))] (hK : Nat.card K = p ^ f) :
    OutLift ℓ (StatedProj (StatedSp r K)) := by
  obtain ⟨-, -, hDF, hDFE, -, hDn, -, hE, hrel, -⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hp hf hr hK
  obtain ⟨hID, -⟩ := standard_outer_quotient (K := K) (r := r) (by omega)
  haveI := hDn
  have h2 : ¬ ℓ ∣ 2 := fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
  refine outLift_of_chain hℓ (D := spLinearAutGroup r K) (F := (fieldAut r K).range) hID
    (by rw [inf_comm]; exact hDF) (fun h => h2 (h.trans (hrel.trans (Nat.gcd_dvd_left _ _)))) ?_
  rw [hDFE]
  exact fun h => h2 (h.trans hE)

theorem liftClause_classical_PSp {n p f : ℕ} :
    FamilyLift fun S _ => StatedClassicalModel S .PSp n p f := by
  intro S _ _ _ hnonab h ℓ hℓ hℓ2 hSℓ
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv S e.toEquiv
  exact OutLift.of_mulEquiv e (outLift_statedProj_sp hℓ hℓ2 hp hf hn hK)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
