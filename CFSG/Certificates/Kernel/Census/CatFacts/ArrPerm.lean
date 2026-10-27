module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen

public section

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.KGroups.Native CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Sporadic.Schreier

variable {n : ℕ}

theorem pairWitnessA_map (C : List (Equiv.Perm (Fin n))) (m : ℕ) :
    pairWitnessA n (C.map toA) m = pairWitness C m := by
  unfold pairWitnessA pairWitness
  simp only [List.any_map, Function.comp_def]
  congr 1
  funext x₁
  congr 1
  funext x₂
  rw [eqA_eq_decide (rep_powA (rep_compA (rep_toA x₁) (rep_toA x₂)) m) (rep_idA (n := n))]

theorem noNilpA_map (LA odd : List (Equiv.Perm (Fin n))) (m : ℕ) :
    noNilpA n (LA.map toA) (odd.map toA) m = noNilpCheck LA odd m := by
  unfold noNilpA noNilpCheck
  simp only [List.all_map, Function.comp_def]
  congr 1
  funext s
  rw [eqA_eq_decide (rep_compA (rep_toA s) (rep_toA s)) (rep_idA (n := n)), List.filter_map]
  have h : odd.filter ((fun x => eqA n (compA n x (toA s)) (compA n (toA s) x)) ∘ toA) =
      odd.filter fun x => decide (x * s = s * x) := by
    congr 1
    funext x
    exact eqA_eq_decide (rep_compA (rep_toA x) (rep_toA s)) (rep_compA (rep_toA s) (rep_toA x))
  rw [h, pairWitnessA_map]

theorem admCheckA_map (LA : List (Equiv.Perm (Fin n))) (QP : RawSchreierDatum n)
    (L5 : List (Equiv.Perm (Fin n))) (s₀ : Equiv.Perm (Fin n)) (cs : List (Equiv.Perm (Fin n))) :
    admCheckA LA QP (L5.map toA) s₀ cs = admCheck LA QP L5 s₀ cs := by
  unfold admCheckA admCheck
  congr 1
  funext s
  have h5 : ((L5.map toA).all fun x => !(eqA n (compA n x (toA s)) (compA n (toA s) x))) =
      L5.all fun x => !(decide (x * s = s * x)) := by
    rw [List.all_map]
    congr 1
    funext x
    simp only [Function.comp_apply]
    rw [eqA_eq_decide (rep_compA (rep_toA x) (rep_toA s)) (rep_compA (rep_toA s) (rep_toA x))]
  simp only
  rw [h5, eqA_eq_decide (rep_compA (rep_toA s) (rep_toA s)) (rep_idA (n := n))]
  generalize decide (s * s = 1) = a
  generalize QP.sift s 0 = b
  generalize cs.any (fun k => decide (k * s₀ * k⁻¹ = s)) = c
  generalize L5.all (fun x => !(decide (x * s = s * x))) = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem filter_toA_pow (L : List (Equiv.Perm (Fin n))) (k : ℕ) :
    (L.map toA).filter (fun a => eqA n (powA n a k) (idA n) && !eqA n a (idA n)) =
      (L.filter fun x => decide (x ^ k = 1) && !decide (x = 1)).map toA := by
  rw [List.filter_map]
  congr 2
  funext x
  simp only [Function.comp_apply]
  rw [eqA_eq_decide (rep_powA (rep_toA x) k) (rep_idA (n := n)),
    eqA_eq_decide (rep_toA x) (rep_idA (n := n))]

theorem filter_toA_pow2 (L : List (Equiv.Perm (Fin n))) (a b : ℕ) :
    (L.map toA).filter (fun x => eqA n (powA n x a) (idA n) || eqA n (powA n x b) (idA n)) =
      (L.filter fun x => decide (x ^ a = 1) || decide (x ^ b = 1)).map toA := by
  rw [List.filter_map]
  congr 2
  funext x
  simp only [Function.comp_apply]
  rw [eqA_eq_decide (rep_powA (rep_toA x) a) (rep_idA (n := n)),
    eqA_eq_decide (rep_powA (rep_toA x) b) (rep_idA (n := n))]

end CFSG.Certificates.Kernel.CatFacts
