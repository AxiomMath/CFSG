module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap CatalogueBOddQuadratic CatalogueBOrthogonalThreeSimilarity

universe u v

variable {K : Type u} [Field K]

@[expose] def planesLineToSelfAdjoint (h2 : (2 : K) ≠ 0) (d : Kˣ) :
    ((Fin 2 → K × K) × (Fin 1 → K)) ≃ₗ[K] selfAdjointSubmodule K :=
  ({ toFun := fun x => ![x.2 0, (x.1 0).1, (x.1 0).2 / (d : K),
        (x.1 1).1, -(x.1 1).2 / (d : K)]
     invFun := fun y => (fun i => if i = 0 then (y 1, (d : K) * y 2)
         else (y 3, -(d : K) * y 4), fun _ => y 0)
     left_inv := by
       intro x
       apply Prod.ext
       · funext i
         fin_cases i
         · apply Prod.ext
           · rfl
           · change (d : K) * ((x.1 0).2 / (d : K)) = (x.1 0).2
             field_simp
         · apply Prod.ext
           · rfl
           · change -(d : K) * (-(x.1 1).2 / (d : K)) = (x.1 1).2
             field_simp
       · funext i
         fin_cases i
         rfl
     right_inv := by
       intro y
       funext i
       fin_cases i
       · rfl
       · rfl
       · change (d : K) * y 2 / (d : K) = y 2
         field_simp
       · rfl
       · change -(-(d : K) * y 4) / (d : K) = y 4
         field_simp
     map_add' := by
       intro x y
       funext i
       fin_cases i <;> simp [add_div]
       ring
     map_smul' := by
       intro a x
       funext i
       fin_cases i <;> simp [smul_eq_mul, mul_div_assoc]
       ring } :
    ((Fin 2 → K × K) × (Fin 1 → K)) ≃ₗ[K] (Fin 5 → K)).trans
      (selfAdjointCoordinates h2)

theorem planesLineToSelfAdjoint_val (h2 : (2 : K) ≠ 0) (d : Kˣ)
    (x : (Fin 2 → K × K) × (Fin 1 → K)) :
    (planesLineToSelfAdjoint h2 d x).val =
      !![x.2 0, (x.1 0).1, 0, (x.1 1).1;
        (x.1 0).2 / (d : K), -x.2 0, -(x.1 1).1, 0;
        0, -(x.1 1).2 / (d : K), x.2 0, (x.1 0).2 / (d : K);
        -(-(x.1 1).2 / (d : K)), 0, (x.1 0).1, -x.2 0] := rfl

theorem planesLineToSelfAdjoint_form (h2 : (2 : K) ≠ 0) (w : Fin 1 → Kˣ)
    (x : (Fin 2 → K × K) × (Fin 1 → K)) :
    ((hyperbolicSumForm K 2).prod (weightedSumSquares K w)) x =
      (w 0 : K) * selfAdjointForm K (planesLineToSelfAdjoint h2 (w 0) x) := by
  rw [QuadraticMap.prod_apply, hyperbolicSumForm_apply, Fin.sum_univ_two,
    weightedSumSquares_apply, Fin.sum_univ_one, selfAdjointForm_apply,
    planesLineToSelfAdjoint_val]
  change (x.1 0).1 * (x.1 0).2 + (x.1 1).1 * (x.1 1).2 +
      (w 0 : K) * (x.2 0 * x.2 0) =
    (w 0 : K) * (x.2 0 * x.2 0 + (x.1 0).1 * ((x.1 0).2 / (w 0 : K)) -
      (x.1 1).1 * (-(x.1 1).2 / (w 0 : K)))
  field_simp
  ring

variable [Finite K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_two_planes_line_isometry (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5) :
    ∃ w : Fin 1 → Kˣ, Nonempty (Q.IsometryEquiv
      ((hyperbolicSumForm K 2).prod (weightedSumSquares K w))) := by
  obtain ⟨m, k, w, hk, _, hrank, he⟩ := exists_hyperbolic_decomposition hodd Q hQ
  have hm : m = 2 := by omega
  have hk' : k = 1 := by omega
  subst m
  subst k
  exact ⟨w, he⟩

theorem exists_selfAdjoint_similarity (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5) :
    ∃ (d : Kˣ) (psi : V ≃ₗ[K] selfAdjointSubmodule K),
      ∀ v, Q v = (d : K) * selfAdjointForm K (psi v) := by
  obtain ⟨w, ⟨e⟩⟩ := exists_two_planes_line_isometry hodd Q hQ hdim
  let h2 := two_ne_zero_of_odd_card hodd
  refine ⟨w 0, e.toLinearEquiv.trans (planesLineToSelfAdjoint h2 (w 0)), ?_⟩
  intro v
  change Q v = (w 0 : K) * selfAdjointForm K (planesLineToSelfAdjoint h2 (w 0) (e v))
  rw [← planesLineToSelfAdjoint_form h2 w (e v), e.map_app]

theorem finite_odd_five_selfAdjoint_form_similarity (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5) :
    ∃ (d : Kˣ) (psi : V ≃ₗ[K] selfAdjointSubmodule K)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)),
      (∀ v, Q v = (d : K) * selfAdjointForm K (psi v)) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : selfAdjointSubmodule K),
        (e g).val X = psi (g.val (psi.symm X))) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) (v : V),
        (e.symm g).val v = psi.symm (g.val (psi v))) := by
  obtain ⟨d, psi, hpsi⟩ := exists_selfAdjoint_similarity hodd Q hQ hdim
  refine ⟨d, psi, similarityOrthogonalEquiv Q (selfAdjointForm K) d psi hpsi,
    hpsi, ?_, ?_⟩
  · exact fun g X => similarityOrthogonalEquiv_apply Q (selfAdjointForm K) d psi hpsi g X
  · exact fun g v => similarityOrthogonalEquiv_symm_apply Q (selfAdjointForm K) d psi hpsi g v

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
