module

public import CFSG.HardMathSupport.Dickson.Bal207.UniInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Polynomial Matrix CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

theorem uni_finrank_coord {n : ℕ} {F : Type} [Field F] (I : Finset (Fin n))
    (W : Submodule F (Fin n → F)) (hW : ∀ v, v ∈ W ↔ ∀ j ∉ I, v j = 0) :
    Module.finrank F W = I.card := by
  classical
  let r : W →ₗ[F] (I → F) :=
    (LinearMap.pi fun i : I => LinearMap.proj (i : Fin n)).comp W.subtype
  have hr : Function.Bijective r := by
    constructor
    · intro v w hvw
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ I
      · exact congrFun hvw ⟨j, hj⟩
      · rw [(hW v).1 v.2 j hj, (hW w).1 w.2 j hj]
    · intro u
      refine ⟨⟨fun j => if hj : j ∈ I then u ⟨j, hj⟩ else 0, (hW _).2 fun j hj => dif_neg hj⟩, ?_⟩
      funext i
      show (if hj : (i : Fin n) ∈ I then u ⟨i, hj⟩ else 0) = u i
      rw [dif_pos i.2]
  rw [(LinearEquiv.ofBijective r hr).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe]

variable {f n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 f F}

theorem uni_inner_component_good (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (hD3 : D ^ 3 = 1)
    (hD1 : primeFormConjHom h (oneGram F n) D ≠ 1) {L : Subgroup (primeFormP h (oneGram F n))}
    (hL : CFSG.Open.IsComponentOf L (fixSubgroup (primeFormConjHom h (oneGram F n) D))) :
    ∃ I : Finset (Fin n), (∃ j, j ∉ I) ∧ 2 ≤ I.card ∧ (I.card ≤ 3 → f = 3) ∧
      L = (blockSU h I.card).map ((uniTheta h hf hn h3).comp (uniBlk h I)) := by
  classical
  haveI := h.finite
  haveI : Finite (GL (Fin n) F) :=
    Finite.of_injective (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) Units.val_injective
  have hfo : Odd f := by rcases hf with rfl | rfl <;> decide
  have hD3' : (D : GL (Fin n) F) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hD3, Subgroup.coe_one]
  have H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin D) :=
    t6psuh_primaryData_toLin' h D.2 Nat.prime_three (by norm_num) (c := 1)
      (by rw [hD3', map_one])
  obtain ⟨i, hi⟩ := LieComp.component_mem_named_factors
    (fun i : t6psub_Idx h n D => (t6psub_block D i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram F n)) n)))
    (fun i => uni_block_isComponent D H i)
    (fun P hPC hP => uni_perfect_le_blocks D H P hPC (Subgroup.isPerfect_iff.1 ⟨hP⟩)) hL
  obtain ⟨d, hd, hid⟩ := u6r_primaryFactor_eq D hD3' i.1.2
  set I : Finset (Fin n) := Finset.univ.filter
    fun j => ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = d with hIdef
  have hI : ∀ j, j ∈ I ↔ ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = d := fun j => by
    rw [hIdef, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ j)
  have hmult : primaryMultiplicity ((t6psub_toLin D :
      LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) (i.1 : F[X]) =
        I.card := by
    have h1 : Module.finrank F (primaryComponent ((t6psub_toLin D :
        LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) (i.1 : F[X])) =
          (i.1 : F[X]).natDegree * primaryMultiplicity ((t6psub_toLin D :
            LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F))
              (i.1 : F[X]) :=
      finrank_primaryComponent _ _
    rw [hid, natDegree_X_sub_C, one_mul] at h1
    rw [hid, ← h1]
    refine uni_finrank_coord I _ fun v => ?_
    rw [uni_mem_V_iff D hD d v]
    constructor
    · intro hv j hj
      have hj' : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j ≠ d := fun h' =>
        hj ((hI j).2 h')
      have h2 : (((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j - d) * v j = 0 := by
        rw [sub_mul, hv j, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hj')
    · intro hv j
      by_cases hj : j ∈ I
      · rw [(hI j).1 hj]
      · rw [hv j hj, mul_zero, mul_zero]
  have hself : dualPoly h.bar (i.1 : F[X]) = i.1 := by
    rw [hid]
    exact u6r_dualPoly h hfo hd
  have h2 : 2 ≤ I.card := by
    rw [← hmult]
    exact i.2.1
  have hns := i.2.2 hself
  rw [hmult, hid, natDegree_X_sub_C, mul_one] at hns
  refine ⟨I, ?_, h2, fun hle => ?_, hi.trans (uni_map_block_eq hf hn h3 D hD hD3' i hd hid hI)⟩
  · by_contra hall
    push Not at hall
    exact hD1 (uni_conjHom_eq_one_of_const D hD fun j => (hI j).1 (hall j))
  · rcases hf with rfl | rfl
    · exfalso
      apply hns
      rcases (show I.card = 2 ∨ I.card = 3 by omega) with hc | hc <;> simp [hc]
    · rfl

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
