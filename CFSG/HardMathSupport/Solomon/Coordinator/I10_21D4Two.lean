module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21D4
public import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
public import Certificates.Certificate13502

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Open (IsElemAbelian StatedClassicalModel)

theorem i1021_rep_powArr {t : Array ℕ} {g : Equiv.Perm (Fin 360)} (h : Rep 360 t g) :
    ∀ k, Rep 360 (powArr t k) (g ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [pow_succ']
    exact rep_compA h (i1021_rep_powArr h k)

theorem i1021_rep_foldr :
    ∀ (L : List (Array ℕ × Equiv.Perm (Fin 360))), (∀ p ∈ L, Rep 360 p.1 p.2) →
      Rep 360 ((L.map Prod.fst).foldr (compA 360) (idA 360)) (L.map Prod.snd).prod
  | [], _ => by
    simpa using rep_idA
  | p :: L, h => by
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    exact rep_compA (h p (by simp)) (i1021_rep_foldr L fun q hq => h q (by simp [hq]))

theorem i1021_d4Word_letters (i : Fin 4) : lettersOK 17 (i1021D4Word i) = true := by
  fin_cases i <;> decide

@[expose] noncomputable def i1021D4Perm (i : Fin 4) : Equiv.Perm (Fin 360) :=
  permOfArr 360 (i1021D4Arr i)

theorem i1021_d4Perm_spec (i : Fin 4) :
    Rep 360 (i1021D4Arr i) (i1021D4Perm i) ∧ i1021D4Perm i ∈ omegaT :=
  omegaW_spec (i1021_d4Word_letters i)

theorem i1021_omegaT_two_rank_four :
    ∃ E : Subgroup (Equiv.Perm (Fin 360)), E ≤ omegaT ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ 4 := by
  obtain ⟨hsq, hcomm, hker⟩ := Certificates.certificate13502
  have hsq' : ∀ i, i1021D4Perm i ^ 2 = 1 := fun i => by
    rw [pow_two]
    exact eq_of_eqA (rep_compA (i1021_d4Perm_spec i).1 (i1021_d4Perm_spec i).1) rep_idA (hsq i)
  have hcomm' : ∀ i j, Commute (i1021D4Perm i) (i1021D4Perm j) := fun i j =>
    eq_of_eqA (rep_compA (i1021_d4Perm_spec i).1 (i1021_d4Perm_spec j).1)
      (rep_compA (i1021_d4Perm_spec j).1 (i1021_d4Perm_spec i).1) (hcomm i j)
  have hker' : ∀ a : Fin 4 → Fin 2, a ≠ 0 →
      (List.ofFn fun i => i1021D4Perm i ^ (a i : ℕ)).prod ≠ 1 := by
    intro a ha hprod
    have hrep := i1021_rep_foldr (List.ofFn fun i =>
      (powArr (i1021D4Arr i) (a i : ℕ), i1021D4Perm i ^ (a i : ℕ))) (by
        intro p hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
        exact i1021_rep_powArr (i1021_d4Perm_spec i).1 _)
    simp only [List.map_ofFn, Function.comp_def] at hrep
    have := (eqA_iff hrep rep_idA).2 (by rw [hprod])
    have h2 := hker a ha
    unfold i1021D4Prod at h2
    rw [this] at h2
    exact absurd h2 (by simp)
  obtain ⟨η, -, -, -, -, hcard⟩ := Sporadic.GLQ.exists_elemAbelian_two i1021D4Perm hsq' hcomm' hker'
  refine ⟨Subgroup.closure (Set.range i1021D4Perm), ?_, ?_, hcard⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact (i1021_d4Perm_spec i).2
  · refine i1020_isElemAbelian_closure ?_ ?_
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hcomm' i j
    · rintro _ ⟨i, rfl⟩
      exact hsq' i

theorem i1021_d4_two_rank_four
    {F : Type} [Group F] (h : StatedClassicalModel F .POmegaPlus 4 2 1) :
    ∃ V : Subgroup F, IsElemAbelian 2 V ∧ Nat.card V = 2 ^ 4 := by
  have hLie : CFSG.Blueprint.LieModel F .POmegaPlus 4 2 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], h⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_omegaT hLie
  obtain ⟨E, hEΩ, hE, hEc⟩ := i1021_omegaT_two_rank_four
  refine ⟨(E.subgroupOf omegaT).map φ.symm.toMonoidHom, ?_, ?_⟩
  · refine CFSG.SectionRank.isElemAbelian_map ?_ _
    exact i1021_isElemAbelian_subgroupOf hE omegaT
  · rw [Subgroup.card_map_of_injective φ.symm.injective,
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΩ).toEquiv), hEc]

end CFSG.HardMathSupport.Solomon.Coordinator
