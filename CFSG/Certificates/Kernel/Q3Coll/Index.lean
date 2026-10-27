module

public import CFSG.ClassicalInvolution.Q3.Q3VCollFast
public import CFSG.ClassicalInvolution.Q3.Q3TWCollB
public import CFSG.ClassicalInvolution.Q3.Q3TWCollTD
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

namespace CFSG.KC.Q3Coll

open CFSG.CosetTable CFSG.Certificates CFSG.KC.MiscCoset CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3Z

variable {m : ℕ}

theorem genSub_eq_top {ws : List (List (Fin m × Bool))} (hm : m < 256) {T : List (Fin m)}
    (h : KB.TableFact m (ws.map encW) (T.map fun x => [(x.val, true)]) 1) :
    genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T = ⊤ := by
  obtain ⟨hfi, hidx⟩ := TableFact.genSub_index ws hm T h
  have := hfi.index_ne_zero
  exact Subgroup.index_eq_one.mp (by omega)

theorem comm_of_genSub_eq_top {ws : List (List (Fin m × Bool))} {T : List (Fin m)}
    (htop : genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T = ⊤)
    (hc : ∀ a ∈ T, ∀ b ∈ T, Commute (PresentedGroup.of a : PG m ws) (PresentedGroup.of b))
    (a b : PG m ws) : a * b = b * a := by
  set gens : Set (PG m ws) := (fun x => PresentedGroup.of x) '' {x | x ∈ T}
  have hgc : gens.Pairwise Commute := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
    exact hc x hx y hy
  have hmem : ∀ c : PG m ws, c ∈ Subgroup.centralizer (Subgroup.centralizer gens) := by
    intro c
    have : c ∈ Subgroup.closure gens := by
      change c ∈ genSub _ T
      rw [htop]
      exact Subgroup.mem_top c
    exact Subgroup.closure_le_centralizer_centralizer gens this
  exact Set.centralizer_centralizer_comm_of_comm hgc a (hmem a) b (hmem b)

theorem commute_of_commOK {ws : List (List (Fin m × Bool))} {S : List ℕ}
    (hcomm : Q3TW.commOK ws S = true) :
    ∀ a ∈ subsetOf m S, ∀ b ∈ subsetOf m S,
      Commute (PresentedGroup.of a : PG m ws) (PresentedGroup.of b) := by
  intro a ha b hb
  have hab' := List.all_eq_true.mp (List.all_eq_true.mp hcomm a ha) b hb
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hab'
  rcases hab' with (rfl | h1) | h1
  · exact Commute.refl _
  · exact Q3TW.commute_of_commRel a b h1
  · exact (Q3TW.commute_of_commRel b a h1).symm

theorem eq_one_of_table {ws : List (List (Fin m × Bool))} (hm : m < 256) {S : List ℕ}
    {cs : Fin m → List (ℕ × ℤ)}
    (h : KB.TableFact m (ws.map encW) ((subsetOf m S).map fun x => [(x.val, true)]) 1)
    (hcomm : Q3TW.commOK ws S = true) (hlat : Q3TW.latticeOK cs ws = true) {G : Type} [Group G]
    (g : Fin m → G) (hg : RelsHold g ws) (i : Fin m) : g i = 1 := by
  let _ : CommGroup (PG m ws) := { (inferInstance : Group (PG m ws)) with
    mul_comm := comm_of_genSub_eq_top (genSub_eq_top hm h) (commute_of_commOK hcomm) }
  have hone : ∀ j, (PresentedGroup.of j : PG m ws) = 1 := fun j =>
    Q3TW.eq_one_of_lattice (fun j => (PresentedGroup.of j : PG m ws)) (Q3TW.relsHold_of ws) hlat j
  obtain ⟨f, hf⟩ := exists_hom_of_relsHold ws g hg
  rw [← hf i, hone i, map_one]

theorem b3Collapse_of_tables (h : ∀ k : Fin 24, gluingComplete k = false →
    KB.TableFact 12 ((Q3TW.b3aWords k).map encW)
      ((subsetOf 12 (Q3TW.b3CollSet k)).map fun x => [(x.val, true)]) 1) : Q3TW.B3Collapse := by
  intro k hk G _ g hg i
  exact eq_one_of_table (by norm_num) (h k hk)
    ((Q3TW.b3CollCommOK k).resolve_left (by simp [hk])) (Q3TW.b3CollLatticeOK k) g hg i

theorem td4Collapse_of_tables (h : ∀ k : Fin 24, gluingComplete k = false →
    KB.TableFact 16 ((Q3TW.td4aWords k).map encW)
      ((subsetOf 16 (Q3TW.td4CollSet k)).map fun x => [(x.val, true)]) 1) : Q3TW.TD4Collapse := by
  intro k hk G _ g hg i
  exact eq_one_of_table (by norm_num) (h k hk)
    ((Q3TW.td4CollCommOK k).resolve_left (by simp [hk])) (Q3TW.td4CollLatticeOK k) g hg i

theorem v6Collapse_of_tables (h : ∀ k : Fin 24, gluingComplete k = false →
    KB.TableFact 12 ((v6aWords k).map encW)
      ((subsetOf 12 (Q3V.collSet k)).map fun x => [(x.val, true)]) 1) : V6Collapse := by
  intro k hk G _ g hg i
  have hcomm := (Q3V.collCommOK k).resolve_left (by simp [hk])
  have hc : ∀ a ∈ subsetOf 12 (Q3V.collSet k), ∀ b ∈ subsetOf 12 (Q3V.collSet k),
      Commute (PresentedGroup.of a : PG 12 (v6aWords k)) (PresentedGroup.of b) := by
    intro a ha b hb
    have hab' := List.all_eq_true.mp (List.all_eq_true.mp hcomm a ha) b hb
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hab'
    rcases hab' with (rfl | h1) | h1
    · exact Commute.refl _
    · exact Q3V.commute_of_commRel a b h1
    · exact (Q3V.commute_of_commRel b a h1).symm
  let _ : CommGroup (PG 12 (v6aWords k)) := { (inferInstance : Group (PG 12 (v6aWords k))) with
    mul_comm := comm_of_genSub_eq_top (genSub_eq_top (by norm_num) (h k hk)) hc }
  have hone : ∀ j, (PresentedGroup.of j : PG 12 (v6aWords k)) = 1 := fun j =>
    Q3V.eq_one_of_lattice (fun j => (PresentedGroup.of j : PG 12 (v6aWords k)))
      (Q3V.relsHold_of (v6aWords k)) (Q3V.collLatticeOK_v6a k) j
  obtain ⟨f, hf⟩ := exists_hom_of_relsHold (v6aWords k) g hg
  rw [← hf i, hone i, map_one]

end CFSG.KC.Q3Coll
