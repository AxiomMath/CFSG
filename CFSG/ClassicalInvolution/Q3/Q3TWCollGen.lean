module

public import CFSG.ClassicalInvolution.Q3.Q3ZEval

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.Q3Z

section Lattice

variable {m : ℕ}

@[expose] def netExp (w : List (Fin m × Bool)) (i : Fin m) : ℤ :=
  (w.map fun p => if p.1 = i then (if p.2 then (1 : ℤ) else -1) else 0).sum

@[expose] def combExp (ws : List (List (Fin m × Bool))) (cs : List (ℕ × ℤ)) (i : Fin m) : ℤ :=
  (cs.map fun p => p.2 * netExp (ws.getD p.1 []) i).sum

@[expose] def latticeOK (cs : Fin m → List (ℕ × ℤ)) (ws : List (List (Fin m × Bool))) : Bool :=
  (List.finRange m).all fun j => (List.finRange m).all fun i =>
    decide (combExp ws (cs j) i = if i = j then 1 else 0)

variable {A : Type*} [CommGroup A] (g : Fin m → A)

@[expose] def phi : (Fin m → ℤ) →+ Additive A :=
  AddMonoidHom.mk' (fun v => ∑ i, v i • Additive.ofMul (g i)) (by
    intro v w
    simp [add_smul, Finset.sum_add_distrib])

theorem phi_single (j : Fin m) (c : ℤ) :
    phi g (Pi.single j c) = c • Additive.ofMul (g j) := by
  simp only [phi, AddMonoidHom.mk'_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem netExp_cons (p : Fin m × Bool) (w : List (Fin m × Bool)) :
    (fun i => netExp (p :: w) i) =
      Pi.single p.1 (if p.2 then (1 : ℤ) else -1) + fun i => netExp w i := by
  funext i
  by_cases h : p.1 = i
  · subst h
    simp [netExp]
  · simp [netExp, Ne.symm h, h]

theorem phi_netExp (w : List (Fin m × Bool)) :
    phi g (fun i => netExp w i) = Additive.ofMul (evalW g w) := by
  induction w with
  | nil =>
    have : (fun i => netExp ([] : List (Fin m × Bool)) i) = 0 := by
      funext i
      simp [netExp]
    rw [this, map_zero]
    rfl
  | cons p w ih =>
    rw [netExp_cons, map_add, ih, phi_single, evalW_cons]
    obtain ⟨j, b⟩ := p
    cases b
    · simp [neg_smul]
    · simp

theorem combExp_cons (ws : List (List (Fin m × Bool))) (p : ℕ × ℤ) (cs : List (ℕ × ℤ)) :
    (fun i => combExp ws (p :: cs) i) =
      p.2 • (fun i => netExp (ws.getD p.1 []) i) + fun i => combExp ws cs i := by
  funext i
  simp [combExp]

theorem phi_combExp {ws : List (List (Fin m × Bool))} (hg : RelsHold g ws)
    (cs : List (ℕ × ℤ)) : phi g (fun i => combExp ws cs i) = 0 := by
  induction cs with
  | nil =>
    have : (fun i => combExp ws ([] : List (ℕ × ℤ)) i) = 0 := by
      funext i
      simp [combExp]
    rw [this, map_zero]
  | cons p cs ih =>
    have hone : evalW g (ws.getD p.1 []) = 1 := by
      by_cases h : p.1 < ws.length
      · rw [List.getD_eq_getElem _ _ h]
        exact hg _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ (by omega)]
        rfl
    rw [combExp_cons, map_add, map_zsmul, phi_netExp, hone, ih]
    simp

theorem eq_one_of_lattice {cs : Fin m → List (ℕ × ℤ)} {ws : List (List (Fin m × Bool))}
    (hg : RelsHold g ws) (hws : latticeOK cs ws = true) (j : Fin m) : g j = 1 := by
  have hcoef : ∀ j i, combExp ws (cs j) i = if i = j then 1 else 0 := by
    intro j i
    have := hws
    simp only [latticeOK, List.all_eq_true, List.mem_finRange, forall_const,
      decide_eq_true_eq] at this
    exact this j i
  have h1 : (fun i => combExp ws (cs j) i) = Pi.single j (1 : ℤ) := by
    funext i
    rw [hcoef]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  have h2 := phi_combExp g hg (cs j)
  rw [h1, phi_single, one_smul] at h2
  exact Additive.ofMul.injective (by simpa using h2)

end Lattice

section Presented

variable {m : ℕ}

theorem evalW_eq_lift {G : Type*} [Group G] (g : Fin m → G) (w : List (Fin m × Bool)) :
    FreeGroup.lift g (FreeGroup.mk w) = evalW g w := by
  induction w with
  | nil => simp [evalW]
  | cons p w ih =>
    have hc : FreeGroup.mk (p :: w) = FreeGroup.mk [p] * FreeGroup.mk w := by
      rw [FreeGroup.mul_mk]
      rfl
    rw [hc, map_mul, ih, evalW_cons]
    obtain ⟨i, b⟩ := p
    cases b <;> simp

theorem relsHold_of (ws : List (List (Fin m × Bool))) :
    RelsHold (fun j => (PresentedGroup.of j : PG m ws)) ws := by
  intro w hw
  have h : FreeGroup.lift (fun j => (PresentedGroup.of j : PG m ws)) =
      PresentedGroup.mk _ := by
    ext j
    rfl
  rw [← evalW_eq_lift, h]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

@[expose] def commRel (a b : Fin m) : List (Fin m × Bool) :=
  [(a, false), (b, false), (a, true), (b, true)]

@[expose] def commOK (ws : List (List (Fin m × Bool))) (S : List ℕ) : Bool :=
  (subsetOf m S).all fun a => (subsetOf m S).all fun b =>
    decide (a = b) || ws.contains (commRel a b) || ws.contains (commRel b a)

theorem commute_of_commRel {ws : List (List (Fin m × Bool))} (a b : Fin m)
    (h : [(a, false), (b, false), (a, true), (b, true)] ∈ ws) :
    Commute (PresentedGroup.of a : PG m ws) (PresentedGroup.of b) := by
  have h1 := relsHold_of ws _ h
  simp only [evalW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Bool.false_eq_true, ite_false, ite_true] at h1
  have h2 : (PresentedGroup.of b : PG m ws)⁻¹ * PresentedGroup.of a * PresentedGroup.of b =
      PresentedGroup.of a := by
    have := congrArg (fun y => (PresentedGroup.of a : PG m ws) * y) h1
    simpa [mul_assoc] using this
  show _ * _ = _ * _
  calc (PresentedGroup.of a : PG m ws) * PresentedGroup.of b
      = PresentedGroup.of b * ((PresentedGroup.of b)⁻¹ * PresentedGroup.of a *
          PresentedGroup.of b) := by group
    _ = PresentedGroup.of b * PresentedGroup.of a := by rw [h2]

theorem eq_one_of_fastCheck {ws : List (List (Fin m × Bool))} {S : List ℕ} {cap : ℕ}
    {cs : Fin m → List (ℕ × ℤ)} (hchk : subsetCheck ws S cap 1 = true)
    (hcomm : commOK ws S = true) (hlat : latticeOK cs ws = true) {G : Type} [Group G]
    (g : Fin m → G) (hg : RelsHold g ws) (i : Fin m) : g i = 1 := by
  set T := subsetOf m S with hT
  let gens : Set (PG m ws) := {y | ∃ x ∈ T, y = PresentedGroup.of x}
  have hcheck : check (presParams ws (T.map fun x => [(x, true)])) cap 1 = true := by
    unfold subsetCheck at hchk
    exact hchk
  obtain ⟨hfi, hidx⟩ := index_le_presented ws (T.map fun x => [(x, true)])
    (Subgroup.closure gens)
    (by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      exact Subgroup.subset_closure ⟨x, hx, rfl⟩) hcheck
  have htop : Subgroup.closure gens = ⊤ := by
    have h1 : (Subgroup.closure gens).index = 1 := by
      have := hfi.index_ne_zero
      omega
    exact Subgroup.index_eq_one.mp h1
  have hgc : gens.Pairwise Commute := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    have hab := List.all_eq_true.mp hcomm a ha
    have hab' := List.all_eq_true.mp hab b hb
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hab'
    rcases hab' with (rfl | h1) | h1
    · exact Commute.refl _
    · exact commute_of_commRel a b h1
    · exact (commute_of_commRel b a h1).symm
  have hcommAll : ∀ a b : PG m ws, a * b = b * a := by
    intro a b
    have hmem : ∀ c : PG m ws, c ∈ Subgroup.centralizer (Subgroup.centralizer gens) := by
      intro c
      have : c ∈ Subgroup.closure gens := by rw [htop]; exact Subgroup.mem_top c
      exact Subgroup.closure_le_centralizer_centralizer gens this
    exact Set.centralizer_centralizer_comm_of_comm hgc a (hmem a) b (hmem b)
  let _ : CommGroup (PG m ws) := { (inferInstance : Group (PG m ws)) with mul_comm := hcommAll }
  have hone : ∀ j, (PresentedGroup.of j : PG m ws) = 1 := fun j =>
    eq_one_of_lattice (fun j => (PresentedGroup.of j : PG m ws)) (relsHold_of ws) hlat j
  obtain ⟨f, hf⟩ := exists_hom_of_relsHold ws g hg
  rw [← hf i, hone i, map_one]

end Presented

end CFSG.ClassicalInvolution.Q3.Q3TW
