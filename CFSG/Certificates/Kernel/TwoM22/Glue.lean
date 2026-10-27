module

public import CFSG.Certificates.Kernel.TwoM22.Sound
public import CFSG.Quasithin.Background.TwoM22TwoGens

public section

namespace CFSG.KC.TwoM22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.Quasithin.TwoM22.Gens

variable {n : Nat}

theorem strictN_eqT (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact (Bool.false_ne_true h).elim
  · exact ⟨rfl, h⟩

@[expose] def wordCodes (d : Nat × Nat) : List Nat :=
  (List.range d.2).map fun k => Nat.land (Nat.shiftRight d.1 (2 * k)) 3

theorem wordOf_eq {G : Type*} [Group G] (g : Fin 2 → G) (d : Nat × Nat) :
    wordOf g d = ((wordCodes d).map (letterOf g)).prod := by
  unfold wordOf wordCodes
  rw [List.map_map]
  rfl

theorem wordOf_mem {G : Type*} [Group G] (g : Fin 2 → G) (d : Nat × Nat) :
    wordOf g d ∈ Subgroup.closure (Set.range g) := by
  unfold wordOf
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  have h0 : g 0 ∈ Subgroup.closure (Set.range g) := Subgroup.subset_closure ⟨0, rfl⟩
  have h1 : g 1 ∈ Subgroup.closure (Set.range g) := Subgroup.subset_closure ⟨1, rfl⟩
  unfold letterOf
  split_ifs
  · exact h0
  · exact h1
  · exact Subgroup.inv_mem _ h0
  · exact Subgroup.inv_mem _ h1

theorem map_wordOf {G H : Type*} [Group G] [Group H] (f : G →* H) (g : Fin 2 → G)
    (d : Nat × Nat) : f (wordOf g d) = wordOf (fun i => f (g i)) d := by
  unfold wordOf
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, letterOf]
  split_ifs <;> simp

theorem wordOf_succ {G : Type*} [Group G] (g : Fin 2 → G) (W len : Nat) :
    wordOf g (W, len + 1) =
      wordOf g (W, len) * letterOf g (Nat.land (Nat.shiftRight W (2 * len)) 3) := by
  simp only [wordOf, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]

theorem prep_inv {w P Q : Nat} {σ : Equiv.Perm (Fin n)} (hP : PRep n w P σ)
    (hQ : ∀ i < n, pg w (mask w) Q (pg w (mask w) P i) = i) : PRep n w Q σ⁻¹ := by
  intro x
  have h := hQ _ (σ⁻¹ x).2
  rw [hP (σ⁻¹ x)] at h
  simpa using h

theorem prep_pkPerm {w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    PRep n w P (pkPerm n w P Q) :=
  fun x => (pkPerm_apply h x).symm

theorem prep_pkPerm_inv {w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    PRep n w Q (pkPerm n w P Q)⁻¹ :=
  prep_inv (prep_pkPerm h) fun i hi => ((permOK_facts h).2.2 i hi).2

section Words

variable {w A B Ai Bi : Nat} {g : Fin 2 → Equiv.Perm (Fin n)}

theorem lt_eq (hA : PRep n w A (g 0)) (hB : PRep n w B (g 1)) (hAi : PRep n w Ai (g 0)⁻¹)
    (hBi : PRep n w Bi (g 1)⁻¹) (c : Nat) (x : Fin n) :
    lt w (mask w) A B Ai Bi c x = (letterOf g c x : Nat) := by
  unfold lt letterOf
  by_cases h0 : c = 0
  · subst h0
    exact hA x
  have e0 : Nat.beq c 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  rw [e0, if_neg h0]
  by_cases h1 : c = 1
  · subst h1
    exact hB x
  have e1 : Nat.beq c 1 = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  rw [e1, if_neg h1]
  by_cases h2 : c = 2
  · subst h2
    exact hAi x
  have e2 : Nat.beq c 2 = false := Bool.eq_false_iff.2 fun h => h2 (Nat.eq_of_beq_eq_true h)
  rw [e2, if_neg h2]
  exact hBi x

theorem wpt_eq (hA : PRep n w A (g 0)) (hB : PRep n w B (g 1)) (hAi : PRep n w Ai (g 0)⁻¹)
    (hBi : PRep n w Bi (g 1)⁻¹) (W : Nat) :
    ∀ (len : Nat) (x : Fin n), wpt w (mask w) A B Ai Bi W len x = (wordOf g (W, len) x : Nat)
  | 0, x => by simp [wpt, wordOf]
  | len + 1, x => by
    have e : wpt w (mask w) A B Ai Bi W (len + 1) x =
        strictN (lt w (mask w) A B Ai Bi
          (Nat.land (Nat.shiftRight W (Nat.shiftLeft len 1)) 3) x)
          (wpt w (mask w) A B Ai Bi W len) := rfl
    have hs : Nat.shiftLeft len 1 = 2 * len := by
      change len <<< 1 = 2 * len
      rw [Nat.shiftLeft_eq, pow_one, mul_comm]
    rw [e, strictN_eqT, hs, lt_eq hA hB hAi hBi, wpt_eq hA hB hAi hBi W len, wordOf_succ,
      Equiv.Perm.mul_apply]

end Words

theorem perm_comm_apply {y g : Equiv.Perm (Fin n)} (h : y * g = g * y) (x : Fin n) :
    y (g x) = g (y x) := by
  rw [← Equiv.Perm.mul_apply, h, Equiv.Perm.mul_apply]

theorem eq_one_of_tree {w m A B tr : Nat} {gA gB y : Equiv.Perm (Fin n)} (hn : 0 < n)
    (hA : ∀ x : Fin n, pg w m A x = gA x) (hB : ∀ x : Fin n, pg w m B x = gB x)
    (ht : treeOK n w m A B tr = true) (hcA : y * gA = gA * y) (hcB : y * gB = gB * y)
    (h0 : y ⟨0, hn⟩ = ⟨0, hn⟩) : y = 1 := by
  obtain ⟨-, hpar⟩ := treeOK_sound hn ht
  have key : ∀ d, ∀ p (hp : p < n), trDep tr p = d → y ⟨p, hp⟩ = ⟨p, hp⟩ := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp hd
      by_cases hp0 : p = 0
      · subst hp0
        exact h0
      obtain ⟨hpl, hdep, hgen⟩ := hpar p hp hp0
      have hy : y ⟨trPar tr p, hpl⟩ = ⟨trPar tr p, hpl⟩ := ih _ (by omega) _ hpl rfl
      by_cases hl : trLab tr p = 0
      · rw [if_pos hl] at hgen
        have hq : gA ⟨trPar tr p, hpl⟩ = ⟨p, hp⟩ := Fin.ext (by rw [← hA]; exact hgen)
        calc y ⟨p, hp⟩ = y (gA ⟨trPar tr p, hpl⟩) := by rw [hq]
          _ = gA (y ⟨trPar tr p, hpl⟩) := perm_comm_apply hcA _
          _ = ⟨p, hp⟩ := by rw [hy, hq]
      · rw [if_neg hl] at hgen
        have hq : gB ⟨trPar tr p, hpl⟩ = ⟨p, hp⟩ := Fin.ext (by rw [← hB]; exact hgen)
        calc y ⟨p, hp⟩ = y (gB ⟨trPar tr p, hpl⟩) := by rw [hq]
          _ = gB (y ⟨trPar tr p, hpl⟩) := perm_comm_apply hcB _
          _ = ⟨p, hp⟩ := by rw [hy, hq]
  ext p
  exact congrArg Fin.val (key _ p p.2 rfl)

end CFSG.KC.TwoM22

end
