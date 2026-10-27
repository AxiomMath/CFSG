module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderShape

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def matchingGroup (t : Perm Ω) : Subgroup (Perm Ω) :=
  Subgroup.closure (Set.range fun i => swap i (t i))

@[expose] def IsMatchingGroup (B : Subgroup (Perm Ω)) : Prop :=
  ∃ t : Perm Ω, (∀ i, t i ≠ i) ∧ (∀ i, t (t i) = i) ∧ B = matchingGroup t

variable {t : Perm Ω}

theorem swap_mem_matchingGroup (i : Ω) : swap i (t i) ∈ matchingGroup t :=
  Subgroup.subset_closure ⟨i, rfl⟩

@[expose] def pairPres (ht2 : ∀ i, t (t i) = i) : Subgroup (Perm Ω) where
  carrier := {g | ∀ i, g i = i ∨ g i = t i}
  mul_mem' := by
    intro g h hg hh i
    show g (h i) = i ∨ g (h i) = t i
    rcases hh i with h1 | h1 <;> rw [h1]
    · exact hg i
    · rcases hg (t i) with h2 | h2
      · exact Or.inr h2
      · exact Or.inl (h2.trans (ht2 i))
  one_mem' := fun _ => Or.inl rfl
  inv_mem' := by
    intro g hg i
    show g⁻¹ i = i ∨ g⁻¹ i = t i
    have hgi : g (g⁻¹ i) = i := g.apply_symm_apply i
    rcases hg (g⁻¹ i) with h1 | h1
    · exact Or.inl (h1.symm.trans hgi)
    · right
      rw [← ht2 (g⁻¹ i), ← h1, hgi]

theorem swap_mem_pairPres (ht2 : ∀ i, t (t i) = i) (j : Ω) : swap j (t j) ∈ pairPres ht2 := by
  intro i
  show swap j (t j) i = i ∨ swap j (t j) i = t i
  by_cases hij : i = j
  · subst hij
    exact Or.inr (swap_apply_left _ _)
  by_cases hit : i = t j
  · subst hit
    right
    rw [swap_apply_right, ht2]
  · exact Or.inl (swap_apply_of_ne_of_ne hij hit)

theorem pairPres_le_matchingGroup (ht2 : ∀ i, t (t i) = i) : pairPres ht2 ≤ matchingGroup t := by
  suffices h : ∀ (k : ℕ) (g : Perm Ω), g.support.card = k → g ∈ pairPres ht2 →
      g ∈ matchingGroup t from fun g hg => h _ g rfl hg
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hk hg
    by_cases h1 : g = 1
    · rw [h1]
      exact one_mem _
    obtain ⟨i, hi⟩ : ∃ i, g i ≠ i := by
      by_contra h
      push Not at h
      exact h1 (Perm.ext h)
    have hgi : g i = t i := (hg i).resolve_left hi
    have hlt := card_support_swap_mul hi
    rw [hgi] at hlt
    have hmem : swap i (t i) * g ∈ pairPres ht2 := mul_mem (swap_mem_pairPres ht2 i) hg
    have hrec := ih _ (hk ▸ hlt) _ rfl hmem
    have heq : g = swap i (t i) * (swap i (t i) * g) := by
      rw [← mul_assoc, swap_mul_self, one_mul]
    rw [heq]
    exact mul_mem (swap_mem_matchingGroup i) hrec

theorem matchingGroup_le_pairPres (ht2 : ∀ i, t (t i) = i) : matchingGroup t ≤ pairPres ht2 := by
  rw [matchingGroup, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact swap_mem_pairPres ht2 j

theorem mem_matchingGroup_iff (ht2 : ∀ i, t (t i) = i) {g : Perm Ω} :
    g ∈ matchingGroup t ↔ ∀ i, g i = i ∨ g i = t i :=
  ⟨fun h => matchingGroup_le_pairPres ht2 h, fun h => pairPres_le_matchingGroup ht2 h⟩

theorem isExp2_matchingGroup (ht2 : ∀ i, t (t i) = i) : IsExp2 (matchingGroup t) := by
  intro g hg
  have hg' := (mem_matchingGroup_iff ht2).1 hg
  ext i
  show g (g i) = i
  rcases hg' i with h | h
  · rw [h, h]
  · rw [h]
    rcases hg' (t i) with h2 | h2
    · have : i = t i := g.injective (h.trans h2.symm)
      rw [h2, ← this]
    · rw [h2, ht2]

theorem orbit_matchingGroup (ht2 : ∀ i, t (t i) = i) (i : Ω) :
    orbit (matchingGroup t) i = {i, t i} := by
  ext j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact (mem_matchingGroup_iff ht2).1 g.2 i
  · rintro (rfl | rfl)
    · exact mem_orbit_self _
    · exact ⟨⟨swap i (t i), swap_mem_matchingGroup i⟩, swap_apply_left _ _⟩

theorem card_orbit_matchingGroup (ht : ∀ i, t i ≠ i) (ht2 : ∀ i, t (t i) = i) (i : Ω) :
    Nat.card (orbit (matchingGroup t) i) = 2 := by
  rw [Nat.card_coe_set_eq, orbit_matchingGroup ht2, Set.ncard_pair (ht i).symm]

theorem card_eq_two_mul_card_orb {E : Subgroup (Perm Ω)}
    (h2 : ∀ i : Ω, Nat.card (orbit E i) = 2) :
    Nat.card Ω = 2 * Nat.card (Orb E) := by
  rw [card_eq_sum_orbits E]
  simp only [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Nat.card_eq_fintype_card (α := Orb E), mul_comm]

theorem IsMatchingGroup.even_card {B : Subgroup (Perm Ω)} (h : IsMatchingGroup B) :
    Even (Nat.card Ω) := by
  obtain ⟨t, ht, ht2, rfl⟩ := h
  exact ⟨_, (card_eq_two_mul_card_orb (card_orbit_matchingGroup ht ht2)).trans (two_mul _)⟩

theorem card_FixP_eq (E : Subgroup (Perm Ω)) : Nat.card (FixP E) = 2 ^ Nat.card (Orb E) := by
  refine le_antisymm (card_FixP_le E) ?_
  let f : (Orb E → ZMod 2) → FixP E := fun c =>
    ⟨fun i => c (Quotient.mk'' i), fun g hg i => by
      show c (Quotient.mk'' (g i)) = c (Quotient.mk'' i)
      congr 1
      exact Quotient.sound' (orbitRel_apply.2 ⟨⟨g, hg⟩, rfl⟩)⟩
  have hf : Function.Injective f := by
    intro c c' h
    funext ω
    induction ω using Quotient.inductionOn' with
    | h i => exact congrFun (congrArg Subtype.val h) i
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fun, Nat.card_zmod] at this

theorem apply_eq_of_mem_FixP_matchingGroup {x : Ω → ZMod 2} (hx : x ∈ FixP (matchingGroup t))
    (i : Ω) : x (t i) = x i := by
  have := hx (swap i (t i)) (swap_mem_matchingGroup i) i
  rwa [swap_apply_left] at this

theorem FixP_matchingGroup_le (ht : ∀ i, t i ≠ i) (ht2 : ∀ i, t (t i) = i) :
    FixP (matchingGroup t) ≤ FixUp (matchingGroup t) := by
  intro x hx
  refine ⟨?_, fun g hg => Or.inl (hx g hg)⟩
  refine Finset.sum_ninvolution t (fun i => ?_) (fun i _ => ht i) (fun i => Finset.mem_univ _) ht2
  rw [apply_eq_of_mem_FixP_matchingGroup hx]
  exact zmod2_add_self _

theorem FixUp_matchingGroup_le (h3 : 3 ≤ Nat.card Ω) (ht2 : ∀ i, t (t i) = i) :
    FixUp (matchingGroup t) ≤ FixP (matchingGroup t) := by
  intro x hx
  have hxt : ∀ i, x (t i) = x i := by
    intro i
    have hlt : ({i, t i} : Finset Ω).card < (Finset.univ : Finset Ω).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt Finset.card_le_two (by omega)
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hki : k ≠ i := fun h => hk (by simp [h])
    have hkt : k ≠ t i := fun h => hk (by simp [h])
    rcases hx.2 (swap i (t i)) (swap_mem_matchingGroup i) with h | h
    · have := h i
      rwa [swap_apply_left] at this
    · exfalso
      have := h k
      rw [swap_apply_of_ne_of_ne hki hkt] at this
      have h1 : x k + 0 = x k + 1 := by rw [add_zero]; exact this
      exact absurd (add_left_cancel h1) (by decide)
  intro g hg i
  rcases (mem_matchingGroup_iff ht2).1 hg i with h | h <;> rw [h]
  exact hxt i

@[expose] def flipOf (ht2 : ∀ i, t (t i) = i) (x : Ω → ZMod 2) (hx : ∀ i, x (t i) = x i) :
    Perm Ω :=
  Function.Involutive.toPerm (fun i => if x i = 1 then t i else i) fun i => by
    by_cases h : x i = 1
    · have h' : x (t i) = 1 := by rw [hx]; exact h
      simp only [h, h', ite_true, ht2]
    · simp only [h, ite_false]

theorem flipOf_apply (ht2 : ∀ i, t (t i) = i) (x : Ω → ZMod 2) (hx : ∀ i, x (t i) = x i)
    (i : Ω) : flipOf ht2 x hx i = if x i = 1 then t i else i := rfl

theorem flipOf_mem (ht2 : ∀ i, t (t i) = i) (x : Ω → ZMod 2) (hx : ∀ i, x (t i) = x i) :
    flipOf ht2 x hx ∈ matchingGroup t := by
  rw [mem_matchingGroup_iff ht2]
  intro i
  rw [flipOf_apply]
  by_cases h : x i = 1
  · exact Or.inr (ite_eq_left h)
  · exact Or.inl (ite_eq_right h)

theorem card_FixP_le_card_matchingGroup (ht : ∀ i, t i ≠ i) (ht2 : ∀ i, t (t i) = i) :
    Nat.card (FixP (matchingGroup t)) ≤ Nat.card (matchingGroup t) := by
  let f : FixP (matchingGroup t) → matchingGroup t := fun x =>
    ⟨flipOf ht2 x.1 (apply_eq_of_mem_FixP_matchingGroup x.2),
      flipOf_mem ht2 _ (apply_eq_of_mem_FixP_matchingGroup x.2)⟩
  refine Nat.card_le_card_of_injective f fun x y hxy => ?_
  apply Subtype.ext
  funext i
  have h := congrFun (congrArg (fun g : matchingGroup t => ((g : Perm Ω) : Ω → Ω)) hxy) i
  simp only [f, flipOf_apply] at h
  rcases zmod2_cases (x.1 i) with hx | hx <;> rcases zmod2_cases (y.1 i) with hy | hy
  · rw [hx, hy]
  · rw [hx, hy] at h
    simp only [show (0 : ZMod 2) ≠ 1 by decide, ite_false, ite_true] at h
    exact absurd h.symm (ht i)
  · rw [hx, hy] at h
    simp only [show (0 : ZMod 2) ≠ 1 by decide, ite_false, ite_true] at h
    exact absurd h (ht i)
  · rw [hx, hy]

theorem card_mul_card_FixUp_matchingGroup (h3 : 3 ≤ Nat.card Ω) (ht : ∀ i, t i ≠ i)
    (ht2 : ∀ i, t (t i) = i) :
    Nat.card (matchingGroup t) * Nat.card (FixUp (matchingGroup t)) = 2 ^ Nat.card Ω := by
  have h2 := card_orbit_matchingGroup ht ht2
  have hn := card_eq_two_mul_card_orb h2
  have hP := card_FixP_eq (matchingGroup t)
  have hU : FixUp (matchingGroup t) = FixP (matchingGroup t) :=
    le_antisymm (FixUp_matchingGroup_le h3 ht2) (FixP_matchingGroup_le ht ht2)
  have hle : Nat.card (matchingGroup t) ≤ 2 ^ Nat.card (Orb (matchingGroup t)) := by
    have := card_E_le (isExp2_matchingGroup ht2)
    rwa [Finset.prod_congr rfl fun ω _ => h2 ω.out, Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card] at this
  have hge := card_FixP_le_card_matchingGroup ht ht2
  rw [hP] at hge
  rw [hU, hP, le_antisymm hle hge, ← pow_add, hn, two_mul]

theorem isMatchingGroup_of_card {E : Subgroup (Perm Ω)} (h2 : ∀ i : Ω, Nat.card (orbit E i) = 2)
    (hcard : 2 ^ Nat.card (Orb E) ≤ Nat.card E) : IsMatchingGroup E := by
  classical
  have hK : Nat.card (orbitStab E) ≤ 2 ^ Nat.card (Orb E) := by
    have := Nat.card_le_card_of_injective _ (evalOrb_injective_K (E := E) fun i => (h2 i).le)
    rwa [Nat.card_pi, Finset.prod_congr rfl fun ω _ => h2 ω.out, Finset.prod_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  have hEq : E = orbitStab E := Subgroup.eq_of_le_of_card_ge le_orbitStab (hK.trans hcard)
  have hex : ∀ i : Ω, ∃ j, j ∈ orbit E i ∧ j ≠ i := fun i =>
    Set.exists_ne_of_one_lt_ncard (by rw [← Nat.card_coe_set_eq, h2]; norm_num) i
  choose tf htf_mem htf_ne using hex
  have hpair : ∀ i j, j ∈ orbit E i → j = i ∨ j = tf i := fun i j hj =>
    eq_of_mem_of_ncard_le (Set.toFinite _) (by rw [← Nat.card_coe_set_eq, h2])
      (mem_orbit_self i) (htf_mem i) (htf_ne i).symm hj
  have hinv : Function.Involutive tf := by
    intro i
    have hmem : tf (tf i) ∈ orbit E i := by
      rw [← orbit_eq_iff.2 (htf_mem i)]
      exact htf_mem (tf i)
    exact (hpair i _ hmem).resolve_right (htf_ne (tf i))
  set t : Perm Ω := Function.Involutive.toPerm tf hinv with ht
  have ht1 : ∀ i, t i ≠ i := htf_ne
  have ht2 : ∀ i, t (t i) = i := hinv
  refine ⟨t, ht1, ht2, le_antisymm ?_ ?_⟩
  · intro g hg
    rw [mem_matchingGroup_iff ht2]
    exact fun i => hpair i (g i) ⟨⟨g, hg⟩, rfl⟩
  · rw [matchingGroup, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine hEq.ge fun i => ?_
    show swap j (tf j) i ∈ orbit E i
    by_cases hij : i = j
    · subst hij
      rw [swap_apply_left]
      exact htf_mem i
    by_cases hit : i = tf j
    · subst hit
      rw [swap_apply_right, orbit_eq_iff.2 (htf_mem j)]
      exact mem_orbit_self j
    · rw [swap_apply_of_ne_of_ne hij hit]
      exact mem_orbit_self i

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
