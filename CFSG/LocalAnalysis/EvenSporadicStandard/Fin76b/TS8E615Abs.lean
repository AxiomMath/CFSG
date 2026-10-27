module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.EvenSporadicStandard.Fin76b.E615

variable {Γ : Type*} [Group Γ]

@[expose] def mulStep (S : List Γ) (b : Γ) : List Γ := S ++ S.map (· * b)

@[expose] def subProd (P : List Γ) : List Γ := P.foldl mulStep [1]

@[expose] def IndepOn : List Γ → List Γ → Prop
  | _, [] => True
  | P, g :: G => g ∉ subProd P ∧ IndepOn (P ++ [g]) G

theorem subProd_snoc (P : List Γ) (b : Γ) :
    subProd (P ++ [b]) = subProd P ++ (subProd P).map (· * b) := by
  simp [subProd, mulStep, List.foldl_append]

theorem mem_foldl_mulStep {x : Γ} (P S : List Γ) (h : x ∈ S) : x ∈ P.foldl mulStep S := by
  induction P generalizing S with
  | nil => exact h
  | cons b P ih => exact ih _ (List.mem_append_left _ h)

theorem one_mem_subProd (P : List Γ) : (1 : Γ) ∈ subProd P :=
  mem_foldl_mulStep P [1] (List.mem_singleton_self 1)

theorem mem_subProd_snoc_left {P : List Γ} {b x : Γ} (h : x ∈ subProd P) :
    x ∈ subProd (P ++ [b]) := by
  rw [subProd_snoc]
  exact List.mem_append_left _ h

theorem mul_mem_subProd_snoc {P : List Γ} {b x : Γ} (h : x ∈ subProd P) :
    x * b ∈ subProd (P ++ [b]) := by
  rw [subProd_snoc]
  exact List.mem_append_right _ (List.mem_map_of_mem h)

theorem length_foldl_mulStep (P S : List Γ) :
    (P.foldl mulStep S).length = S.length * 2 ^ P.length := by
  induction P generalizing S with
  | nil => simp
  | cons b P ih =>
    rw [List.foldl_cons, ih]
    simp only [mulStep, List.length_append, List.length_map, List.length_cons, pow_succ]
    ring

theorem length_subProd (P : List Γ) : (subProd P).length = 2 ^ P.length := by
  simpa [subProd] using length_foldl_mulStep P [1]

theorem card_le_length_of_subset (A : Subgroup Γ) (S : List Γ) (h : ∀ b ∈ A, b ∈ S) :
    Nat.card A ≤ S.length := by
  classical
  have hf : Function.Injective
      (fun b : A => (⟨b.1, List.mem_toFinset.2 (h b.1 b.2)⟩ : S.toFinset)) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : S.toFinset => z.1) hxy
  calc Nat.card A ≤ Nat.card S.toFinset := Nat.card_le_card_of_injective _ hf
    _ = S.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ S.length := List.toFinset_card_le S

theorem exists_chain {β : Type*} (A : Subgroup Γ) (F : Γ → β)
    (hF : ∀ a ∈ A, ∀ b ∈ A, F a = F b → a = b) (hA : 16 < Nat.card A) :
    ∀ (L : List β) (P : List Γ) (k : ℕ), P.length + k = 5 →
      (∀ b ∈ A, b ∉ subProd P → F b ∈ L) →
      ∃ G : List Γ, G.length = k ∧ (∀ g ∈ G, g ∈ A) ∧ IndepOn P G ∧
        List.Sublist (G.map F) L := by
  intro L
  induction L with
  | nil =>
    intro P k hPk hL
    cases k with
    | zero => exact ⟨[], rfl, by simp, trivial, List.Sublist.slnil⟩
    | succ k =>
      exfalso
      have hsub : ∀ b ∈ A, b ∈ subProd P := fun b hb => by
        by_contra hn
        have h := hL b hb hn
        simp at h
      have hcard := card_le_length_of_subset A (subProd P) hsub
      rw [length_subProd] at hcard
      have h16 : 2 ^ P.length ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      norm_num at h16
      omega
  | cons X L ih =>
    intro P k hPk hL
    cases k with
    | zero => exact ⟨[], rfl, by simp, trivial, List.nil_sublist _⟩
    | succ k =>
      by_cases hx : ∃ x ∈ A, x ∉ subProd P ∧ F x = X
      · obtain ⟨x, hxA, hxP, hxX⟩ := hx
        have hxmem : x ∈ subProd (P ++ [x]) := by
          have h1 : (1 : Γ) * x ∈ subProd (P ++ [x]) :=
            mul_mem_subProd_snoc (one_mem_subProd P)
          simpa using h1
        have hL' : ∀ b ∈ A, b ∉ subProd (P ++ [x]) → F b ∈ L := by
          intro b hb hbn
          have hbP : b ∉ subProd P := fun h => hbn (mem_subProd_snoc_left h)
          rcases List.mem_cons.1 (hL b hb hbP) with h | h
          · exfalso
            have hbx : b = x := hF b hb x hxA (h.trans hxX.symm)
            exact hbn (by rw [hbx]; exact hxmem)
          · exact h
        obtain ⟨G, hG, hGA, hInd, hsub⟩ :=
          ih (P ++ [x]) k (by simp only [List.length_append, List.length_singleton]; omega) hL'
        refine ⟨x :: G, by simp [hG], ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_cons.1 hg with rfl | hg
          · exact hxA
          · exact hGA g hg
        · show x ∉ subProd P ∧ IndepOn (P ++ [x]) G
          exact ⟨hxP, hInd⟩
        · rw [List.map_cons, hxX]
          exact hsub.cons_cons X
      · push_neg at hx
        have hL' : ∀ b ∈ A, b ∉ subProd P → F b ∈ L := by
          intro b hb hbP
          rcases List.mem_cons.1 (hL b hb hbP) with h | h
          · exact absurd h (hx b hb hbP)
          · exact h
        obtain ⟨G, hG, hGA, hInd, hsub⟩ := ih P (k + 1) hPk hL'
        exact ⟨G, hG, hGA, hInd, hsub.cons X⟩

theorem cons_tails_of_sublist' {α : Type*} {l₁ l₂ : List α} (h : List.Sublist l₁ l₂) :
    ∀ (X : α) (Q : List α), l₁ = X :: Q → ∃ T, (X :: T) ∈ l₂.tails ∧ List.Sublist Q T := by
  induction h with
  | slnil => intro X Q hX; simp at hX
  | @cons l₁' l₂' a _ ih =>
    intro X Q hX
    obtain ⟨T, hT, hQ⟩ := ih X Q hX
    exact ⟨T, by rw [List.tails_cons]; exact List.mem_cons_of_mem _ hT, hQ⟩
  | @cons_cons l₁' l₂' a h' _ =>
    intro X Q hX
    simp only [List.cons.injEq] at hX
    obtain ⟨rfl, rfl⟩ := hX
    exact ⟨l₂', by rw [List.tails_cons]; simp, h'⟩

end CFSG.EvenSporadicStandard.Fin76b.E615
