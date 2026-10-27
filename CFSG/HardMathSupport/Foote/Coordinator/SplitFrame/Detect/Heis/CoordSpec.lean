module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.StandardType.RootCentExc

set_option linter.unusedSectionVars false



variable (τ : Tag) (K : Type) [Field K]

structure HeisCoordSpec (coord : ModGL τ K → (Fin τ.rank → ℤ) → K) : Prop where
  mul : ∀ q ∈ Qθ τ K, ∀ q' ∈ Qθ τ K, coord (q * q') = coord q + coord q'
  pinnedX_deg1 : ∀ β ∈ Deg1 τ, ∀ c : K, coord (pinnedX τ K β c) = Pi.single β c
  pinnedX_highRoot : ∀ c : K, coord (pinnedX τ K (highRoot τ) c) = 0
  eq_zero_iff : ∀ q ∈ Qθ τ K, coord q = 0 ↔ q ∈ Uθ τ K
  support : ∀ q ∈ Qθ τ K, ∀ β, β ∉ Deg1 τ → coord q β = 0
  surj : ∀ f : (Fin τ.rank → ℤ) → K, (∀ β, β ∉ Deg1 τ → f β = 0) →
    ∃ q ∈ Qθ τ K, coord q = f
  commute_disjoint : ∀ q ∈ Qθ τ K, ∀ β ∈ Deg1 τ, ∀ c : K,
    (∀ γ, coord q γ ≠ 0 → γ + β ∉ rootFinset τ) → q * pinnedX τ K β c = pinnedX τ K β c * q

namespace CoordAux

theorem deg_facts (τ : Tag) :
    (∀ α ∈ rootFinset τ, α (iθ τ) ≤ 2) ∧
    (∀ α ∈ rootFinset τ, 2 ≤ α (iθ τ) → α = highRoot τ) ∧ highRoot τ (iθ τ) = 2 := by
  cases τ <;> decide +kernel

variable {τ K}

theorem degree_le_two {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : α (iθ τ) ≤ 2 :=
  (deg_facts τ).1 α (mem_rootFinset.2 hα)

theorem eq_highRoot_of_two_le {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h : 2 ≤ α (iθ τ)) :
    α = highRoot τ :=
  (deg_facts τ).2.1 α (mem_rootFinset.2 hα) h

theorem highRoot_degree (τ : Tag) : highRoot τ (iθ τ) = 2 := (deg_facts τ).2.2

theorem mem_Deg1 {β : Fin τ.rank → ℤ} : β ∈ Deg1 τ ↔ IsRoot τ β ∧ β (iθ τ) = 1 := Iff.rfl

theorem Deg1.height_pos {β : Fin τ.rank → ℤ} (h : β ∈ Deg1 τ) : 0 < height β := by
  obtain ⟨hr, hd⟩ := mem_Deg1.1 h
  rcases IsRoot.height_pos_or_neg hr with hp | hn
  · exact hp
  · have := (IsRoot.height_neg_iff hr).1 hn (iθ τ)
    omega

theorem Deg1.ne_highRoot {β : Fin τ.rank → ℤ} (h : β ∈ Deg1 τ) : β ≠ highRoot τ := by
  intro e
  have h1 := (mem_Deg1.1 h).2
  rw [e, highRoot_degree] at h1
  omega

theorem Deg1.ne_neg {γ β : Fin τ.rank → ℤ} (hγ : γ ∈ Deg1 τ) (hβ : β ∈ Deg1 τ) : γ ≠ -β := by
  intro h
  have h1 := (mem_Deg1.1 hγ).2
  have h2 := (mem_Deg1.1 hβ).2
  rw [h, Pi.neg_apply] at h1
  omega

theorem parabolicDegree_Jθ (α : Fin τ.rank → ℤ) : parabolicDegree τ (Jθ τ) α = α (iθ τ) := by
  classical
  unfold parabolicDegree
  rw [Finset.sum_eq_single (iθ τ)]
  · simp [Jθ]
  · intro i _ hi
    simp [Jθ, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_radRoots_iff (α : Fin τ.rank → ℤ) :
    α ∈ parabolicRadicalRoots τ (Jθ τ) ↔ α ∈ Deg1 τ ∨ α = highRoot τ := by
  constructor
  · intro hα
    have h1 := one_le_parabolicDegree_of_mem hα
    rw [parabolicDegree_Jθ] at h1
    have h2 := degree_le_two hα.1.1
    by_cases h : α (iθ τ) = 1
    · exact Or.inl ⟨hα.1.1, h⟩
    · exact Or.inr (eq_highRoot_of_two_le hα.1.1 (by omega))
  · rintro (h | rfl)
    · exact mem_parabolicRadicalRoots_of_degree (mem_Deg1.1 h).1 (Deg1.height_pos h) (by
        rw [parabolicDegree_Jθ, (mem_Deg1.1 h).2]
        exact one_ne_zero)
    · exact mem_parabolicRadicalRoots_of_degree (isRoot_highRoot τ) (height_highRoot_pos τ) (by
        rw [parabolicDegree_Jθ, highRoot_degree]
        exact two_ne_zero)

theorem exists_list_Deg1 :
    ∃ L₁ : List (Fin τ.rank → ℤ), L₁.Nodup ∧ ∀ α, α ∈ L₁ ↔ α ∈ Deg1 τ :=
  exists_list_of_finite ((finite_setOf_isRoot τ).subset fun _ h => (mem_Deg1.1 h).1)

def prodX (l : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → K) : ModGL τ K :=
  (l.map fun α => pinnedX τ K α (c α)).prod

theorem prodX_nil (c : (Fin τ.rank → ℤ) → K) : prodX ([] : List (Fin τ.rank → ℤ)) c = 1 := by
  simp [prodX]

theorem prodX_cons (α : Fin τ.rank → ℤ) (l : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → K) :
    prodX (α :: l) c = pinnedX τ K α (c α) * prodX l c := by
  simp [prodX]

theorem prodX_singleton (α : Fin τ.rank → ℤ) (c : (Fin τ.rank → ℤ) → K) :
    prodX [α] c = pinnedX τ K α (c α) := by
  simp [prodX]

theorem prodX_append (l₁ l₂ : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → K) :
    prodX (l₁ ++ l₂) c = prodX l₁ c * prodX l₂ c := by
  simp [prodX]

theorem prodX_congr {l : List (Fin τ.rank → ℤ)} {c c' : (Fin τ.rank → ℤ) → K}
    (h : ∀ α ∈ l, c α = c' α) : prodX l c = prodX l c' := by
  unfold prodX
  congr 1
  exact List.map_congr_left fun α hα => by rw [h α hα]

theorem prodX_eq_one {l : List (Fin τ.rank → ℤ)} {c : (Fin τ.rank → ℤ) → K}
    (h : ∀ α ∈ l, c α = 0) : prodX l c = 1 := by
  unfold prodX
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
  rw [h α hα, pinnedX_zero]

theorem prodX_single (L : List (Fin τ.rank → ℤ)) (hnd : L.Nodup) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ L) (c : K) : prodX L (Pi.single β c) = pinnedX τ K β c := by
  induction L with
  | nil => exact absurd hβ List.not_mem_nil
  | cons α l ih =>
    obtain ⟨hα, hndl⟩ := List.nodup_cons.1 hnd
    rw [prodX_cons]
    by_cases h : α = β
    · subst h
      rw [Pi.single_eq_same, prodX_eq_one, mul_one]
      intro γ hγ
      have hγα : γ ≠ α := fun e => hα (e ▸ hγ)
      simp [Pi.single_apply, hγα]
    · rw [Pi.single_eq_of_ne h, pinnedX_zero, one_mul]
      exact ih hndl ((List.mem_cons.1 hβ).resolve_left fun e => h e.symm)

theorem prodX_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ α ∈ l, α ∈ S) (c : (Fin τ.rank → ℤ) → K) : prodX l c ∈ rootSpan τ K S :=
  list_map_prod_pinnedX_mem_rootSpan K hl c

theorem pinnedX_mem_pos {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) (b : K) :
    pinnedX τ K β b ∈ posUnipotent τ K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α})
    ⟨(mem_Deg1.1 hβ).1, Deg1.height_pos hβ⟩ b

theorem prodX_mem_pos {l : List (Fin τ.rank → ℤ)} (hl : ∀ α ∈ l, α ∈ Deg1 τ)
    (c : (Fin τ.rank → ℤ) → K) : prodX l c ∈ posUnipotent τ K :=
  pinnedX_list_prod_mem_posUnipotent l (fun α hα => ⟨(mem_Deg1.1 (hl α hα)).1,
    Deg1.height_pos (hl α hα)⟩) c

theorem isMaxHeight_highRoot' : IsMaxHeight τ (highRoot τ) :=
  ⟨isRoot_highRoot τ, fun _ hα => height_le_height_highRoot hα⟩

theorem Uθ_comm {u g : ModGL τ K} (hu : u ∈ Uθ τ K) (hg : g ∈ posUnipotent τ K) :
    u * g = g * u := by
  obtain ⟨b, rfl⟩ := mem_rootSubgroup.1 hu
  exact (commute_of_mem_posUnipotent isMaxHeight_highRoot' hg b).eq.symm

theorem commPairs_aux {γ β : Fin τ.rank → ℤ} (hγ : γ ∈ Deg1 τ) (hβ : β ∈ Deg1 τ) {p : ℕ × ℕ}
    (hp : p ∈ commPairs τ γ β) :
    p.1 • γ + p.2 • β = highRoot τ ∧ p.1 = 1 ∧ p.2 = 1 := by
  obtain ⟨hc, hr⟩ := mem_commPairs.1 hp
  obtain ⟨⟨h1, -⟩, h2, -⟩ := mem_commCandidates.1 hc
  have hd : (p.1 • γ + p.2 • β) (iθ τ) = p.1 + p.2 := by
    simp [(mem_Deg1.1 hγ).2, (mem_Deg1.1 hβ).2]
  have heq := eq_highRoot_of_two_le hr (by rw [hd]; omega)
  have hd2 : (p.1 • γ + p.2 • β) (iθ τ) = 2 := by rw [heq, highRoot_degree]
  rw [hd] at hd2
  exact ⟨heq, by omega, by omega⟩

theorem exists_comm_pinnedX {γ β : Fin τ.rank → ℤ} (hγ : γ ∈ Deg1 τ) (hβ : β ∈ Deg1 τ)
    (a b : K) : ∃ u ∈ Uθ τ K,
      pinnedX τ K γ a * pinnedX τ K β b = pinnedX τ K β b * pinnedX τ K γ a * u := by
  by_cases hne : γ = β
  · subst hne
    exact ⟨1, one_mem _, by rw [mul_one, ← pinnedX_add, ← pinnedX_add, add_comm]⟩
  · obtain ⟨-, -, -, -, hF⟩ := root_commutator_formula.{0} τ (mem_Deg1.1 hγ).1
      (mem_Deg1.1 hβ).1 hne (Deg1.ne_neg hγ hβ)
    have h1 := hF K a b
    rw [← pinnedX_neg τ K γ a, ← pinnedX_neg τ K β b] at h1
    have hU : pinnedX τ K γ a * pinnedX τ K β b * (pinnedX τ K γ a)⁻¹ *
        (pinnedX τ K β b)⁻¹ ∈ Uθ τ K := by
      rw [h1]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      rw [(commPairs_aux hγ hβ hp).1]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩
    refine ⟨_, hU, ?_⟩
    have hc := Uθ_comm hU (mul_mem (pinnedX_mem_pos hβ b) (pinnedX_mem_pos hγ a))
    calc pinnedX τ K γ a * pinnedX τ K β b
        = (pinnedX τ K γ a * pinnedX τ K β b * (pinnedX τ K γ a)⁻¹ * (pinnedX τ K β b)⁻¹) *
            (pinnedX τ K β b * pinnedX τ K γ a) := by group
      _ = (pinnedX τ K β b * pinnedX τ K γ a) *
            (pinnedX τ K γ a * pinnedX τ K β b * (pinnedX τ K γ a)⁻¹ * (pinnedX τ K β b)⁻¹) := hc

theorem commute_pinnedX_of_not_isRoot_add {γ β : Fin τ.rank → ℤ} (hγ : γ ∈ Deg1 τ)
    (hβ : β ∈ Deg1 τ) (hnot : γ + β ∉ rootFinset τ) (a b : K) :
    Commute (pinnedX τ K γ a) (pinnedX τ K β b) := by
  by_cases hne : γ = β
  · subst hne
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · have hnil : commPairs τ γ β = [] := by
      refine List.eq_nil_iff_forall_not_mem.2 fun p hp => hnot ?_
      obtain ⟨-, h1, h2⟩ := commPairs_aux hγ hβ hp
      have := (mem_commPairs.1 hp).2
      rw [h1, h2, one_smul, one_smul] at this
      exact mem_rootFinset.2 this
    obtain ⟨-, -, -, -, hF⟩ := root_commutator_formula.{0} τ (mem_Deg1.1 hγ).1
      (mem_Deg1.1 hβ).1 hne (Deg1.ne_neg hγ hβ)
    have h1 := hF K a b
    rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg τ K γ a, ← pinnedX_neg τ K β b] at h1
    exact commutatorElement_eq_one_iff_commute.1 (by rw [commutatorElement_def]; exact h1)

theorem exists_comm_prodX {l : List (Fin τ.rank → ℤ)} (hl : ∀ α ∈ l, α ∈ Deg1 τ)
    (c : (Fin τ.rank → ℤ) → K) {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) (b : K) :
    ∃ u ∈ Uθ τ K, prodX l c * pinnedX τ K β b = pinnedX τ K β b * prodX l c * u := by
  induction l with
  | nil => exact ⟨1, one_mem _, by simp [prodX_nil]⟩
  | cons γ l ih =>
    obtain ⟨u', hu', e'⟩ := ih fun α hα => hl α (List.mem_cons_of_mem _ hα)
    obtain ⟨u₀, hu₀, e₀⟩ := exists_comm_pinnedX (hl γ List.mem_cons_self) hβ (c γ) b
    have hP : prodX l c ∈ posUnipotent τ K :=
      prodX_mem_pos (fun α hα => hl α (List.mem_cons_of_mem _ hα)) c
    refine ⟨u₀ * u', mul_mem hu₀ hu', ?_⟩
    rw [prodX_cons]
    calc pinnedX τ K γ (c γ) * prodX l c * pinnedX τ K β b
        = pinnedX τ K γ (c γ) * (prodX l c * pinnedX τ K β b) := by rw [mul_assoc]
      _ = pinnedX τ K γ (c γ) * (pinnedX τ K β b * prodX l c * u') := by rw [e']
      _ = (pinnedX τ K γ (c γ) * pinnedX τ K β b) * prodX l c * u' := by simp only [mul_assoc]
      _ = (pinnedX τ K β b * pinnedX τ K γ (c γ) * u₀) * prodX l c * u' := by rw [e₀]
      _ = pinnedX τ K β b * pinnedX τ K γ (c γ) * (u₀ * prodX l c) * u' := by
        simp only [mul_assoc]
      _ = pinnedX τ K β b * pinnedX τ K γ (c γ) * (prodX l c * u₀) * u' := by
        rw [Uθ_comm hu₀ hP]
      _ = pinnedX τ K β b * (pinnedX τ K γ (c γ) * prodX l c) * (u₀ * u') := by
        simp only [mul_assoc]

theorem exists_mul_prodX {l : List (Fin τ.rank → ℤ)} (hl : ∀ α ∈ l, α ∈ Deg1 τ)
    (c c' : (Fin τ.rank → ℤ) → K) :
    ∃ u ∈ Uθ τ K, prodX l c * prodX l c' = prodX l (c + c') * u := by
  induction l with
  | nil => exact ⟨1, one_mem _, by simp [prodX_nil]⟩
  | cons γ l ih =>
    have hl' : ∀ α ∈ l, α ∈ Deg1 τ := fun α hα => hl α (List.mem_cons_of_mem _ hα)
    obtain ⟨u₂, hu₂, e₂⟩ := ih hl'
    obtain ⟨u₁, hu₁, e₁⟩ := exists_comm_prodX hl' c (hl γ List.mem_cons_self) (c' γ)
    have hP' : prodX l c' ∈ posUnipotent τ K := prodX_mem_pos hl' c'
    refine ⟨u₂ * u₁, mul_mem hu₂ hu₁, ?_⟩
    rw [prodX_cons, prodX_cons, prodX_cons]
    calc pinnedX τ K γ (c γ) * prodX l c * (pinnedX τ K γ (c' γ) * prodX l c')
        = pinnedX τ K γ (c γ) * (prodX l c * pinnedX τ K γ (c' γ)) * prodX l c' := by
          simp only [mul_assoc]
      _ = pinnedX τ K γ (c γ) * (pinnedX τ K γ (c' γ) * prodX l c * u₁) * prodX l c' := by
          rw [e₁]
      _ = (pinnedX τ K γ (c γ) * pinnedX τ K γ (c' γ)) * prodX l c * (u₁ * prodX l c') := by
          simp only [mul_assoc]
      _ = (pinnedX τ K γ (c γ) * pinnedX τ K γ (c' γ)) * prodX l c * (prodX l c' * u₁) := by
          rw [Uθ_comm hu₁ hP']
      _ = pinnedX τ K γ (c γ + c' γ) * (prodX l c * prodX l c') * u₁ := by
          rw [pinnedX_add]
          simp only [mul_assoc]
      _ = pinnedX τ K γ ((c + c') γ) * (prodX l (c + c') * u₂) * u₁ := by
          rw [e₂]
          rfl
      _ = pinnedX τ K γ ((c + c') γ) * prodX l (c + c') * (u₂ * u₁) := by
          simp only [mul_assoc]

theorem commute_prodX {l : List (Fin τ.rank → ℤ)} {c : (Fin τ.rank → ℤ) → K}
    {β : Fin τ.rank → ℤ} {b : K}
    (h : ∀ α ∈ l, c α ≠ 0 → Commute (pinnedX τ K α (c α)) (pinnedX τ K β b)) :
    Commute (prodX l c) (pinnedX τ K β b) := by
  unfold prodX
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
  by_cases h0 : c α = 0
  · rw [h0, pinnedX_zero]
    exact Commute.one_left _
  · exact h α hα h0

open Classical in
def coordFn (L : List (Fin τ.rank → ℤ)) (q : ModGL τ K) : (Fin τ.rank → ℤ) → K :=
  fun β => if β ∈ Deg1 τ then (if h : ∃ c, prodX L c = q then h.choose β else 0) else 0

open Classical in
theorem coordFn_prodX {L : List (Fin τ.rank → ℤ)} (hnd : L.Nodup)
    (hpos : ∀ α ∈ L, IsRoot τ α ∧ 0 < height α) (hD : ∀ β ∈ Deg1 τ, β ∈ L)
    (c : (Fin τ.rank → ℤ) → K) (β : Fin τ.rank → ℤ) :
    coordFn L (prodX L c) β = if β ∈ Deg1 τ then c β else 0 := by
  unfold coordFn
  by_cases hβ : β ∈ Deg1 τ
  · rw [if_pos hβ, if_pos hβ]
    have h : ∃ c', prodX L c' = prodX L c := ⟨c, rfl⟩
    rw [dif_pos h]
    exact pinnedX_list_prod_injective L hnd hpos _ _ h.choose_spec β (hD β hβ)
  · rw [if_neg hβ, if_neg hβ]

end CoordAux

theorem exists_heisCoord : ∃ coord : ModGL τ K → (Fin τ.rank → ℤ) → K, HeisCoordSpec τ K coord := by
  classical
  obtain ⟨L₁, hnd₁, hmem₁⟩ := CoordAux.exists_list_Deg1 (τ := τ)
  obtain ⟨L, hL⟩ : ∃ L : List (Fin τ.rank → ℤ), L = L₁ ++ [highRoot τ] := ⟨_, rfl⟩
  have hLS : ∀ α, α ∈ L ↔ α ∈ parabolicRadicalRoots τ (Jθ τ) := by
    intro α
    rw [hL, List.mem_append, List.mem_singleton, CoordAux.mem_radRoots_iff, hmem₁]
  have hnd : L.Nodup := by
    rw [hL, List.nodup_append]
    refine ⟨hnd₁, List.nodup_singleton _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    exact CoordAux.Deg1.ne_highRoot ((hmem₁ a).1 ha)
  have hθL : highRoot τ ∈ L := by
    rw [hL]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hD : ∀ β ∈ Deg1 τ, β ∈ L := fun β hβ => (hLS β).2 ((CoordAux.mem_radRoots_iff β).2 (Or.inl hβ))
  have hpos : ∀ α ∈ L, IsRoot τ α ∧ 0 < height α := fun α hα => ((hLS α).1 hα).1
  have hfac : ∀ q ∈ Qθ τ K, ∃ c, CoordAux.prodX L c = q := fun q hq =>
    exists_list_prod_pinnedX_eq K (S := parabolicRadicalRoots τ (Jθ τ)) (fun α hα => hα.1)
      (fun α hα β hβ a b ha hb hr => add_mem_parabolicRadicalRoots hα.1 hβ ha hb hr) hnd hLS hq
  have hPmem : ∀ c : (Fin τ.rank → ℤ) → K, CoordAux.prodX L c ∈ Qθ τ K := fun c =>
    CoordAux.prodX_mem_rootSpan (fun α hα => (hLS α).1 hα) c
  have hcoord : ∀ (c : (Fin τ.rank → ℤ) → K) β, CoordAux.coordFn L (CoordAux.prodX L c) β =
      if β ∈ Deg1 τ then c β else 0 := fun c β => CoordAux.coordFn_prodX hnd hpos hD c β
  have hsingle : ∀ β ∈ L, ∀ c : K, CoordAux.coordFn L (pinnedX τ K β c) =
      fun γ => if γ ∈ Deg1 τ then (Pi.single β c : (Fin τ.rank → ℤ) → K) γ else 0 := by
    intro β hβ c
    rw [← CoordAux.prodX_single L hnd hβ c]
    funext γ
    exact hcoord _ γ
  have h_deg1 : ∀ β ∈ Deg1 τ, ∀ c : K, CoordAux.coordFn L (pinnedX τ K β c) = Pi.single β c := by
    intro β hβ c
    rw [hsingle β (hD β hβ) c]
    funext γ
    by_cases hγ : γ ∈ Deg1 τ
    · rw [if_pos hγ]
    · rw [if_neg hγ]
      have hγβ : γ ≠ β := fun e => hγ (e ▸ hβ)
      simp [Pi.single_apply, hγβ]
  have h_high : ∀ c : K, CoordAux.coordFn L (pinnedX τ K (highRoot τ) c) = 0 := by
    intro c
    rw [hsingle _ hθL c]
    funext γ
    by_cases hγ : γ ∈ Deg1 τ
    · rw [if_pos hγ]
      have hγθ : γ ≠ highRoot τ := CoordAux.Deg1.ne_highRoot hγ
      simp [Pi.single_apply, hγθ]
    · rw [if_neg hγ]
      rfl
  have h_mul : ∀ q ∈ Qθ τ K, ∀ q' ∈ Qθ τ K,
      CoordAux.coordFn L (q * q') = CoordAux.coordFn L q + CoordAux.coordFn L q' := by
    intro q hq q' hq'
    obtain ⟨c, rfl⟩ := hfac q hq
    obtain ⟨c', rfl⟩ := hfac q' hq'
    have hL₁ : ∀ α ∈ L₁, α ∈ Deg1 τ := fun α hα => (hmem₁ α).1 hα
    obtain ⟨u, hu, e⟩ := CoordAux.exists_mul_prodX hL₁ c c'
    obtain ⟨w, rfl⟩ := mem_rootSubgroup.1 hu
    let d : (Fin τ.rank → ℤ) → K := fun α =>
      if α = highRoot τ then w + (c (highRoot τ) + c' (highRoot τ)) else c α + c' α
    have hd₁ : ∀ α ∈ L₁, d α = c α + c' α := fun α hα => by
      have : α ≠ highRoot τ := CoordAux.Deg1.ne_highRoot (hL₁ α hα)
      simp [d, this]
    have hdθ : d (highRoot τ) = w + (c (highRoot τ) + c' (highRoot τ)) := by simp [d]
    have hθc' : pinnedX τ K (highRoot τ) (c (highRoot τ)) * CoordAux.prodX L₁ c' =
        CoordAux.prodX L₁ c' * pinnedX τ K (highRoot τ) (c (highRoot τ)) :=
      CoordAux.Uθ_comm (mem_rootSubgroup.2 ⟨c (highRoot τ), rfl⟩) (CoordAux.prodX_mem_pos hL₁ c')
    have hprod : CoordAux.prodX L c * CoordAux.prodX L c' = CoordAux.prodX L d := by
      rw [hL, CoordAux.prodX_append, CoordAux.prodX_append, CoordAux.prodX_append,
        CoordAux.prodX_singleton, CoordAux.prodX_singleton, CoordAux.prodX_singleton]
      calc CoordAux.prodX L₁ c * pinnedX τ K (highRoot τ) (c (highRoot τ)) *
            (CoordAux.prodX L₁ c' * pinnedX τ K (highRoot τ) (c' (highRoot τ)))
          = CoordAux.prodX L₁ c * (pinnedX τ K (highRoot τ) (c (highRoot τ)) *
              CoordAux.prodX L₁ c') * pinnedX τ K (highRoot τ) (c' (highRoot τ)) := by
            simp only [mul_assoc]
        _ = CoordAux.prodX L₁ c * (CoordAux.prodX L₁ c' *
              pinnedX τ K (highRoot τ) (c (highRoot τ))) *
              pinnedX τ K (highRoot τ) (c' (highRoot τ)) := by rw [hθc']
        _ = (CoordAux.prodX L₁ c * CoordAux.prodX L₁ c') *
              (pinnedX τ K (highRoot τ) (c (highRoot τ)) *
                pinnedX τ K (highRoot τ) (c' (highRoot τ))) := by simp only [mul_assoc]
        _ = (CoordAux.prodX L₁ (c + c') * pinnedX τ K (highRoot τ) w) *
              (pinnedX τ K (highRoot τ) (c (highRoot τ)) *
                pinnedX τ K (highRoot τ) (c' (highRoot τ))) := by rw [e]
        _ = CoordAux.prodX L₁ (c + c') * pinnedX τ K (highRoot τ)
              (w + (c (highRoot τ) + c' (highRoot τ))) := by
            rw [pinnedX_add, pinnedX_add, mul_assoc]
        _ = CoordAux.prodX L₁ d * pinnedX τ K (highRoot τ) (d (highRoot τ)) := by
            rw [hdθ, CoordAux.prodX_congr (l := L₁) (c := c + c') (c' := d)
              fun α hα => (hd₁ α hα).symm]
    rw [hprod]
    funext β
    rw [hcoord, Pi.add_apply, hcoord, hcoord]
    by_cases hβ : β ∈ Deg1 τ
    · rw [if_pos hβ, if_pos hβ, if_pos hβ]
      exact hd₁ β ((hmem₁ β).2 hβ)
    · simp [hβ]
  have h_eq0 : ∀ q ∈ Qθ τ K, CoordAux.coordFn L q = 0 ↔ q ∈ Uθ τ K := by
    intro q hq
    obtain ⟨c, rfl⟩ := hfac q hq
    constructor
    · intro h0
      have hc0 : ∀ α ∈ L₁, c α = 0 := fun α hα => by
        have := congrFun h0 α
        rw [hcoord, if_pos ((hmem₁ α).1 hα)] at this
        exact this
      have : CoordAux.prodX L c = pinnedX τ K (highRoot τ) (c (highRoot τ)) := by
        rw [hL, CoordAux.prodX_append, CoordAux.prodX_eq_one hc0, one_mul,
          CoordAux.prodX_singleton]
      rw [this]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩
    · intro hU
      obtain ⟨z, hz⟩ := mem_rootSubgroup.1 hU
      rw [← hz]
      exact h_high z
  have h_supp : ∀ q ∈ Qθ τ K, ∀ β, β ∉ Deg1 τ → CoordAux.coordFn L q β = 0 := by
    intro q _ β hβ
    simp [CoordAux.coordFn, hβ]
  have h_surj : ∀ f : (Fin τ.rank → ℤ) → K, (∀ β, β ∉ Deg1 τ → f β = 0) →
      ∃ q ∈ Qθ τ K, CoordAux.coordFn L q = f := by
    intro f hf
    refine ⟨CoordAux.prodX L f, hPmem f, ?_⟩
    funext β
    rw [hcoord]
    by_cases hβ : β ∈ Deg1 τ
    · rw [if_pos hβ]
    · rw [if_neg hβ, hf β hβ]
  have h_comm : ∀ q ∈ Qθ τ K, ∀ β ∈ Deg1 τ, ∀ c : K,
      (∀ γ, CoordAux.coordFn L q γ ≠ 0 → γ + β ∉ rootFinset τ) →
        q * pinnedX τ K β c = pinnedX τ K β c * q := by
    intro q hq β hβ b hcomm
    obtain ⟨c, rfl⟩ := hfac q hq
    refine (CoordAux.commute_prodX (fun α hα hc0 => ?_)).eq
    rcases List.mem_append.1 ((hL ▸ hα : α ∈ L₁ ++ [highRoot τ])) with h | h
    · have hαD : α ∈ Deg1 τ := (hmem₁ α).1 h
      have hnz : CoordAux.coordFn L (CoordAux.prodX L c) α ≠ 0 := by
        rw [hcoord, if_pos hαD]
        exact hc0
      exact CoordAux.commute_pinnedX_of_not_isRoot_add hαD hβ (hcomm α hnz) (c α) b
    · have : α = highRoot τ := List.mem_singleton.1 h
      subst this
      exact (commute_of_mem_posUnipotent CoordAux.isMaxHeight_highRoot'
        (CoordAux.pinnedX_mem_pos hβ b) (c (highRoot τ))).symm
  exact ⟨CoordAux.coordFn L, ⟨h_mul, h_deg1, h_high, h_eq0, h_supp, h_surj, h_comm⟩⟩

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
