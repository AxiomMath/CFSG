module

public import CFSG.LieType.Chevalley.E6GraphInvolutionForms
public import CFSG.LieType.Chevalley.E6GraphLeviTheta

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphRadical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphInvolution
open scoped commutatorElement

@[expose] def pairFirsts : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [(![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ),
    (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ),
    (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ)]

@[expose] def fixedList : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [(![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ),
    (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ),
    (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ),
    (![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)]

@[expose] def degOneList : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  (pairFirsts.flatMap fun β => [β, permLattice TwistTag.E6.perm β]) ++ fixedList

@[expose] def radList : List (Fin TwistTag.E6.tag.rank → ℤ) := degOneList ++ [e6HighestRoot]

theorem radList_nodup : radList.Nodup := by decide

theorem radList_facts : ∀ α ∈ radList, α ∈ rootFinset TwistTag.E6.tag ∧ 0 < height α ∧
    α (e6Idx 1) ≠ 0 := by
  decide +kernel

theorem mem_radList_of_root : ∀ α ∈ rootFinset TwistTag.E6.tag, 0 < height α →
    α (e6Idx 1) ≠ 0 → α ∈ radList := by
  decide +kernel

theorem mem_radList_iff (α : Fin TwistTag.E6.tag.rank → ℤ) :
    α ∈ radList ↔ α ∈ parabolicRadicalRoots TwistTag.E6.tag setA := by
  rw [mem_parabolicRadicalRoots_iff]
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := radList_facts α h
    exact ⟨mem_rootFinset.1 h1, h2, e6Idx 1, fun h => h rfl, h3⟩
  · rintro ⟨h1, h2, i, hi, h3⟩
    have hi' : i = e6Idx 1 := by
      by_contra h
      exact hi h
    subst hi'
    exact mem_radList_of_root α (mem_rootFinset.2 h1) h2 h3

theorem radList_pos
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ radList) :
    IsRoot TwistTag.E6.tag α ∧ 0 < height α :=
  parabolicRadicalRoots_pos ((mem_radList_iff α).1 hα)

theorem radRoots_closed
    : ∀ α ∈ parabolicRadicalRoots TwistTag.E6.tag setA,
    ∀ β ∈ parabolicRadicalRoots TwistTag.E6.tag setA, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) →
        a • α + b • β ∈ parabolicRadicalRoots TwistTag.E6.tag setA :=
  fun _ hα _ hβ _ _ ha hb hr => add_mem_parabolicRadicalRoots (parabolicRadicalRoots_pos hα) hβ
    ha hb hr

theorem radList_add : ∀ α ∈ radList, ∀ β ∈ radList, α + β ∈ rootFinset TwistTag.E6.tag →
    α + β = e6HighestRoot := by
  decide +kernel

theorem degOneList_sub : degOneList ⊆ radList := List.subset_append_left _ _

theorem theta_not_mem_degOneList : e6HighestRoot ∉ degOneList := by decide

theorem ne_theta_of_mem_degOneList {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ degOneList) :
    β ≠ e6HighestRoot := fun h => theta_not_mem_degOneList (h ▸ hβ)

section Reorder

variable {E : Type} [Field E]

theorem pinnedX_mem_parabolicRadical
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ radList)
    (c : E) : pinnedX TwistTag.E6.tag E α c ∈ parabolicRadical TwistTag.E6.tag E setA :=
  pinnedX_mem_rootSpan ((mem_radList_iff α).1 hα) c

theorem list_prod_mem_parabolicRadical
    {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hL : L ⊆ radList) (c : (Fin TwistTag.E6.tag.rank → ℤ) → E) :
    (L.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod ∈
      parabolicRadical TwistTag.E6.tag E setA := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hg
  exact pinnedX_mem_parabolicRadical (hL hα) _

theorem mem_posUnipotent_of_mem_parabolicRadical
    {g : ModGL TwistTag.E6.tag E}
    (hg : g ∈ parabolicRadical TwistTag.E6.tag E setA) : g ∈ posUnipotent TwistTag.E6.tag E :=
  parabolicRadical_le_posUnipotent setA hg

theorem theta_mul_comm
    {g : ModGL TwistTag.E6.tag E}
    (hg : g ∈ parabolicRadical TwistTag.E6.tag E setA) (e : E) :
    pinnedX TwistTag.E6.tag E e6HighestRoot e * g = g * pinnedX TwistTag.E6.tag E e6HighestRoot e :=
  (commute_e6HighestRoot_of_mem_posUnipotent E (mem_posUnipotent_of_mem_parabolicRadical hg)
    e).eq.symm

theorem pinnedX_mul_pinnedX_radList
    (h2 : (2 : E) = 0) {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ radList) (hβ : β ∈ radList) (c d : E) :
    ∃ e : E, pinnedX TwistTag.E6.tag E α c * pinnedX TwistTag.E6.tag E β d =
      pinnedX TwistTag.E6.tag E β d * pinnedX TwistTag.E6.tag E α c *
        pinnedX TwistTag.E6.tag E e6HighestRoot e := by
  have hαr := radList_pos hα
  have hβr := radList_pos hβ
  by_cases hab : α = β
  · subst hab
    refine ⟨0, ?_⟩
    rw [pinnedX_zero, mul_one, ← pinnedX_add, ← pinnedX_add, add_comm]
  have hne' : α ≠ -β := by
    intro h
    have := hαr.2
    rw [h, height_neg] at this
    linarith [hβr.2]
  by_cases hr : IsRoot TwistTag.E6.tag (α + β)
  · have hθ := radList_add α hα β hβ (mem_rootFinset.2 hr)
    have hc := commutator_pinnedX_of_two h2 hαr.1 hβr.1 hab hne' hr c d
    rw [hθ] at hc
    refine ⟨c * d, ?_⟩
    have e1 : pinnedX TwistTag.E6.tag E α c * pinnedX TwistTag.E6.tag E β d =
        pinnedX TwistTag.E6.tag E e6HighestRoot (c * d) *
          (pinnedX TwistTag.E6.tag E β d * pinnedX TwistTag.E6.tag E α c) := by
      rw [← hc, commutatorElement_def]
      group
    rw [e1, theta_mul_comm (mul_mem (pinnedX_mem_parabolicRadical hβ d)
      (pinnedX_mem_parabolicRadical hα c))]
  · refine ⟨0, ?_⟩
    rw [pinnedX_zero, mul_one]
    exact ((simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl)) hαr.1 hβr.1
      hab hne').2 hr E _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)).eq

theorem list_prod_mul_pinnedX
    (h2 : (2 : E) = 0) {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hL : L ⊆ radList) (d : (Fin TwistTag.E6.tag.rank → ℤ) → E)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : γ ∈ radList) (t : E) :
    ∃ e : E, (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod *
        pinnedX TwistTag.E6.tag E γ t =
      pinnedX TwistTag.E6.tag E γ t * (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod *
        pinnedX TwistTag.E6.tag E e6HighestRoot e := by
  induction L with
  | nil =>
    refine ⟨0, ?_⟩
    simp [pinnedX_zero]
  | cons α L ih =>
    have hα : α ∈ radList := hL (List.mem_cons_self ..)
    obtain ⟨e₁, he₁⟩ := ih fun x hx => hL (List.mem_cons_of_mem _ hx)
    obtain ⟨e₂, he₂⟩ := pinnedX_mul_pinnedX_radList h2 hα hγ (d α) t
    refine ⟨e₂ + e₁, ?_⟩
    have hP := list_prod_mem_parabolicRadical (fun x hx => hL (List.mem_cons_of_mem _ hx)) d
    rw [List.map_cons, List.prod_cons, mul_assoc, he₁, ← mul_assoc, ← mul_assoc, he₂,
      pinnedX_add]
    calc pinnedX TwistTag.E6.tag E γ t * pinnedX TwistTag.E6.tag E α (d α) *
          pinnedX TwistTag.E6.tag E e6HighestRoot e₂ *
          (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod *
          pinnedX TwistTag.E6.tag E e6HighestRoot e₁ =
        pinnedX TwistTag.E6.tag E γ t * pinnedX TwistTag.E6.tag E α (d α) *
          (pinnedX TwistTag.E6.tag E e6HighestRoot e₂ *
            (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod) *
          pinnedX TwistTag.E6.tag E e6HighestRoot e₁ := by group
      _ = _ := by rw [theta_mul_comm hP]; group

theorem list_prod_mul_list_prod
    (h2 : (2 : E) = 0) {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hL : L ⊆ radList) (c d : (Fin TwistTag.E6.tag.rank → ℤ) → E) :
    ∃ e : E, (L.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod *
        (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod =
      (L.map fun α => pinnedX TwistTag.E6.tag E α (c α + d α)).prod *
        pinnedX TwistTag.E6.tag E e6HighestRoot e := by
  induction L with
  | nil =>
    refine ⟨0, ?_⟩
    simp [pinnedX_zero]
  | cons α L ih =>
    have hα : α ∈ radList := hL (List.mem_cons_self ..)
    have hL' : L ⊆ radList := fun x hx => hL (List.mem_cons_of_mem _ hx)
    obtain ⟨e₁, he₁⟩ := list_prod_mul_pinnedX h2 hL' c hα (d α)
    obtain ⟨e₂, he₂⟩ := ih hL'
    refine ⟨e₂ + e₁, ?_⟩
    have hPd := list_prod_mem_parabolicRadical hL' d
    simp only [List.map_cons, List.prod_cons]
    calc pinnedX TwistTag.E6.tag E α (c α) *
          (L.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod *
          (pinnedX TwistTag.E6.tag E α (d α) *
            (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod) =
        pinnedX TwistTag.E6.tag E α (c α) *
          ((L.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod *
            pinnedX TwistTag.E6.tag E α (d α)) *
          (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod := by group
      _ = pinnedX TwistTag.E6.tag E α (c α) * pinnedX TwistTag.E6.tag E α (d α) *
          (L.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod *
          (pinnedX TwistTag.E6.tag E e6HighestRoot e₁ *
            (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod) := by rw [he₁]; group
      _ = pinnedX TwistTag.E6.tag E α (c α + d α) *
          ((L.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod *
            (L.map fun α => pinnedX TwistTag.E6.tag E α (d α)).prod) *
          pinnedX TwistTag.E6.tag E e6HighestRoot e₁ := by
          rw [theta_mul_comm hPd, pinnedX_add]; group
      _ = _ := by
          rw [he₂, pinnedX_add (τ := TwistTag.E6.tag) (R := E) e6HighestRoot e₂ e₁]
          group

theorem list_prod_perm_eq_mul
    (h2 : (2 : E) = 0) {L L' : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hp : L.Perm L') (hL : L ⊆ radList) (f : (Fin TwistTag.E6.tag.rank → ℤ) → E) :
    ∃ e : E, (L.map fun α => pinnedX TwistTag.E6.tag E α (f α)).prod =
      (L'.map fun α => pinnedX TwistTag.E6.tag E α (f α)).prod *
        pinnedX TwistTag.E6.tag E e6HighestRoot e := by
  induction hp with
  | nil =>
    refine ⟨0, ?_⟩
    simp [pinnedX_zero]
  | cons x p ih =>
    obtain ⟨e, he⟩ := ih fun y hy => hL (List.mem_cons_of_mem _ hy)
    refine ⟨e, ?_⟩
    simp only [List.map_cons, List.prod_cons]
    rw [he, mul_assoc]
  | swap x y l =>
    have hx : x ∈ radList := hL (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hy : y ∈ radList := hL (List.mem_cons_self ..)
    have hl : l ⊆ radList := fun z hz =>
      hL (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
    obtain ⟨e, he⟩ := pinnedX_mul_pinnedX_radList h2 hy hx (f y) (f x)
    refine ⟨e, ?_⟩
    have hP := list_prod_mem_parabolicRadical hl f
    simp only [List.map_cons, List.prod_cons]
    calc pinnedX TwistTag.E6.tag E y (f y) * (pinnedX TwistTag.E6.tag E x (f x) *
          (l.map fun α => pinnedX TwistTag.E6.tag E α (f α)).prod) =
        pinnedX TwistTag.E6.tag E y (f y) * pinnedX TwistTag.E6.tag E x (f x) *
          (l.map fun α => pinnedX TwistTag.E6.tag E α (f α)).prod := by group
      _ = pinnedX TwistTag.E6.tag E x (f x) * pinnedX TwistTag.E6.tag E y (f y) *
          (pinnedX TwistTag.E6.tag E e6HighestRoot e *
            (l.map fun α => pinnedX TwistTag.E6.tag E α (f α)).prod) := by rw [he]; group
      _ = _ := by rw [theta_mul_comm hP]; group
  | trans p₁ p₂ ih₁ ih₂ =>
    obtain ⟨e₁, he₁⟩ := ih₁ hL
    obtain ⟨e₂, he₂⟩ := ih₂ fun z hz => hL (p₁.symm.subset hz)
    refine ⟨e₂ + e₁, ?_⟩
    rw [he₁, he₂, pinnedX_add (τ := TwistTag.E6.tag) (R := E) e6HighestRoot e₂ e₁, mul_assoc]

end Reorder

section Coord

variable {E : Type} [Field E]

theorem exists_radParams
    {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA) :
    ∃ c : (Fin TwistTag.E6.tag.rank → ℤ) → E,
      (radList.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod = q :=
  exists_list_prod_pinnedX_eq E (S := parabolicRadicalRoots TwistTag.E6.tag setA)
    (fun _ hα => parabolicRadicalRoots_pos hα) radRoots_closed radList_nodup mem_radList_iff hq

open _root_.Classical in
@[expose] def radCoord
    (q : ModGL TwistTag.E6.tag E) : (Fin TwistTag.E6.tag.rank → ℤ) → E :=
  if h : q ∈ parabolicRadical TwistTag.E6.tag E setA then (exists_radParams h).choose else 0

theorem radCoord_spec
    {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA) :
    (radList.map fun α => pinnedX TwistTag.E6.tag E α (radCoord q α)).prod = q := by
  rw [radCoord, dite_eq_left hq]
  exact (exists_radParams hq).choose_spec

theorem list_prod_radList
    (c : (Fin TwistTag.E6.tag.rank → ℤ) → E) :
    (radList.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod =
      (degOneList.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod *
        pinnedX TwistTag.E6.tag E e6HighestRoot (c e6HighestRoot) := by
  rw [radList, List.map_append, List.prod_append]
  simp

theorem radCoord_eq_of_mul
    {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA) {c : (Fin TwistTag.E6.tag.rank → ℤ) → E}
    {e : E} (h : (radList.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod *
      pinnedX TwistTag.E6.tag E e6HighestRoot e = q) :
    ∀ β ∈ degOneList, c β = radCoord q β := by
  set c' := Function.update c e6HighestRoot (c e6HighestRoot + e) with hc'
  have hdeg : (degOneList.map fun α => pinnedX TwistTag.E6.tag E α (c' α)) =
      degOneList.map fun α => pinnedX TwistTag.E6.tag E α (c α) :=
    List.map_congr_left fun β hβ => by
      rw [hc', Function.update_of_ne (ne_theta_of_mem_degOneList hβ)]
  have hq' : (radList.map fun α => pinnedX TwistTag.E6.tag E α (c' α)).prod = q := by
    rw [list_prod_radList, hdeg, hc', Function.update_self, pinnedX_add, ← mul_assoc,
      ← list_prod_radList, h]
  have := pinnedX_list_prod_injective radList radList_nodup (fun α hα => radList_pos hα) c'
    (radCoord q) (by rw [hq', radCoord_spec hq])
  intro β hβ
  rw [← this β (degOneList_sub hβ), hc', Function.update_of_ne (ne_theta_of_mem_degOneList hβ)]

theorem radCoord_mul
    (h2 : (2 : E) = 0) {q q' : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA)
    (hq' : q' ∈ parabolicRadical TwistTag.E6.tag E setA) :
    ∀ β ∈ degOneList, radCoord (q * q') β = radCoord q β + radCoord q' β := by
  obtain ⟨e, he⟩ := list_prod_mul_list_prod h2 (List.Subset.refl radList) (radCoord q)
    (radCoord q')
  rw [radCoord_spec hq, radCoord_spec hq'] at he
  intro β hβ
  exact (radCoord_eq_of_mul (mul_mem hq hq') he.symm β hβ).symm

theorem list_prod_ite_eq_one
    {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : γ ∉ L) (t : E) :
    (L.map fun α => pinnedX TwistTag.E6.tag E α (if α = γ then t else 0)).prod = 1 := by
  induction L with
  | nil => rfl
  | cons α L ih =>
    rw [List.map_cons, List.prod_cons, ih (fun h => hγ (List.mem_cons_of_mem _ h)),
      ite_eq_right (fun h : α = γ => hγ (h ▸ List.mem_cons_self ..)), pinnedX_zero, one_mul]

theorem list_prod_ite
    {L : List (Fin TwistTag.E6.tag.rank → ℤ)} (hL : L.Nodup)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : γ ∈ L) (t : E) :
    (L.map fun α => pinnedX TwistTag.E6.tag E α (if α = γ then t else 0)).prod =
      pinnedX TwistTag.E6.tag E γ t := by
  induction L with
  | nil => simp at hγ
  | cons α L ih =>
    rw [List.map_cons, List.prod_cons]
    obtain ⟨hαL, hL'⟩ := List.nodup_cons.1 hL
    by_cases h : α = γ
    · subst h
      rw [ite_eq_left rfl, list_prod_ite_eq_one hαL, mul_one]
    · rw [ite_eq_right h, pinnedX_zero, one_mul,
        ih hL' ((List.mem_cons.1 hγ).resolve_left (Ne.symm h))]

theorem radCoord_pinnedX
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : γ ∈ degOneList) (t : E) :
    ∀ β ∈ degOneList, radCoord (pinnedX TwistTag.E6.tag E γ t) β = if β = γ then t else 0 := by
  have h := list_prod_ite (E := E) radList_nodup (degOneList_sub hγ) t
  have h' : (radList.map fun α => pinnedX TwistTag.E6.tag E α (if α = γ then t else 0)).prod *
      pinnedX TwistTag.E6.tag E e6HighestRoot 0 = pinnedX TwistTag.E6.tag E γ t := by
    rw [pinnedX_zero, mul_one, h]
  intro β hβ
  exact (radCoord_eq_of_mul (pinnedX_mem_parabolicRadical (degOneList_sub hγ) t) h' β hβ).symm

theorem radCoord_one
    : ∀ β ∈ degOneList, radCoord (1 : ModGL TwistTag.E6.tag E) β = 0 := by
  have h : (radList.map fun α => pinnedX TwistTag.E6.tag E α ((fun _ => (0 : E)) α)).prod *
      pinnedX TwistTag.E6.tag E e6HighestRoot 0 = 1 := by
    simp [pinnedX_zero]
  intro β hβ
  exact (radCoord_eq_of_mul (one_mem _) h β hβ).symm

theorem radCoord_inv
    (h2 : (2 : E) = 0) {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA) :
    ∀ β ∈ degOneList, radCoord q⁻¹ β = -radCoord q β := by
  intro β hβ
  have h := radCoord_mul h2 hq (inv_mem hq) β hβ
  rw [mul_inv_cancel, radCoord_one β hβ] at h
  linear_combination -h

theorem eq_pinnedX_theta_of_radCoord
    {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA)
    (h : ∀ β ∈ degOneList, radCoord q β = 0) :
    q = pinnedX TwistTag.E6.tag E e6HighestRoot (radCoord q e6HighestRoot) := by
  conv_lhs => rw [← radCoord_spec hq]
  rw [list_prod_radList]
  have h1 : (degOneList.map fun α => pinnedX TwistTag.E6.tag E α (radCoord q α)) =
      degOneList.map fun _ => 1 :=
    List.map_congr_left fun β hβ => by rw [h β hβ, pinnedX_zero]
  rw [h1]
  simp

theorem radCoord_transport
    (h2 : (2 : E) = 0) (q : ModGL TwistTag.E6.tag E)
    {π π' : (Fin TwistTag.E6.tag.rank → ℤ) → (Fin TwistTag.E6.tag.rank → ℤ)}
    (hπ : (radList.map π).Perm radList) (hπ'π : ∀ α ∈ radList, π' (π α) = α) (g : E → E)
    {q' : ModGL TwistTag.E6.tag E}
    (hq' : q' = (radList.map fun α => pinnedX TwistTag.E6.tag E (π α) (g (radCoord q α))).prod) :
    q' ∈ parabolicRadical TwistTag.E6.tag E setA ∧
      ∀ β ∈ degOneList, radCoord q' β = g (radCoord q (π' β)) := by
  have hL : (radList.map fun α => pinnedX TwistTag.E6.tag E (π α) (g (radCoord q α))) =
      (radList.map π).map fun β => pinnedX TwistTag.E6.tag E β (g (radCoord q (π' β))) := by
    rw [List.map_map]
    exact List.map_congr_left fun α hα => by simp only [Function.comp_apply, hπ'π α hα]
  obtain ⟨e, he⟩ := list_prod_perm_eq_mul h2 hπ (fun x hx => hπ.subset hx)
    (fun β => g (radCoord q (π' β)))
  rw [← hL, ← hq'] at he
  have hmem : q' ∈ parabolicRadical TwistTag.E6.tag E setA := by
    rw [he]
    exact mul_mem (list_prod_mem_parabolicRadical (List.Subset.refl _) _)
      (pinnedX_mem_parabolicRadical (List.mem_append_right _ (List.mem_singleton_self _)) e)
  exact ⟨hmem, fun β hβ => (radCoord_eq_of_mul hmem he.symm β hβ).symm⟩

end Coord

section Maps

variable {E : Type} [Field E]

theorem conj_list_prod {G : Type*} [Group G] (g : G) {ι : Type*} (L : List ι) (f : ι → G) :
    g * (L.map f).prod * g⁻¹ = (L.map fun x => g * f x * g⁻¹).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    group

theorem radList_perm_permLattice : (radList.map (permLattice TwistTag.E6.perm)).Perm radList := by
  decide +kernel

theorem diagramMap_conj_pinnedX_of_two
    (h2 : (2 : E) = 0) {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (c : E) :
    diagramMap TwistTag.E6 E * pinnedX TwistTag.E6.tag E α c * (diagramMap TwistTag.E6 E)⁻¹ =
      pinnedX TwistTag.E6.tag E (permLattice TwistTag.E6.perm α) c := by
  rw [← twistHom_id_eq, twistHom_id_pinnedX h2 hα]

theorem radCoord_diagramMap_conj
    (h2 : (2 : E) = 0) {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA) :
    diagramMap TwistTag.E6 E * q * (diagramMap TwistTag.E6 E)⁻¹ ∈
        parabolicRadical TwistTag.E6.tag E setA ∧
      ∀ β ∈ degOneList, radCoord (diagramMap TwistTag.E6 E * q * (diagramMap TwistTag.E6 E)⁻¹) β =
        radCoord q (permLattice TwistTag.E6.perm.symm β) := by
  refine radCoord_transport h2 q radList_perm_permLattice
    (fun α _ => permLattice_symm_permLattice _ α) id ?_
  conv_lhs => rw [← radCoord_spec hq]
  rw [conj_list_prod]
  exact congrArg List.prod (List.map_congr_left fun α hα =>
    diagramMap_conj_pinnedX_of_two h2 (radList_pos hα).1 _)

theorem radCoord_twistHom
    (h2 : (2 : E) = 0) (σ : E →+* E) {q : ModGL TwistTag.E6.tag E}
    (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA) :
    twistHom TwistTag.E6 E σ q ∈ parabolicRadical TwistTag.E6.tag E setA ∧
      ∀ β ∈ degOneList, radCoord (twistHom TwistTag.E6 E σ q) β =
        σ (radCoord q (permLattice TwistTag.E6.perm.symm β)) := by
  refine radCoord_transport h2 q radList_perm_permLattice
    (fun α _ => permLattice_symm_permLattice _ α) σ ?_
  conv_lhs => rw [← radCoord_spec hq]
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun α hα => by
    simp only [Function.comp_apply]
    rw [twistHom_apply, units_map_entrywiseHom_pinnedX',
      diagramMap_conj_pinnedX_of_two h2 (radList_pos hα).1])

theorem radCoord_wordElt_conj
    (h2 : (2 : E) = 0) (ω : List (Fin TwistTag.E6.tag.rank))
    (hω : (radList.map fun α => (coxeterSystem TwistTag.E6.tag).wordProd ω • α).Perm radList)
    {q : ModGL TwistTag.E6.tag E} (hq : q ∈ parabolicRadical TwistTag.E6.tag E setA) :
    wordElt E ω * q * (wordElt E ω)⁻¹ ∈ parabolicRadical TwistTag.E6.tag E setA ∧
      ∀ β ∈ degOneList, radCoord (wordElt E ω * q * (wordElt E ω)⁻¹) β =
        radCoord q (((coxeterSystem TwistTag.E6.tag).wordProd ω)⁻¹ • β) := by
  refine radCoord_transport h2 q hω (fun α _ => inv_smul_smul _ α) id ?_
  conv_lhs => rw [← radCoord_spec hq]
  rw [conj_list_prod]
  exact congrArg List.prod (List.map_congr_left fun α hα =>
    wordElt_conj_pinnedX h2 ω (radList_pos hα).1 _)

end Maps

end CFSG.LieType.Chevalley.E6GraphRadical
