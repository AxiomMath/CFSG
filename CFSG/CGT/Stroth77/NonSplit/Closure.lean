module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Card

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [DecidableEq G]

@[expose] def expandList (gens : List G) (s : G) (vis : List G) : List G :=
  gens.foldl (fun acc g => if s * g ∈ acc then acc else acc ++ [s * g]) vis

@[expose] def closeList (gens : List G) : ℕ → List G → ℕ → List G
  | 0, vis, _ => vis
  | fuel + 1, vis, i =>
    if h : i < vis.length then closeList gens fuel (expandList gens (vis[i]) vis) (i + 1) else vis

@[expose] def bfsList (gens : List G) (fuel : ℕ) : List G := closeList gens fuel [1] 0

theorem expandList_subset (gens : List G) (s : G) (vis : List G) {S : Set G}
    (hs : s ∈ S) (hg : ∀ g ∈ gens, g ∈ S) (hS : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hvis : ∀ v ∈ vis, v ∈ S) : ∀ v ∈ expandList gens s vis, v ∈ S := by
  unfold expandList
  suffices h : ∀ (l : List G), (∀ g ∈ l, g ∈ gens) → ∀ acc : List G, (∀ v ∈ acc, v ∈ S) →
      ∀ v ∈ l.foldl (fun acc g => if s * g ∈ acc then acc else acc ++ [s * g]) acc, v ∈ S from
    h gens (fun _ h => h) vis hvis
  intro l
  induction l with
  | nil => intro _ acc hacc; simpa using hacc
  | cons g l ih =>
    intro hl acc hacc
    simp only [List.foldl_cons]
    refine ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ ?_
    split_ifs with h
    · exact hacc
    · intro v hv
      rcases List.mem_append.1 hv with h' | h'
      · exact hacc v h'
      · rw [List.mem_singleton.1 h']
        exact hS _ hs _ (hg g (hl g (List.mem_cons_self)))

theorem expandList_sublist (gens : List G) (s : G) (vis : List G) :
    ∀ v ∈ vis, v ∈ expandList gens s vis := by
  unfold expandList
  suffices h : ∀ (l : List G) (acc : List G), ∀ v ∈ acc,
      v ∈ l.foldl (fun acc g => if s * g ∈ acc then acc else acc ++ [s * g]) acc from h gens vis
  intro l
  induction l with
  | nil => intro acc v hv; simpa using hv
  | cons g l ih =>
    intro acc v hv
    simp only [List.foldl_cons]
    refine ih _ v ?_
    split_ifs with h
    · exact hv
    · exact List.mem_append_left _ hv

theorem expandList_length (gens : List G) (s : G) (vis : List G) :
    vis.length ≤ (expandList gens s vis).length := by
  unfold expandList
  suffices h : ∀ (l : List G) (acc : List G),
      acc.length ≤ (l.foldl (fun acc g => if s * g ∈ acc then acc else acc ++ [s * g]) acc).length
    from h gens vis
  intro l
  induction l with
  | nil => intro acc; simp
  | cons g l ih =>
    intro acc
    simp only [List.foldl_cons]
    refine le_trans ?_ (ih _)
    split_ifs with h
    · exact le_rfl
    · simp

theorem closeList_subset (gens : List G) {S : Set G} (hg : ∀ g ∈ gens, g ∈ S)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) :
    ∀ (fuel : ℕ) (vis : List G) (i : ℕ), (∀ v ∈ vis, v ∈ S) → ∀ v ∈ closeList gens fuel vis i,
      v ∈ S := by
  intro fuel
  induction fuel with
  | zero => intro vis i h v hv; exact h v hv
  | succ fuel ih =>
    intro vis i hvis v hv
    unfold closeList at hv
    split_ifs at hv with hi
    · refine ih _ _ ?_ v hv
      exact expandList_subset gens _ vis (hvis _ (List.getElem_mem hi)) hg hS hvis
    · exact hvis v hv

theorem bfsList_subset (gens : List G) (fuel : ℕ) :
    ∀ v ∈ bfsList gens fuel, v ∈ Subgroup.closure {g | g ∈ gens} := by
  refine closeList_subset gens (S := Subgroup.closure {g | g ∈ gens})
    (fun g hg => Subgroup.subset_closure hg) (fun a ha b hb => mul_mem ha hb) fuel [1] 0 ?_
  intro v hv
  rw [List.mem_singleton.1 hv]
  exact one_mem _

theorem one_mem_bfsList (gens : List G) (fuel : ℕ) : (1 : G) ∈ bfsList gens fuel := by
  have : ∀ (fuel : ℕ) (vis : List G) (i : ℕ), (1 : G) ∈ vis → (1 : G) ∈ closeList gens fuel vis i := by
    intro fuel
    induction fuel with
    | zero => intro vis i h; exact h
    | succ fuel ih =>
      intro vis i h
      unfold closeList
      split_ifs with hi
      · exact ih _ _ (expandList_sublist gens _ vis _ h)
      · exact h
  exact this fuel [1] 0 (List.mem_singleton_self 1)

variable [Finite G]

theorem closure_subset_of_closed (gens : List G) (L : List G) (h1 : 1 ∈ L)
    (hS : ∀ s ∈ L, ∀ g ∈ gens, s * g ∈ L) : ∀ c ∈ Subgroup.closure {g | g ∈ gens}, c ∈ L := by
  classical
  let S : Finset G := L.toFinset
  have key : ∀ h : G, (∀ s ∈ S, s * h ∈ S) → ∀ s ∈ S, s * h⁻¹ ∈ S := by
    intro h hh
    have hinj : Function.Injective fun s : G => s * h := fun a b hab => mul_right_cancel hab
    have himg : S.image (fun s => s * h) = S :=
      Finset.eq_of_subset_of_card_le (fun y hy => by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy; exact hh s hs)
        (by rw [Finset.card_image_of_injective _ hinj])
    intro s hs
    have : s ∈ S.image (fun s => s * h) := by rw [himg]; exact hs
    obtain ⟨s', hs', hss'⟩ := Finset.mem_image.1 this
    have : s * h⁻¹ = s' := by rw [← hss']; simp
    rw [this]; exact hs'
  let H : Subgroup G :=
    { carrier := {h | ∀ s ∈ S, s * h ∈ S}
      mul_mem' := fun {a b} ha hb s hs => by
        have := hb _ (ha s hs); rwa [mul_assoc] at this
      one_mem' := fun s hs => by simpa using hs
      inv_mem' := fun {h} hh => key h hh }
  have hle : Subgroup.closure {g | g ∈ gens} ≤ H :=
    (Subgroup.closure_le H).2 fun g hg s hs => by
      simpa [S] using hS s (by simpa [S] using hs) g hg
  intro c hc
  have := hle hc 1 (by simpa [S] using h1)
  simpa [S] using this

theorem mem_closure_iff_of_stable (gens L : List G) (h1 : 1 ∈ L)
    (hsub : ∀ s ∈ L, s ∈ Subgroup.closure {g | g ∈ gens})
    (hst : ∀ s ∈ L, ∀ g ∈ gens, s * g ∈ L) (g : G) :
    g ∈ Subgroup.closure {g | g ∈ gens} ↔ g ∈ L :=
  ⟨closure_subset_of_closed gens L h1 hst g, hsub g⟩

theorem card_closure_of_stable (gens L : List G) (h1 : 1 ∈ L)
    (hsub : ∀ s ∈ L, s ∈ Subgroup.closure {g | g ∈ gens})
    (hst : ∀ s ∈ L, ∀ g ∈ gens, s * g ∈ L) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = L.toFinset.card := by
  have hset : ((Subgroup.closure {g | g ∈ gens} : Subgroup G) : Set G) = ↑L.toFinset :=
    Set.ext fun g => by
      rw [SetLike.mem_coe, mem_closure_iff_of_stable gens L h1 hsub hst, Finset.mem_coe,
        List.mem_toFinset]
  show Nat.card ((Subgroup.closure {g | g ∈ gens} : Subgroup G) : Set G) = _
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset]

@[expose] def stableB (gens L : List G) : Bool := L.all fun s => gens.all fun g => decide (s * g ∈ L)

theorem stableB_iff (gens L : List G) :
    stableB gens L = true ↔ ∀ s ∈ L, ∀ g ∈ gens, s * g ∈ L := by
  simp [stableB]

theorem mem_closure_bfs (gens : List G) (fuel : ℕ) (h : stableB gens (bfsList gens fuel) = true)
    (g : G) : g ∈ Subgroup.closure {g | g ∈ gens} ↔ g ∈ bfsList gens fuel :=
  mem_closure_iff_of_stable gens _ (one_mem_bfsList gens fuel) (bfsList_subset gens fuel)
    ((stableB_iff _ _).1 h) g

theorem card_closure_bfs (gens : List G) (fuel : ℕ) (h : stableB gens (bfsList gens fuel) = true) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = (bfsList gens fuel).toFinset.card :=
  card_closure_of_stable gens _ (one_mem_bfsList gens fuel) (bfsList_subset gens fuel)
    ((stableB_iff _ _).1 h)

end CFSG.CGT.Stroth77
