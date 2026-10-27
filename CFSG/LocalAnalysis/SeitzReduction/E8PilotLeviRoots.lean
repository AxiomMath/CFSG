module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots

public section

namespace CFSG.SeitzReduction.E8Pilot

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction.EPilot

@[expose] def e7Node (j : Fin (Tag.rank .E7)) : Fin (Tag.rank .E8) :=
  ⟨j, Nat.lt_succ_of_lt j.isLt⟩

@[expose] def e7Embed (v : Fin (Tag.rank .E7) → ℤ) : Fin (Tag.rank .E8) → ℤ :=
  fun i => if h : (i : ℕ) < Tag.rank .E7 then v ⟨i, h⟩ else 0

@[expose] def e8Restrict (γ : Fin (Tag.rank .E8) → ℤ) : Fin (Tag.rank .E7) → ℤ :=
  fun i => γ (e7Node i)

theorem e7Embed_e7Node (v : Fin (Tag.rank .E7) → ℤ) (j : Fin (Tag.rank .E7)) :
    e7Embed v (e7Node j) = v j :=
  dite_eq_left (c := ((e7Node j : Fin (Tag.rank .E8)) : ℕ) < Tag.rank .E7) j.isLt

theorem e7Embed_highNode (v : Fin (Tag.rank .E7) → ℤ) : e7Embed v (highNode .E8) = 0 :=
  dite_eq_right (c := ((highNode .E8 : Fin (Tag.rank .E8)) : ℕ) < Tag.rank .E7) (by decide)

theorem e8Restrict_e7Embed (v : Fin (Tag.rank .E7) → ℤ) : e8Restrict (e7Embed v) = v := by
  funext i
  exact e7Embed_e7Node v i

theorem eq_e7Node_or_eq_highNode (i : Fin (Tag.rank .E8)) :
    (∃ j, i = e7Node j) ∨ i = highNode .E8 := by
  by_cases h : (i : ℕ) < Tag.rank .E7
  · exact Or.inl ⟨⟨i, h⟩, Fin.ext rfl⟩
  · refine Or.inr (Fin.ext ?_)
    have := i.isLt
    change (i : ℕ) < 8 at this
    change ¬ (i : ℕ) < 7 at h
    change (i : ℕ) = 7
    omega

theorem e7Embed_e8Restrict {γ : Fin (Tag.rank .E8) → ℤ} (hγ : γ (highNode .E8) = 0) :
    e7Embed (e8Restrict γ) = γ := by
  funext i
  rcases eq_e7Node_or_eq_highNode i with ⟨j, rfl⟩ | rfl
  · rw [e7Embed_e7Node]
    rfl
  · rw [e7Embed_highNode, hγ]

theorem e7Embed_injective : Function.Injective e7Embed := fun v w h => by
  rw [← e8Restrict_e7Embed v, h, e8Restrict_e7Embed]

theorem ext_e7Node {γ δ : Fin (Tag.rank .E8) → ℤ} (h : ∀ j, γ (e7Node j) = δ (e7Node j))
    (h0 : γ (highNode .E8) = δ (highNode .E8)) : γ = δ := by
  funext i
  rcases eq_e7Node_or_eq_highNode i with ⟨j, rfl⟩ | rfl
  exacts [h j, h0]

theorem e7Embed_add (v w : Fin (Tag.rank .E7) → ℤ) :
    e7Embed (v + w) = e7Embed v + e7Embed w :=
  ext_e7Node (fun j => by simp only [e7Embed_e7Node, Pi.add_apply])
    (by simp only [e7Embed_highNode, Pi.add_apply, add_zero])

theorem e7Embed_neg (v : Fin (Tag.rank .E7) → ℤ) : e7Embed (-v) = -e7Embed v :=
  ext_e7Node (fun j => by simp only [e7Embed_e7Node, Pi.neg_apply])
    (by simp only [e7Embed_highNode, Pi.neg_apply, neg_zero])

theorem e7Embed_sub (v w : Fin (Tag.rank .E7) → ℤ) :
    e7Embed (v - w) = e7Embed v - e7Embed w := by
  rw [sub_eq_add_neg, e7Embed_add, e7Embed_neg, ← sub_eq_add_neg]

theorem e7Embed_smul (n : ℤ) (v : Fin (Tag.rank .E7) → ℤ) : e7Embed (n • v) = n • e7Embed v :=
  ext_e7Node (fun j => by simp only [e7Embed_e7Node, Pi.smul_apply])
    (by simp only [e7Embed_highNode, Pi.smul_apply, smul_zero])

theorem e7Embed_zero : e7Embed 0 = 0 :=
  ext_e7Node (fun j => by simp only [e7Embed_e7Node, Pi.zero_apply])
    (by simp only [e7Embed_highNode, Pi.zero_apply])

theorem e7Node_injective : Function.Injective e7Node := fun _ _ h =>
  Fin.ext (congrArg Fin.val h :)

theorem e7Node_ne_highNode (j : Fin (Tag.rank .E7)) : e7Node j ≠ highNode .E8 := by
  intro h
  have h' := congrArg Fin.val h
  have := j.isLt
  change (j : ℕ) = 7 at h'
  change (j : ℕ) < 7 at this
  omega

theorem e7Embed_single (j : Fin (Tag.rank .E7)) :
    e7Embed (Pi.single j 1) = Pi.single (e7Node j) 1 := by
  refine ext_e7Node (fun i => ?_) ?_
  · rw [e7Embed_e7Node]
    by_cases hij : i = j
    · rw [hij, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (fun h => hij (e7Node_injective h))]
  · rw [e7Embed_highNode, Pi.single_eq_of_ne (e7Node_ne_highNode j).symm]

theorem cartan_E8_e7Node_check : ∀ p : Fin (Tag.rank .E7) × Fin (Tag.rank .E7),
    Tag.cartan .E8 (e7Node p.1) (e7Node p.2) = Tag.cartan .E7 p.1 p.2 := by
  decide

theorem cartan_E8_e7Node (i j : Fin (Tag.rank .E7)) :
    Tag.cartan .E8 (e7Node i) (e7Node j) = Tag.cartan .E7 i j :=
  cartan_E8_e7Node_check (i, j)

theorem sum_E8_eq (f : Fin (Tag.rank .E8) → ℤ) :
    ∑ j, f j = ∑ j : Fin (Tag.rank .E7), f (e7Node j) + f (highNode .E8) :=
  Fin.sum_univ_castSucc (n := 7) f

theorem sum_cartan_E8_mul_e7Embed (i : Fin (Tag.rank .E7)) (v : Fin (Tag.rank .E7) → ℤ) :
    ∑ j, Tag.cartan .E8 (e7Node i) j * e7Embed v j = ∑ j, Tag.cartan .E7 i j * v j := by
  rw [sum_E8_eq, e7Embed_highNode, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cartan_E8_e7Node, e7Embed_e7Node]

theorem e7Embed_reflect (i : Fin (Tag.rank .E7)) (v : Fin (Tag.rank .E7) → ℤ) :
    e7Embed (reflect .E7 i v) = reflect .E8 (e7Node i) (e7Embed v) := by
  simp only [reflect]
  rw [e7Embed_sub, e7Embed_smul, e7Embed_single, sum_cartan_E8_mul_e7Embed]

theorem isRoot_e7Embed {v : Fin (Tag.rank .E7) → ℤ} (hv : IsRoot .E7 v) :
    IsRoot .E8 (e7Embed v) := by
  induction hv with
  | basis j =>
    rw [e7Embed_single]
    exact IsRoot.basis _
  | reflect i _ ih =>
    rw [e7Embed_reflect]
    exact IsRoot.reflect _ ih

set_option maxRecDepth 100000 in
theorem perpRoots_check :
    ∀ γ ∈ rootFinset .E8, γ (highNode .E8) = 0 → e8Restrict γ ∈ rootFinset .E7 := by
  decide +kernel

theorem e7Embed_mem_perpRoots {v : Fin (Tag.rank .E7) → ℤ} (hv : IsRoot .E7 v) :
    e7Embed v ∈ perpRoots .E8 :=
  ⟨isRoot_e7Embed hv, e7Embed_highNode v⟩


theorem isRoot_e8Restrict {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ)
    (h0 : γ (highNode .E8) = 0) : IsRoot .E7 (e8Restrict γ) :=
  mem_rootFinset.1 (perpRoots_check γ (mem_rootFinset.2 hγ) h0)

theorem isRoot_e7Embed_iff {v : Fin (Tag.rank .E7) → ℤ} :
    IsRoot .E8 (e7Embed v) ↔ IsRoot .E7 v := by
  refine ⟨fun h => ?_, isRoot_e7Embed⟩
  have := isRoot_e8Restrict h (e7Embed_highNode v)
  rwa [e8Restrict_e7Embed] at this

theorem exists_e7Embed_eq_of_mem_perpRoots {γ : Fin (Tag.rank .E8) → ℤ}
    (hγ : γ ∈ perpRoots .E8) : ∃ v, IsRoot .E7 v ∧ e7Embed v = γ :=
  ⟨e8Restrict γ, isRoot_e8Restrict hγ.1 hγ.2, e7Embed_e8Restrict hγ.2⟩

theorem perpRoots_eq_image : perpRoots .E8 = e7Embed '' {v | IsRoot .E7 v} := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨v, hv, rfl⟩ := exists_e7Embed_eq_of_mem_perpRoots hγ
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact e7Embed_mem_perpRoots hv

end CFSG.SeitzReduction.E8Pilot
