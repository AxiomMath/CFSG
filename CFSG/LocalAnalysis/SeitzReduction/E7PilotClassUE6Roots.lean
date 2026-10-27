module

public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SeitzReduction.E7Pilot

open CFSG.Blueprint.Chevalley

@[expose] def e6Node (j : Fin (Tag.rank .E6)) : Fin (Tag.rank .E7) :=
  ⟨j, Nat.lt_succ_of_lt j.isLt⟩

@[expose] def e7LastNode : Fin (Tag.rank .E7) := ⟨6, by decide⟩

@[expose] def e6Embed (v : Fin (Tag.rank .E6) → ℤ) : Fin (Tag.rank .E7) → ℤ :=
  fun i => if h : (i : ℕ) < Tag.rank .E6 then v ⟨i, h⟩ else 0

@[expose] def e7Restrict (γ : Fin (Tag.rank .E7) → ℤ) : Fin (Tag.rank .E6) → ℤ :=
  fun i => γ (e6Node i)

theorem e6Embed_e6Node (v : Fin (Tag.rank .E6) → ℤ) (j : Fin (Tag.rank .E6)) :
    e6Embed v (e6Node j) = v j :=
  dite_eq_left (c := ((e6Node j : Fin (Tag.rank .E7)) : ℕ) < Tag.rank .E6) j.isLt

theorem e6Embed_last (v : Fin (Tag.rank .E6) → ℤ) : e6Embed v e7LastNode = 0 :=
  dite_eq_right (c := ((e7LastNode : Fin (Tag.rank .E7)) : ℕ) < Tag.rank .E6) (by decide)

theorem e7Restrict_e6Embed (v : Fin (Tag.rank .E6) → ℤ) : e7Restrict (e6Embed v) = v := by
  funext i
  exact e6Embed_e6Node v i

theorem eq_e6Node_or_eq_last (i : Fin (Tag.rank .E7)) :
    (∃ j, i = e6Node j) ∨ i = e7LastNode := by
  by_cases h : (i : ℕ) < Tag.rank .E6
  · exact Or.inl ⟨⟨i, h⟩, Fin.ext rfl⟩
  · refine Or.inr (Fin.ext ?_)
    have := i.isLt
    change (i : ℕ) < 7 at this
    change ¬ (i : ℕ) < 6 at h
    change (i : ℕ) = 6
    omega

theorem e6Embed_e7Restrict {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ e7LastNode = 0) :
    e6Embed (e7Restrict γ) = γ := by
  funext i
  rcases eq_e6Node_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [e6Embed_e6Node]
    rfl
  · rw [e6Embed_last, hγ]

theorem e6Embed_injective : Function.Injective e6Embed := fun v w h => by
  rw [← e7Restrict_e6Embed v, h, e7Restrict_e6Embed]

theorem ext_e6Node {γ δ : Fin (Tag.rank .E7) → ℤ} (h : ∀ j, γ (e6Node j) = δ (e6Node j))
    (h0 : γ e7LastNode = δ e7LastNode) : γ = δ := by
  funext i
  rcases eq_e6Node_or_eq_last i with ⟨j, rfl⟩ | rfl
  exacts [h j, h0]

theorem e6Embed_add (v w : Fin (Tag.rank .E6) → ℤ) :
    e6Embed (v + w) = e6Embed v + e6Embed w :=
  ext_e6Node (fun j => by simp only [e6Embed_e6Node, Pi.add_apply])
    (by simp only [e6Embed_last, Pi.add_apply, add_zero])

theorem e6Embed_neg (v : Fin (Tag.rank .E6) → ℤ) : e6Embed (-v) = -e6Embed v :=
  ext_e6Node (fun j => by simp only [e6Embed_e6Node, Pi.neg_apply])
    (by simp only [e6Embed_last, Pi.neg_apply, neg_zero])

theorem e6Embed_sub (v w : Fin (Tag.rank .E6) → ℤ) :
    e6Embed (v - w) = e6Embed v - e6Embed w := by
  rw [sub_eq_add_neg, e6Embed_add, e6Embed_neg, ← sub_eq_add_neg]

theorem e6Embed_smul (n : ℤ) (v : Fin (Tag.rank .E6) → ℤ) : e6Embed (n • v) = n • e6Embed v :=
  ext_e6Node (fun j => by simp only [e6Embed_e6Node, Pi.smul_apply])
    (by simp only [e6Embed_last, Pi.smul_apply, smul_zero])

theorem e6Embed_zero : e6Embed 0 = 0 :=
  ext_e6Node (fun j => by simp only [e6Embed_e6Node, Pi.zero_apply])
    (by simp only [e6Embed_last, Pi.zero_apply])

theorem e6Node_injective : Function.Injective e6Node := fun _ _ h =>
  Fin.ext (congrArg Fin.val h :)

theorem e6Node_ne_last (j : Fin (Tag.rank .E6)) : e6Node j ≠ e7LastNode := by
  intro h
  have h' := congrArg Fin.val h
  have := j.isLt
  change (j : ℕ) = 6 at h'
  change (j : ℕ) < 6 at this
  omega

theorem e6Embed_single (j : Fin (Tag.rank .E6)) :
    e6Embed (Pi.single j 1) = Pi.single (e6Node j) 1 := by
  refine ext_e6Node (fun i => ?_) ?_
  · rw [e6Embed_e6Node]
    by_cases hij : i = j
    · rw [hij, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (fun h => hij (e6Node_injective h))]
  · rw [e6Embed_last, Pi.single_eq_of_ne (e6Node_ne_last j).symm]

theorem cartan_E7_e6Node_check : ∀ p : Fin (Tag.rank .E6) × Fin (Tag.rank .E6),
    Tag.cartan .E7 (e6Node p.1) (e6Node p.2) = Tag.cartan .E6 p.1 p.2 := by
  decide

theorem cartan_E7_e6Node (i j : Fin (Tag.rank .E6)) :
    Tag.cartan .E7 (e6Node i) (e6Node j) = Tag.cartan .E6 i j :=
  cartan_E7_e6Node_check (i, j)

theorem sum_E7_eq (f : Fin (Tag.rank .E7) → ℤ) :
    ∑ j, f j = ∑ j : Fin (Tag.rank .E6), f (e6Node j) + f e7LastNode :=
  Fin.sum_univ_castSucc (n := 6) f

theorem sum_cartan_E7_mul_e6Embed (i : Fin (Tag.rank .E6)) (v : Fin (Tag.rank .E6) → ℤ) :
    ∑ j, Tag.cartan .E7 (e6Node i) j * e6Embed v j = ∑ j, Tag.cartan .E6 i j * v j := by
  rw [sum_E7_eq, e6Embed_last, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cartan_E7_e6Node, e6Embed_e6Node]

theorem e6Embed_reflect (i : Fin (Tag.rank .E6)) (v : Fin (Tag.rank .E6) → ℤ) :
    e6Embed (reflect .E6 i v) = reflect .E7 (e6Node i) (e6Embed v) := by
  simp only [reflect]
  rw [e6Embed_sub, e6Embed_smul, e6Embed_single, sum_cartan_E7_mul_e6Embed]

theorem isRoot_e6Embed {v : Fin (Tag.rank .E6) → ℤ} (hv : IsRoot .E6 v) :
    IsRoot .E7 (e6Embed v) := by
  induction hv with
  | basis j =>
    rw [e6Embed_single]
    exact IsRoot.basis _
  | reflect i _ ih =>
    rw [e6Embed_reflect]
    exact IsRoot.reflect _ ih

set_option maxRecDepth 100000 in
theorem levelZero_check :
    ∀ γ ∈ rootFinset .E7, γ e7LastNode = 0 → e7Restrict γ ∈ rootFinset .E6 := by
  decide +kernel


theorem isRoot_e7Restrict {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (h0 : γ e7LastNode = 0) : IsRoot .E6 (e7Restrict γ) :=
  mem_rootFinset.1 (levelZero_check γ (mem_rootFinset.2 hγ) h0)

theorem isRoot_e6Embed_iff {v : Fin (Tag.rank .E6) → ℤ} :
    IsRoot .E7 (e6Embed v) ↔ IsRoot .E6 v := by
  refine ⟨fun h => ?_, isRoot_e6Embed⟩
  have := isRoot_e7Restrict h (e6Embed_last v)
  rwa [e7Restrict_e6Embed] at this

theorem exists_e6Embed_eq {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (h0 : γ e7LastNode = 0) : ∃ v, IsRoot .E6 v ∧ e6Embed v = γ :=
  ⟨e7Restrict γ, isRoot_e7Restrict hγ h0, e6Embed_e7Restrict h0⟩

end CFSG.SeitzReduction.E7Pilot
