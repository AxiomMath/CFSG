module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.LieType.Universal.Spin.Datum

public section

namespace CFSG.SeitzReduction.E7Pilot

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction.EPilot CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD toStdD rootsD_eq boolSign)
open CFSG.LieType.RootSystem (roots weylAction coxeterMatrix reflection reflection_apply
  weylAction_simple weylAction_mul_apply)

@[expose] def d6Node (i : Fin 6) : Fin (Tag.rank .E7) :=
  ⟨6 - (i : ℕ), by have := i.isLt; change 6 - (i : ℕ) < 7; omega⟩

@[expose] def d6Embed (v : Fin 6 → ℤ) : Fin (Tag.rank .E7) → ℤ :=
  fun j => if h : (j : ℕ) = 0 then 0 else
    v ⟨6 - (j : ℕ), by have := j.isLt; change (j : ℕ) < 7 at this; omega⟩

@[expose] def e7RestrictD (γ : Fin (Tag.rank .E7) → ℤ) : Fin 6 → ℤ :=
  fun i => γ (d6Node i)

theorem highNode_E7_eq : highNode .E7 = (⟨0, by decide⟩ : Fin (Tag.rank .E7)) := rfl

theorem d6Node_val (i : Fin 6) : ((d6Node i : Fin (Tag.rank .E7)) : ℕ) = 6 - (i : ℕ) := rfl

theorem d6Embed_d6Node (v : Fin 6 → ℤ) (i : Fin 6) : d6Embed v (d6Node i) = v i := by
  have hi := i.isLt
  have h0 : ¬ ((d6Node i : Fin (Tag.rank .E7)) : ℕ) = 0 := by rw [d6Node_val]; omega
  simp only [d6Embed, h0, ↓reduceDIte]
  congr 1
  apply Fin.ext
  simp only [d6Node_val]
  omega

theorem d6Embed_highNode (v : Fin 6 → ℤ) : d6Embed v (highNode .E7) = 0 := by
  simp [d6Embed, highNode_E7_eq]

theorem e7RestrictD_d6Embed (v : Fin 6 → ℤ) : e7RestrictD (d6Embed v) = v := by
  funext i
  exact d6Embed_d6Node v i

theorem eq_d6Node_or_eq_highNode (j : Fin (Tag.rank .E7)) :
    (∃ i, j = d6Node i) ∨ j = highNode .E7 := by
  have hj := j.isLt
  change (j : ℕ) < 7 at hj
  by_cases h : (j : ℕ) = 0
  · exact Or.inr (Fin.ext h)
  · refine Or.inl ⟨⟨6 - (j : ℕ), by omega⟩, Fin.ext ?_⟩
    rw [d6Node_val]
    change (j : ℕ) = 6 - (6 - (j : ℕ))
    omega

theorem d6Embed_e7RestrictD {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ (highNode .E7) = 0) :
    d6Embed (e7RestrictD γ) = γ := by
  funext j
  rcases eq_d6Node_or_eq_highNode j with ⟨i, rfl⟩ | rfl
  · rw [d6Embed_d6Node]
    rfl
  · rw [d6Embed_highNode, hγ]

theorem d6Embed_injective : Function.Injective d6Embed := fun v w h => by
  rw [← e7RestrictD_d6Embed v, h, e7RestrictD_d6Embed]

theorem ext_d6Node {γ δ : Fin (Tag.rank .E7) → ℤ} (h : ∀ i, γ (d6Node i) = δ (d6Node i))
    (h0 : γ (highNode .E7) = δ (highNode .E7)) : γ = δ := by
  funext j
  rcases eq_d6Node_or_eq_highNode j with ⟨i, rfl⟩ | rfl
  exacts [h i, h0]

theorem d6Embed_add (v w : Fin 6 → ℤ) : d6Embed (v + w) = d6Embed v + d6Embed w :=
  ext_d6Node (fun i => by simp only [d6Embed_d6Node, Pi.add_apply])
    (by simp only [d6Embed_highNode, Pi.add_apply, add_zero])

theorem d6Embed_neg (v : Fin 6 → ℤ) : d6Embed (-v) = -d6Embed v :=
  ext_d6Node (fun i => by simp only [d6Embed_d6Node, Pi.neg_apply])
    (by simp only [d6Embed_highNode, Pi.neg_apply, neg_zero])

theorem d6Embed_sub (v w : Fin 6 → ℤ) : d6Embed (v - w) = d6Embed v - d6Embed w := by
  rw [sub_eq_add_neg, d6Embed_add, d6Embed_neg, ← sub_eq_add_neg]

theorem d6Embed_smul (n : ℤ) (v : Fin 6 → ℤ) : d6Embed (n • v) = n • d6Embed v :=
  ext_d6Node (fun i => by simp only [d6Embed_d6Node, Pi.smul_apply])
    (by simp only [d6Embed_highNode, Pi.smul_apply, smul_zero])

theorem d6Embed_zero : d6Embed 0 = 0 :=
  ext_d6Node (fun i => by simp only [d6Embed_d6Node, Pi.zero_apply])
    (by simp only [d6Embed_highNode, Pi.zero_apply])

theorem d6Node_injective : Function.Injective d6Node := fun i j h => by
  have h' := congrArg Fin.val h
  simp only [d6Node_val] at h'
  have := i.isLt
  have := j.isLt
  exact Fin.ext (by omega)

theorem d6Node_ne_highNode (i : Fin 6) : d6Node i ≠ highNode .E7 := by
  intro h
  have h' := congrArg Fin.val h
  have h0 : ((highNode .E7 : Fin (Tag.rank .E7)) : ℕ) = 0 := rfl
  rw [d6Node_val, h0] at h'
  have := i.isLt
  omega

theorem d6Embed_single (i : Fin 6) : d6Embed (Pi.single i 1) = Pi.single (d6Node i) 1 := by
  refine ext_d6Node (fun j => ?_) ?_
  · rw [d6Embed_d6Node]
    by_cases hij : j = i
    · rw [hij, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (fun h => hij (d6Node_injective h))]
  · rw [d6Embed_highNode, Pi.single_eq_of_ne (d6Node_ne_highNode i).symm]

theorem cartan_E7_d6Node_check : ∀ p : Fin 6 × Fin 6,
    Tag.cartan .E7 (d6Node p.1) (d6Node p.2) = cartanD 6 p.1 p.2 := by
  decide

theorem cartan_E7_d6Node (i j : Fin 6) :
    Tag.cartan .E7 (d6Node i) (d6Node j) = cartanD 6 i j :=
  cartan_E7_d6Node_check (i, j)

theorem sum_E7_eq_d6 (f : Fin (Tag.rank .E7) → ℤ) :
    ∑ j, f j = f (highNode .E7) + ∑ i : Fin 6, f (d6Node i) := by
  refine (Fin.sum_univ_succ (n := 6) f).trans ?_
  congr 1
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  apply Fin.ext
  simp only [Fin.revPerm_apply, Fin.val_succ, Fin.val_rev, d6Node_val]
  have := i.isLt
  omega

theorem sum_cartan_E7_mul_d6Embed (i : Fin 6) (v : Fin 6 → ℤ) :
    ∑ j, Tag.cartan .E7 (d6Node i) j * d6Embed v j = ∑ j, cartanD 6 i j * v j := by
  rw [sum_E7_eq_d6, d6Embed_highNode, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cartan_E7_d6Node, d6Embed_d6Node]

theorem d6Embed_reflection (i : Fin 6) (v : Fin 6 → ℤ) :
    d6Embed (reflection (cartanD 6) i v) = reflect .E7 (d6Node i) (d6Embed v) := by
  rw [reflection_apply, reflect, d6Embed_sub, d6Embed_smul, d6Embed_single,
    sum_cartan_E7_mul_d6Embed]

theorem isRoot_d6Embed {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅) :
    IsRoot .E7 (d6Embed v) := by
  rcases hv with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · obtain ⟨ω, rfl⟩ :=
      (coxeterMatrix (isFiniteType_cartanD 6)).toCoxeterSystem.wordProd_surjective w
    induction ω with
    | nil =>
      rw [CoxeterSystem.wordProd_nil, map_one, Module.End.one_apply, d6Embed_single]
      exact IsRoot.basis _
    | cons j ω ih =>
      rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
        d6Embed_reflection]
      exact IsRoot.reflect _ ih
  · exact absurd hi (Set.notMem_empty i)

set_option maxRecDepth 100000 in
theorem perpRootsD_check :
    ∀ γ ∈ rootFinset .E7, γ (highNode .E7) = 0 → ∃ i j : Fin 6, i ≠ j ∧ ∃ s t : Bool,
      toStdD 6 (e7RestrictD γ) = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  decide +kernel

theorem d6Embed_mem_perpRoots {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅) :
    d6Embed v ∈ perpRoots .E7 :=
  ⟨isRoot_d6Embed hv, d6Embed_highNode v⟩


theorem mem_rootsD_e7RestrictD {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (h0 : γ (highNode .E7) = 0) : e7RestrictD γ ∈ roots (isFiniteType_cartanD 6) ∅ := by
  obtain ⟨i, j, hij, s, t, h⟩ := perpRootsD_check γ (mem_rootFinset.2 hγ) h0
  rw [rootsD_eq (n := 6) (by norm_num)]
  exact ⟨i, j, boolSign s, boolSign t, hij,
    CFSG.LieType.Universal.Spin.boolSign_eq_one_or_eq_neg_one s,
    CFSG.LieType.Universal.Spin.boolSign_eq_one_or_eq_neg_one t, h⟩

theorem isRoot_d6Embed_iff {v : Fin 6 → ℤ} :
    IsRoot .E7 (d6Embed v) ↔ v ∈ roots (isFiniteType_cartanD 6) ∅ := by
  refine ⟨fun h => ?_, isRoot_d6Embed⟩
  have := mem_rootsD_e7RestrictD h (d6Embed_highNode v)
  rwa [e7RestrictD_d6Embed] at this

theorem exists_d6Embed_eq_of_mem_perpRoots {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ perpRoots .E7) :
    ∃ v, v ∈ roots (isFiniteType_cartanD 6) ∅ ∧ d6Embed v = γ :=
  ⟨e7RestrictD γ, mem_rootsD_e7RestrictD hγ.1 hγ.2, d6Embed_e7RestrictD hγ.2⟩

theorem perpRoots_E7_eq_image :
    perpRoots .E7 = d6Embed '' roots (isFiniteType_cartanD 6) ∅ := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨v, hv, rfl⟩ := exists_d6Embed_eq_of_mem_perpRoots hγ
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact d6Embed_mem_perpRoots hv

theorem not_isRoot_add_self_E7'
    {α : Fin (Tag.rank .E7) → ℤ} : ¬ IsRoot .E7 (α + α) := by
  intro h
  have h2 := iform_self_eq_two (τ := .E7) (Or.inr (Or.inl rfl)) h
  have h1 : iform (α + α) (α + α) = 4 * iform α α := by
    simp only [iform_add_left, iform_add_right]
    ring
  have h3 : (2 : ℤ) = 4 * iform α α := h2 ▸ h1
  omega

theorem add_self_not_mem_rootsD {α : Fin 6 → ℤ} :
    α + α ∉ roots (isFiniteType_cartanD 6) ∅ := fun h => by
  have := isRoot_d6Embed h
  rw [d6Embed_add] at this
  exact not_isRoot_add_self_E7' this

end CFSG.SeitzReduction.E7Pilot
