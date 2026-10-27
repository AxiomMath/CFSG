module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Core3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

variable (B : Subgroup (OGroup Q)) [Fintype ↥B] [DecidableEq ↥B]

open Classical in
@[expose] noncomputable def fgS : Finset (↥B → ZMod 3) :=
  Finset.univ.filter (fun χ => χ ≠ (fun _ => (1 : ZMod 3)) ∧ fgWt (fgT B) χ ≠ ⊥)

theorem mem_fgS_iff {χ : ↥B → ZMod 3} :
    χ ∈ fgS B ↔ χ ≠ (fun _ => (1 : ZMod 3)) ∧ fgWt (fgT B) χ ≠ ⊥ := by
  simp [fgS]

theorem triv_notMem_fgS : (fun _ => (1 : ZMod 3)) ∉ fgS B := fun h => ((mem_fgS_iff B).1 h).1 rfl

variable (hB : IsElemAb2 B 4) (hdim : Module.finrank (ZMod 3) V = 6) (f : OGroup Q)
  (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1)

theorem fgS_perm_iff (χ : ↥B → ZMod 3) :
    fgPerm B (ZMod 3) (fgCj B f hf) χ ∈ fgS B ↔ χ ∈ fgS B := by
  have h1 : fgPerm B (ZMod 3) (fgCj B f hf) (fun _ => (1 : ZMod 3)) = fun _ => 1 := rfl
  have h : fgPerm B (ZMod 3) (fgCj B f hf) χ = (fun _ => (1 : ZMod 3)) ↔
      χ = (fun _ => (1 : ZMod 3)) :=
    ⟨fun h' => (fgPerm B (ZMod 3) (fgCj B f hf)).injective (h'.trans h1.symm),
      fun h' => by rw [h']; exact h1⟩
  rw [mem_fgS_iff, mem_fgS_iff, fgWt_perm_ne_bot_iff B f hf χ]
  simp only [ne_eq, h]

include hB hdim hf hf5 hf1

theorem fgS_perm_ne_self {χ : ↥B → ZMod 3} (hχ : χ ∈ fgS B) :
    fgPerm B (ZMod 3) (fgCj B f hf) χ ≠ χ :=
  fg_perm_ne_self B hB hdim f hf hf5 hf1 ((mem_fgS_iff B).1 hχ).2 ((mem_fgS_iff B).1 hχ).1

theorem fg_orbit_structure :
    (fgS B).card = 5 ∧ ∀ χ ∈ fgS B, Module.finrank (ZMod 3) (fgWt (fgT B) χ) = 1 := by
  set σ : Equiv.Perm (↥B → ZMod 3) := fgPerm B (ZMod 3) (fgCj B f hf) with hσdef
  have hσ5 : σ ^ 5 = 1 := fgPerm_pow_five B (ZMod 3) f hf hf5
  have hS : ∀ χ, χ ∈ fgS B ↔ σ χ ∈ fgS B := fun χ => (fgS_perm_iff B f hf χ).symm
  have hfree : ∀ χ ∈ fgS B, σ χ ≠ χ := fun χ hχ => fgS_perm_ne_self B hB hdim f hf hf5 hf1 hχ
  have hd : ∀ χ, Module.finrank (ZMod 3) (fgWt (fgT B) (σ χ)) =
      Module.finrank (ZMod 3) (fgWt (fgT B) χ) := fun χ => finrank_fgWt_perm B f hf χ
  have hpos : ∀ χ ∈ fgS B, 1 ≤ Module.finrank (ZMod 3) (fgWt (fgT B) χ) := fun χ hχ =>
    Submodule.one_le_finrank_iff.mpr ((mem_fgS_iff B).1 hχ).2
  have hne : (fgS B).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hall : ∀ g : ↥B, g = 1 := by
      intro g
      apply fgT_eq_of_weights B hB g 1
      intro χ hχ
      by_cases htr : χ = fun _ => (1 : ZMod 3)
      · subst htr
        rfl
      · exfalso
        have hmem : χ ∈ fgS B := (mem_fgS_iff B).2 ⟨htr, hχ⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty χ)
    have hB16 : Nat.card ↥B = 16 := by
      rw [hB.2]
      norm_num
    haveI : Subsingleton ↥B := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have h1 : Nat.card ↥B = 1 := Nat.card_unique (α := ↥B)
    omega
  have hsum : ∑ χ ∈ fgS B, Module.finrank (ZMod 3) (fgWt (fgT B) χ) ≤ 6 := by
    calc ∑ χ ∈ fgS B, Module.finrank (ZMod 3) (fgWt (fgT B) χ)
        ≤ ∑ χ : ↥B → ZMod 3, Module.finrank (ZMod 3) (fgWt (fgT B) χ) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 6 := by
          rw [fgWt_finrank_sum (fgT B) (fgT_sq B hB) (fgT_comm B hB), hdim]
  exact fg_orbit_count σ hσ5 (fgS B) hS hfree
    (fun χ => Module.finrank (ZMod 3) (fgWt (fgT B) χ)) hd hpos hne hsum

theorem fg_finrank_triv :
    Module.finrank (ZMod 3) (fgWt (fgT B) (fun _ => (1 : ZMod 3))) = 1 := by
  obtain ⟨hcard, hd1⟩ := fg_orbit_structure B hB hdim f hf hf5 hf1
  have hsum := fgWt_finrank_sum (fgT B) (fgT_sq B hB) (fgT_comm B hB)
  rw [hdim] at hsum
  have h1 : ∑ χ ∈ insert (fun _ => (1 : ZMod 3)) (fgS B),
      Module.finrank (ZMod 3) (fgWt (fgT B) χ) =
      ∑ χ : ↥B → ZMod 3, Module.finrank (ZMod 3) (fgWt (fgT B) χ) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro χ _ hχ
    have hχ' : fgWt (fgT B) χ = ⊥ := by
      by_contra hne
      by_cases htr : χ = fun _ => (1 : ZMod 3)
      · exact hχ (by rw [htr]; exact Finset.mem_insert_self _ _)
      · exact hχ (Finset.mem_insert_of_mem ((mem_fgS_iff B).2 ⟨htr, hne⟩))
    rw [hχ']
    simp
  rw [Finset.sum_insert (triv_notMem_fgS B), hsum] at h1
  have h2 : ∑ χ ∈ fgS B, Module.finrank (ZMod 3) (fgWt (fgT B) χ) = 5 := by
    rw [Finset.sum_congr rfl hd1]
    simp [hcard]
  omega

theorem fg_exists_family :
    ∃ χo : Option (Fin 5) → (↥B → ZMod 3), Function.Injective χo ∧
      χo none = (fun _ => (1 : ZMod 3)) ∧ (∀ i, χo (some i) ∈ fgS B) ∧
      ∀ o, fgWt (fgT B) (χo o) ≠ ⊥ := by
  obtain ⟨hcard, -⟩ := fg_orbit_structure B hB hdim f hf hf5 hf1
  let e5 : ↥(fgS B) ≃ Fin 5 := (fgS B).equivFinOfCardEq hcard
  let χo : Option (Fin 5) → (↥B → ZMod 3) := fun o =>
    o.elim (fun _ => (1 : ZMod 3)) (fun i => ((e5.symm i : ↥(fgS B)) : ↥B → ZMod 3))
  have hsome : ∀ i, χo (some i) ∈ fgS B := fun i => (e5.symm i).2
  refine ⟨χo, ?_, rfl, hsome, ?_⟩
  · intro o o' h
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some j =>
        have h2 : χo (some j) ∈ fgS B := hsome j
        rw [← h] at h2
        exact absurd h2 (triv_notMem_fgS B)
    | some i =>
      cases o' with
      | none =>
        have h2 : χo (some i) ∈ fgS B := hsome i
        rw [h] at h2
        exact absurd h2 (triv_notMem_fgS B)
      | some j =>
        have h1 : e5.symm i = e5.symm j := Subtype.ext h
        rw [e5.symm.injective h1]
  · intro o
    cases o with
    | none =>
      intro hbot
      have h1 := fg_finrank_triv B hB hdim f hf hf5 hf1
      change fgWt (fgT B) (fun _ => (1 : ZMod 3)) = ⊥ at hbot
      rw [hbot] at h1
      simp at h1
    | some i => exact ((mem_fgS_iff B).1 (hsome i)).2

end CFSG.OddStandard.SmallF3.Omega
