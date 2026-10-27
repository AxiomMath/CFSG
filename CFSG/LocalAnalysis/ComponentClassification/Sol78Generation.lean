module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

public section

namespace CFSG.ComponentClassification.Sol78

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

theorem ncard_evenInvolutions_le_four {n : ℕ} {D : Finset (Fin n)} (hD : D.card = 4) :
    {π : Perm (Fin n) | π * π = 1 ∧ sign π = 1 ∧ ∀ ω ∉ D, π ω = ω}.ncard ≤ 4 := by
  classical
  let f : Fin 4 ≃ {x // x ∈ D} := (finCongr hD.symm).trans D.equivFin.symm
  set T : Set (Perm (Fin 4)) := {τ | τ * τ = 1 ∧ sign τ = 1} with hT
  have hTcard : T.ncard = 4 := by
    have hTf : T = ↑(Finset.univ.filter fun τ : Perm (Fin 4) => τ * τ = 1 ∧ sign τ = 1) := by
      ext τ
      simp [hT]
    rw [hTf, Set.ncard_coe_finset]
    decide +kernel
  let g : Perm (Fin 4) → Perm (Fin n) := fun τ => ofSubtype (f.permCongr τ)
  have hsub : {π : Perm (Fin n) | π * π = 1 ∧ sign π = 1 ∧ ∀ ω ∉ D, π ω = ω} ⊆ g '' T := by
    rintro π ⟨h2, hs, hsupp⟩
    have hπ2 : ∀ x, π (π x) = x := fun x => by
      have := congrArg (fun σ : Perm (Fin n) => σ x) h2
      simpa [Perm.mul_apply] using this
    have hpres : ∀ x, π x ∈ D ↔ x ∈ D := by
      intro x
      constructor
      · intro hx
        by_contra hxD
        rw [hsupp x hxD] at hx
        exact hxD hx
      · intro hx
        by_contra hxD
        have h1 := hsupp _ hxD
        rw [hπ2] at h1
        rw [← h1] at hxD
        exact hxD hx
    have hmove : ∀ x, π x ≠ x → x ∈ D := fun x hx => by
      by_contra hxD
      exact hx (hsupp x hxD)
    set ρ := π.subtypePerm hpres with hρ
    refine ⟨f.symm.permCongr ρ, ⟨?_, ?_⟩, ?_⟩
    · ext x
      simp [Perm.mul_apply, permCongr_apply, hρ, hπ2]
    · have h := sign_subtypePerm π hpres hmove
      rw [hs] at h
      rw [sign_permCongr, hρ]
      convert h
    · change ofSubtype (f.permCongr (f.symm.permCongr ρ)) = π
      rw [← permCongr_symm, Equiv.apply_symm_apply, hρ, ofSubtype_subtypePerm _ hmove]
  calc _ ≤ (g '' T).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ T.ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 4 := hTcard

theorem apply_mem_iff_of_mem_stabilizer {n : ℕ} {D : Finset (Fin n)}
    {σ : alternatingGroup (Fin n)}
    (hσ : σ ∈ MulAction.stabilizer (alternatingGroup (Fin n)) (D : Set (Fin n))) (ω : Fin n) :
    (σ : Perm (Fin n)) ω ∈ D ↔ ω ∈ D := by
  rw [MulAction.mem_stabilizer_iff] at hσ
  have h1 : (σ : Perm (Fin n)) ω = σ • ω := rfl
  rw [← Finset.mem_coe, ← Finset.mem_coe, h1]
  conv_lhs => rw [← hσ]
  exact Set.smul_mem_smul_set_iff

theorem stabilizer_le_normalizer_of_support {n : ℕ} {D : Finset (Fin n)} (hD : D.card = 4)
    {E : Subgroup (alternatingGroup (Fin n))} (hE : Nat.card E = 4) (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hsupp : ∀ e ∈ E, ∀ ω ∉ D, (e : Perm (Fin n)) ω = ω) :
    MulAction.stabilizer (alternatingGroup (Fin n)) (D : Set (Fin n)) ≤
      normalizer (E : Set (alternatingGroup (Fin n))) := by
  classical
  set S := {π : Perm (Fin n) | π * π = 1 ∧ sign π = 1 ∧ ∀ ω ∉ D, π ω = ω} with hS
  set E' : Set (Perm (Fin n)) :=
    (fun x : alternatingGroup (Fin n) => (x : Perm (Fin n))) '' (E : Set _) with hE'
  have hE'S : E' ⊆ S := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨?_, ?_, hsupp e he⟩
    · have := congrArg Subtype.val (hE2 e he)
      simpa [sq] using this
    · exact e.2
  have hE'card : E'.ncard = 4 := by
    rw [hE', Set.ncard_image_of_injective _ Subtype.val_injective, ← hE]
    exact (Nat.card_coe_set_eq _).symm
  have hEq : E' = S :=
    Set.eq_of_subset_of_ncard_le hE'S (by rw [hE'card]; exact ncard_evenInvolutions_le_four hD)
      (Set.toFinite _)
  have hconj : ∀ σ ∈ MulAction.stabilizer (alternatingGroup (Fin n)) (D : Set (Fin n)),
      ∀ e ∈ E, σ * e * σ⁻¹ ∈ E := by
    intro σ hσ e he
    have hσ' : σ⁻¹ ∈ MulAction.stabilizer (alternatingGroup (Fin n)) (D : Set (Fin n)) :=
      inv_mem hσ
    have hmem : ((σ * e * σ⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ S := by
      refine ⟨?_, (σ * e * σ⁻¹).2, ?_⟩
      · have h1 : (σ * e * σ⁻¹) * (σ * e * σ⁻¹) = σ * (e * e) * σ⁻¹ := by group
        have h2 : e * e = 1 := by rw [← sq]; exact hE2 e he
        rw [← Subgroup.coe_mul, h1, h2, mul_one, mul_inv_cancel, Subgroup.coe_one]
      · intro ω hω
        have h1 : (σ⁻¹ : alternatingGroup (Fin n)).val ω ∉ D := fun h =>
          hω ((apply_mem_iff_of_mem_stabilizer hσ' ω).mp h)
        have h2 := hsupp e he _ h1
        change (σ : Perm (Fin n)) ((e : Perm (Fin n)) ((σ⁻¹ : alternatingGroup (Fin n)).val ω)) = ω
        rw [h2]
        change (σ * σ⁻¹ : alternatingGroup (Fin n)).val ω = ω
        rw [mul_inv_cancel]
        rfl
    rw [← hEq] at hmem
    obtain ⟨e', he', hee'⟩ := hmem
    rw [Subtype.val_injective hee'] at he'
    exact he'
  intro σ hσ
  rw [mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact hconj σ hσ e he
  · intro he
    have h1 := hconj σ⁻¹ (inv_mem hσ) _ he
    have h2 : σ⁻¹ * (σ * e * σ⁻¹) * σ⁻¹⁻¹ = e := by group
    rwa [h2] at h1

theorem mem_stabilizer_of_fix {n : ℕ} {D : Finset (Fin n)} {σ : alternatingGroup (Fin n)}
    (h : ∀ ω ∈ D, (σ : Perm (Fin n)) ω = ω) :
    σ ∈ MulAction.stabilizer (alternatingGroup (Fin n)) (D : Set (Fin n)) := by
  rw [MulAction.mem_stabilizer_iff]
  ext ω
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have hinv : ∀ x ∈ D, (σ⁻¹ : alternatingGroup (Fin n)).val x = x := by
    intro x hx
    have h1 := h x hx
    calc (σ⁻¹ : alternatingGroup (Fin n)).val x =
          (σ⁻¹ : alternatingGroup (Fin n)).val ((σ : Perm (Fin n)) x) := by rw [h1]
      _ = x := by
          change ((σ⁻¹ * σ : alternatingGroup (Fin n)) : Perm (Fin n)) x = x
          rw [inv_mul_cancel]
          rfl
  constructor
  · intro hω
    have hω' : (σ⁻¹ : alternatingGroup (Fin n)).val ω ∈ D := hω
    by_contra hωD
    have h1 := h _ hω'
    change (σ : Perm (Fin n)) ((σ⁻¹ : alternatingGroup (Fin n)).val ω) = _ at h1
    have h2 : (σ : Perm (Fin n)) ((σ⁻¹ : alternatingGroup (Fin n)).val ω) = ω := by
      change ((σ * σ⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω
      rw [mul_inv_cancel]
      rfl
    rw [h2] at h1
    rw [← h1] at hω'
    exact hωD hω'
  · intro hω
    change (σ⁻¹ : alternatingGroup (Fin n)).val ω ∈ D
    rw [hinv ω hω]
    exact hω

theorem stabilizer_sup_stabilizer_eq_top {n : ℕ} (hn : 9 ≤ n) {D D' : Finset (Fin n)}
    (hD : D.card = 4) (hD' : D'.card = 4) (hdisj : Disjoint D D') :
    MulAction.stabilizer (alternatingGroup (Fin n)) (D : Set (Fin n)) ⊔
      MulAction.stabilizer (alternatingGroup (Fin n)) (D' : Set (Fin n)) = ⊤ := by
  classical
  have hcard : (D ∪ D').card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_union_of_disjoint hdisj, hD, hD', Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hcD : c ∉ D := fun h => hc (Finset.mem_union_left _ h)
  have hcD' : c ∉ D' := fun h => hc (Finset.mem_union_right _ h)
  obtain ⟨d₁, hd₁, d₂, hd₂, hd₁₂⟩ := Finset.one_lt_card.mp (by rw [hD]; norm_num : 1 < D.card)
  have hd₁c : d₁ ≠ c := fun h => hcD (h ▸ hd₁)
  have hd₂c : d₂ ≠ c := fun h => hcD (h ▸ hd₂)
  have hd₁' : d₁ ∉ D' := Finset.disjoint_left.mp hdisj hd₁
  have hd₂' : d₂ ∉ D' := Finset.disjoint_left.mp hdisj hd₂
  set g : alternatingGroup (Fin n) := ⟨swap d₁ c * swap d₁ d₂, by
    rw [mem_alternatingGroup, map_mul, sign_swap hd₁c, sign_swap hd₁₂]
    decide⟩ with hg
  have hgD' : g ∈ MulAction.stabilizer (alternatingGroup (Fin n)) (D' : Set (Fin n)) := by
    apply mem_stabilizer_of_fix
    intro ω hω
    have h1 : ω ≠ d₁ := fun h => hd₁' (h ▸ hω)
    have h2 : ω ≠ d₂ := fun h => hd₂' (h ▸ hω)
    have h3 : ω ≠ c := fun h => hcD' (h ▸ hω)
    change (swap d₁ c * swap d₁ d₂) ω = ω
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]
  have hgD : g ∉ MulAction.stabilizer (alternatingGroup (Fin n)) (D : Set (Fin n)) := by
    intro h
    have h1 := (apply_mem_iff_of_mem_stabilizer h d₂).mpr hd₂
    change (swap d₁ c * swap d₁ d₂) d₂ ∈ D at h1
    rw [Perm.mul_apply, swap_apply_right, swap_apply_left] at h1
    exact hcD h1
  have hco := alternatingGroup.isCoatom_stabilizer (α := Fin n) (s := (D : Set (Fin n)))
    (Finset.coe_nonempty.mpr ⟨d₁, hd₁⟩) ⟨c, hcD⟩
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin, Set.ncard_coe_finset, hD]; omega)
  apply hco.2
  refine lt_of_le_of_ne le_sup_left fun h => hgD ?_
  rw [h]
  exact mem_sup_right hgD'

theorem normalizer_sup_normalizer_eq_top {n : ℕ} (hn : 9 ≤ n)
    {E F : Subgroup (alternatingGroup (Fin n))} (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) (hF2 : ∀ f ∈ F, f ^ 2 = 1) {DE DF : Finset (Fin n)}
    (hDE : DE.card = 4) (hDF : DF.card = 4) (hdisj : Disjoint DE DF)
    (hEs : ∀ e ∈ E, ∀ ω ∉ DE, (e : Perm (Fin n)) ω = ω)
    (hFs : ∀ f ∈ F, ∀ ω ∉ DF, (f : Perm (Fin n)) ω = ω) :
    normalizer (E : Set (alternatingGroup (Fin n))) ⊔
      normalizer (F : Set (alternatingGroup (Fin n))) = ⊤ := by
  rw [eq_top_iff, ← stabilizer_sup_stabilizer_eq_top hn hDE hDF hdisj]
  exact sup_le_sup (stabilizer_le_normalizer_of_support hDE hE hE2 hEs)
    (stabilizer_le_normalizer_of_support hDF hF hF2 hFs)

end CFSG.ComponentClassification.Sol78
