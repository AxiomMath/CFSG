module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.Order.CompletePartialOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Representation

variable {k X V : Type*} [Field k] [Group X] [AddCommGroup V] [Module k V]
  {ρ : Representation k X V}

theorem map_rho_map_rho (ρ : Representation k X V) (g h : X) (W : Submodule k V) :
    (W.map (ρ g)).map (ρ h) = W.map (ρ (h * g)) := by
  rw [← Submodule.map_comp]
  congr 1
  ext v
  simp [map_mul]

@[simp]
theorem map_rho_one (ρ : Representation k X V) (W : Submodule k V) : W.map (ρ 1) = W := by
  rw [map_one]
  exact Submodule.map_id W

theorem mem_invtSubmodule_comp_subtype_iff (ρ : Representation k X V) (A : Subgroup X)
    {W : Submodule k V} :
    W ∈ Representation.invtSubmodule (ρ.comp A.subtype) ↔ ∀ a ∈ A, W.map (ρ a) ≤ W := by
  rw [Representation.mem_invtSubmodule]
  simp only [Module.End.mem_invtSubmodule, Submodule.map_le_iff_le_comap, Subtype.forall,
    MonoidHom.coe_comp, Function.comp_apply]
  exact ⟨fun h a ha => h a ha, fun h a ha => h a ha⟩

theorem map_mem_invtSubmodule_comp_subtype (ρ : Representation k X V) {A : Subgroup X} [A.Normal]
    {W : Submodule k V} (hW : W ∈ Representation.invtSubmodule (ρ.comp A.subtype)) (y : X) :
    W.map (ρ y) ∈ Representation.invtSubmodule (ρ.comp A.subtype) := by
  rw [mem_invtSubmodule_comp_subtype_iff] at hW ⊢
  intro a ha
  rw [map_rho_map_rho]
  have hay : a * y = y * (y⁻¹ * a * y) := by group
  rw [hay, ← map_rho_map_rho]
  exact Submodule.map_mono (hW _ (by simpa using Subgroup.Normal.conj_mem' ‹A.Normal› a ha y))

theorem map_rho_ne_bot (ρ : Representation k X V) (g : X) {W : Submodule k V} (h : W ≠ ⊥) :
    W.map (ρ g) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨ρ g v, Submodule.mem_map_of_mem hv, ?_⟩
  exact fun hc => hv0 (by simpa using (ρ.apply_bijective g).1 (hc.trans (map_zero _).symm))

theorem finrank_map_rho (ρ : Representation k X V) (g : X) (W : Submodule k V) :
    finrank k (W.map (ρ g)) = finrank k W :=
  ((Submodule.equivMapOfInjective _ (ρ.apply_bijective g).1 W).finrank_eq).symm

theorem eq_top_of_isIrreducible_of_map_le (hρ : ρ.IsIrreducible) {W : Submodule k V}
    (hW : ∀ g : X, W.map (ρ g) ≤ W) (hW0 : W ≠ ⊥) : W = ⊤ := by
  let σ : Subrepresentation ρ := ⟨W, fun g _ hv => hW g (Submodule.mem_map_of_mem hv)⟩
  rcases hρ.eq_bot_or_eq_top σ with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) hW0
  · exact congrArg Subrepresentation.toSubmodule h

theorem isIrreducible_of_forall_map_le [Nontrivial V]
    (h : ∀ W : Submodule k V, (∀ g : X, W.map (ρ g) ≤ W) → W = ⊥ ∨ W = ⊤) : ρ.IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⊥, ⊤, fun hc => ?_⟩
    have h' := congrArg Subrepresentation.toSubmodule hc
    simp only [show (⊥ : Subrepresentation ρ).toSubmodule = ⊥ from rfl,
      show (⊤ : Subrepresentation ρ).toSubmodule = ⊤ from rfl] at h'
    exact absurd h' (bot_ne_top (α := Submodule k V))
  refine ⟨fun σ => ?_⟩
  rcases h σ.toSubmodule (fun g => by
    rw [Submodule.map_le_iff_le_comap]
    exact fun v hv => σ.apply_mem_toSubmodule g hv) with hb | ht
  · exact Or.inl (Subrepresentation.ext hb)
  · exact Or.inr (Subrepresentation.ext ht)

theorem iSupIndep_fin_cons {α : Type*} [CompleteLattice α] [IsModularLattice α] {n : ℕ}
    {p : Fin n → α} {a : α} (hp : iSupIndep p) (ha : Disjoint a (⨆ i, p i)) :
    iSupIndep (Fin.cons a p) := by
  classical
  rw [iSupIndep_iff_supIndep_univ, Fin.univ_succ]
  have hs : (Finset.map ⟨Fin.succ, Fin.succ_injective n⟩ (Finset.univ : Finset (Fin n))).SupIndep
      (Fin.cons a p) := by
    rw [Finset.supIndep_map]
    simpa using iSupIndep_iff_supIndep_univ.1 hp
  have hsup : (Finset.map ⟨Fin.succ, Fin.succ_injective n⟩ (Finset.univ : Finset (Fin n))).sup
      (Fin.cons a p) = ⨆ i, p i := by
    rw [Finset.sup_map]
    simpa using Finset.sup_univ_eq_iSup p
  rw [Finset.cons_eq_insert]
  exact hs.insert (by simpa [hsup] using ha)

theorem eq_bot_or_eq_map_of_le_map {A : Subgroup X} [A.Normal] {S : Submodule k V}
    (hSsimple : ∀ T ∈ Representation.invtSubmodule (ρ.comp A.subtype), T ≤ S → T = ⊥ ∨ T = S)
    (y : X) {T : Submodule k V} (hT : T ∈ Representation.invtSubmodule (ρ.comp A.subtype))
    (hTle : T ≤ S.map (ρ y)) : T = ⊥ ∨ T = S.map (ρ y) := by
  have hTback : (T.map (ρ y⁻¹)).map (ρ y) = T := by
    rw [map_rho_map_rho, mul_inv_cancel, map_rho_one]
  have hle : T.map (ρ y⁻¹) ≤ S := by
    have h := Submodule.map_mono (f := (ρ y⁻¹ : V →ₗ[k] V)) hTle
    rwa [map_rho_map_rho, inv_mul_cancel, map_rho_one] at h
  rcases hSsimple _ (map_mem_invtSubmodule_comp_subtype ρ hT y⁻¹) hle with h | h
  · exact Or.inl (by rw [← hTback, h, Submodule.map_bot])
  · exact Or.inr (by rw [← hTback, h])

theorem finrank_eq_sum_of_isInternal {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional k V] {p : ι → Submodule k V} (h : DirectSum.IsInternal p) :
    finrank k V = ∑ i, finrank k (p i) := by
  rw [Module.finrank_eq_card_basis (h.collectedBasis fun i => Module.finBasis k (p i))]
  simp [Fintype.card_sigma]

theorem exists_conjugates_isInternal [FiniteDimensional k V] (hρ : ρ.IsIrreducible)
    {A : Subgroup X} [A.Normal] {S : Submodule k V} (hS0 : S ≠ ⊥)
    (hSinvt : S ∈ Representation.invtSubmodule (ρ.comp A.subtype))
    (hSsimple : ∀ T ∈ Representation.invtSubmodule (ρ.comp A.subtype), T ≤ S → T = ⊥ ∨ T = S) :
    ∃ (t : ℕ) (x : Fin t → X), DirectSum.IsInternal (fun i => S.map (ρ (x i))) ∧
      finrank k V = t * finrank k S := by
  classical
  set 𝒩 : Set ℕ := {n | ∃ x : Fin n → X, iSupIndep fun i => S.map (ρ (x i))} with h𝒩
  have h1 : 1 ∈ 𝒩 := ⟨fun _ => 1, iSupIndep_subsingleton _⟩
  have hbdd : ∀ n ∈ 𝒩, n ≤ finrank k V := by
    rintro n ⟨x, hx⟩
    have hne : ∀ i, (fun i => S.map (ρ (x i))) i ≠ ⊥ := fun i => map_rho_ne_bot ρ _ hS0
    have : Fintype {i // (fun i => S.map (ρ (x i))) i ≠ ⊥} := Fintype.ofFinite _
    have h2 := hx.subtype_ne_bot_le_finrank
    rwa [Fintype.card_congr (Equiv.subtypeUnivEquiv hne), Fintype.card_fin] at h2
  have hbdd' : BddAbove 𝒩 := ⟨finrank k V, fun _ hn => hbdd _ hn⟩
  obtain ⟨x, hx⟩ := Nat.sSup_mem ⟨1, h1⟩ hbdd'
  have hconj : ∀ (y : X) (W : Submodule k V),
      W ∈ Representation.invtSubmodule (ρ.comp A.subtype) →
      ∀ a ∈ A, (W.map (ρ y)).map (ρ a) ≤ W.map (ρ y) := fun y W hW a ha =>
    (mem_invtSubmodule_comp_subtype_iff ρ A).1 (map_mem_invtSubmodule_comp_subtype ρ hW y) a ha
  set D : Submodule k V := ⨆ i, S.map (ρ (x i)) with hD
  have hDinvt : D ∈ Representation.invtSubmodule (ρ.comp A.subtype) := by
    rw [mem_invtSubmodule_comp_subtype_iff]
    intro a ha
    rw [hD, Submodule.map_iSup]
    exact iSup_mono fun i => hconj (x i) S hSinvt a ha
  have hall : ∀ y : X, S.map (ρ y) ≤ D := by
    intro y
    have hTinvt : S.map (ρ y) ⊓ D ∈ Representation.invtSubmodule (ρ.comp A.subtype) := by
      rw [mem_invtSubmodule_comp_subtype_iff]
      intro a ha
      exact le_inf (le_trans (Submodule.map_mono inf_le_left) (hconj y S hSinvt a ha))
        (le_trans (Submodule.map_mono inf_le_right)
          ((mem_invtSubmodule_comp_subtype_iff ρ A).1 hDinvt a ha))
    rcases eq_bot_or_eq_map_of_le_map hSsimple y hTinvt inf_le_left with h | h
    ·
      exfalso
      have hnew : sSup 𝒩 + 1 ∈ 𝒩 := by
        refine ⟨Fin.cons y x, ?_⟩
        have hcons : (fun i => S.map (ρ ((Fin.cons y x : Fin (sSup 𝒩 + 1) → X) i)))
            = Fin.cons (S.map (ρ y)) (fun i => S.map (ρ (x i))) := by
          funext i
          refine Fin.cases ?_ ?_ i <;> simp
        rw [hcons]
        exact iSupIndep_fin_cons hx (disjoint_iff.2 h)
      exact absurd (le_csSup hbdd' hnew) (by omega)
    · exact h ▸ inf_le_right
  have hDtop : D = ⊤ := by
    refine eq_top_of_isIrreducible_of_map_le hρ (fun g => ?_) ?_
    · rw [hD, Submodule.map_iSup]
      exact iSup_le fun i => by rw [map_rho_map_rho]; exact hall _
    · intro hc
      have hSD : S ≤ D := (map_rho_one ρ S) ▸ hall 1
      rw [hc] at hSD
      exact hS0 (le_bot_iff.1 hSD)
  have hint : DirectSum.IsInternal (fun i => S.map (ρ (x i))) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hx hDtop
  refine ⟨sSup 𝒩, x, hint, ?_⟩
  rw [finrank_eq_sum_of_isInternal hint]
  simp [finrank_map_rho, mul_comm]

end CFSG.FeitThompson
