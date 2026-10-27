module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIYCriterion

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoHypIIY
open scoped commutatorElement

variable {α β : Type*}

theorem perm_apply_inv (σ : Perm β) (b : β) : σ (σ⁻¹ b) = b :=
  σ.apply_symm_apply b

theorem viaEmbeddingHom_apply_image (ι : α ↪ β) (π : Perm α) (a : α) :
    viaEmbeddingHom ι π (ι a) = ι (π a) :=
  viaEmbedding_apply π ι a

theorem viaEmbeddingHom_apply_of_notMem (ι : α ↪ β) (π : Perm α) {b : β}
    (hb : b ∉ Set.range ι) : viaEmbeddingHom ι π b = b :=
  viaEmbedding_apply_of_notMem π ι b hb

theorem conj_viaEmbedding (ι : α ↪ β) {σ : Perm β} {τ : Perm α} (h : ∀ a, σ (ι a) = ι (τ a))
    (π : Perm α) :
    σ * viaEmbeddingHom ι π * σ⁻¹ = viaEmbeddingHom ι (τ * π * τ⁻¹) := by
  have hinv : ∀ a, σ⁻¹ (ι a) = ι (τ⁻¹ a) := fun a => by
    rw [Perm.inv_eq_iff_eq, h, perm_apply_inv]
  ext b
  by_cases hb : b ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hb
    simp only [Perm.mul_apply, hinv, viaEmbeddingHom_apply_image, h]
  · have hb' : σ⁻¹ b ∉ Set.range ι := by
      rintro ⟨a, ha⟩
      apply hb
      refine ⟨τ a, ?_⟩
      rw [← h, ha, perm_apply_inv]
    simp only [Perm.mul_apply, viaEmbeddingHom_apply_of_notMem ι _ hb',
      viaEmbeddingHom_apply_of_notMem ι _ hb, perm_apply_inv]

theorem viaEmbeddingHom_mul_comm (ι : α ↪ β) {σ : Perm β} {τ : Perm α}
    (h : ∀ a, σ (ι a) = ι (τ a)) {π : Perm α} (hπ : π * τ = τ * π) :
    viaEmbeddingHom ι π * σ = σ * viaEmbeddingHom ι π := by
  have h1 := conj_viaEmbedding ι h π
  rw [show τ * π * τ⁻¹ = π by rw [← hπ, mul_inv_cancel_right]] at h1
  calc viaEmbeddingHom ι π * σ = (σ * viaEmbeddingHom ι π * σ⁻¹) * σ := by rw [h1]
    _ = σ * viaEmbeddingHom ι π := by group

theorem viaEmbeddingHom_commutatorElement (ι : α ↪ β) {σ : Perm β} {τ : Perm α}
    (h : ∀ a, σ (ι a) = ι (τ a)) (π : Perm α) :
    viaEmbeddingHom ι ⁅τ, π⁆ = ⁅σ, viaEmbeddingHom ι π⁆ := by
  rw [commutatorElement_def, commutatorElement_def, map_mul (viaEmbeddingHom ι) (τ * π * τ⁻¹),
    ← conj_viaEmbedding ι h, map_inv]

theorem forall_mem_closure_pair (ι : α ↪ β) {E : Subgroup (Perm β)} {a b : Perm α}
    {ya yb : Perm β} (hya : ya ∈ E) (hyb : yb ∈ E) (ha : ∀ i, ya (ι i) = ι (a i))
    (hb : ∀ i, yb (ι i) = ι (b i)) :
    ∀ x ∈ closure ({a, b} : Set (Perm α)), ∃ y ∈ E, ∀ i, y (ι i) = ι (x i) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨ya, hya, ha⟩
    · exact ⟨yb, hyb, hb⟩
  | one => exact ⟨1, E.one_mem, fun i => rfl⟩
  | mul x x' _ _ ih ih' =>
    obtain ⟨y, hy, hyx⟩ := ih
    obtain ⟨y', hy', hyx'⟩ := ih'
    exact ⟨y * y', E.mul_mem hy hy', fun i => by simp only [Perm.mul_apply, hyx', hyx]⟩
  | inv x _ ih =>
    obtain ⟨y, hy, hyx⟩ := ih
    refine ⟨y⁻¹, E.inv_mem hy, fun i => ?_⟩
    rw [Perm.inv_eq_iff_eq, hyx, perm_apply_inv]

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem sign_viaEmbeddingHom (ι : α ↪ β) (π : Perm α) : sign (viaEmbeddingHom ι π) = sign π := by
  classical
  rw [viaEmbeddingHom_apply, viaEmbedding]
  convert sign_extendDomain π (Equiv.ofInjective ι.1 ι.2)

theorem viaEmbeddingHom_mem_alternatingGroup (ι : α ↪ β) {π : Perm α}
    (hπ : π ∈ alternatingGroup α) : viaEmbeddingHom ι π ∈ alternatingGroup β := by
  rw [mem_alternatingGroup, sign_viaEmbeddingHom]
  exact mem_alternatingGroup.mp hπ

theorem map_nE_le (ι : α ↪ β) {E' : Subgroup (Perm α)} {E : Subgroup (Perm β)}
    (hE : ∀ x ∈ E', ∃ y ∈ E, ∀ a, y (ι a) = ι (x a)) :
    (nE (alternatingGroup α) E').map (viaEmbeddingHom ι) ≤ nE (alternatingGroup β) E := by
  have hC : ∀ x ∈ E', x ≠ 1 → ∃ y ∈ E, y ≠ 1 ∧
      (alternatingGroup α ⊓ centralizer ({x} : Set (Perm α))).map (viaEmbeddingHom ι) ≤
        alternatingGroup β ⊓ centralizer ({y} : Set (Perm β)) := by
    intro x hx hx1
    obtain ⟨y, hy, hyx⟩ := hE x hx
    refine ⟨y, hy, ?_, ?_⟩
    · rintro rfl
      apply hx1
      ext a
      exact (ι.injective (by simpa using (hyx a).symm))
    · rintro _ ⟨c, ⟨hcA, hcC⟩, rfl⟩
      have hcC' : c ∈ centralizer ({x} : Set (Perm α)) := hcC
      refine ⟨viaEmbeddingHom_mem_alternatingGroup ι hcA, ?_⟩
      show viaEmbeddingHom ι c ∈ centralizer ({y} : Set (Perm β))
      rw [mem_centralizer_singleton_iff]
      exact viaEmbeddingHom_mul_comm ι hyx (mem_centralizer_singleton_iff.mp hcC')
  have hΓ : (gammaE (alternatingGroup α) E').map (viaEmbeddingHom ι) ≤
      gammaE (alternatingGroup β) E := by
    rw [gammaE, Subgroup.map_iSup]
    refine iSup_le fun x => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hx => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hx1 => ?_
    obtain ⟨y, hy, hy1, hle⟩ := hC x hx hx1
    rw [centDer, Subgroup.map_commutator]
    exact (commutator_mono hle hle).trans (le_iSup₂_of_le y hy (le_iSup_of_le hy1 le_rfl))
  rw [nE, Subgroup.map_le_iff_le_comap, commutator_le]
  intro x hx h hh
  obtain ⟨y, hy, hyx⟩ := hE x hx
  rw [Subgroup.mem_comap, viaEmbeddingHom_commutatorElement ι hyx]
  exact commutator_mem_commutator hy (hΓ ⟨h, hh, rfl⟩)

theorem even_card_alternatingGroup (h4 : 4 ≤ Fintype.card α) :
    Even (Nat.card (alternatingGroup α)) := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial h4
  rw [hk, show Nat.factorial 4 = 2 * 12 by rfl, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  exact ⟨6 * k, by ring⟩

theorem qWitness_of_alternatingGroup_le_nE (ι : α ↪ β) (h5 : 5 ≤ Fintype.card α)
    {E' : Subgroup (Perm α)} {E : Subgroup (Perm β)}
    (hE : ∀ x ∈ E', ∃ y ∈ E, ∀ a, y (ι a) = ι (x a))
    (hA : alternatingGroup α ≤ nE (alternatingGroup α) E') :
    QWitness (alternatingGroup β) E := by
  refine ⟨(alternatingGroup α).map (viaEmbeddingHom ι),
    (Subgroup.map_mono hA).trans (map_nE_le ι hE), ?_, ?_⟩
  · rw [← Subgroup.map_commutator,
      commutator_alternatingGroup_eq_self (by rwa [Nat.card_eq_fintype_card])]
  · rw [Subgroup.card_map_of_injective (viaEmbeddingHom_injective ι)]
    exact even_card_alternatingGroup (by omega)

section Map

variable {W W' : Type*} [Group W] [Group W'] (f : W' →* W) (hf : Function.Injective f)
include hf

theorem map_inf_centralizer (X : Subgroup W') (e : W') :
    (X ⊓ centralizer ({e} : Set W')).map f = X.map f ⊓ centralizer ({f e} : Set W) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxX, hxC⟩, rfl⟩
    have hxC' : x ∈ centralizer ({e} : Set W') := hxC
    refine ⟨⟨x, hxX, rfl⟩, ?_⟩
    show f x ∈ centralizer ({f e} : Set W)
    rw [mem_centralizer_singleton_iff] at hxC' ⊢
    rw [← map_mul, ← map_mul, hxC']
  · rintro ⟨⟨x, hxX, rfl⟩, hC⟩
    have hC' : f x ∈ centralizer ({f e} : Set W) := hC
    refine ⟨x, ⟨hxX, ?_⟩, rfl⟩
    show x ∈ centralizer ({e} : Set W')
    rw [mem_centralizer_singleton_iff] at hC' ⊢
    exact hf (by rw [map_mul, map_mul, hC'])

theorem map_centDer (X : Subgroup W') (e : W') :
    (centDer X e).map f = centDer (X.map f) (f e) := by
  rw [centDer, centDer, Subgroup.map_commutator, map_inf_centralizer f hf]

theorem map_gammaE (X E : Subgroup W') : (gammaE X E).map f = gammaE (X.map f) (E.map f) := by
  apply le_antisymm
  · rw [gammaE, Subgroup.map_iSup]
    refine iSup_le fun e => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun he => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun he1 => ?_
    rw [map_centDer f hf]
    exact le_iSup₂_of_le (f e) ⟨e, he, rfl⟩
      (le_iSup_of_le (fun h => he1 (hf (h.trans (map_one f).symm))) le_rfl)
  · refine iSup₂_le fun y hy => iSup_le fun hy1 => ?_
    obtain ⟨e, he, rfl⟩ := hy
    rw [← map_centDer f hf]
    exact Subgroup.map_mono
      (le_iSup₂_of_le e he (le_iSup_of_le (fun h => hy1 (by rw [h, map_one])) le_rfl))

theorem map_nE (X E : Subgroup W') : (nE X E).map f = nE (X.map f) (E.map f) := by
  rw [nE, nE, Subgroup.map_commutator, map_gammaE f hf]

end Map

theorem nE_mono {W : Type*} [Group W] {X E E' : Subgroup W} (h : E ≤ E') : nE X E ≤ nE X E' := by
  have hΓ : gammaE X E ≤ gammaE X E' :=
    iSup₂_le fun e he => iSup_le fun he1 => le_iSup₂_of_le e (h he) (le_iSup_of_le he1 le_rfl)
  exact commutator_mono h hΓ

end CFSG.ComponentClassification.RankTwoAlt
