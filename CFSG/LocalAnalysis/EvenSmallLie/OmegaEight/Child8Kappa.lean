module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Bridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8UArg

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup Weyl

namespace Bridge

@[expose] noncomputable def commHom (h : WeylPackage) {c : Equiv.Perm (Fin 240)} (hc : c ∈ tSub) :
    e1Sub →* Equiv.Perm (Fin 240) where
  toFun e := e * c * (e : Equiv.Perm (Fin 240))⁻¹ * c⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hmem : ∀ x : e1Sub, (x : Equiv.Perm (Fin 240)) * c * (x : Equiv.Perm (Fin 240))⁻¹ *
        c⁻¹ ∈ e1Sub := fun x => by
      have e : (x : Equiv.Perm (Fin 240)) * c * (x : Equiv.Perm (Fin 240))⁻¹ * c⁻¹ =
          (x : Equiv.Perm (Fin 240)) * (c * (x : Equiv.Perm (Fin 240))⁻¹ * c⁻¹) := by group
      rw [e]
      exact mul_mem x.2 (conj_mem_e1Sub h hc (inv_mem x.2))
    have h1 := h.abelian.comm_e1Sub _ a.2 _ (hmem b)
    have h2 := h.abelian.comm_e1Sub _ (hmem a) _ (hmem b)
    simp only [coe_mul, mul_inv_rev]
    rw [show (a : Equiv.Perm (Fin 240)) * b * c * ((b : Equiv.Perm (Fin 240))⁻¹ *
        (a : Equiv.Perm (Fin 240))⁻¹) * c⁻¹ = a * (b * c * (b : Equiv.Perm (Fin 240))⁻¹ * c⁻¹) *
          c * (a : Equiv.Perm (Fin 240))⁻¹ * c⁻¹ by group, h1,
      show (b : Equiv.Perm (Fin 240)) * c * (b : Equiv.Perm (Fin 240))⁻¹ * c⁻¹ * a * c *
        (a : Equiv.Perm (Fin 240))⁻¹ * c⁻¹ = (b * c * (b : Equiv.Perm (Fin 240))⁻¹ * c⁻¹) *
          (a * c * (a : Equiv.Perm (Fin 240))⁻¹ * c⁻¹) by group, h2]

variable (h : WeylPackage)
include h

theorem mem_range_commHom {c : Equiv.Perm (Fin 240)} (hc : c ∈ tSub) {g : Equiv.Perm (Fin 240)} :
    g ∈ (commHom h hc).range ↔ ∃ e ∈ e1Sub, g = e * c * e⁻¹ * c⁻¹ :=
  ⟨fun ⟨e, he⟩ => ⟨e, e.2, he.symm⟩, fun ⟨e, he, hg⟩ => ⟨⟨e, he⟩, hg.symm⟩⟩

theorem map_ker_commHom {c : Equiv.Perm (Fin 240)} (hc : c ∈ tSub) :
    (commHom h hc).ker.map e1Sub.subtype = e1Sub ⊓ centralizer {c} := by
  ext g
  constructor
  · rintro ⟨e, he, rfl⟩
    have he : (e : Equiv.Perm (Fin 240)) * c * (e : Equiv.Perm (Fin 240))⁻¹ * c⁻¹ = 1 := he
    refine Subgroup.mem_inf.2 ⟨e.2, mem_centralizer_singleton_iff.2 ?_⟩
    calc (e : Equiv.Perm (Fin 240)) * c =
          e * c * (e : Equiv.Perm (Fin 240))⁻¹ * c⁻¹ * (c * e) := by group
      _ = c * e := by rw [he, one_mul]
  · intro hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
    refine ⟨⟨g, hg1⟩, ?_, rfl⟩
    change g * c * g⁻¹ * c⁻¹ = 1
    rw [mem_centralizer_singleton_iff.1 hg2]
    group

theorem card_mul_card_range {c : Equiv.Perm (Fin 240)} (hc : c ∈ tSub) :
    Nat.card (e1Sub ⊓ centralizer {c} : Subgroup (Equiv.Perm (Fin 240))) *
      Nat.card (commHom h hc).range = 2 ^ 8 := by
  rw [← map_ker_commHom h hc, card_map_of_injective e1Sub.subtype_injective,
    ← index_ker, card_mul_index, h.abelian.card_e1Sub]

@[expose] def coordSub (i j : Fin 8) : Subgroup (Equiv.Perm (Fin 240)) where
  carrier := {g | ∃ v : FrameVec, v i = 0 ∧ v j = 0 ∧ frameElt v = g}
  mul_mem' := by
    rintro _ _ ⟨v, hv1, hv2, rfl⟩ ⟨w, hw1, hw2, rfl⟩
    exact ⟨v + w, by simp [hv1, hw1], by simp [hv2, hw2], h.coords.frameElt_add v w⟩
  one_mem' := ⟨0, rfl, rfl, frameElt_zero h⟩
  inv_mem' := by
    rintro _ ⟨v, hv1, hv2, rfl⟩
    refine ⟨v, hv1, hv2, (inv_eq_of_mul_eq_one_right ?_).symm⟩
    rw [← h.coords.frameElt_add, frameVec_add_self, frameElt_zero h]

theorem S01_frame : signPerm (vec2 0 1) = frameElt (vec2 0 1) :=
  h.coords.signPerm_pair 0 (by decide)

theorem S23_frame : signPerm (vec2 2 3) = frameElt (vec2 2 3) :=
  h.coords.signPerm_pair 2 (by decide)

theorem S45_frame : signPerm (vec2 4 5) = frameElt (vec2 4 5) :=
  h.coords.signPerm_pair 4 (by decide)

theorem S67_frame : signPerm (vec2 6 7) = frameElt (vec2 6 7) :=
  h.coords.signPerm_pair 6 (by decide)

theorem S45_not_mem :
    signPerm (vec2 4 5) ∉ closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} := by
  intro hmem
  have hle : closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} ≤ coordSub h 4 5 := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨vec2 0 1, by decide, by decide, (S01_frame h).symm⟩
    · exact ⟨vec2 2 3, by decide, by decide, (S23_frame h).symm⟩
  obtain ⟨v, hv1, -, hv⟩ := hle hmem
  rw [S45_frame h] at hv
  rw [h.coords.frameElt_injective hv] at hv1
  exact absurd hv1 (by decide)

theorem S01_not_mem :
    signPerm (vec2 0 1) ∉ closure {signPerm (vec2 4 5), signPerm (vec2 6 7)} := by
  intro hmem
  have hle : closure {signPerm (vec2 4 5), signPerm (vec2 6 7)} ≤ coordSub h 0 1 := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨vec2 4 5, by decide, by decide, (S45_frame h).symm⟩
    · exact ⟨vec2 6 7, by decide, by decide, (S67_frame h).symm⟩
  obtain ⟨v, hv1, -, hv⟩ := hle hmem
  rw [S01_frame h] at hv
  rw [h.coords.frameElt_injective hv] at hv1
  exact absurd hv1 (by decide)

omit h in
theorem ne_of_mul_card_eq {A B : Subgroup (Equiv.Perm (Fin 240))} (hAB : A ≤ B) (hne : A ≠ B)
    {k₁ k₂ : ℕ} (h1 : k₁ * Nat.card A = 2 ^ 8) (h2 : k₂ * Nat.card B = 2 ^ 8) : k₁ ≠ k₂ := by
  rintro rfl
  have hcard : Nat.card A < Nat.card B :=
    lt_of_le_of_ne (card_le_of_le hAB) fun he => hne (eq_of_le_of_card_ge hAB he.ge)
  have hk0 : 0 < k₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
  have h3 := Nat.mul_lt_mul_of_pos_left hcard hk0
  omega

theorem tSub_mem {v : FrameVec} (hv : v ∈ evenSub) : signPerm v ∈ tSub :=
  eSub_le_tSub h (signPerm_mem_eSub h hv)

omit h in
theorem v0246_mem : vec2 0 2 + vec2 4 6 ∈ evenSub := add_mem v02_mem v46_mem

theorem kappa_eq (v : FrameVec) (hv : v ∈ evenSub)
    {S : Set (Equiv.Perm (Fin 240))}
    (hS : ∀ g, (∃ e ∈ e1Sub, g = e * signPerm v * e⁻¹ * (signPerm v)⁻¹) ↔ g ∈ closure S) :
    Nat.card (e1Sub ⊓ centralizer {signPerm v} : Subgroup (Equiv.Perm (Fin 240))) *
      Nat.card (closure S) = 2 ^ 8 := by
  have h1 := card_mul_card_range h (tSub_mem h hv)
  have h2 : (commHom h (tSub_mem h hv)).range = closure S := by
    ext g
    rw [mem_range_commHom, hS]
  rwa [h2] at h1

theorem card_ne_S02 : Nat.card (e1Sub ⊓ centralizer {signPerm (vec2 0 2)} :
    Subgroup (Equiv.Perm (Fin 240))) ≠ Nat.card (e1Sub ⊓
      centralizer {signPerm (vec2 0 2 + vec2 4 6)} : Subgroup (Equiv.Perm (Fin 240))) := by
  have h1 := kappa_eq h _ v02_mem h.uArg.comm_02
  have h2 := kappa_eq h _ v0246_mem h.uArg.comm_0246
  have hle : closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} ≤
      closure {signPerm (vec2 0 1), signPerm (vec2 2 3), signPerm (vec2 4 5),
        signPerm (vec2 6 7)} := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hS45 : signPerm (vec2 4 5) ∈ closure {signPerm (vec2 0 1), signPerm (vec2 2 3),
      signPerm (vec2 4 5), signPerm (vec2 6 7)} :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hne : closure {signPerm (vec2 0 1), signPerm (vec2 2 3)} ≠
      closure {signPerm (vec2 0 1), signPerm (vec2 2 3), signPerm (vec2 4 5),
        signPerm (vec2 6 7)} := fun he => by
    rw [← he] at hS45
    exact S45_not_mem h hS45
  exact ne_of_mul_card_eq hle hne h1 h2

theorem card_ne_S46 : Nat.card (e1Sub ⊓ centralizer {signPerm (vec2 4 6)} :
    Subgroup (Equiv.Perm (Fin 240))) ≠ Nat.card (e1Sub ⊓
      centralizer {signPerm (vec2 0 2 + vec2 4 6)} : Subgroup (Equiv.Perm (Fin 240))) := by
  have h1 := kappa_eq h _ v46_mem h.uArg.comm_46
  have h2 := kappa_eq h _ v0246_mem h.uArg.comm_0246
  have hle : closure {signPerm (vec2 4 5), signPerm (vec2 6 7)} ≤
      closure {signPerm (vec2 0 1), signPerm (vec2 2 3), signPerm (vec2 4 5),
        signPerm (vec2 6 7)} := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl)))
  have hS01 : signPerm (vec2 0 1) ∈ closure {signPerm (vec2 0 1), signPerm (vec2 2 3),
      signPerm (vec2 4 5), signPerm (vec2 6 7)} := subset_closure (Set.mem_insert _ _)
  have hne : closure {signPerm (vec2 4 5), signPerm (vec2 6 7)} ≠
      closure {signPerm (vec2 0 1), signPerm (vec2 2 3), signPerm (vec2 4 5),
        signPerm (vec2 6 7)} := fun he => by
    rw [← he] at hS01
    exact S01_not_mem h hS01
  exact ne_of_mul_card_eq hle hne h1 h2

end Bridge

end CFSG.EvenSmallLie.OmegaEight.Child8
