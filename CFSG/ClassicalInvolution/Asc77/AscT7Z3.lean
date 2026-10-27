module

public import CFSG.ClassicalInvolution.Generic.TypeA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

namespace T7Z

theorem eq_top_of_index_le_four {U : Type} [Group U] [Finite U] [Group.IsPerfect U]
    (H : Subgroup U) (hH : H.index ≤ 4) : H = ⊤ := by
  classical
  by_contra hne
  have hi : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  set φ : U →* Equiv.Perm (U ⧸ H) := MulAction.toPermHom U (U ⧸ H) with hφ
  have hcard : Nat.card (U ⧸ H) ≤ 4 := by
    rw [← Subgroup.index_eq_card]
    exact hH
  have hsolv : Group.IsSolvable φ.range := by
    have : Group.IsSolvable (Equiv.Perm (U ⧸ H)) := Equiv.Perm.isSolvable hcard
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective φ.range)
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have htriv : Subsingleton φ.range := by
    by_contra hns
    have : Nontrivial φ.range := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable φ.range hsolv
  have hfix : ∀ g : U, g ∈ H := by
    intro g
    have h1 : φ g = 1 := by
      have := Subsingleton.elim (⟨φ g, ⟨g, rfl⟩⟩ : φ.range) 1
      exact congrArg Subtype.val this
    have h2 := congrArg (fun σ : Equiv.Perm (U ⧸ H) => σ (QuotientGroup.mk 1)) h1
    simp only [hφ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one,
      id_eq] at h2
    have h3 : (QuotientGroup.mk (g * 1) : U ⧸ H) = QuotientGroup.mk 1 := h2
    rw [mul_one] at h3
    have h4 := QuotientGroup.eq.mp h3
    simpa using H.inv_mem h4
  exact hne (eq_top_iff.mpr fun g _ => hfix g)

theorem card_center_sl_four_le (F : Type) [Field F] :
    Nat.card (Subgroup.center SL(4, F)) ≤ 4 := by
  classical
  have h := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 4) (R := F)
  rw [Nat.card_congr h.toEquiv]
  have hne : NeZero (max (Fintype.card (Fin 4)) 1) := ⟨by simp⟩
  exact (card_rootsOfUnity (k := max (Fintype.card (Fin 4)) 1) (R := F)).trans (by simp)

theorem linearBlockStandardPair_range_eq_sup {F : Type} [Field F] {X : Type} [Group X]
    {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) : W = U ⊔ V := by
  obtain ⟨θ, c, hW, -, hUV⟩ := h
  have htop : ((CFSG.ClassicalInvolution.WeakCT.B12 F).map (MulAut.conj c⁻¹).toMonoidHom) ⊔
      ((CFSG.ClassicalInvolution.WeakCT.B23 F).map (MulAut.conj c⁻¹).toMonoidHom) = ⊤ := by
    rw [← Subgroup.map_sup, CFSG.ClassicalInvolution.WeakCT.B12_sup_B23, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj c⁻¹).surjective
  rw [← hW, MonoidHom.range_eq_map, ← htop, Subgroup.map_sup]
  rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

theorem sup_eq_top_of_chain {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card F = p ^ f) (hq : 4 ≤ p ^ f) [Group.IsPerfect SL(4, F)]
    {R₁ R₂ R₃ : Subgroup SL(4, F)} (h12 : ∃ W, LinearBlockStandardPair F W R₁ R₂)
    (h23 : ∃ W, LinearBlockStandardPair F W R₂ R₃) (h13 : Commutes R₁ R₃) :
    R₁ ⊔ R₂ ⊔ R₃ = ⊤ := by
  classical
  set H : Subgroup SL(4, F) := R₁ ⊔ R₂ ⊔ R₃ with hH
  have hR₁ : R₁ ≤ H := le_sup_left.trans le_sup_left
  have hR₂ : R₂ ≤ H := le_sup_right.trans le_sup_left
  have hR₃ : R₃ ≤ H := le_sup_right
  obtain ⟨W₁, hW₁⟩ := h12
  obtain ⟨W₂, hW₂⟩ := h23
  have hW₁H : W₁ ≤ H := by
    rw [linearBlockStandardPair_range_eq_sup hW₁]
    exact sup_le hR₁ hR₂
  have hW₂H : W₂ ≤ H := by
    rw [linearBlockStandardPair_range_eq_sup hW₂]
    exact sup_le hR₂ hR₃
  let U' : Fin 3 → Subgroup ↥H := ![R₁.subgroupOf H, R₂.subgroupOf H, R₃.subgroupOf H]
  have hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ U' i, ∀ y ∈ U' j, x * y = y * x := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j <;> simp at hij
    exact Subtype.ext (h13 _ hx _ hy)
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F W (U' i) (U' j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact ⟨_, Generic.linearBlockStandardPair_subgroupOf hW₁H hW₁⟩
    · exact ⟨_, Generic.linearBlockStandardPair_subgroupOf hW₂H hW₂⟩
  have hgen : ⨆ i, U' i = ⊤ := by
    have h1 := Subgroup.subgroupOf_sup (A := R₁ ⊔ R₂) (A' := R₃) (B := H) (sup_le hR₁ hR₂) hR₃
    have h2 := Subgroup.subgroupOf_sup (A := R₁) (A' := R₂) (B := H) hR₁ hR₂
    have h3 : (R₁ ⊔ R₂ ⊔ R₃).subgroupOf H = ⊤ := Subgroup.subgroupOf_self H
    refine eq_top_iff.mpr ?_
    rw [← h3, h1, h2]
    exact sup_le (sup_le (le_iSup U' 0) (le_iSup U' 1)) (le_iSup U' 2)
  obtain ⟨ψ, hsurj, hker, -, -⟩ := CFSG.ClassicalInvolution.WeakCT.weakCT_recognition_of_pairs F p
    f hp hK hq (n := 3) (by norm_num) hcomm hpair hgen
  have hcent : Nat.card ψ.ker ≤ 4 :=
    (Subgroup.card_le_of_le hker).trans (card_center_sl_four_le F)
  have hkeridx : ψ.ker.index = Nat.card ↥H := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv
  have h1 : H.index * Nat.card ↥H = Nat.card SL(4, F) := Subgroup.index_mul_card H
  have h2 : ψ.ker.index * Nat.card ψ.ker = Nat.card SL(4, F) := Subgroup.index_mul_card ψ.ker
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have hidx : H.index = Nat.card ψ.ker := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← h2, hkeridx, mul_comm]
  exact eq_top_of_index_le_four H (hidx ▸ hcent)

end T7Z

end CFSG.ClassicalInvolution.Asc77
