module

public import CFSG.ClassicalGroups.Alternating.I4SpPlane
public import CFSG.Monster.B.TwoA.Base.GeomLin

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

@[expose] def PlaneAdj (BN : BilinForm K N) (D σ σ' : Submodule K N) : Prop :=
  IsPlane BN σ ∧ IsPlane BN σ' ∧ finrank K ↥(σ ⊓ σ') = 2 ∧ D ≤ σ ∧ D ≤ σ'

section Chain

variable [FiniteDimensional K N] (hBN : BN.IsAlt)

include hBN in
theorem exists_plane_adj_step {π π' : Submodule K N} (hπ : IsPlane BN π) (hπ' : IsPlane BN π')
    (hdim : finrank K ↥(π ⊓ π') ≤ 1) :
    ∃ π₁ : Submodule K N, IsPlane BN π₁ ∧ finrank K ↥(π ⊓ π₁) = 2 ∧ π ⊓ π' ≤ π₁ ∧
      finrank K ↥(π ⊓ π') + 1 ≤ finrank K ↥(π₁ ⊓ π') := by
  obtain ⟨x, hxπ', hxπ⟩ : ∃ x ∈ π', x ∉ π := by
    by_contra hcon
    push Not at hcon
    have hle : π' ≤ π := hcon
    have : π ⊓ π' = π' := inf_eq_right.mpr hle
    rw [this, hπ'.2] at hdim
    omega
  have hx0 : x ≠ 0 := fun h => hxπ (h ▸ π.zero_mem)
  let φ : ↥π →ₗ[K] K := (BN x).comp π.subtype
  let Z : Submodule K N := (LinearMap.ker φ).map π.subtype
  have hZdim : 2 ≤ finrank K Z := by
    have h3 := hπ.2
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : finrank K (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      rwa [Module.finrank_self] at this
    rw [Submodule.finrank_map_subtype_eq]
    omega
  have hZmem : ∀ y ∈ Z, y ∈ π ∧ BN x y = 0 := by
    rintro _ ⟨⟨y, hy⟩, hyk, rfl⟩
    exact ⟨hy, hyk⟩
  have hDZ : π ⊓ π' ≤ Z := by
    rintro y ⟨hyπ, hyπ'⟩
    exact ⟨⟨y, hyπ⟩, hπ'.1 x hxπ' y hyπ', rfl⟩
  obtain ⟨L, hDL, hLZ, hL2⟩ := CFSG.Monster.B.TwoA.exists_submodule_between hDZ
    (k := 2) (by omega) hZdim
  have hLπ : L ≤ π := fun y hy => (hZmem y (hLZ hy)).1
  have hxL : x ∉ L := fun h => hxπ (hLπ h)
  refine ⟨L ⊔ Submodule.span K {x}, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro u hu v hv
    obtain ⟨l, hl, s, hs, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨l', hl', t, ht, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp ht
    have e1 : BN x l = 0 := (hZmem l (hLZ hl)).2
    have e2 : BN x l' = 0 := (hZmem l' (hLZ hl')).2
    have e3 : BN l x = 0 := hBN.eq_iff.mp e1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e2,
      e3, hπ.1 l (hLπ hl) l' (hLπ hl'), hBN.self_eq_zero]
    ring
  · rw [CFSG.Monster.B.TwoA.finrank_sup_span_singleton_of_not_mem hxL, hL2]
  ·
    have : π ⊓ (L ⊔ Submodule.span K {x}) = L := by
      refine le_antisymm ?_ (le_inf hLπ le_sup_left)
      rintro y ⟨hyπ, hy⟩
      obtain ⟨l, hl, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
      have hs : s • x ∈ π := by
        have := π.sub_mem hyπ (hLπ hl)
        rwa [add_sub_cancel_left] at this
      have hs0 : s = 0 := by
        by_contra hs0
        exact hxπ (by simpa [smul_smul, inv_mul_cancel₀ hs0] using π.smul_mem s⁻¹ hs)
      rw [hs0, zero_smul, add_zero]
      exact hl
    rw [this, hL2]
  · exact hDL.trans le_sup_left
  ·
    have hxD : x ∉ π ⊓ π' := fun h => hxπ h.1
    have hle : (π ⊓ π') ⊔ Submodule.span K {x} ≤ (L ⊔ Submodule.span K {x}) ⊓ π' :=
      sup_le (le_inf (hDL.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right ((Submodule.span_singleton_le_iff_mem x π').mpr hxπ'))
    have := Submodule.finrank_mono hle
    rwa [CFSG.Monster.B.TwoA.finrank_sup_span_singleton_of_not_mem hxD] at this


theorem eq_of_finrank_inf_eq_three {π π' : Submodule K N} (hπ : IsPlane BN π)
    (hπ' : IsPlane BN π') (h : finrank K ↥(π ⊓ π') = 3) : π = π' := by
  have h1 : π ⊓ π' = π := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h, hπ.2])
  have hle : π ≤ π' := h1 ▸ inf_le_right
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hπ.2, hπ'.2])

include hBN in
theorem exists_planeAdj_chain_aux {π' D : Submodule K N} (hπ' : IsPlane BN π') :
    ∀ n : ℕ, ∀ π : Submodule K N, IsPlane BN π → D ≤ π ⊓ π' → 3 ≤ finrank K ↥(π ⊓ π') + n →
      Relation.ReflTransGen (PlaneAdj BN D) π π' := by
  intro n
  induction n with
  | zero =>
    intro π hπ hD h3
    have : π = π' := eq_of_finrank_inf_eq_three hπ hπ' (by
      have := Submodule.finrank_mono (inf_le_left : π ⊓ π' ≤ π)
      rw [hπ.2] at this
      omega)
    rw [this]
  | succ n ih =>
    intro π hπ hD h3
    by_cases h2 : 2 ≤ finrank K ↥(π ⊓ π')
    · by_cases h : π = π'
      · rw [h]
      · have hle3 := Submodule.finrank_mono (inf_le_left : π ⊓ π' ≤ π)
        rw [hπ.2] at hle3
        have hne : finrank K ↥(π ⊓ π') ≠ 3 := fun h3' => h (eq_of_finrank_inf_eq_three hπ hπ' h3')
        exact Relation.ReflTransGen.single
          ⟨hπ, hπ', by omega, hD.trans inf_le_left, hD.trans inf_le_right⟩
    · push Not at h2
      obtain ⟨π₁, hπ₁, hπ₁dim, hπ₁D, hπ₁fin⟩ := exists_plane_adj_step hBN hπ hπ' (by omega)
      exact Relation.ReflTransGen.head
        ⟨hπ, hπ₁, hπ₁dim, hD.trans inf_le_left, hD.trans hπ₁D⟩
        (ih π₁ hπ₁ (le_inf (hD.trans hπ₁D) (hD.trans inf_le_right)) (by omega))

include hBN in
theorem exists_planeAdj_chain {π π' : Submodule K N} (hπ : IsPlane BN π) (hπ' : IsPlane BN π') :
    Relation.ReflTransGen (PlaneAdj BN (π ⊓ π')) π π' :=
  exists_planeAdj_chain_aux hBN hπ' 3 π hπ le_rfl (by omega)

include hBN in
theorem exists_planeAdj_chain_through {π π' : Submodule K N} (hπ : IsPlane BN π)
    (hπ' : IsPlane BN π') {a : N} (ha : a ∈ π ⊓ π') :
    Relation.ReflTransGen (fun σ σ' => PlaneAdj BN (π ⊓ π') σ σ' ∧ a ∈ σ ∧ a ∈ σ') π π' := by
  have key := exists_planeAdj_chain hBN hπ hπ'
  exact Relation.ReflTransGen.mono
    (p := fun σ σ' => PlaneAdj BN (π ⊓ π') σ σ' ∧ a ∈ σ ∧ a ∈ σ')
    (fun σ σ' h => ⟨h, h.2.2.2.1 ha, h.2.2.2.2 ha⟩) π π' key

end Chain

end CFSG.ClassicalGroups.Alternating
