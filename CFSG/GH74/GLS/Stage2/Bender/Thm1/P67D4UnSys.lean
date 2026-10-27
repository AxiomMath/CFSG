module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldNoAbel

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X} {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem FoldData.fixed_mem_sup (hf : FoldData R φ) {x : X} (hx : x ∈ H ⊔ U) (hφ : φ x = x) :
    ∃ u ∈ U ⊓ foldFix φ, ∃ h ∈ H ⊓ foldFix φ, x = u * h := by
  obtain ⟨u, hu, h, hh, rfl⟩ := (R.mem_sup_iff_UH).1 hx
  have hu' : φ u ∈ U := hf.toStab.mem_U hu
  have hh' : φ h ∈ H := hf.mem_H h hh
  rw [map_mul] at hφ
  have hmem : (φ u)⁻¹ * u ∈ U ⊓ H := by
    refine ⟨U.mul_mem (U.inv_mem hu') hu, ?_⟩
    have e : (φ u)⁻¹ * u = φ h * h⁻¹ := by
      calc (φ u)⁻¹ * u = (φ u)⁻¹ * (u * h) * h⁻¹ := by group
        _ = (φ u)⁻¹ * (φ u * φ h) * h⁻¹ := by rw [hφ]
        _ = φ h * h⁻¹ := by group
    rw [e]
    exact H.mul_mem hh' (H.inv_mem hh)
  rw [R.U_inf_H, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hφh : φ h = h := by
    rw [hmem] at hφ
    exact mul_left_cancel hφ
  exact ⟨u, ⟨hu, hmem⟩, h, ⟨hh, hφh⟩, rfl⟩

theorem FoldData.exists_system (hf : FoldData R φ) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    (hC : ∀ t ∈ H ⊓ foldFix φ, (∀ u ∈ U ⊓ foldFix φ, t * u = u * t) → t = 1)
    {m₁ m₂ : X} (h1 : φ m₁ = m₁) (h1H : r₁⁻¹ * m₁ ∈ H) (h2 : φ m₂ = m₂)
    (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * m₂ ∈ H) :
    ∃ D : RankTwoSystem ↥(foldFix φ) 3,
      (∀ k, IsRoot 3 k → ∀ x : ↥(foldFix φ), x ∈ D.root k ↔ (x : X) ∈ foldRoot φ root k) ∧
      (∀ x : ↥(foldFix φ), x ∈ D.U ↔ (x : X) ∈ U) ∧
      (∀ x : ↥(foldFix φ), x ∈ D.B ⊓ D.N ↔ (x : X) ∈ H) ∧
      (∀ x : ↥(foldFix φ), x ∈ D.B ↔ (x : X) ∈ H ⊔ U) ∧
      (∃ n₁ n₂ : D.N, (n₁ : D.Weyl) = D.w₁ ∧ (n₂ : D.Weyl) = D.w₂ ∧
        (((n₁ : ↥(foldFix φ)) : ↥(foldFix φ)) : X) = m₁ ∧
          (((n₂ : ↥(foldFix φ)) : ↥(foldFix φ)) : X) = m₂) := by
  classical
  have hr₁ : m₁ ∈ foldFix φ := h1
  have hr₂ : m₂ ∈ foldFix φ := h2
  have hroot : ∀ i, IsRoot 3 i → foldRoot φ root i ≤ foldFix φ := fun i _ => inf_le_right
  have R' := hf.rgd2 h1 h1H h2 h2H
  have hgen'' := R'.restrict_gen (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
    (fun x hx => hf.generation hgen hZ hz h1 h1H h2 h2H hx)
  have R'' := R'.restrict (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
  have hcn := R''.cartan_normal
  have hZ'' : ∀ g ∈ (H ⊓ foldFix φ).subgroupOf (foldFix φ),
      (∀ i, IsRoot 3 i → ∀ x ∈ (foldRoot φ root i).subgroupOf (foldFix φ), g * x = x * g) →
        g = 1 := by
    intro g hg hcomm
    have hcen : ∀ u ∈ (U ⊓ foldFix φ).subgroupOf (foldFix φ), g * u = u * g := by
      intro u hu
      have hu' : u ∈ chainProd (fun i => (foldRoot φ root i).subgroupOf (foldFix φ))
          (intList 1 ((3 : ℕ) : ℤ)) := by
        rw [← R''.carrier_eq]
        exact hu
      have hmem := chainProd_subset (fun i => (foldRoot φ root i).subgroupOf (foldFix φ))
        (Subgroup.centralizer {g}) (intList 1 ((3 : ℕ) : ℤ)) (fun k hk x hx => by
          have hk' := mem_intList_iff.1 hk
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact hcomm k (isRoot_of_pos_le hk'.1 hk'.2) x hx) hu'
      exact (Subgroup.mem_centralizer_iff.1 hmem) g rfl
    have hg' : (g : X) ∈ H ⊓ foldFix φ := Subgroup.mem_subgroupOf.1 hg
    exact Subtype.ext (hC (g : X) hg' fun u hu =>
      congrArg Subtype.val (hcen ⟨u, hu.2⟩ (Subgroup.mem_subgroupOf.2 hu)))
  refine ⟨(R''.toPre hgen'').toSystem (R''.faithful hgen'' hZ''), ?_, ?_, ?_, ?_, ?_⟩
  · intro k _ x
    exact Iff.rfl
  · intro x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  · intro x
    show x ∈ (_ ⊔ _) ⊓ R''.N ↔ _
    rw [R''.B_inf_N]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  · intro x
    constructor
    · intro hx
      have hx' : x ∈ (H ⊔ U).subgroupOf (foldFix φ) :=
        (sup_le (Subgroup.subgroupOf_mono _ (le_sup_left.trans' inf_le_left))
          (Subgroup.subgroupOf_mono _ (le_sup_right.trans' inf_le_left))) hx
      exact hx'
    · intro hx
      obtain ⟨u, hu, h, hh, hxe⟩ := hf.fixed_mem_sup hx x.2
      have e : x = (⟨u, hu.2⟩ : ↥(foldFix φ)) * ⟨h, hh.2⟩ := Subtype.ext hxe
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hu))
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hh))
  · exact ⟨R''.nrep 0, R''.nrep 1, rfl, rfl, rfl, rfl⟩

end CFSG.GH74.GLS.SP
