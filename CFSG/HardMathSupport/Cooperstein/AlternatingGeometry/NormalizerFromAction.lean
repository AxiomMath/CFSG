module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {Q : Type*} [Group Q] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_map_subgroupOf_iff {Lb : Subgroup Q} (H : Subgroup Q) (φ : ↥Lb ≃* AltB ι)
    (x : AltB ι) :
    x ∈ (H.subgroupOf Lb).map φ.toMonoidHom ↔ ((φ.symm x : ↥Lb) : Q) ∈ H := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have e : φ.symm (φ.toMonoidHom z) = z := φ.symm_apply_apply z
    rw [e]
    exact hz
  · intro h
    exact ⟨φ.symm x, h, by simp⟩

theorem conj_mem_of_mem_NA {Lb Sb : Subgroup Q} (φ : ↥Lb ≃* AltB ι)
    (hS : ((Sb ⊓ Lb).subgroupOf Lb).map φ.toMonoidHom = EA ι)
    (hSL : Sb ≤ Subgroup.normalizer (Lb : Set Q))
    (hact : ∀ s ∈ Sb, ∃ σ ∈ blockFix ι, ∀ l l' : ↥Lb, (l' : Q) = s * l * s⁻¹ →
      ((φ l' : AltB ι) : Perm (ι × Bool)) = σ * ((φ l : AltB ι) : Perm (ι × Bool)) * σ⁻¹)
    {y : ↥Lb} (hy : φ y ∈ NA ι) {s : Q} (hs : s ∈ Sb) :
    (y : Q) * s * (y : Q)⁻¹ ∈ Sb := by
  obtain ⟨σ, hσ, hσact⟩ := hact s hs
  have hsl : ∀ z ∈ Lb, s * z * s⁻¹ ∈ Lb := fun z hz =>
    (Subgroup.mem_normalizer_iff.1 (hSL hs) z).1 hz
  have hl' : s * ((y⁻¹ : ↥Lb) : Q) * s⁻¹ ∈ Lb := hsl _ (y⁻¹).2
  set l' : ↥Lb := ⟨s * ((y⁻¹ : ↥Lb) : Q) * s⁻¹, hl'⟩ with hl'def
  have hφl' : ((φ l' : AltB ι) : Perm (ι × Bool)) =
      σ * ((φ y : AltB ι) : Perm (ι × Bool))⁻¹ * σ⁻¹ := by
    have := hσact y⁻¹ l' rfl
    rw [this, map_inv]
    rfl
  set cz : ↥Lb := y * l' with hcz
  have hc : ((cz : ↥Lb) : Q) = (y : Q) * s * (y : Q)⁻¹ * s⁻¹ := by
    simp [hcz, hl'def, mul_assoc]
  have hφcz : ((φ cz : AltB ι) : Perm (ι × Bool)) =
      ((φ y : AltB ι) : Perm (ι × Bool)) * (σ * ((φ y : AltB ι) : Perm (ι × Bool))⁻¹ * σ⁻¹) := by
    rw [hcz, map_mul]
    show ((φ y : AltB ι) : Perm (ι × Bool)) * ((φ l' : AltB ι) : Perm (ι × Bool)) = _
    rw [hφl']
  have hφcz' : ((φ cz : AltB ι) : Perm (ι × Bool)) ∈ blockFix ι := by
    rw [hφcz, ← mul_assoc, ← mul_assoc]
    have h1 : ((φ y : AltB ι) : Perm (ι × Bool)) * σ *
        ((φ y : AltB ι) : Perm (ι × Bool))⁻¹ ∈ blockFix ι :=
      conj_mem_blockFix (mem_NA.1 hy) hσ
    exact mul_mem h1 (inv_mem hσ)
  have hcz_mem : φ cz ∈ EA ι := hφcz'
  rw [← hS, mem_map_subgroupOf_iff] at hcz_mem
  simp only [MulEquiv.symm_apply_apply, Subgroup.mem_inf] at hcz_mem
  rw [hc] at hcz_mem
  have : (y : Q) * s * (y : Q)⁻¹ = ((y : Q) * s * (y : Q)⁻¹ * s⁻¹) * s := by group
  rw [this]
  exact Sb.mul_mem hcz_mem.1 hs

theorem map_normalizer_eq_NA (hι : 2 ≤ Fintype.card ι) {Lb Sb : Subgroup Q} (φ : ↥Lb ≃* AltB ι)
    (hS : ((Sb ⊓ Lb).subgroupOf Lb).map φ.toMonoidHom = EA ι)
    (hSL : Sb ≤ Subgroup.normalizer (Lb : Set Q))
    (hact : ∀ s ∈ Sb, ∃ σ ∈ blockFix ι, ∀ l l' : ↥Lb, (l' : Q) = s * l * s⁻¹ →
      ((φ l' : AltB ι) : Perm (ι × Bool)) = σ * ((φ l : AltB ι) : Perm (ι × Bool)) * σ⁻¹) :
    ((Subgroup.normalizer (Sb : Set Q) ⊓ Lb).subgroupOf Lb).map φ.toMonoidHom = NA ι := by
  rw [← normalizer_EA hι]
  ext x
  rw [mem_map_subgroupOf_iff]
  set y : ↥Lb := φ.symm x with hy
  have hxy : φ y = x := by simp [hy]
  have hymem : ∀ z : ↥Lb, (z : Q) ∈ Sb ⊓ Lb ↔ φ z ∈ EA ι := by
    intro z
    rw [← hS, mem_map_subgroupOf_iff]
    simp
  constructor
  ·
    intro hyN
    simp only [Subgroup.mem_inf] at hyN
    rw [Subgroup.mem_normalizer_iff]
    intro h
    set z : ↥Lb := φ.symm h with hz
    have hzh : φ z = h := by simp [hz]
    have hconj : φ (y * z * y⁻¹) = x * h * x⁻¹ := by
      rw [map_mul, map_mul, map_inv, hxy, hzh]
    have hyL : ∀ w : ↥Lb, ((y * w * y⁻¹ : ↥Lb) : Q) = (y : Q) * w * (y : Q)⁻¹ := fun w => rfl
    have e1 : h ∈ EA ι ↔ (z : Q) ∈ Sb ⊓ Lb := by rw [← hzh]; exact (hymem z).symm
    have e2 : x * h * x⁻¹ ∈ EA ι ↔ ((y * z * y⁻¹ : ↥Lb) : Q) ∈ Sb ⊓ Lb := by
      rw [← hconj]; exact (hymem _).symm
    rw [e1, e2, hyL]
    simp only [Subgroup.mem_inf]
    constructor
    · intro ⟨h1, _⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hyN.1 _).1 h1, (y * z * y⁻¹).2⟩
    · intro ⟨h1, _⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hyN.1 _).2 h1, z.2⟩
  ·
    intro hx
    have hxNA : φ y ∈ NA ι := by rw [hxy, ← normalizer_EA hι]; exact hx
    have hx' : φ y⁻¹ ∈ NA ι := by rw [map_inv]; exact inv_mem hxNA
    simp only [Subgroup.mem_inf]
    refine ⟨?_, y.2⟩
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      exact conj_mem_of_mem_NA φ hS hSL hact hxNA hs
    · intro hs
      have := conj_mem_of_mem_NA φ hS hSL hact hx' hs
      have e : ((y⁻¹ : ↥Lb) : Q) * ((y : Q) * s * (y : Q)⁻¹) * ((y⁻¹ : ↥Lb) : Q)⁻¹ = s := by
        simp [mul_assoc]
      rwa [e] at this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
