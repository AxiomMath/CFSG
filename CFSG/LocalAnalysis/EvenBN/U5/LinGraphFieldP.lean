module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
public import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomesExclusions

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinGF

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.Open (IsElemAbelian)
open CFSG.ABGLocalTools (IsSylowOf)

variable {K : Type} [Field K] [Finite K]

theorem semilinear_conj_mem (γ : MulAut (projectiveSL 3 K)) {x : MulAut (projectiveSL 3 K)}
    (hx : x ∈ semilinearAutGroup 3 K) : γ * x * γ⁻¹ ∈ semilinearAutGroup 3 K := by
  obtain ⟨hR, -⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  have hN := (standard_outer_quotients (K := K) (n := 3)).2.2.2.1
  have hγ : γ ∈ standardAutGroup 3 K := by
    rw [hR]
    exact Subgroup.mem_top γ
  have := hN.conj_mem ⟨x, semilinearAutGroup_le_standardAutGroup hx⟩ (mem_subgroupOf.2 hx)
    ⟨γ, hγ⟩
  exact mem_subgroupOf.1 this

theorem swap_of_stab_unip [CharP K 2] (α : MulAut (projectiveSL 3 K))
    (hα : α ∉ semilinearAutGroup 3 K) (hU : (projUnip K).map α.toMonoidHom = projUnip K) :
    (projRad K 0).map α.toMonoidHom = projRad K 1 ∧
      (projRad K 1).map α.toMonoidHom = projRad K 0 := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hgen α
  have hε1 : ε = 1 := by
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · exfalso
      apply hα
      rw [hαeq, pow_zero, mul_one]
      exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
        (fieldAut_mem_semilinearAutGroup σ)
    · rfl
  rw [hε1, pow_one] at hαeq
  have hrad := radicals_projUnip (K := K)
  have key : ∀ W : Subgroup (projectiveSL 3 K), (W = projRad K 0 ∨ W = projRad K 1) →
      W.map α.toMonoidHom = projRad K 0 ∨ W.map α.toMonoidHom = projRad K 1 := by
    intro W hW
    obtain ⟨hle, hel, hcard⟩ := hrad.property hW
    refine hrad.eq_of_card _ ?_ ?_ ?_
    · rw [← hU]
      exact Subgroup.map_mono hle
    · exact isElemAbelian_map _ hel
    · rw [Subgroup.card_map_of_injective α.injective]
      exact hcard
  have h0 : (projRad K 0).map α.toMonoidHom ≠ projRad K 0 := fun h =>
    TwoF4.L3.not_dual_le_projRad_zero A σ fun x hx => by
      have : α x ∈ (projRad K 0).map α.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h, hαeq] at this
      exact this
  have h1 : (projRad K 1).map α.toMonoidHom ≠ projRad K 1 := fun h =>
    TwoF4.L3.not_dual_le_projRad_one A σ fun x hx => by
      have : α x ∈ (projRad K 1).map α.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h, hαeq] at this
      exact this
  exact ⟨(key _ (Or.inl rfl)).resolve_left h0, (key _ (Or.inr rfl)).resolve_right h1⟩

theorem swap_radicals [CharP K 2] (y : MulAut (projectiveSL 3 K))
    (hy : y ∉ semilinearAutGroup 3 K) {V V₁ V₂ : Subgroup (projectiveSL 3 K)}
    (hV : IsSylowOf 2 V ⊤) (hrad : Radicals V V₁ V₂ (Nat.card K))
    (hyV : V.map y.toMonoidHom = V) :
    V₁.map y.toMonoidHom = V₂ ∧ V₂.map y.toMonoidHom = V₁ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨F⟩ := exists_frame (G := projectiveSL 3 K) (A := ⊤) (V := V) Subgroup.topEquiv hV
  have hsurj : Function.Surjective F.φ := by
    intro x
    have : x ∈ F.φ.range := by
      rw [F.range_eq]
      exact Subgroup.mem_top x
    exact this
  let φe : MulAut (projectiveSL 3 K) := MulEquiv.ofBijective F.φ ⟨F.injective, hsurj⟩
  have hφe : ∀ x, φe x = F.φ x := fun x => rfl
  obtain ⟨τ', hτ'⟩ : ∃ τ' : MulAut (projectiveSL 3 K), τ' = φe⁻¹ * y * φe := ⟨_, rfl⟩
  have hyφ : ∀ x, y (F.φ x) = F.φ (τ' x) := by
    intro x
    have : φe (τ' x) = y (φe x) := by
      rw [hτ']
      simp only [MulAut.mul_apply, MulAut.apply_inv_self]
    exact this.symm
  have hτ'E : τ' ∉ semilinearAutGroup 3 K := by
    intro h
    apply hy
    have := semilinear_conj_mem φe h
    rwa [hτ', show φe * (φe⁻¹ * y * φe) * φe⁻¹ = y by group] at this
  have hτ'U : (projUnip K).map τ'.toMonoidHom = projUnip K := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h1 : F.φ (τ' u) ∈ V := by
        rw [← hyφ]
        have : y (F.φ u) ∈ V.map y.toMonoidHom := ⟨F.φ u, F.mem_V hu, rfl⟩
        rwa [hyV] at this
      obtain ⟨w, hw, hwx⟩ := F.exists_eq_of_mem_V h1
      have h2 : τ' u = w := (F.injective hwx).symm
      show τ' u ∈ projUnip K
      rw [h2]
      exact hw
    · intro hx
      have h1 : F.φ x ∈ V.map y.toMonoidHom := by
        rw [hyV]
        exact F.mem_V hx
      obtain ⟨v, hv, hvx⟩ := h1
      obtain ⟨u, hu, rfl⟩ := F.exists_eq_of_mem_V hv
      refine ⟨u, hu, ?_⟩
      have : F.φ (τ' u) = F.φ x := by rw [← hyφ]; exact hvx
      exact F.injective this
  obtain ⟨h01, h10⟩ := swap_of_stab_unip τ' hτ'E hτ'U
  have hmap : ∀ W : Subgroup (projectiveSL 3 K),
      (W.map F.φ).map y.toMonoidHom = (W.map τ'.toMonoidHom).map F.φ := by
    intro W
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨τ' w, ⟨w, hw, rfl⟩, (hyφ w).symm⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨F.φ w, ⟨w, hw, rfl⟩, hyφ w⟩
  rcases F.radicals.eq_or_eq hq hrad with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hmap, hmap, h01, h10]
    exact ⟨rfl, rfl⟩
  · rw [h1, h2, hmap, hmap, h01, h10]
    exact ⟨rfl, rfl⟩

end LinGF

end CFSG.LocalAnalysis.EvenBN.U5
