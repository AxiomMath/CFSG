module

import CFSG.Sporadic.Schreier.LySylow
public import CFSG.Sporadic.Schreier.LyData

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

private theorem exists_central_involution_of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {A : Subgroup X} {S : Subgroup Y} {τ : Y} (hA : ∀ x, x ∈ A ↔ e x ∈ S)
    (hτS : τ ∈ S) (hτ2 : orderOf τ = 2) (hc : ∀ s ∈ S, s * τ = τ * s)
    (hu : ∀ s ∈ S, (∀ a ∈ S, a * s = s * a) → s = 1 ∨ s = τ) (hcomm : τ ∈ ⁅S, S⁆) :
    ∃ τ : X, τ ∈ A ∧ orderOf τ = 2 ∧ (∀ a ∈ A, a * τ = τ * a) ∧
      (∀ s ∈ A, (∀ a ∈ A, a * s = s * a) → s = 1 ∨ s = τ) ∧ τ ∈ ⁅A, A⁆ := by
  have hAmap : A = S.map e.symm.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, hA]
  refine ⟨e.symm τ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hA, MulEquiv.apply_symm_apply]
    exact hτS
  · rw [MulEquiv.orderOf_eq]
    exact hτ2
  · intro a ha
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc _ ((hA a).1 ha)
  · intro s hs hsc
    have hes : e s ∈ S := (hA s).1 hs
    rcases hu (e s) hes (fun a ha => by
        have ha' : e.symm a ∈ A := by rw [hA, MulEquiv.apply_symm_apply]; exact ha
        have := congrArg e (hsc _ ha')
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this) with h | h
    · left
      apply e.injective
      rw [h, map_one]
    · right
      apply e.injective
      rw [h, MulEquiv.apply_symm_apply]
  · rw [hAmap, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ hcomm

private theorem sylow_conj_mem {G : Type*} [Group G] [Finite G] (S T : Sylow 2 G) :
    ∃ h : G, ∀ x : G, x ∈ (T : Subgroup G) ↔ ∃ s ∈ (S : Subgroup G), h * s * h⁻¹ = x := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S T
  refine ⟨h, fun x => ?_⟩
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  simp [MulAut.smul_def]

private theorem exists_central_involution_of_sylow_model {X G : Type*} [Group X] [Group G]
    [Finite G] (e₀ : X ≃* G) {S : Subgroup G} {τ : G}
    (hS : Nat.card S = 2 ^ (Nat.card G).factorization 2) (hτS : τ ∈ S) (hτ2 : orderOf τ = 2)
    (hc : ∀ s ∈ S, s * τ = τ * s) (hu : ∀ s ∈ S, (∀ a ∈ S, a * s = s * a) → s = 1 ∨ s = τ)
    (hcomm : τ ∈ ⁅S, S⁆) {A : Subgroup X} (hA : Nat.card A = 2 ^ (Nat.card G).factorization 2) :
    ∃ τ : X, τ ∈ A ∧ orderOf τ = 2 ∧ (∀ a ∈ A, a * τ = τ * a) ∧
      (∀ s ∈ A, (∀ a ∈ A, a * s = s * a) → s = 1 ∨ s = τ) ∧ τ ∈ ⁅A, A⁆ := by
  have hcardG : Nat.card (A.map e₀.toMonoidHom) = 2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective e₀.injective, hA]
  obtain ⟨g, hg⟩ := sylow_conj_mem (Sylow.ofCard S hS) (Sylow.ofCard (A.map e₀.toMonoidHom) hcardG)
  simp only [Sylow.coe_ofCard] at hg
  have hAe : ∀ x, x ∈ A ↔ (e₀.trans (MulAut.conj g).symm) x ∈ S := by
    intro x
    have h1 : x ∈ A ↔ e₀ x ∈ A.map e₀.toMonoidHom := by
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rw [h1, hg, MulEquiv.trans_apply, MulAut.conj_symm_apply]
    constructor
    · rintro ⟨s, hs, hsx⟩
      have : g⁻¹ * e₀ x * g = s := by rw [← hsx]; group
      rw [this]
      exact hs
    · intro h
      exact ⟨_, h, by group⟩
  exact exists_central_involution_of_mulEquiv _ hAe hτS hτ2 hc hu hcomm

private theorem central_involution_of_center {G : Type*} [Group G] {S : Subgroup G} {z : S}
    (h2 : orderOf z = 2) (hz : ∀ g : S, g ∈ Subgroup.center S ↔ g = 1 ∨ g = z)
    (hcomm : z ∈ commutator S) :
    (z : G) ∈ S ∧ orderOf (z : G) = 2 ∧ (∀ s ∈ S, s * (z : G) = (z : G) * s) ∧
      (∀ s ∈ S, (∀ a ∈ S, a * s = s * a) → s = 1 ∨ s = (z : G)) ∧ (z : G) ∈ ⁅S, S⁆ := by
  refine ⟨z.2, by rw [Subgroup.orderOf_coe]; exact h2, fun s hs => ?_, fun s hs hsc => ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 ((hz z).2 (Or.inr rfl)) ⟨s, hs⟩)
  · have hmem : (⟨s, hs⟩ : S) ∈ Subgroup.center S :=
      Subgroup.mem_center_iff.2 fun h => Subtype.ext (hsc h h.2)
    rcases (hz _).1 hmem with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · have h := Subgroup.mem_map_of_mem S.subtype hcomm
    rwa [Subgroup.map_subtype_commutator] at h

theorem exists_central_involution_sylow_ly
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Ly))
    {A : Subgroup X} (hA : Nat.card ↥A = 2 ^ 8) :
    ∃ τ : X, τ ∈ A ∧ orderOf τ = 2 ∧ (∀ a ∈ A, a * τ = τ * a) ∧
      (∀ s ∈ A, (∀ a ∈ A, a * s = s * a) → s = 1 ∨ s = τ) ∧ τ ∈ ⁅A, A⁆ := by
  obtain ⟨e₀⟩ := hX
  obtain ⟨h1, h2, h3, h4, h5⟩ := central_involution_of_center (G := J) (S := lyS) (z := zS)
    orderOf_zS (fun g => by rw [center_lyS, mem_zpowers_zS]) zS_mem_commutator
  exact exists_central_involution_of_sylow_model (G := J) (by exact e₀.trans lyEquivJ)
    (by rw [card_lyS, card_J_factorization]; norm_num) h1 h2 h3 h4 h5
    (by rw [hA, card_J_factorization])

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
