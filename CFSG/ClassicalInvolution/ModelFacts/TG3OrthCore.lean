module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Gen
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem elemOn_le_centralizer_of_fix {U : Submodule F V} {h : V ≃ₗ[F] V}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ x ∈ U, h x = x) :
    elemOn Q U ≤ Subgroup.centralizer ({h} : Set (V ≃ₗ[F] V)) := by
  rw [elemOn, Subgroup.closure_le]
  rintro _ ⟨u, w, hu, hw, -, -, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h1 := eichler_conj hh u w
  rw [hfix u hu, hfix w hw] at h1
  calc eichler Q u w * h = h * eichler Q u w * h⁻¹ * h := by rw [h1]
    _ = h * eichler Q u w := by group

section Core

variable [Finite F] [FiniteDimensional F V]

theorem exists_subspaces_of_involution (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) {A W : Submodule F V} (hA : PolarNondegOn Q A)
    (h3 : 3 ≤ Module.finrank F A) (hWA : IsCompl W A) (horth : ∀ x ∈ W, ∀ a ∈ A, polar Q x a = 0)
    {g g' : V ≃ₗ[F] V} (hg2 : ∀ x, g (g x) = x)
    (hgA : ∀ x ∈ A, g x = x) (hgW : ∀ x ∈ W, g x ∈ W) (hg'A : ∀ x ∈ A, g' x = x)
    (hg' : ∀ x ∈ W, g x = -x → g' x = x) :
    ∃ S₂ S₁ : Submodule F V, elementaryGroup Q ≤ elemOn Q S₂ ⊔ elemOn Q S₁ ∧
      (∀ x ∈ S₂, g x = x) ∧ (∀ x ∈ S₁, g' x = x) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  let U₁ : Submodule F V := LinearMap.ker ((g : V →ₗ[F] V) + LinearMap.id)
  let U₂ : Submodule F V := W ⊓ LinearMap.ker ((g : V →ₗ[F] V) - LinearMap.id)
  have hU₁ : ∀ x, x ∈ U₁ ↔ g x = -x := fun x => by
    simp only [U₁, LinearMap.mem_ker, LinearMap.add_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply]
    exact add_eq_zero_iff_eq_neg
  have hU₂ : ∀ x, x ∈ U₂ ↔ x ∈ W ∧ g x = x := fun x => by
    simp only [U₂, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero]
  have hsum : ∀ x : V, ∃ w ∈ W, ∃ a ∈ A, w + a = x := fun x => by
    have hx : x ∈ W ⊔ A := by rw [hWA.sup_eq_top]; trivial
    exact Submodule.mem_sup.mp hx
  have hU₁W : ∀ x ∈ U₁, x ∈ W := by
    intro x hx
    rw [hU₁] at hx
    obtain ⟨w, hw, a, ha, rfl⟩ := hsum x
    have h1 : g (w + a) = g w + a := by rw [map_add, hgA a ha]
    rw [h1] at hx
    have h2' : g w + w = (-2 : F) • a := by
      calc g w + w = (g w + a) + w - a := by abel
        _ = -(w + a) + w - a := by rw [hx]
        _ = (-2 : F) • a := by module
    have hmemW : g w + w ∈ W := W.add_mem (hgW w hw) hw
    have hmemA : (-2 : F) • a ∈ A := A.smul_mem _ ha
    have h0 : (-2 : F) • a = 0 := by
      rw [h2'] at hmemW
      exact (Submodule.disjoint_def.mp hWA.disjoint) _ hmemW hmemA
    have ha0 : a = 0 := (smul_eq_zero.mp h0).resolve_left (by simpa using h2)
    rw [ha0, add_zero]
    exact hw
  have htop : U₁ ⊔ U₂ ⊔ A = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨w, hw, a, ha, rfl⟩ := hsum x
    have hgw := hgW w hw
    have hu₂ : (2 : F)⁻¹ • (w + g w) ∈ U₂ := by
      rw [hU₂]
      refine ⟨W.smul_mem _ (W.add_mem hw hgw), ?_⟩
      rw [map_smul, map_add, hg2 w, add_comm]
    have hu₁ : (2 : F)⁻¹ • (w - g w) ∈ U₁ := by
      rw [hU₁, map_smul, map_sub, hg2 w, ← smul_neg, neg_sub]
    have hw' : w = (2 : F)⁻¹ • (w - g w) + (2 : F)⁻¹ • (w + g w) := by
      rw [← smul_add]
      have : w - g w + (w + g w) = (2 : F) • w := by module
      rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
    have hx : w + a = (2 : F)⁻¹ • (w - g w) + (2 : F)⁻¹ • (w + g w) + a := by rw [← hw']
    rw [hx]
    refine (U₁ ⊔ U₂ ⊔ A).add_mem ((U₁ ⊔ U₂ ⊔ A).add_mem ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left hu₁)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right hu₂)
    · exact Submodule.mem_sup_right ha
  have hU₁A : ∀ x ∈ U₁, ∀ y ∈ A, polar Q x y = 0 := fun x hx y hy => horth x (hU₁W x hx) y hy
  have hU₂A : ∀ x ∈ U₂, ∀ y ∈ A, polar Q x y = 0 := fun x hx y hy =>
    horth x ((hU₂ x).mp hx).1 y hy
  have hmain := elementaryGroup_le_join_of_decomp hodd hQ (U₁ := U₁) (U₂ := U₂) hA h3 hU₁A hU₂A
    htop
  refine ⟨U₂ ⊔ A, U₁ ⊔ A, hmain, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, ((hU₂ u).mp hu).2, hgA a ha]
  · intro x hx
    obtain ⟨u, hu, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hg' u (hU₁W u hu) ((hU₁ u).mp hu), hg'A a ha]

theorem elementaryGroup_le_sup_of_involution (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) {A W : Submodule F V} (hA : PolarNondegOn Q A)
    (h3 : 3 ≤ Module.finrank F A) (hWA : IsCompl W A) (horth : ∀ x ∈ W, ∀ a ∈ A, polar Q x a = 0)
    {g g' : V ≃ₗ[F] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : ∀ x, g (g x) = x)
    (hgA : ∀ x ∈ A, g x = x) (hgW : ∀ x ∈ W, g x ∈ W) (hg'A : ∀ x ∈ A, g' x = x)
    (hg' : ∀ x ∈ W, g x = -x → g' x = x) :
    elementaryGroup Q ≤ (elementaryGroup Q ⊓ Subgroup.centralizer ({g} : Set (V ≃ₗ[F] V))) ⊔
      (elementaryGroup Q ⊓ Subgroup.centralizer ({g'} : Set (V ≃ₗ[F] V))) := by
  obtain ⟨S₂, S₁, hle, h₂, h₁⟩ := exists_subspaces_of_involution hodd hQ hA h3 hWA horth hg2 hgA
    hgW hg'A hg'
  refine hle.trans (sup_le_sup ?_ ?_)
  · exact le_inf elemOn_le_elementaryGroup (elemOn_le_centralizer_of_fix hgO h₂)
  · exact le_inf elemOn_le_elementaryGroup (elemOn_le_centralizer_of_fix hg'O h₁)

end Core

end CFSG.ClassicalInvolution.ModelFacts.TG3
