module

public import CFSG.ClassicalGroups.Alternating.I4SpPlane
public import CFSG.ClassicalGroups.Alternating.RT1SpWitt
public import CFSG.Monster.B.TwoA.Sp8.SubgeomLin
public import CFSG.ClassicalGroups.Alternating.I4SpLineElt

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem Gsp.lin_injective (g : Gsp BN) : Function.Injective g.lin := fun x y h => by
  have := congrArg (fun z => g⁻¹.app z) h
  simpa [Gsp.lin_apply, Gsp.app_inv_app] using this

theorem Gsp.finrank_map_lin (g : Gsp BN) (σ : Submodule K N) :
    finrank K ↥(σ.map g.lin) = finrank K σ :=
  LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.toLinearEquiv
    (g : LinearMap.GeneralLinearGroup K N)) σ

theorem Gsp.isotropic_map_lin (g : Gsp BN) {σ : Submodule K N}
    (hσ : ∀ x ∈ σ, ∀ y ∈ σ, BN x y = 0) :
    ∀ x ∈ σ.map g.lin, ∀ y ∈ σ.map g.lin, BN x y = 0 := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [Gsp.lin_apply, Gsp.lin_apply, Gsp.form_app, hσ x hx y hy]

theorem IsLine.map {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) (g : Gsp BN) :
    IsLine BN (ℓ.map g.lin) :=
  ⟨g.isotropic_map_lin hℓ.1, by rw [g.finrank_map_lin, hℓ.2]⟩

theorem IsPlane.map {π : Submodule K N} (hπ : IsPlane BN π) (g : Gsp BN) :
    IsPlane BN (π.map g.lin) :=
  ⟨g.isotropic_map_lin hπ.1, by rw [g.finrank_map_lin, hπ.2]⟩

variable (hBN : BN.IsAlt)

include hBN in
theorem map_planeGroup_conj (g : Gsp BN) (σ : Submodule K N) :
    (planeGroup hBN σ).map (MulAut.conj g).toMonoidHom = planeGroup hBN (σ.map g.lin) := by
  rw [planeGroup, planeGroup, MonoidHom.map_closure]
  congr 1
  ext h
  constructor
  · rintro ⟨_, ⟨a, ha, c, hc, rfl⟩, rfl⟩
    exact ⟨g.app a, ⟨a, ha, rfl⟩, g.app c, ⟨c, hc, rfl⟩, conj_lineElt hBN g a c⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨lineElt hBN a c, ⟨a, ha, c, hc, rfl⟩, conj_lineElt hBN g a c⟩

include hBN in
theorem conj_mem_planeGroup_map_iff (g h : Gsp BN) (σ : Submodule K N) :
    g * h * g⁻¹ ∈ planeGroup hBN (σ.map g.lin) ↔ h ∈ planeGroup hBN σ := by
  rw [← map_planeGroup_conj hBN g σ]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = h := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]
  · intro hh
    exact ⟨h, hh, by simp [MulAut.conj_apply]⟩

section Witt

variable [FiniteDimensional K N] (hBNnd : BN.Nondegenerate)

include hBN hBNnd in
theorem exists_gsp_map_chain (T : Finset ℕ) {F F' : ℕ → Submodule K N}
    (hF : ∀ s ∈ T, ∀ t ∈ T, s ≤ t → F s ≤ F t) (hF' : ∀ s ∈ T, ∀ t ∈ T, s ≤ t → F' s ≤ F' t)
    (hd : ∀ t ∈ T, finrank K (F t) = t) (hd' : ∀ t ∈ T, finrank K (F' t) = t)
    (hi : ∀ t ∈ T, ∀ x ∈ F t, ∀ y ∈ F t, BN x y = 0)
    (hi' : ∀ t ∈ T, ∀ x ∈ F' t, ∀ y ∈ F' t, BN x y = 0) :
    ∃ g : Gsp BN, ∀ t ∈ T, (F t).map g.lin = F' t := by
  obtain ⟨r, hr⟩ := hBN.even_finrank hBNnd
  obtain ⟨e, he, heF⟩ := CFSG.Monster.B.TwoA.Sp8.exists_isometry_map_chain hBN hBNnd
    (r := r) (by omega) T hF hF' hd hd' hi hi'
  have hiso : ∀ x y, BN (e x) (e y) = BN x y := TauCeti.BilinForm.mem_isometryGroup_iff.mp he
  exact ⟨⟨LinearMap.GeneralLinearGroup.ofLinearEquiv e,
    CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mpr hiso⟩, heF⟩

include hBN hBNnd in
theorem exists_gsp_map_eq_of_isLine {ℓ ℓ' : Submodule K N} (hℓ : IsLine BN ℓ)
    (hℓ' : IsLine BN ℓ') : ∃ g : Gsp BN, ℓ.map g.lin = ℓ' := by
  obtain ⟨g, hg⟩ := exists_gsp_map_chain hBN hBNnd {2} (F := fun _ => ℓ) (F' := fun _ => ℓ')
    (fun _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl)
    (fun t ht => by rw [Finset.mem_singleton.1 ht]; exact hℓ.2)
    (fun t ht => by rw [Finset.mem_singleton.1 ht]; exact hℓ'.2)
    (fun _ _ => hℓ.1) (fun _ _ => hℓ'.1)
  exact ⟨g, hg 2 (Finset.mem_singleton_self _)⟩

include hBN hBNnd in
theorem exists_gsp_map_eq_of_isPlane {π π' : Submodule K N} (hπ : IsPlane BN π)
    (hπ' : IsPlane BN π') : ∃ g : Gsp BN, π.map g.lin = π' := by
  obtain ⟨g, hg⟩ := exists_gsp_map_chain hBN hBNnd {3} (F := fun _ => π) (F' := fun _ => π')
    (fun _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl)
    (fun t ht => by rw [Finset.mem_singleton.1 ht]; exact hπ.2)
    (fun t ht => by rw [Finset.mem_singleton.1 ht]; exact hπ'.2)
    (fun _ _ => hπ.1) (fun _ _ => hπ'.1)
  exact ⟨g, hg 3 (Finset.mem_singleton_self _)⟩

include hBN hBNnd in
theorem exists_conj_lineElt_eq {a c a' c' : N} (hac : BN a c = 0) (hac' : BN a' c' = 0)
    (hind : LinearIndependent K ![a, c]) (hind' : LinearIndependent K ![a', c']) :
    ∃ g : Gsp BN, g * lineElt hBN a c * g⁻¹ = lineElt hBN a' c' := by
  obtain ⟨g, hga, hgc⟩ := exists_gsp_apply_eq_of_isotropic_pair hBN hBNnd hind hind' hac hac'
  exact ⟨g, by rw [conj_lineElt hBN, hga, hgc]⟩

end Witt

end CFSG.ClassicalGroups.Alternating
