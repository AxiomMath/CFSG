module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Diag.Step

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {H : Type} [Group H]

theorem le_of_perfect_diag {X₁ X₂ D C : Subgroup H} (hX₁ : ⁅X₁, X₁⁆ = X₁)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hD : ∀ x ∈ X₁, ∃ y ∈ X₂, x * y ∈ D)
    (hDC : D ≤ C) (hconj : ∀ g ∈ X₁, D.map (MulAut.conj g).toMonoidHom ≤ C) : X₁ ≤ C := by
  refine le_trans (le_of_eq hX₁.symm) (commutator_le.2 fun a ha b hb => ?_)
  obtain ⟨y, hy, hyD⟩ := hD a⁻¹ (X₁.inv_mem ha)
  have h1 : (a⁻¹ * y)⁻¹ ∈ C := C.inv_mem (hDC hyD)
  have h2 : b * (a⁻¹ * y) * b⁻¹ ∈ C := hconj b hb ⟨_, hyD, by simp [MulAut.conj_apply]⟩
  have hu : (a * b * a⁻¹) * y = y * (a * b * a⁻¹) :=
    hcomm _ (X₁.mul_mem (X₁.mul_mem ha hb) (X₁.inv_mem ha)) y hy
  have e : (a⁻¹ * y)⁻¹ * (b * (a⁻¹ * y) * b⁻¹) = ⁅a, b⁆ := by
    simp only [commutatorElement_def]
    calc (a⁻¹ * y)⁻¹ * (b * (a⁻¹ * y) * b⁻¹) = y⁻¹ * ((a * b * a⁻¹) * y) * b⁻¹ := by group
      _ = y⁻¹ * (y * (a * b * a⁻¹)) * b⁻¹ := by rw [hu]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [← e]
  exact C.mul_mem h1 h2

section Link

variable [Finite H] {T W W' M K : Subgroup H} {s : H}

omit [Finite H] in
theorem DiagData.s_mem_normalizer (h : DiagData T W W' M K s) :
    s ∈ normalizer ((W' ⊔ T : Subgroup H) : Set H) := by
  have hW' : s ∈ normalizer (W' : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => h.conj_mem s h.s_mem x hx, fun hx => ?_⟩
    have := h.conj_mem s⁻¹ (W.inv_mem h.s_mem) _ hx
    simpa [mul_assoc] using this
  exact mem_normalizer_sup hW' (h.W_le_normalizer h.s_mem)

theorem DiagData.isComp_conj_diagX (h : DiagData T W W' M K s) :
    IsCompIn ((diagX h).map (MulAut.conj s).toMonoidHom)
      (centralizer ((W' ⊔ T : Subgroup H) : Set H)) :=
  isCompIn_map_conj_of_mem_normalizer h.isComp_diagX
    (mem_normalizer_centralizer_of_mem_normalizer h.s_mem_normalizer)

theorem DiagData.commute_diagX (h : DiagData T W W' M K s) :
    ∀ a ∈ diagX h, ∀ b ∈ (diagX h).map (MulAut.conj s).toMonoidHom, a * b = b * a :=
  h.isComp_diagX.commute_of_ne h.isComp_conj_diagX h.diagX_ne.symm

theorem DiagData.layer_eq (h : DiagData T W W' M K s) :
    diagX h ⊔ (diagX h).map (MulAut.conj s).toMonoidHom =
      conjClosure K (layerIn (centralizer ((W' ⊔ T : Subgroup H) : Set H))) := by
  set X := diagX h with hXdef
  set Y' := centralizer ((W' ⊔ T : Subgroup H) : Set H) with hY'
  have hX : IsCompIn X Y' := h.isComp_diagX
  have hXs : IsCompIn (X.map (MulAut.conj s).toMonoidHom) Y' := h.isComp_conj_diagX
  have hlayer : layerIn Y' ≤ normalizer ((X ⊔ X.map (MulAut.conj s).toMonoidHom : Subgroup H) :
      Set H) := by
    rw [layerIn_le_iff]
    intro Z hZ
    by_cases hZX : Z = X
    · rw [hZX]
      exact le_trans le_sup_left Subgroup.le_normalizer
    by_cases hZXs : Z = X.map (MulAut.conj s).toMonoidHom
    · rw [hZXs]
      exact le_trans le_sup_right Subgroup.le_normalizer
    intro z hz
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_sup.2 ⟨?_, ?_⟩)
    · exact mem_centralizer_iff.2 fun g hg => (hZ.commute_of_ne hX hZX z hz g hg).symm
    · exact mem_centralizer_iff.2 fun g hg => (hZ.commute_of_ne hXs hZXs z hz g hg).symm
  refine le_antisymm ?_ (conjClosure_le_of_le_normalizer h.K_le_sup_X hlayer)
  have hconjC : ∀ g ∈ layerIn Y',
      K.map (MulAut.conj g).toMonoidHom ≤ conjClosure K (layerIn Y') := fun g hg =>
    map_conj_le_conjClosure hg
  have hKC : K ≤ conjClosure K (layerIn Y') := le_conjClosure K _
  refine sup_le ?_ ?_
  · refine le_of_perfect_diag h.perfect_diagX h.commute_diagX
      (fun x hx => ⟨s * x * s⁻¹, ⟨x, hx, by simp [MulAut.conj_apply]⟩, h.mem_K_of_mem_X hx⟩)
      hKC (fun g hg => hconjC g (le_layerIn_of_isCompIn hX hg))
  · have hperf : ⁅X.map (MulAut.conj s).toMonoidHom, X.map (MulAut.conj s).toMonoidHom⁆ =
        X.map (MulAut.conj s).toMonoidHom := by
      rw [← Subgroup.map_commutator, h.perfect_diagX]
    refine le_of_perfect_diag hperf (fun a ha b hb => (h.commute_diagX b hb a ha).symm)
      (fun y hy => ?_) hKC (fun g hg => hconjC g (le_layerIn_of_isCompIn hXs hg))
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, hx, ?_⟩
    have hmem := h.mem_K_of_mem_X hx
    have hc : (MulAut.conj s).toMonoidHom x * x = x * (MulAut.conj s).toMonoidHom x :=
      (h.commute_diagX x hx _ ⟨x, hx, rfl⟩).symm
    rw [hc]
    exact hmem

theorem diag_step (h : DiagData T W W' M K s) :
    ∃ X : Subgroup H, IsCompIn X (centralizer ((W' ⊔ T : Subgroup H) : Set H)) ∧
      X ≠ X.map (MulAut.conj s).toMonoidHom ∧
      K ≤ X ⊔ X.map (MulAut.conj s).toMonoidHom ∧
      X ⊔ X.map (MulAut.conj s).toMonoidHom =
        conjClosure K (layerIn (centralizer ((W' ⊔ T : Subgroup H) : Set H))) ∧
      Nonempty ((↥X ⧸ center ↥X) ≃* (↥K ⧸ center ↥K)) ∧ X ≤ conjClosure M W' :=
  ⟨diagX h, h.isComp_diagX, h.diagX_ne.symm, h.K_le_sup_X, h.layer_eq, h.cqEquiv_diagX,
    h.diagX_le_conjClosure⟩

end Link

end CFSG.EvenSporadicStandard.Induction.Junction
