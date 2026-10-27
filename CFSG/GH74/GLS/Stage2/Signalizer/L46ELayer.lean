module

public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Subgroup CFSG
open scoped commutatorElement

section CompJoin

variable {A : Type} [Group A]

@[expose] def l46e_compJoin (K : Subgroup A) : Subgroup A :=
  sSup {J : Subgroup A | IsComponent J ∧ J ≤ K}

theorem l46e_le_compJoin {K J : Subgroup A} (hJ : IsComponent J) (h : J ≤ K) :
    J ≤ l46e_compJoin K :=
  le_sSup ⟨hJ, h⟩

theorem l46e_conj_mem_compJoin {K : Subgroup A} {g : A} (hg : g ∈ normalizer (K : Set A)) {m : A}
    (hm : m ∈ l46e_compJoin K) : g * m * g⁻¹ ∈ l46e_compJoin K := by
  have hle : l46e_compJoin K ≤ (l46e_compJoin K).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine l46e_le_compJoin (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ.1) ?_
    rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg j).mp (hJ.2 hj)
  exact hle hm

theorem l46e_normalizer_le_normalizer_compJoin (K : Subgroup A) :
    normalizer (K : Set A) ≤ normalizer (l46e_compJoin K : Set A) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun m => ⟨l46e_conj_mem_compJoin hg, fun h => ?_⟩
  have h' := l46e_conj_mem_compJoin (inv_mem hg) h
  have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
  rwa [e] at h'

end CompJoin

section Layer

variable {A : Type} [Group A] [Finite A]

theorem l46e_component_le_or_le_centralizer {J : Subgroup A} (hJ : IsComponent J)
    (X : Subgroup A) : J ≤ ⁅layer A, X⁆ ∨ J ≤ centralizer (X : Set A) := by
  have hEn : (layer A).Normal :=
    Subgroup.normal_of_characteristic _ (h := CFSG.LocalCores.layer_characteristic)
  have hMsub : (⁅layer A, X⁆).IsSubnormal :=
    Subgroup.IsSubnormal.step _ (layer A) (Subgroup.commutator_le_left _ _) hEn.isSubnormal
      (Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left _ _))
  rcases CFSG.LocalCores.component_subnormal_subgroup hJ hMsub with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have hJX : ⁅J, X⁆ ≤ ⁅layer A, X⁆ :=
      Subgroup.commutator_mono (CFSG.LocalCores.component_le_layer hJ) le_rfl
    have h1 : ⁅⁅J, X⁆, J⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅J, X⁆, J⁆ ≤ ⁅⁅layer A, X⁆, J⁆ := Subgroup.commutator_mono hJX le_rfl
        _ = ⁅J, ⁅layer A, X⁆⁆ := Subgroup.commutator_comm _ _
        _ = ⊥ := h
        _ ≤ ⊥ := le_rfl
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.perfect_double_commutator hJ.1.1 h1)

theorem l46e_comm_layer_le_compJoin (X : Subgroup A) :
    ⁅layer A, X⁆ ≤ l46e_compJoin ⁅layer A, X⁆ := by
  set K : Subgroup A := ⁅layer A, X⁆ with hK
  set M : Subgroup A := l46e_compJoin K with hM
  have hLN : layer A ≤ normalizer (M : Set A) :=
    (Subgroup.normalizer_commutator_ge_left (layer A) X).trans
      (l46e_normalizer_le_normalizer_compJoin K)
  have hXN : X ≤ normalizer (M : Set A) :=
    (Subgroup.normalizer_commutator_ge_right (layer A) X).trans
      (l46e_normalizer_le_normalizer_compJoin K)
  let S : Subgroup A :=
    { carrier := {l | l ∈ normalizer (M : Set A) ∧ ∀ x ∈ X, ⁅l, x⁆ ∈ M}
      mul_mem' := by
        rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
        refine ⟨mul_mem ha hb, fun x hx => ?_⟩
        have h1 : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp ha _).mp (hbx x hx)) (hax x hx)
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, hax⟩
        refine ⟨inv_mem ha, fun x hx => ?_⟩
        have h1 : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact (Subgroup.mem_normalizer_iff.mp (inv_mem ha) _).mp (inv_mem (hax x hx)) }
  have hS : layer A ≤ S := by
    refine sSup_le fun J hJ l hl => ?_
    refine ⟨hLN (CFSG.LocalCores.component_le_layer hJ hl), fun x hx => ?_⟩
    rcases l46e_component_le_or_le_centralizer hJ X with h | h
    · have hlM : l ∈ M := l46e_le_compJoin hJ h hl
      have h1 : ⁅l, x⁆ = l * (x * l⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [h1]
      exact mul_mem hlM ((Subgroup.mem_normalizer_iff.mp (hXN hx) _).mp (inv_mem hlM))
    · have hcomm : x * l = l * x := Subgroup.mem_centralizer_iff.mp (h hl) x hx
      have h1 : ⁅l, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
      rw [h1]
      exact one_mem _
  exact Subgroup.commutator_le.mpr fun l hl x hx => (hS hl).2 x hx

theorem l46e_component_comm_eq_bot {D : Subgroup A} [D.Normal] (hD : Group.IsSolvable ↥D)
    {J E : Subgroup A} (hJ : IsComponent J) (h : ⁅J, E⁆ ≤ D) : ⁅J, E⁆ = ⊥ := by
  have hJD : ⁅J, D⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hD
      (inferInstance : D.Normal).isSubnormal).1 J hJ
  refine CFSG.LocalCores.perfect_double_commutator hJ.1.1 (le_bot_iff.mp ?_)
  calc ⁅⁅J, E⁆, J⁆ ≤ ⁅D, J⁆ := Subgroup.commutator_mono h le_rfl
    _ = ⁅J, D⁆ := Subgroup.commutator_comm _ _
    _ = ⊥ := hJD
    _ ≤ ⊥ := le_rfl

theorem l46e_centralizes_commutator_layer {D : Subgroup A} [D.Normal] (hD : Group.IsSolvable ↥D)
    (X E : Subgroup A) (hcomm : ∀ e ∈ E, ∀ k ∈ ⁅layer A, X⁆, ⁅k, e⁆ ∈ D) :
    E ≤ centralizer ((⁅layer A, X⁆ : Subgroup A) : Set A) := by
  rw [Subgroup.le_centralizer_iff]
  refine (l46e_comm_layer_le_compJoin X).trans (sSup_le fun J hJ => ?_)
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (l46e_component_comm_eq_bot hD hJ.1 ?_)
  exact Subgroup.commutator_le.mpr fun j hj e he => hcomm e he j (hJ.2 hj)

theorem centralizes_commutator_layer {D : Subgroup A} [D.Normal] (hD : Group.IsSolvable ↥D)
    (X E : Subgroup A) (_hEX : E ≤ centralizer (X : Set A))
    (hcomm : ∀ e ∈ E, ∀ k ∈ ⁅layer A, X⁆, ⁅k, e⁆ ∈ D) :
    E ≤ centralizer ((⁅layer A, X⁆ : Subgroup A) : Set A) :=
  l46e_centralizes_commutator_layer hD X E hcomm

end Layer

end CFSG.GH74.GLS.Stage2.Signalizer.L46E
