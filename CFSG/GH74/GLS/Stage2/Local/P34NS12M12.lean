module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34NS

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.ComponentClassification.M12Cover
open scoped commutatorElement

@[expose] def pE : Equiv.Perm (Fin 12) :=
  List.formPerm [2, 7] * List.formPerm [4, 9] * List.formPerm [5, 8] * List.formPerm [6, 10]

@[expose] def qE : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 2, 11] * List.formPerm [1, 3, 9] * List.formPerm [4, 6, 10] * List.formPerm [5, 8, 7]

@[expose] def cgens2 : List (Equiv.Perm (Fin 12)) := m12CentWords2.map (evalCodes [m12gA, m12gB])

theorem pE_eq : evalCodes cgens2 [-2, -2, 1, 1] = pE := by
  unfold cgens2
  decide +kernel

theorem qE_eq : evalCodes cgens2 [-2, -2, 1] = qE := by
  unfold cgens2
  decide +kernel

theorem pE_ne_one : pE ≠ 1 := by decide +kernel

theorem pE_comm : evalCodes [pE, qE] [-1, -2, -1, -2, -1, 2] * evalCodes [pE, qE] [-1, -2, -1, -2, -1, 2, -1] *
    (evalCodes [pE, qE] [-1, -2, -1, -2, -1, 2])⁻¹ * (evalCodes [pE, qE] [-1, -2, -1, -2, -1, 2, -1])⁻¹ = pE := by
  unfold pE qE
  decide +kernel

theorem qE_comm : evalCodes [pE, qE] [-2, 1, 2, 1, -2, 1, 2, 1, 2] * evalCodes [pE, qE] [-1, -2, -1, 2, -1, -2, -1, 2, -1] *
    (evalCodes [pE, qE] [-2, 1, 2, 1, -2, 1, 2, 1, 2])⁻¹ * (evalCodes [pE, qE] [-1, -2, -1, 2, -1, -2, -1, 2, -1])⁻¹ = qE := by
  unfold pE qE
  decide +kernel

@[expose] def A5E : Subgroup (Equiv.Perm (Fin 12)) := Subgroup.closure {pE, qE}

theorem pE_mem_A5E : pE ∈ A5E := Subgroup.subset_closure (by simp)

theorem qE_mem_A5E : qE ∈ A5E := Subgroup.subset_closure (by simp)

theorem A5E_perfect : ⁅A5E, A5E⁆ = A5E := by
  apply le_antisymm (Subgroup.commutator_le_self A5E)
  have hS : ∀ g ∈ [pE, qE], g ∈ A5E := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact pE_mem_A5E
    · exact qE_mem_A5E
  have key : ∀ (w₁ w₂ : List ℤ), ⁅evalCodes [pE, qE] w₁, evalCodes [pE, qE] w₂⁆ ∈ ⁅A5E, A5E⁆ :=
    fun w₁ w₂ => Subgroup.commutator_mem_commutator (evalCodes_mem A5E hS w₁) (evalCodes_mem A5E hS w₂)
  show Subgroup.closure {pE, qE} ≤ ⁅A5E, A5E⁆
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · have := key [-1, -2, -1, -2, -1, 2] [-1, -2, -1, -2, -1, 2, -1]
    rwa [commutatorElement_def, pE_comm] at this
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    have := key [-2, 1, 2, 1, -2, 1, 2, 1, 2] [-1, -2, -1, 2, -1, -2, -1, 2, -1]
    rwa [commutatorElement_def, qE_comm] at this

theorem A5E_le_cent :
    A5E ≤ centralizerIn NativeSporadic.M12 m12Rep2 := by
  have hgs : ∀ g ∈ cgens2, g ∈ m12CentQ2.originalSubgroup := fun g hg => by
    rw [m12CentQ2, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  have hp : pE ∈ centralizerIn NativeSporadic.M12 m12Rep2 := by
    rw [centralizerIn_m12Rep2, ← pE_eq]
    exact evalCodes_mem _ hgs _
  have hq : qE ∈ centralizerIn NativeSporadic.M12 m12Rep2 := by
    rw [centralizerIn_m12Rep2, ← qE_eq]
    exact evalCodes_mem _ hgs _
  show Subgroup.closure {pE, qE} ≤ _
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact hp
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hq

@[expose] def M12Facts : Prop :=
  Nat.card NativeSporadic.M12 = 95040 ∧
  ∀ a b : NativeSporadic.M12, orderOf a = 2 → orderOf b = 2 →
    64 ∣ Nat.card ↥(centralizer ({a} : Set NativeSporadic.M12)) → ¬ IsConj a b →
      ∃ P : Subgroup NativeSporadic.M12, P ≤ centralizer ({b} : Set NativeSporadic.M12) ∧
        ⁅P, P⁆ = P ∧ P ≠ ⊥

theorem m12Facts :
    M12Facts := by
  refine ⟨m12_card, ?_⟩
  intro a b ha hb h64 hnc
  have hr1m : m12Rep1 ∈ NativeSporadic.M12 := (m12_reps_mem m12Rep1 (by simp)).1
  have hr2m : m12Rep2 ∈ NativeSporadic.M12 := (m12_reps_mem m12Rep2 (by simp)).1
  let r1 : NativeSporadic.M12 := ⟨m12Rep1, hr1m⟩
  let r2 : NativeSporadic.M12 := ⟨m12Rep2, hr2m⟩
  have hcls : ∀ u : NativeSporadic.M12, orderOf u = 2 →
      (∃ c : NativeSporadic.M12, c * r1 * c⁻¹ = u) ∨ (∃ c : NativeSporadic.M12, c * r2 * c⁻¹ = u) := by
    intro u hu
    have hu' : orderOf (u : Equiv.Perm (Fin 12)) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    obtain ⟨r, hr, c, hc, hcu⟩ :=
      (m12_involution_cover).1 (u : Equiv.Perm (Fin 12)) (by simp) hu'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inl ⟨⟨c, hc⟩, Subtype.ext hcu.symm⟩
    · exact Or.inr ⟨⟨c, hc⟩, Subtype.ext hcu.symm⟩
  have hcard : ∀ c r : NativeSporadic.M12,
      Nat.card ↥(centralizer ({c * r * c⁻¹} : Set NativeSporadic.M12)) =
        Nat.card ↥(centralizer ({r} : Set NativeSporadic.M12)) := by
    intro c r
    have := Nat.card_congr (centralizerEquiv (MulAut.conj c) r).toEquiv
    simpa [MulAut.conj_apply] using this.symm
  have hc2 : Nat.card ↥(centralizer ({r2} : Set NativeSporadic.M12)) = 240 := by
    rw [card_centralizer_eq_centralizerIn]
    exact card_centralizerIn_m12Rep2
  rcases hcls a ha with ⟨c, hc⟩ | ⟨c, hc⟩
  · rcases hcls b hb with ⟨c', hc'⟩ | ⟨c', hc'⟩
    · exact absurd (isConj_iff.2 ⟨c' * c⁻¹, by rw [← hc, ← hc']; group⟩) hnc
    ·
      have hA5M : A5E ≤ NativeSporadic.M12 := A5E_le_cent.trans inf_le_left
      set P₀ : Subgroup NativeSporadic.M12 := A5E.subgroupOf NativeSporadic.M12 with hP₀
      have hP₀c : P₀ ≤ centralizer ({r2} : Set NativeSporadic.M12) := by
        intro g hg
        have h1 := A5E_le_cent (Subgroup.mem_subgroupOf.1 hg)
        rw [mem_centralizerIn] at h1
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext h1.2
      have hP₀p : ⁅P₀, P₀⁆ = P₀ := by
        apply Subgroup.map_injective NativeSporadic.M12.subtype_injective
        rw [Subgroup.map_commutator, hP₀, Subgroup.map_subgroupOf_eq_of_le hA5M, A5E_perfect]
      have hP₀n : P₀ ≠ ⊥ := by
        intro h
        have hmem : (⟨pE, hA5M pE_mem_A5E⟩ : NativeSporadic.M12) ∈ P₀ :=
          Subgroup.mem_subgroupOf.2 pE_mem_A5E
        rw [h, Subgroup.mem_bot] at hmem
        exact pE_ne_one (congrArg Subtype.val hmem)
      refine ⟨P₀.map (MulAut.conj c').toMonoidHom, ?_, ?_, ?_⟩
      · rintro _ ⟨g, hg, rfl⟩
        have hg' := Subgroup.mem_centralizer_singleton_iff.1 (hP₀c hg)
        rw [Subgroup.mem_centralizer_singleton_iff, ← hc']
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc c' * g * c'⁻¹ * (c' * r2 * c'⁻¹) = c' * (g * r2) * c'⁻¹ := by group
          _ = c' * (r2 * g) * c'⁻¹ := by rw [hg']
          _ = c' * r2 * c'⁻¹ * (c' * g * c'⁻¹) := by group
      · rw [← Subgroup.map_commutator, hP₀p]
      · intro h
        apply hP₀n
        exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c').injective).1 h
  · exfalso
    rw [← hc, hcard, hc2] at h64
    norm_num at h64

end CFSG.GH74.GLS.Stage2.Local.P34NS
