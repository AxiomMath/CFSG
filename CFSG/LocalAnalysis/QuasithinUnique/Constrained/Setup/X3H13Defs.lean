module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer

variable {k : Type*} [Field k]

section Simple

variable {V' : Type*} [AddCommGroup V'] [Module k V'] {X : Type*} [Group X]

@[expose] def IsLSimple (σ : X →* (V' ≃ₗ[k] V')) (L : Subgroup X) (U : Submodule k V') : Prop :=
  Offender.IsInvariant σ L U ∧ U ≠ ⊥ ∧
    ∀ W : Submodule k V', Offender.IsInvariant σ L W → W ≤ U → W = ⊥ ∨ W = U

@[expose] def IsNontrivialLSimple (σ : X →* (V' ≃ₗ[k] V')) (L : Subgroup X)
    (U : Submodule k V') : Prop :=
  IsLSimple σ L U ∧ ¬ U ≤ fixSub σ L

theorem isInvariant_inf {σ : X →* (V' ≃ₗ[k] V')} {L : Subgroup X} {U W : Submodule k V'}
    (hU : Offender.IsInvariant σ L U) (hW : Offender.IsInvariant σ L W) :
    Offender.IsInvariant σ L (U ⊓ W) :=
  fun l hl u hu => ⟨hU l hl u hu.1, hW l hl u hu.2⟩

theorem isInvariant_sup {σ : X →* (V' ≃ₗ[k] V')} {L : Subgroup X} {U W : Submodule k V'}
    (hU : Offender.IsInvariant σ L U) (hW : Offender.IsInvariant σ L W) :
    Offender.IsInvariant σ L (U ⊔ W) := by
  intro l hl u hu
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add]
  exact Submodule.add_mem_sup (hU l hl x hx) (hW l hl y hy)

theorem isInvariant_finset_sup {σ : X →* (V' ≃ₗ[k] V')} {L : Subgroup X}
    (s : Finset (Submodule k V')) (h : ∀ U ∈ s, Offender.IsInvariant σ L U) :
    Offender.IsInvariant σ L (s.sup id) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro l hl u hu
    simp only [Finset.sup_empty, Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  | insert U s hU ih =>
    rw [Finset.sup_insert]
    exact isInvariant_sup (h U (Finset.mem_insert_self U s))
      (ih fun V hV => h V (Finset.mem_insert_of_mem hV))

theorem exists_supIndep_subset {σ : X →* (V' ≃ₗ[k] V')} {L : Subgroup X}
    (𝒰 : Finset (Submodule k V')) (h : ∀ U ∈ 𝒰, IsLSimple σ L U) :
    ∃ s ⊆ 𝒰, s.SupIndep id ∧ s.sup id = 𝒰.sup id := by
  classical
  induction 𝒰 using Finset.induction_on with
  | empty => exact ⟨∅, subset_rfl, Finset.supIndep_empty _, rfl⟩
  | insert U 𝒰 hU ih =>
    obtain ⟨s, hs, hind, hsup⟩ := ih fun V hV => h V (Finset.mem_insert_of_mem hV)
    have hUs : IsLSimple σ L U := h U (Finset.mem_insert_self U 𝒰)
    by_cases hle : U ≤ s.sup id
    · refine ⟨s, hs.trans (Finset.subset_insert U 𝒰), hind, ?_⟩
      rw [Finset.sup_insert, ← hsup]
      exact (sup_eq_right.2 (by simpa using hle)).symm
    · have hinv : Offender.IsInvariant σ L (U ⊓ s.sup id) :=
        isInvariant_inf hUs.1 (isInvariant_finset_sup s fun W hW => (h W (Finset.mem_insert_of_mem
          (hs hW))).1)
      rcases hUs.2.2 _ hinv inf_le_left with hbot | hU'
      · refine ⟨insert U s, Finset.insert_subset_insert U hs, ?_, ?_⟩
        · refine hind.insert ?_
          rw [disjoint_iff]
          simpa using hbot
        · rw [Finset.sup_insert, Finset.sup_insert, hsup]
      · exfalso
        exact hle (by rw [← hU']; exact inf_le_right)

end Simple

section Action

variable {V : Type*} [AddCommGroup V] [Module k V] {N : Type*} [Group N]
  (ρ : N →* (V ≃ₗ[k] V)) (L : Subgroup N) [L.Normal]

theorem fixSub_invariant : ∀ x, ∀ z ∈ fixSub ρ L, ρ x z ∈ fixSub ρ L := fun x z hz =>
  (mem_fixSub_map_iff ρ (Subgroup.normalizer_eq_top (H := L) ▸ Subgroup.mem_top x) z).2 hz

@[expose] noncomputable def cvAct : N →* ((V ⧸ fixSub ρ L) ≃ₗ[k] (V ⧸ fixSub ρ L)) :=
  quotHom ρ (fixSub ρ L) (fixSub_invariant ρ L)

theorem cvAct_mkQ (x : N) (v : V) : cvAct ρ L x ((fixSub ρ L).mkQ v) = (fixSub ρ L).mkQ (ρ x v) :=
  quotHom_mkQ ρ (fixSub ρ L) (fixSub_invariant ρ L) x v

end Action

end CFSG.QuasithinUnique.Setup.X3
