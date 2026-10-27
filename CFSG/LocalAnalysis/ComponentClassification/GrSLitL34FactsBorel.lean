module

public import Certificates.Certificate22200
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def T0 : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure (wordSet wT₀)

@[expose] def B0 : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure (wordSet wB₀)

@[expose] def P1 : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure (wordSet wP₁)

@[expose] def P2 : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure (wordSet wP₂)

theorem parabolicParts : ParabolicParts :=
  Certificates.certificate22200


theorem enumerates_T0 : Enumerates T0 (enumBFS 42 (wordTabs wT₀) 64).tabs.toList :=
  enumerates_wordClosure parabolicParts.okT

theorem enumerates_B0 : Enumerates B0 (enumBFS 42 (wordTabs wB₀) 192).tabs.toList :=
  enumerates_wordClosure parabolicParts.okB

theorem enumerates_P1 : Enumerates P1 (enumBFS 42 (wordTabs wP₁) 960).tabs.toList :=
  enumerates_wordClosure parabolicParts.ok₁

theorem enumerates_P2 : Enumerates P2 (enumBFS 42 (wordTabs wP₂) 960).tabs.toList :=
  enumerates_wordClosure parabolicParts.ok₂

theorem card_T0 : Nat.card T0 = 64 := by
  rw [enumerates_T0.card, Array.length_toList, parabolicParts.sizeT]

theorem card_P1 : Nat.card P1 = 960 := by
  rw [enumerates_P1.card, Array.length_toList, parabolicParts.size₁]

theorem card_P2 : Nat.card P2 = 960 := by
  rw [enumerates_P2.card, Array.length_toList, parabolicParts.size₂]

theorem T0_le_S : T0 ≤ S := closure_wordSet_le _

theorem B0_le_S : B0 ≤ S := closure_wordSet_le _

theorem B0_le_P1_P2 : B0 ≤ P1 ∧ B0 ≤ P2 := by
  constructor <;>
  · rw [B0, Subgroup.closure_le]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_wordSet_iff.1 hg
    have hj' : j < (wordTabs wB₀).size := by rw [size_wordTabs]; exact hj
    have hrep := tabRep_wordTabs wB₀ hj
    rw [← getElem!_pos wB₀ j hj] at hrep
    first
    | exact mem_of_found_enum enumerates_P1 hrep (parabolicParts.inP j hj').1
    | exact mem_of_found_enum enumerates_P2 hrep (parabolicParts.inP j hj').2

theorem B0_le_normalizer : B0 ≤ Subgroup.normalizer (T0 : Set (Equiv.Perm (Fin 42))) := by
  rw [B0, Subgroup.closure_le]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := mem_wordSet_iff.1 ha
  have hj' : j < (wordTabs wB₀).size := by rw [size_wordTabs]; exact hj
  have hrep := tabRep_wordTabs wB₀ hj
  rw [← getElem!_pos wB₀ j hj] at hrep
  have key : ∀ s ∈ wordSet wT₀, wordPerm wB₀[j]! * s * (wordPerm wB₀[j]!)⁻¹ ∈ T0 ∧
      (wordPerm wB₀[j]!)⁻¹ * s * wordPerm wB₀[j]! ∈ T0 := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := mem_wordSet_iff.1 hs
    have hi' : i < (wordTabs wT₀).size := by rw [size_wordTabs]; exact hi
    have hsrep := tabRep_wordTabs wT₀ hi
    rw [← getElem!_pos wT₀ i hi] at hsrep
    exact conj_mem_of_normalOK enumerates_T0 parabolicParts.normal hj' hi' hrep hsrep
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_closure fun s hs => (key s hs).1
  · intro hh
    have := conj_mem_closure (a := (wordPerm wB₀[j]!)⁻¹)
      (fun s hs => by rw [inv_inv]; exact (key s hs).2) hh
    rwa [show (wordPerm wB₀[j]!)⁻¹ * (wordPerm wB₀[j]! * h * (wordPerm wB₀[j]!)⁻¹) *
      (wordPerm wB₀[j]!)⁻¹⁻¹ = h by group] at this

theorem exists_rep {g : Equiv.Perm (Fin 42)} (hg : g ∈ S) :
    ∃ k < wReps.length, (wordPerm (wReps.getD k []))⁻¹ * g ∈ B0 := by
  obtain ⟨i, hi, hrep⟩ := enumerates_S.exists_pos hg
  obtain ⟨k, hk, hf⟩ := parabolicParts.cosets i hi
  have hk' : k < wReps.length := by rwa [size_wordTabs] at hk
  have hy := tabRep_wordTabs wReps hk'
  have hyi := invsOK_spec parabolicParts.invs hk hy
  refine ⟨k, hk', ?_⟩
  rw [List.getD_eq_getElem _ _ hk']
  exact mem_of_found_enum enumerates_B0 (hyi.comp hrep) hf

theorem rep_cases {k : ℕ} (hk : k < wReps.length) :
    wordPerm (wReps.getD k []) ∈ P1 ∨ wordPerm (wReps.getD k []) ∈ P2 ∨
      Subgroup.closure (wordSet (wB₀ ++ [wReps.getD k []])) = S :=
  parabolicParts.reps k hk

theorem eq_S_of_borel_le {X : Subgroup (Equiv.Perm (Fin 42))}
    (hXS : X ≤ S) (hB : B0 ≤ X) (h9 : 9 ∣ Nat.card X) : X = S := by
  by_contra hne
  have key : ∀ g ∈ X, g ∈ P1 ∨ g ∈ P2 := by
    intro g hg
    obtain ⟨k, hk, hb⟩ := exists_rep (hXS hg)
    have hyX : wordPerm (wReps.getD k []) ∈ X := by
      have := X.mul_mem hg (X.inv_mem (hB hb))
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    have hg' : g = wordPerm (wReps.getD k []) * ((wordPerm (wReps.getD k []))⁻¹ * g) := by
      group
    rcases rep_cases hk with h | h | h
    · left
      rw [hg']
      exact P1.mul_mem h (B0_le_P1_P2.1 hb)
    · right
      rw [hg']
      exact P2.mul_mem h (B0_le_P1_P2.2 hb)
    · exfalso
      apply hne
      refine le_antisymm hXS ?_
      rw [← h, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rcases List.mem_append.1 hw with hw | hw
      · exact hB (Subgroup.subset_closure ⟨w, hw, rfl⟩)
      · rw [List.mem_singleton.1 hw]
        exact hyX
  have hsub : (X : Set (Equiv.Perm (Fin 42))) ⊆ (P1 : Set _) ∪ P2 := fun g hg => key g hg
  rcases SubgroupClass.subset_union.1 hsub with h | h
  · have hd := Subgroup.card_dvd_of_le h
    rw [card_P1] at hd
    exact absurd (h9.trans hd) (by norm_num)
  · have hd := Subgroup.card_dvd_of_le h
    rw [card_P2] at hd
    exact absurd (h9.trans hd) (by norm_num)

end CFSG.ComponentClassification.GrSLit.L34Facts
