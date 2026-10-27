module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.K54Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open CFSG.ComponentClassification CFSG.ComponentClassification.SemisimpleComponentStructure
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z : G}

abbrev compG (z : G) (i : ComponentIndex ↥(centZ z)) : Subgroup G := i.val.map (centZ z).subtype

def normAll (z t : G) : Subgroup G :=
  centPair z t ⊓ ⨅ i : ComponentIndex ↥(centZ z), normalizer ((compG z i : Subgroup G) : Set G)

theorem mem_normAll {k : G} : k ∈ normAll z t ↔ k ∈ centPair z t ∧
    ∀ i : ComponentIndex ↥(centZ z), ∀ n ∈ compG z i, k * n * k⁻¹ ∈ compG z i := by
  unfold normAll
  rw [mem_inf, mem_iInf]
  refine and_congr_right fun _ => forall_congr' fun i => ⟨fun h n hn => ?_, fun h => ?_⟩
  · exact (mem_normalizer_iff.1 h n).1 hn
  · exact mem_normalizer_fintype h

theorem normAll_conj {k n : G} (hk : k ∈ centPair z t) (hn : n ∈ normAll z t) :
    k * n * k⁻¹ ∈ normAll z t := by
  rw [mem_normAll] at hn ⊢
  refine ⟨mul_mem (mul_mem hk hn.1) (inv_mem hk), fun i x hx => ?_⟩
  set k' : ↥(centZ z) := ⟨k, centPair_le_centZ z t hk⟩ with hk'
  let j : ComponentIndex ↥(centZ z) :=
    ⟨i.val.map (MulAut.conj k'⁻¹).toMonoidHom, (LocalComponents.equiv_iff _ _).2 i.property⟩
  have h1 : k⁻¹ * x * k ∈ compG z j := by
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨(MulAut.conj k'⁻¹).toMonoidHom a, ⟨a, ha, rfl⟩, by simp [k']⟩
  obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hn.2 j _ h1
  have hb' : k⁻¹ * (a : G) * k = n * (k⁻¹ * x * k) * n⁻¹ := by
    simpa [k', MulAut.conj_apply] using hb
  have : k * n * k⁻¹ * x * (k * n * k⁻¹)⁻¹ = (a : G) := by
    calc k * n * k⁻¹ * x * (k * n * k⁻¹)⁻¹ = k * (n * (k⁻¹ * x * k) * n⁻¹) * k⁻¹ := by group
      _ = k * (k⁻¹ * (a : G) * k) * k⁻¹ := by rw [hb']
      _ = (a : G) := by group
  rw [this]
  exact ⟨a, ha, rfl⟩

section Certified


theorem Level55.normAll_eq_of_not_le (d : Level55 G t z)
    (h : ¬ normAll z t ≤ O2In (centPair z t)) : normAll z t = centPair z t :=
  d.eq_K_of_not_le_O2K inf_le_left (fun _ hk _ hn => normAll_conj hk hn) h

end Certified

end CFSG.EvenSporadicStandard.TwoB
