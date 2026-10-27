module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin

namespace TwinThmE

section Sec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem quat_of_q8
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2)) :
    ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
  intro J hJ P hP
  obtain ⟨P₀, hP₀, ⟨e⟩⟩ := hq8 J hJ
  obtain ⟨k, -, hk⟩ := exists_conjSub_eq_of_isSylow2In hP₀ hP
  subst hk
  exact ⟨(Subgroup.equivMapOfInjective P₀ (MulAut.conj k).toMonoidHom
    (MulAut.conj k).injective).symm.trans e⟩

theorem twinT4Hyp_of (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (hO : classicalInvolutionOddCore G = ⊥) :
    TwinT4Hyp 3 G Ω :=
  ⟨hΩ, h2, quat_of_q8 hq8, hA, hO⟩

theorem exists_mem_USet_le_gen (hΩ : HypOmegaGen Ω) {J : Subgroup G} (hJ : J ∈ Ω) :
    ∃ U ∈ USet Ω, U ≤ J := by
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  obtain ⟨U, hUR, hc, hcard⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_cyclic_index_two
  exact ⟨U, mem_USet_of_natCard hJ hRJ hUR hc hcard, hUR.trans hRJ.1⟩

theorem dstarAdj_of_commutes_gen (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    (hJ : J ∈ Ω) (hne : J ≠ K) (hc : Commutes J K) : dstarAdj Ω K J := by
  obtain ⟨U, hU, hUJ⟩ := exists_mem_USet_le_gen hΩ hJ
  exact ⟨hJ, Or.inl ⟨hJ, hne, U, hU, hUJ, fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes (hUJ hu) hc)⟩⟩

theorem dichotomy_of_thm4Twin {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card G < n)
    (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hO : classicalInvolutionOddCore G = ⊥) (hA : ∀ L ∈ Ω, AEmpty Ω L) {L : Subgroup G}
    (hL : L ∈ Ω) :
    (∀ M ∈ Ω, M ∈ dstarComp Ω L) ∨ (∀ M ∈ Ω, ∃ y : G, conjSub y L = M) := by
  have hT := twinT4Hyp_of hΩ hq8 h2 hA hO
  by_cases hall : ∀ M ∈ Ω, ∃ y : G, conjSub y L = M
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨M₀, hM₀, hM₀c⟩ := hall
  have hLM₀ : M₀ ≠ L := fun h => hM₀c 1 (by rw [conjSub_one, h])
  have hc0 : Commutes L M₀ := h4.apply hlt hT hL hM₀ (fun ⟨g, hg⟩ => hM₀c g hg)
  have hadj0 : dstarAdj Ω L M₀ := dstarAdj_of_commutes_gen hΩ hM₀ hLM₀ hc0.symm
  intro M hM
  by_cases hMc : ∃ y : G, conjSub y L = M
  · obtain ⟨y, rfl⟩ := hMc
    have hnot : ¬ ∃ g : G, conjSub g (conjSub y L) = M₀ := by
      rintro ⟨g, hg⟩
      exact hM₀c (g * y) (by rw [conjSub_mul]; exact hg)
    have hc1 : Commutes (conjSub y L) M₀ := h4.apply hlt hT hM hM₀ hnot
    have hne : M₀ ≠ conjSub y L := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj0)
      (dstarAdj_of_commutes_gen hΩ hM hne.symm hc1)
  · have hc : Commutes L M := h4.apply hlt hT hL hM (fun ⟨g, hg⟩ => hMc ⟨g, hg⟩)
    have hne : M ≠ L := fun h => hMc ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.single (dstarAdj_of_commutes_gen hΩ hM hne hc.symm)

end Sec

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
