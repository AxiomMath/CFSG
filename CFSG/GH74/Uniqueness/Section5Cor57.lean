module

public import CFSG.GH74.Uniqueness.Section5Prop52

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.cor57 (S : ZDSetup X Z M) : Cor57Stmt Z M := by
  intro hnot p hp hp2
  have hZ := S.invariant
  have h := S.prodDisc
  have : Fact p.Prime := ⟨hp⟩
  have hcrit : ¬ ∀ β ∈ omega M, ∀ γ ∈ omega M, β ≠ γ → ∀ P : Subgroup X,
      ABGLocalTools.IsSylowOf p P (β ⊓ γ) → omegaFix M (P : Set X) = {β, γ} :=
    fun hall => hnot (h.doublyTransitive_of_sylow hp hp2 hall)
  push Not at hcrit
  obtain ⟨β, hβ, γ, hγ, hβγ, P, hP, hne⟩ := hcrit
  have hβP : β ∈ omegaFix M (P : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hβ, hP.le.trans inf_le_left⟩
  have hγP : γ ∈ omegaFix M (P : Set X) :=
    h.mem_omegaFix_iff.mpr ⟨hγ, hP.le.trans inf_le_right⟩
  have h3 : 3 ≤ (omegaFix M (P : Set X)).ncard := by
    by_contra hlt
    apply hne
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro x (rfl | rfl)
      · exact hβP
      · exact hγP
    · rw [Set.ncard_pair hβγ]
      omega
  obtain ⟨s, hs, hsP, hs1, -⟩ := h.exists_swap_of_isSylowOf hZ hp hp2 hβ hγ hβγ hP
  have hcnt : zCosetNum Z P s = zNumShare Z M p :=
    h.lemma39_card hZ hβ hβγ hp hp2 hs hs1 hP hsP
  have hcond : Prop52Cond Z M p P := ⟨hP.isPGroup, h3, s, hs, hsP, hcnt⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨Q₁, -, hmax⟩ := Finite.exists_le_maximal hcond
    have h52 := S.prop52 p hp hp2 Q₁ hmax
    obtain ⟨u, hu, huN, hucnt⟩ := hmax.1.exists_u
    exact ⟨u, hu, Q₁, hmax.1.pgroup, hmax.1.three_le, huN, hucnt,
      fun β' hβ' hfix => h52.1.2 u hu huN β' hβ' hfix⟩
  · exact ⟨s, hs, P, hP.isPGroup, h3, hsP, hcnt, β, hβP, by rw [hs1]; exact hβγ.symm,
      by rw [hs1]; exact hP⟩

end CFSG.GH74.Uniqueness
