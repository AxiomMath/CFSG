module

public import CFSG.ClassicalInvolution.Q3.Q3T8B00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform

section Edge

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_mul_of_nbr_nbr_of_noFrame (hs : Std8 Ω K J S R T W z t)
    (hnf : ¬ ∃ A₀ : Subgroup G, Q3NL.FuzzyFrame3 Ω A₀)
    {K' : Subgroup G} {u : G} (hKK' : K' ∈ omegaNbr Ω K) (hJK' : K' ∈ omegaNbr Ω J)
    (hu : IsUniqueInvolution K' u) : u = z * t := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  by_contra hne
  have hcomm : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hind : u ∉ Subgroup.closure ({z, t} : Set G) := fun hmem => by
    rcases Thompson.eq_of_mem_closure_pair hs.hz.sq hs.ht.sq hcomm hmem with h1 | h1 | h1 | h1
    · exact hu.ne_one h1
    · have : IsUniqueInvolution K' z := h1 ▸ hu
      exact hKK'.2.1 (hnt K hs.stand.mem K' ⟨hKK'.1, z, hs.hz, this⟩)
    · have : IsUniqueInvolution K' t := h1 ▸ hu
      exact hJK'.2.1 (hnt J hs.hJ.1 K' ⟨hJK'.1, t, hs.ht, this⟩)
    · exact hne h1
  exact hnf ⟨_, fuzzyFrame3_of_adj hΩ hs.stand.modU hnt hs.stand.mem hs.hz hs.ht hu hs.hJ hKK'
    hJK' hind⟩

theorem BadStd8.eq_mul_of_nbr_nbr_at [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {J₁ : Subgroup G} {S₁ : Sylow 2 G} {R₁ T₁ W₁ : Subgroup G} {t₁ : G}
    (hs₁ : Std8 Ω K J₁ S₁ R₁ T₁ W₁ z t₁) {K' : Subgroup G} {u : G}
    (hKK' : K' ∈ omegaNbr Ω K) (hJK' : K' ∈ omegaNbr Ω J₁) (hu : IsUniqueInvolution K' u) :
    u = z * t₁ :=
  eq_mul_of_nbr_nbr_of_noFrame hs₁ h.not_fuzzyFrame hKK' hJK' hu

end Edge

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
