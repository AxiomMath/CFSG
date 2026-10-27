module

public import CFSG.Quasithin.EmptyFaithful.S146F6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146A0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Inputs

variable {G : Type} [Group G]

theorem stage14614At_of_F4 (h : Stage14614_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M : Subgroup G}
    (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) : Stage14614At T H p :=
  h G T M S H PQ p hred hmax

end Inputs

section U2

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.isInvU_of_fixed_F4 (S : Setting146 G T M) (h5 : Stage1461Five) (h16 : Stage14616_F4)
    {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T)) {u : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u) : IsInvU T M H u := by
  have hTeq := h.tZero_eq S hred hu huZ huT
  obtain ⟨hidx, hnorm⟩ := h16 G T M S H PQ p hred hmax H₀ H₁ H₂ t h
  refine ⟨uHi_le_conjClosure (h.le₁.trans h.le) hu, h.isSylowTwoOf_tU S hred hu huZ huT, ?_,
    h.not_mem_centralizer_pCore S h5 hred hMod hF hu huZ,
    fun s hsT hs => h.not_mem_centralizer_pCore_mul S h5 hred hMod hF hu huZ huT hsT hs, ?_⟩
  · rw [hTeq]
    exact hidx
  · rw [hTeq]
    exact hnorm

end U2

end CFSG.Quasithin
