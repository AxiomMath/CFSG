module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealMark
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASuConj
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.GLTheoremA.RationalModel CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem l154RealTypeA_holds : L154RealTypeA := by
  intro τ L _ _ _ p₀ S p a i hp _ hT hap ha1 hqi hA
  rcases typeA_frame_cases S hp hT hap ha1 i ⟨by omega, hA.2⟩ with ⟨h1, -⟩ | h | h
  · exact absurd h1 (by have := hA.1; omega)
  · obtain ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩ := h
    obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
    obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    obtain rfl : r = 2 := CharP.eq L hchar (by assumption)
    obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
    obtain ⟨σQ, hσc, W, hRW, hker⟩ := split_exists_hom_W S hT i hν hψ hΨ π hπ hr hchar hq
    haveI : Fact (Nat.Prime 2) := ⟨hr⟩
    obtain ⟨hfin, hcard⟩ := finite_card_fixSubfield (L := L) (r := 2)
      (n := e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (Nat.mul_pos he hs0) σQ hσc
    haveI := hfin
    exact l154_realizedMarking_of_split (by omega) (Nat.mul_pos he hs0) hcard W hRW.symm hker hqi
  · obtain ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩ := h
    obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
    obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    obtain rfl : r = 2 := CharP.eq L hchar (by assumption)
    obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
    have h32 := not_unitaryFrame_three_two S hT i hν hψ hΨ π hπ hr hchar he hq hqi
    obtain ⟨F, σQ, hFcard, hσc, W, hRW, hker⟩ :=
      unitary_exists_hom_W S hT i hν hψ hΨ π hπ hr hchar he hq h32
    haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
      rw [hFcard]
      exact (pow_pos (pow_pos hr.pos _) 2).ne')
    exact l154_realizedMarking_of_unitary (by omega) (Nat.mul_pos he hs0) h32 hFcard W hRW.symm
      hker hqi

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
