module

public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeDStep

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup GH74.GLS GH74.GLS.TwoThin DPrime

theorem theoremDPrimeEsc_holds :
    ∀ (Typ Esc : ∀ (K : Type) [Group K], Prop) (q₀ : ℕ), Odd q₀ → 5 ≤ q₀ →
      VerticalCentralEsc Typ Esc → CoreInvariant Typ → CoreInvariant Esc →
      DiagonalTransfer q₀ Typ →
      ∀ (X : Type) [Group X] [Finite X],
      (∀ v : X, orderOf v = 2 → SectionRank.IsKGroupCat ↥(centralizer ({v} : Set X))) →
      ∀ (t : X) (K₀ N : Subgroup X) (c : X), IsDatum q₀ t K₀ N c → Typ ↥K₀ →
        (∃ (w : X) (J N' : Subgroup X), IsDatum q₀ w J N' w ∧ w ∈ J ∧ Typ ↥J) ∨
          ∃ (v : X) (M : Subgroup X), orderOf v = 2 ∧ M ≤ centralizer ({v} : Set X) ∧
            IsPComponent 2 (M.subgroupOf (centralizer ({v} : Set X))) ∧ Esc ↥M := by
  intro Typ Esc q₀ hq₀ h5 hVC hCI hCE hDT X _ _ hK t K₀ N c hD hTyp
  by_cases hct : c = t
  · subst hct
    exact Or.inl ⟨c, K₀, N, hD, hD.2.2.2.1 hD.2.2.2.2.2.2.2.1, hTyp⟩
  obtain ⟨I, hI, hcI, hNI, ⟨eI⟩⟩ := datum_cover hD
  obtain ⟨ht, hK₀C, -, hNK₀, hNp, hNSL, hc, hcN, hNc, -⟩ := hD
  have hTypI : Typ ↥I := hCI _ _ ⟨eI.symm⟩ hTyp
  have htc : t ∈ centralizer ({c} : Set X) := mem_centralizer_symm (hK₀C (hNK₀ hcN))
  obtain ⟨-, -, L, hL, hcases, -⟩ := pumpupY_structure (orderOf_mk_centralizer htc ht)
    (le_centralizer_mk hI.1 htc) (isTwoComponent_centralizer_mk hI htc)
  rcases hcases with ⟨hLt, hIL⟩ | ⟨-, hAB, hIδ⟩
  · exact vertical_step hVC hCI hCE ht hc htc (hK c hc) hI hTypI hcI hNI hNp hNSL hcN hNc hL hLt
      hIL
  · obtain ⟨u, hsu, Iu, Nu, hu, hIu, hTypIu, huIu, hNuIu, hNup, hNuSL, huNu, hNuu, hsE⟩ :=
      diagonal_step hq₀ h5 hCI hDT ht hc htc hI hTypI hNI hNSL hcN hL hAB hIδ
    obtain ⟨-, -, Lu, hLu, hcasesu, -⟩ := pumpupY_structure (orderOf_mk_centralizer hsu hc)
      (le_centralizer_mk hIu.1 hsu) (isTwoComponent_centralizer_mk hIu hsu)
    have hLus := conjSub_eq_of_mem_twoLayer hsE hLu
    rcases hcasesu with ⟨-, hIuL⟩ | ⟨hne, -, -⟩
    · exact vertical_step hVC hCI hCE hc hu hsu (hK u hu) hIu hTypIu huIu hNuIu hNup hNuSL huNu
        hNuu hLu hLus hIuL
    · exact absurd hLus hne

theorem theoremDPrime_holds :
    TheoremDPrime := by
  intro Typ q₀ hq₀ h5 hVC hCI hDT X _ _ hK t K₀ N c hD hTyp
  have hVCE : VerticalCentralEsc Typ fun _ _ => False :=
    fun H _ _ hH M hM x hx hxN T hTM hTC hTpc hT w hw hwT hwZ =>
      Or.inl (hVC H hH M hM x hx hxN T hTM hTC hTpc hT w hw hwT hwZ)
  have hCE : CoreInvariant fun _ _ => False := fun _ _ _ _ _ h => h
  rcases theoremDPrimeEsc_holds Typ (fun _ _ => False) q₀ hq₀ h5 hVCE hCI hCE hDT X hK t K₀ N c
      hD hTyp with h | ⟨_, _, _, _, _, h⟩
  · exact h
  · exact h.elim

end CFSG.ComponentClassification.GS82PumpInputs
