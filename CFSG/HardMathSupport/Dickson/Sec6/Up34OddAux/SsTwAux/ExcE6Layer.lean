module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Layer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)


section E6Layer

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L]
  {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem ssBig_e6_layer (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L)
    (hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α ∈ parabolicRoots τ (e6Nodes τ)) :
    SsBig ℓ (rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have hw : MapsJ τ (e6Set τ) (weylQuotientHom τ L ⟨n, hn⟩) := by
    intro α hα
    have := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at this
  obtain ⟨u, hu, π, hπ, hact⟩ := exists_action hw
  have hπJ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_symm_mem hi
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ :=
    CFSG.RankThree.PartOne.KE6.exists_conj_twistedFixed hf hn hπJ hπJ' hu hact
  have hP' : rootSpan τ L (parabolicRoots τ (e6Nodes τ)) = subsystemGroup τ L (e6Set τ) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  rw [hP']
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    Or.inr (Or.inr (M27Ok.isE7E8 (τ := τ)))
  have m0 : e6Idx (τ := τ) 0 ∈ e6Set τ := e6Idx_mem_e6Set 0
  have m5 : e6Idx (τ := τ) 5 ∈ e6Set τ := e6Idx_mem_e6Set 5
  have h05 : e6Idx (τ := τ) 0 ≠ e6Idx 5 := e6Idx_ne (by decide)
  have c05 : τ.cartan (e6Idx 0) (e6Idx 5) = 0 := ssTw_cartan_e6Idx (by decide)
  rcases hπ with rfl | rfl
  · exact ssBig_of_std_fixed hτ' hℓ5 hf hh hlang m0 m5 h05 c05
      (fun c => by simpa using (hgen _ m0 c).1) (fun c => by simpa using (hgen _ m5 c).1)
  · exact ssBig_of_std_swap hτ' hℓ5 hf hh hlang m0 m5 h05 c05
      (fun c => by
        have := (hgen _ m0 c).1
        rwa [rhoτ_e6Idx, show rho6 0 = 5 by decide] at this)
      (fun c => by
        have := (hgen _ m5 c).1
        rwa [rhoτ_e6Idx, show rho6 5 = 0 by decide] at this)

end E6Layer

end CFSG.HardMathSupport.Dickson.Sec6
