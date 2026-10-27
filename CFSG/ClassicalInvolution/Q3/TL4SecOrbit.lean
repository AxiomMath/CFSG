module

public import CFSG.ClassicalInvolution.Q3.TL4VtxDich
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lift

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

section Graph

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dstarConnected_of_dConnected (hΦ : HypOmegaGen Φ) (h : DConnected Φ) :
    T3.DStarConnected Φ := by
  intro K hK J hJ
  have hp := h K hK J hJ
  clear hJ
  show Relation.ReflTransGen (dstarAdj Φ) K J
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ⟨hbc.1, ?_⟩
    rcases hbc.2 with h' | h'
    · exact Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΦ _ h')
    · exact Or.inr (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΦ _ h')

omit [Finite X] in
theorem omegaConj_symm {K L : Subgroup X} (h : ∃ g ∈ omegaGen Φ, conjSub g K = L) :
    ∃ g ∈ omegaGen Φ, conjSub g L = K := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g⁻¹, (omegaGen Φ).inv_mem hg, ?_⟩
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

omit [Finite X] in
theorem omegaConj_trans {K L M : Subgroup X} (h : ∃ g ∈ omegaGen Φ, conjSub g K = L)
    (h' : ∃ g ∈ omegaGen Φ, conjSub g L = M) : ∃ g ∈ omegaGen Φ, conjSub g K = M := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', rfl⟩ := h'
  exact ⟨g' * g, (omegaGen Φ).mul_mem hg' hg, conjSub_mul g' g K⟩

end Graph

section Orbits

variable {n : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem adj_of_not_conj (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {M N : Subgroup X}
    (hM : M ∈ Φ) (hN : N ∈ Φ) (hnc : ¬ ∃ g ∈ omegaGen Φ, conjSub g M = N) :
    N ∈ Φ ∧ dAdj Φ M N := by
  have hne : N ≠ M := fun e => hnc ⟨1, (omegaGen Φ).one_mem, by rw [conjSub_one, e]⟩
  exact ⟨hN, Or.inl (mem_omegaNbr_of_commutes hN hne
    (Vtx.commutes_of_not_conj h4 h hO hn hM hN hnc))⟩

theorem dConnected_of_not_conj (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {K L : Subgroup X}
    (hK : K ∈ Φ) (hL : L ∈ Φ) (hKL : ¬ ∃ g ∈ omegaGen Φ, conjSub g K = L) : DConnected Φ := by
  intro M hM N hN
  have adj := fun {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ Φ)
    (hnc : ¬ ∃ g ∈ omegaGen Φ, conjSub g A = B) => adj_of_not_conj h4 h hO hn hA hB hnc
  by_cases hMN : ∃ g ∈ omegaGen Φ, conjSub g M = N
  · by_cases hMK : ∃ g ∈ omegaGen Φ, conjSub g M = K
    ·
      have hML : ¬ ∃ g ∈ omegaGen Φ, conjSub g M = L := fun hML =>
        hKL (omegaConj_trans (omegaConj_symm hMK) hML)
      have hLN : ¬ ∃ g ∈ omegaGen Φ, conjSub g L = N := fun hLN =>
        hML (omegaConj_trans hMN (omegaConj_symm hLN))
      exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (adj hM hL hML))
        (adj hL hN hLN)
    ·
      have hKN : ¬ ∃ g ∈ omegaGen Φ, conjSub g K = N := fun hKN =>
        hMK (omegaConj_trans hMN (omegaConj_symm hKN))
      exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (adj hM hK hMK))
        (adj hK hN hKN)
  · exact Relation.ReflTransGen.single (adj hM hN hMN)

theorem omegaTransitive_of_not_dConnected (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {K : Subgroup X}
    (hK : K ∈ Φ) (hc : ¬ DConnected Φ) : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g K = L :=
  fun _ hL => by_contra fun hnc => hc (dConnected_of_not_conj h4 h hO hn hK hL hnc)

theorem omegaTransitive_of_not_dstarConnected (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {K : Subgroup X}
    (hK : K ∈ Φ) (hc : ¬ T3.DStarConnected Φ) : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g K = L :=
  omegaTransitive_of_not_dConnected h4 h hO hn hK fun hd =>
    hc (dstarConnected_of_dConnected h.hyp hd)

theorem omegaTransitive_of_dEdgeless (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {K : Subgroup X}
    (hK : K ∈ Φ) (he : Disconnected.DEdgeless Φ) :
    ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g K = L :=
  fun L hL => by_contra fun hnc => he K hK L hL (adj_of_not_conj h4 h hO hn hK hL hnc).2

end Orbits

section Trans

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem tightCls_of_transitive (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) {K : Subgroup X} (hK : K ∈ Φ)
    (htr : ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (S : Sylow 2 ↥K) (z : X) :
    TightCls X K S z := by
  refine ⟨Vtx.nonempty_sylow_equiv h hK S, ?_, hO⟩
  have hcore : tightCore K = K := h.closure_twoElts hK
  show (⨆ g : X, conjSub g (tightCore K)) = ⊤
  rw [hcore, eq_top_iff, ← hgen]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨g, rfl⟩ := htr L hL
  exact le_iSup (fun g : X => conjSub g K) g

omit [Finite X] in
theorem conjClass_tightCore_eq (h : TypeRFam 3 Φ) {K : Subgroup X} (hK : K ∈ Φ)
    (htr : ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) : CoreAssembly.conjClass (tightCore K) = Φ := by
  have hcore : tightCore K = K := h.closure_twoElts hK
  rw [hcore]
  ext L
  constructor
  · rintro ⟨g, rfl⟩
    exact h.hyp.conjInvariant g K hK
  · intro hL
    exact htr L hL

theorem exists_datum_of_omegaTransitive (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤) {K : Subgroup X}
    (hK : K ∈ Φ) (htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g K = L) :
    ∃ (S : Sylow 2 ↥K) (z : X), TightDatum K S z ∧ TightCls X K S z ∧
      CoreAssembly.conjClass (tightCore K) = Φ := by
  have htr' : ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := fun L hL => by
    obtain ⟨g, -, hg⟩ := htr L hL
    exact ⟨g, hg⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  exact ⟨S, z, Vtx.tightDatum_of_mem h hK hz S, tightCls_of_transitive h hO hgen hK htr' S z,
    conjClass_tightCore_eq h hK htr'⟩

end Trans

end CFSG.ClassicalInvolution.Q3.TL4
