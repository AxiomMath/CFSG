module

public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


section Layers

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem e7T3_layer_A2_eq {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) (hkind : cm.kind = 0) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      P = rootSpan Tag.E7 L ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm.kind)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm.kind)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
            parabolicRoots Tag.E7 (e7T3J cm.kind)) : Set (ModGL Tag.E7 L))) := by
  obtain ⟨hg, hact⟩ := e7T3_comp_eps hε hnW h
  have hg' : (coxeterSystem Tag.E7).wordProd cm.u ∈ parabolicWeylGroup Tag.E7 support13 := by
    rw [hkind] at hg
    exact hg
  obtain ⟨P, hPeq, hfac, -, -⟩ := e7_a2_factor hf hk hε hq2 ((coxeterSystem Tag.E7).wordProd w) n
    hnm ((coxeterSystem Tag.E7).wordProd cm.u) hg' (fun α hα => by
      have h1 := hact α (by rw [hkind]; exact hα)
      rw [h1, hkind]
      simp [e7T3Beta, permLattice_one])
  rw [hkind]
  exact ⟨P, hPeq, hfac⟩

theorem e7T3_stab_A2 {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) (hkind : cm.kind = 0) :
    ∀ β ∈ parabolicRoots Tag.E7 (e7T3J 0),
      (((coxeterSystem Tag.E7).wordProd w)⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ *
        (coxeterSystem Tag.E7).wordProd w) • β ∈ parabolicRoots Tag.E7 (e7T3J 0) := by
  obtain ⟨hg, hact⟩ := e7T3_comp_eps hε hnW h
  rw [hkind] at hg hact
  intro β hβ
  rw [hact β hβ]
  have hb : e7T3Beta 0 cm.rot = 1 := by simp [e7T3Beta]
  rw [hb, permLattice_one]
  have h1 := smul_mem_parabolicRoots hg hβ
  rcases hε with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]
    exact neg_mem_parabolicRoots h1

theorem e7T3_stab_A1 {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) (hkind : cm.kind = 1) :
    ∀ β ∈ parabolicRoots Tag.E7 (e7T3J 1),
      (((coxeterSystem Tag.E7).wordProd w)⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ *
        (coxeterSystem Tag.E7).wordProd w) • β ∈ parabolicRoots Tag.E7 (e7T3J 1) := by
  obtain ⟨-, hact⟩ := e7T3_comp_eps hε hnW h
  have hu : cm.u = [] := h.2.2.1 hkind
  rw [hkind] at hact
  intro β hβ
  rw [hact β hβ, hu, CoxeterSystem.wordProd_nil, one_smul]
  have hset : parabolicRoots Tag.E7 (e7T3J 1) =
      threeRootSet (Pi.single (1 : Fin Tag.E7.rank) 1) (Pi.single 4 1) (Pi.single 6 1) :=
    parabolicRoots_a1Nodes_eq
  have hmem : ∀ x ∈ threeRootSet (Pi.single (1 : Fin Tag.E7.rank) 1) (Pi.single 4 1)
      (Pi.single 6 1), x ∈ parabolicRoots Tag.E7 (e7T3J 1) := fun x hx => hset ▸ hx
  have m1 := hmem (Pi.single 1 1) (by simp [threeRootSet])
  have m4 := hmem (Pi.single 4 1) (by simp [threeRootSet])
  have m6 := hmem (Pi.single 6 1) (by simp [threeRootSet])
  have n1 := neg_mem_parabolicRoots m1
  have n4 := neg_mem_parabolicRoots m4
  have n6 := neg_mem_parabolicRoots m6
  have key : ∀ (π : Equiv.Perm (Fin Tag.E7.rank)), π 1 ∈ ({1, 4, 6} : Set (Fin Tag.E7.rank)) →
      π 4 ∈ ({1, 4, 6} : Set (Fin Tag.E7.rank)) → π 6 ∈ ({1, 4, 6} : Set (Fin Tag.E7.rank)) →
      ∀ x ∈ parabolicRoots Tag.E7 (e7T3J 1), permLattice π x ∈ parabolicRoots Tag.E7 (e7T3J 1) := by
    intro π h1 h4 h6 x hx
    have hsing : ∀ i : Fin Tag.E7.rank, π i ∈ ({1, 4, 6} : Set (Fin Tag.E7.rank)) →
        (Pi.single (π i) 1 : Fin Tag.E7.rank → ℤ) ∈ parabolicRoots Tag.E7 (e7T3J 1) ∧
          (-Pi.single (π i) 1 : Fin Tag.E7.rank → ℤ) ∈ parabolicRoots Tag.E7 (e7T3J 1) := by
      intro i hi
      rcases hi with hi | hi | hi
      · rw [hi]; exact ⟨m1, n1⟩
      · rw [hi]; exact ⟨m4, n4⟩
      · rw [hi]; exact ⟨m6, n6⟩
    rw [hset] at hx
    simp only [threeRootSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [permLattice_single]; exact (hsing 1 h1).1
    · have : permLattice π (-Pi.single 1 1) = -permLattice π (Pi.single 1 1) := rfl
      rw [this, permLattice_single]; exact (hsing 1 h1).2
    · rw [permLattice_single]; exact (hsing 4 h4).1
    · have : permLattice π (-Pi.single 4 1) = -permLattice π (Pi.single 4 1) := rfl
      rw [this, permLattice_single]; exact (hsing 4 h4).2
    · rw [permLattice_single]; exact (hsing 6 h6).1
    · have : permLattice π (-Pi.single 6 1) = -permLattice π (Pi.single 6 1) := rfl
      rw [this, permLattice_single]; exact (hsing 6 h6).2
  have hperm : ∀ x ∈ parabolicRoots Tag.E7 (e7T3J 1), permLattice (e7T3Beta 1 cm.rot) x ∈
      parabolicRoots Tag.E7 (e7T3J 1) := by
    cases cm.rot
    · exact key _ (by decide) (by decide) (by decide)
    · exact key _ (by decide) (by decide) (by decide)
  have h1 := hperm β hβ
  rcases hε with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]
    exact neg_mem_parabolicRoots h1

end Layers

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
