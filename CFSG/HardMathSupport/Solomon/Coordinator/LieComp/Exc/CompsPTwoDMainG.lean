module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDRecog
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDAll

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPTwoDMainG

open CompsPTwoDMain CompsPTwoDRecog


variable {τ : Tag}

theorem rationalLieType_of_dClassTwistedG (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨r, e, m, hr, hchar, hm5, z, ε, D, hq, he, hDe, hRC, hDs, hCart, hfix, hswap⟩ :=
    CompsPTwoDExport.exists_twoD_export S hτ hTor i hkind h5
  haveI := hr
  haveI := hchar
  have hrc : ringChar L = r := ringChar.eq L r
  have hQ' : Q r (r ^ e) := by
    have h := hQ
    rw [hrc, hq] at h
    exact h
  have hR : CompsPTwoDDatumG.TwoDChainRecog r L D.e m := by
    rw [hDe]
    exact hrec r e m he hm5 hQ'
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hsl : ∀ β ∈ componentRoots (rootCharHom a) i, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  have hbroot : ∀ j : Fin m, IsRoot τ (ε.symm j : Fin τ.rank → ℤ) := fun j =>
    simpleRoots_isRoot (ε.symm j).2
  have hbinj : Function.Injective (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) :=
    fun j k h => ε.symm.injective (Subtype.ext h)
  have hG : ∀ j k : Fin m, iform (ε.symm j : Fin τ.rank → ℤ) (ε.symm k) =
      CFSG.LieType.Universal.Spin.cartanD m j k := by
    intro j k
    have h := hCart (ε.symm j) (ε.symm k)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [← h]
    exact (CompsPTwoDBase.corootPair_eq_iform (hbroot j)
      (hsl _ (simpleRoots_subset (ε.symm j).2)) _).symm
  have hrange : Set.range (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) =
      ((simpleRoots (componentRoots (rootCharHom a) i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      exact (ε.symm j).2
    · intro hβ
      exact ⟨ε ⟨β, hβ⟩, by simp⟩
  have hsw := hswap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)
  have hdat := CompsPTwoDDatumG.rationalLieType_of_datum_gen hτ D hm5 hR
    (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) hbroot hbinj hG (hDs.trans hrange.symm) hfix
    hsw.1 hsw.2
    (fun j k hjk => exists_dFrames hτ K hK hT hadj hcheck hlt hcard hcount htrees hframes S hp hpL
      hTp i (by omega) hn ε hCart L j k hjk)
  rw [hrc]
  exact rationalLieType_of_map_eq (MulAut.conj z⁻¹) hRC (hrc ▸ hdat)

section PerTag

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}

theorem rationalLieType_of_dClassTwistedG_E6 (S : LangSetup Tag.E6 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_dClassTwistedG (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check
    e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i h5
    hn hkind Q hrec hQ

theorem rationalLieType_of_dClassTwistedG_E7 (S : LangSetup Tag.E7 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_dClassTwistedG (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj
    e7_check e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor
    hTp i h5 hn hkind Q hrec hQ

theorem rationalLieType_of_dClassTwistedG_E8 (S : LangSetup Tag.E8 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_dClassTwistedG (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj
    e8_check e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor
    hTp i h5 hn hkind Q hrec hQ

end PerTag

end CompsPTwoDMainG

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
