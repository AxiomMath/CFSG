module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDCheck2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

@[expose] def exc3core_posRows (τ : Tag) : List ℕ :=
  (RD.bRoots τ).map fun w =>
    (RD.accum (2 ^ τ.artifactRoots.length - 1) (RD.colsOf τ.rank τ.artifactRoots) (RD.digs3 w)
      (0, 0)).1

@[expose] def exc3core_posTbl (τ : Tag) : ℕ :=
  RD.tblOf (2 ^ τ.artifactRoots.length) (exc3core_posRows τ)

@[expose] def exc3core_posRow (τ : Tag) (k : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (exc3core_posTbl τ) (τ.artifactRoots.length * k))
    (2 ^ τ.artifactRoots.length - 1)

@[expose] def exc3core_sig (τ : Tag) (V k : ℕ) : ℕ := Nat.land (exc3core_posRow τ k) V

@[expose] def exc3core_sigs (τ : Tag) (V m : ℕ) : List ℕ :=
  (((List.range τ.artifactRoots.length).filter fun l => m.testBit l).map (exc3core_sig τ V))

@[expose] def exc3core_expMasks (τ : Tag) (d : List ℕ) : ℕ × ℕ :=
  RD.accum (2 ^ τ.artifactRoots.length - 1) (RD.colsOf τ.rank τ.artifactRoots) d (0, 0)

@[expose] def exc3core_wObs (τ : Tag) (d : List ℕ) (V : ℕ) : Bool :=
  (List.range τ.artifactRoots.length).any fun k =>
    (exc3core_expMasks τ d).1.testBit k &&
      (exc3core_sigs τ V (exc3core_expMasks τ d).2).all fun s => s != exc3core_sig τ V k

@[expose] def exc3core_wUniq (τ : Tag) (cap : ℕ) (d : List ℕ) (V : ℕ) : Bool :=
  decide (RD.cnt2 (2 * RD.cnt2 cap V) (RD.kerMaskFast τ d) < 2 * RD.cnt2 cap V)

@[expose] def exc3core_okC (τ : Tag) (cap : ℕ) (u w : ℕ → Bool) (d : List ℕ) (V : ℕ) : Bool :=
  !(u (RD.cnt2 cap V)) ||
    (exc3core_wUniq τ cap d V && (!(w (RD.cnt2 cap V)) || exc3core_wObs τ d V))

@[expose] def exc3core_eCheck (τ : Tag) (cap : ℕ) (u w : ℕ → Bool) (d : List ℕ) : Bool :=
  RD.compLoop2 (RD.rowM2 τ) (RD.kerMaskFast τ d) (τ.artifactRoots.length + 1)
    (exc3core_okC τ cap u w d) τ.artifactRoots.length (RD.kerMaskFast τ d)

@[expose] def exc3core_wCheck (τ : Tag) (cap : ℕ) (u w : ℕ → Bool) (vs : List (List ℕ)) : Bool :=
  vs.all (exc3core_eCheck τ cap u w)

@[expose] def exc3core_WObs (τ : Tag) {L : Type} [Field L]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ χ (Multiplicative.ofAdd γ) ≠ 1 ∧
    ∀ γ' : Fin τ.rank → ℤ, IsRoot τ γ' →
      χ (Multiplicative.ofAdd γ') = (χ (Multiplicative.ofAdd γ))⁻¹ →
        ∃ β ∈ Ψ, iform γ' β ≠ iform γ β

@[expose] def exc3core_dngE6 (s : ℕ) : Bool := s == 20 || s == 40

@[expose] def exc3core_dngE7 (s : ℕ) : Bool := s == 40 || s == 42 || s == 72

@[expose] def exc3core_uniE7 (s : ℕ) : Bool := s == 40 || s == 42 || s == 60 || s == 72

@[expose] def exc3core_dngE8 (s : ℕ) : Bool := s == 72 || s == 84

end CFSG.LocalAnalysis.GLTheoremA.I167

end
