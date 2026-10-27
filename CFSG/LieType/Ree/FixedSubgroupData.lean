module

public import CFSG.LieType.Ree.ExceptionalAutomorphismData
public import CFSG.LieType.Ree.FixedWeylData
public import CFSG.LieType.Chevalley.WeylInversion

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

@[expose] def reeGamma :
    Subgroup (ModGL t.tag K) :=
  (t.finiteReeFixedGroup K a).map (adjointGroup t.tag K).subtype

@[expose] def reeFixedBorel
    : Subgroup (ModGL t.tag K) :=
  borelGroup t.tag K ⊓ t.reeGamma K a

@[expose] def reeFixedTorus
    : Subgroup (ModGL t.tag K) :=
  torusGroup t.tag K ⊓ t.reeGamma K a

@[expose] def reeFixedMonomial
    : Subgroup (ModGL t.tag K) :=
  monomialSubgroup t.tag K ⊓ t.reeGamma K a

@[expose] def reeFixedPosUnipotent
    : Subgroup (ModGL t.tag K) :=
  posUnipotent t.tag K ⊓ t.reeGamma K a

@[expose] def reeFixedNegUnipotent
    : Subgroup (ModGL t.tag K) :=
  negUnipotent t.tag K ⊓ t.reeGamma K a

@[expose] def reeFixedCellUnipotent
    (w : WeylGroup t.tag) : Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (inversionSet w) ⊓ t.reeGamma K a

@[expose] def reeFixedOrbitUnipotent
    (j : Fin t.fixedOrbitCount) : Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (t.fixedOrbitRoots j) ⊓ t.reeGamma K a

@[expose] def reeFixedOrbitComplementUnipotent
    (j : Fin t.fixedOrbitCount) :
    Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (t.fixedOrbitComplementRoots j) ⊓ t.reeGamma K a

variable {t K a}

theorem mem_reeGamma
    {g : ModGL t.tag K} :
    g ∈ t.reeGamma K a ↔
      ∃ hg : g ∈ adjointGroup t.tag K, t.finiteReeAut K a ⟨g, hg⟩ = ⟨g, hg⟩ := by
  rw [reeGamma, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem reeGamma_eq_reeFixedGroup :
    t.reeGamma K a = reeFixedGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
      else t.prime ^ (a + 1)) :=
  map_subtype_finiteReeFixedGroup a

end ReeTag

end CFSG.LieType.Ree
