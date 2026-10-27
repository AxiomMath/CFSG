module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDGMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKDInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKCInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeDG

theorem isPComponent_gsFixedLayer_inf
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (e : ↥L ≃* Blueprint.NativeSporadic.He)
    {a u : X} (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u) :
    IsPComponent 2 ((gsFixedLayer L u).subgroupOf
      (centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := gsFixedLayer L u with hKdef
  set Cu := centralizer ({u} : Set X) with hCu
  set Ca := centralizer ({a} : Set X) with hCa
  have hKL : K ≤ L ⊓ Cu := gsFixedLayer_le_inf L u
  have hKp1 : IsPComponent 2 (K.subgroupOf (L ⊓ Cu)) := isPComponent_gsFixedLayer_of_held e hu
  have hLs : (L.subgroupOf Ca).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Ca hLa).1 hLc).1
  have hLs' : ((L ⊓ Cu).subgroupOf (Ca ⊓ Cu)).IsSubnormal := by
    have h1 : ((L.subgroupOf Ca).subgroupOf ((Ca ⊓ Cu).subgroupOf Ca)).IsSubnormal :=
      hLs.subgroupOf
    have h2 := h1.map (f := (subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cu ≤ Ca)).toMonoidHom)
      (subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cu ≤ Ca)).surjective
    convert h2 using 1
    ext k
    simp only [mem_subgroupOf, mem_inf, mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨hkL, -⟩
      exact ⟨⟨⟨k, (mem_inf.mp k.2).1⟩, k.2⟩, hkL, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, (mem_inf.mp ((subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cu ≤ Ca)) y).2).2⟩
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hKL
    (inf_le_inf_right _ hLa) hLs').mpr hKp1

end HeDG

theorem heldKDiagonalStep_of_central
    (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hKDC : HeldKDiagonalCentralStep) : HeldKDiagonalStep := by
  intro X _ _ L hset a u M ha hLa hLc hu hMu hMp hne hfix _
  obtain ⟨hHS, hW, -, ⟨e⟩, -⟩ := id hset
  have hu2 : orderOf u = 2 := hu.2.1
  have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    norm_num at hu2
  have hKL : gsFixedLayer L u ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hKau : gsFixedLayer L u ≤ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X) :=
    le_inf (hKL.trans hLa) ((gsFixedLayer_le_inf L u).trans inf_le_right)
  exact hKDC X L hset a u M ha hLa hLc hu hMu hMp hne hfix
    (HeDG.central_of_diagonal hS hUO hheld hHS hW ha hLa hu.1 huu hu1 hKL hKau
      (HeDG.isPComponent_gsFixedLayer_inf e hLa hLc hu) hMu hMp hne hfix)

end CFSG.ComponentClassification.GrSLit
