module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeCommSpaceAveraging.CoprimeCommSpaceAveraging
public import CFSG.LinearAlgebra.CoprimeActions.HyperplaneDecompositionOnCommSpace

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BinaryCenterDecomposition

open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation
  CFSG.LinearAlgebra.CoprimeActions.HyperplaneDecompositionOnCommSpace

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {W : Type*} [AddCommGroup W] [Module (ZMod p) W]

private theorem core (hp2 : p ≠ 2) (ρ : Representation (ZMod p) G W) (Z : Subgroup G)
    (hZ : CFSG.Open.IsElemAbelian 2 Z) :
    open scoped Classical in
    iSupIndep (fun H : hyperplanes 2 Z => commSpace ρ Z ⊓ fixedSpace ρ H.1) ∧
      (⨆ H : hyperplanes 2 Z, commSpace ρ Z ⊓ fixedSpace ρ H.1) = commSpace ρ Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2' : (2 : ℕ) ≠ p := fun h => hp2 h.symm
  have hcentral : ∀ k ∈ Z, ∀ z ∈ Z, k * z = z * k := fun x hx y hy => by
    have := hZ.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hc : ((Nat.card Z : ℕ) : ZMod p) ≠ 0 :=
    natCard_ne_zero_of_le hp2' hZ (le_refl Z)
  let σ := restrictedRepresentation ρ Z Z hcentral
  have hV : commSpace σ (⊤ : Subgroup Z) = ⊤ :=
    CoprimeCommSpaceAveraging.restricted_commSpace_eq_top ρ Z hZ.1 hc hcentral
  have hTop : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup Z) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · exact Subtype.ext (hZ.1.is_comm.comm a.1 b.1)
    · exact Subtype.ext (hZ.2 x.1 x.2)
  have hind := iSupIndep_fixedSpace hp2' σ ⊤ hTop hV
  have hsup := iSup_fixedSpace_hyperplanes hp2' σ ⊤ hTop hV
  set e := toTop_bijective 2 Z
  have hg : ∀ D : hyperplanes 2 Z, fixedSpace σ (D.1.subgroupOf Z) =
      Submodule.comap (commSpace ρ Z).subtype (commSpace ρ Z ⊓ fixedSpace ρ D.1) :=
    fun D => fixedSpace_restrictedRepresentation ρ Z Z hcentral D.1 D.2.1
  have hmap : ∀ D : hyperplanes 2 Z,
      Submodule.map (commSpace ρ Z).subtype (fixedSpace σ (D.1.subgroupOf Z)) =
        commSpace ρ Z ⊓ fixedSpace ρ D.1 := fun D => by
    rw [hg, Submodule.map_comap_subtype]; simp
  constructor
  · have h1 := hind.comp e.1
    have h2 := LinearMap.iSupIndep_map (commSpace ρ Z).subtype (commSpace ρ Z).injective_subtype h1
    convert h2 using 1
    funext D
    exact (hmap D).symm
  · have h3 : (⨆ D : hyperplanes 2 Z, fixedSpace σ (D.1.subgroupOf Z)) = ⊤ := by
      rw [← hsup]
      apply le_antisymm
      · exact iSup_le fun D => le_iSup (fun E : hyperplanes 2 (⊤ : Subgroup Z) => fixedSpace σ E.1)
          (toTop 2 Z D)
      · exact iSup_le fun E => by
          obtain ⟨D, hD⟩ := e.2 E
          rw [← hD]
          exact le_iSup (fun D : hyperplanes 2 Z => fixedSpace σ (D.1.subgroupOf Z)) D
    calc (⨆ D : hyperplanes 2 Z, commSpace ρ Z ⊓ fixedSpace ρ D.1)
        = ⨆ D : hyperplanes 2 Z, Submodule.map (commSpace ρ Z).subtype
            (fixedSpace σ (D.1.subgroupOf Z)) := by simp only [hmap]
      _ = Submodule.map (commSpace ρ Z).subtype (⨆ D : hyperplanes 2 Z,
            fixedSpace σ (D.1.subgroupOf Z)) := (Submodule.map_iSup _ _).symm
      _ = commSpace ρ Z := by rw [h3, Submodule.map_subtype_top]

theorem iSup_eq (hp2 : p ≠ 2) (ρ : Representation (ZMod p) G W) (Z : Subgroup G)
    (hZ : CFSG.Open.IsElemAbelian 2 Z) :
    (⨆ H : hyperplanes 2 Z, commSpace ρ Z ⊓ fixedSpace ρ H.1) = commSpace ρ Z :=
  (core hp2 ρ Z hZ).2

theorem iSupIndep_inf (hp2 : p ≠ 2) (ρ : Representation (ZMod p) G W) (Z : Subgroup G)
    (hZ : CFSG.Open.IsElemAbelian 2 Z) :
    iSupIndep (fun H : hyperplanes 2 Z => commSpace ρ Z ⊓ fixedSpace ρ H.1) := by
  classical
  exact (core hp2 ρ Z hZ).1

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BinaryCenterDecomposition
