module

public import CFSG.Fischer.Rec23Comp

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Rec23

variable {G : Type} [Group G]

@[expose] def commGraphIso (S : Subgroup G) {K : Set G} (hKS : K ⊆ S) :
    commGraph (Subtype.val ⁻¹' K : Set S) ≃g commGraph K where
  toFun a := ⟨((a : S) : G), a.2⟩
  invFun c := ⟨⟨c, hKS c.2⟩, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {a b} := by
    change (_ ≠ _ ∧ ((a : S) : G) * ((b : S) : G) = ((b : S) : G) * ((a : S) : G)) ↔ _
    simp only [commGraph_adj, ne_eq, Subtype.ext_iff]
    rfl

end Rec23

theorem fi23_of_localPoints
    {X : Type} [Group X] [Finite X] (D : Set X)
    (hcls : ∀ g : X, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : X, g * d * g⁻¹ = e)
    (hne : D.Nonempty)
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hprod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hloc : ∀ d ∈ D, Nonempty (LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) D d))
    (hZ : ∀ d ∈ D, ∀ g : X, (∀ f ∈ insert d (LocalClass D d), g * f = f * g) → g = 1 ∨ g = d) :
    (commGraph D).Connected ∧
      ∃ φ : Subgroup.closure D ≃* CFSG.Blueprint.NativeSporadic.Fi23,
        ∀ y : Subgroup.closure D, (y : X) ∈ D ↔ IsConj CFSG.Sporadic.Fi23.dFi23 (φ y) := by
  have _ := htr
  have hH : Rec23.LocalHyp X D := ⟨hinv, hprod, hloc⟩
  have hK : Rec23.IsStarClosed D D :=
    { subset := fun _ h => h
      nonempty := hne
      nbr := fun _ _ _ hc _ => hc
      conj := fun k hk c hc => by
        have h := hcls k c hc
        rwa [hH.inv_eq hk] at h }
  have hKS : D ⊆ Subgroup.closure D := Subgroup.subset_closure
  have hpair := hK.pair_closure hH
  have hloc' : ∀ f ∈ (Subtype.val ⁻¹' D : Set (Subgroup.closure D)),
      Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D)
        (Subtype.val ⁻¹' D : Set (Subgroup.closure D)) f) := by
    intro f hf
    obtain ⟨L⟩ := hloc (f : X) hf
    exact ⟨Rec23.restrictPoints hK hKS hf L⟩
  have hZ0 : Rec23.HasZ D := hZ
  have hZ' := hZ0.subgroup hK hKS
  have hconn := Rec23.connected_of_hasZ hpair hloc' hZ'
  have hcenter : Subgroup.center (Subgroup.closure D) = ⊥ := by
    refine hZ'.center_eq_bot ⟨⟨hne.some, hKS hne.some_mem⟩, hne.some_mem⟩ fun f hf => ?_
    obtain ⟨L⟩ := hloc' f hf
    exact Rec23.exists_mem_localClass_of_localPoints L
  refine ⟨(Rec23.commGraphIso _ hKS).connected_iff.1 hconn, ?_⟩
  obtain ⟨φ, hφ⟩ := Rec23.exists_mulEquiv_of_connected Sporadic.Fi23.f23_J
    Sporadic.Fi23.center_J Sporadic.Fi23.isSimpleGroup_commutator_J hpair hloc' hconn hcenter
  refine ⟨φ.trans Sporadic.Fi23.fi23EquivJ.symm, fun y => ?_⟩
  have h1 : (y : X) ∈ D ↔ φ y ∈ Sporadic.Fi23.D23 := by
    rw [← hφ]
    exact (φ.injective.mem_set_image (s := Subtype.val ⁻¹' D) (a := y)).symm
  rw [h1]
  have h2 := Sporadic.Fi23.isConj_symm_iff Sporadic.Fi23.fi23EquivJ.toEquiv
    (map_mul Sporadic.Fi23.fi23EquivJ) Sporadic.Fi23.d
    ((φ.trans Sporadic.Fi23.fi23EquivJ.symm) y)
  refine Iff.trans ?_ h2.symm
  show IsConj Sporadic.Fi23.d (φ y) ↔
    IsConj Sporadic.Fi23.d (Sporadic.Fi23.fi23EquivJ (Sporadic.Fi23.fi23EquivJ.symm (φ y)))
  rw [MulEquiv.apply_symm_apply]

end CFSG.Fischer
