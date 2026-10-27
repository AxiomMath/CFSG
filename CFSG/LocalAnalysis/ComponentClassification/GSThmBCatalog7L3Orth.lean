module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroProjective
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoOdd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2PerfectSubnormal

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L3

open Subgroup

universe u v

theorem hom_eq_one_of_perfect {G A : Type*} [Group G] [CommGroup A] [hG : Group.IsPerfect G]
    (φ : G →* A) (g : G) : φ g = 1 := by
  have h : (⊤ : Subgroup G) ≤ φ.ker := by
    rw [← hG.commutator_eq_top]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, mul_comm (φ a) (φ b),
      mul_inv_cancel_right, mul_inv_cancel]
  exact h (mem_top g)

theorem snd_eq_one_of_perfect {X Y : Type*} [Group X] [CommGroup Y] (P : Subgroup (X × Y))
    [Group.IsPerfect P] {z : X × Y} (hz : z ∈ P) : z.2 = 1 :=
  hom_eq_one_of_perfect ((MonoidHom.snd X Y).comp P.subtype) ⟨z, hz⟩

variable {K : Type u} [Field K] [Finite K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem orthThree_perfect_subnormal (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 3)
    (Y : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) [Group.IsPerfect Y] (hY : Y ≠ ⊥)
    (hYs : Y.IsSubnormal) :
    3 < Nat.card K ∧ Nonempty (Y ≃* GorensteinWalter.PSL2 K) := by
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨-, -, e, -⟩ :=
    CatalogueBOrthogonalThreeSimilarity.exists_trace_zero_similarity_and_orthogonal_equiv hodd Q
      hQ hdim
  set E : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
      (GorensteinWalter.PGL2 K × rootsOfUnity 2 K) :=
    e.trans (CatalogueBOrthogonal.traceZeroProjectiveEquiv h2).symm with hE
  set Y' := Y.map E.toMonoidHom with hY'
  let eY : Y ≃* Y' := Y.equivMapOfInjective E.toMonoidHom E.injective
  have : Group.IsPerfect Y' := Group.IsPerfect.ofSurjective (f := eY.toMonoidHom) eY.surjective
  have hY's : Y'.IsSubnormal := hYs.map E.surjective
  set fst := MonoidHom.fst (GorensteinWalter.PGL2 K) (rootsOfUnity 2 K) with hfst
  have hinj : Function.Injective (fst.comp Y'.subtype) := by
    intro y z h
    apply Subtype.ext
    apply Prod.ext h
    exact (snd_eq_one_of_perfect Y' y.2).trans (snd_eq_one_of_perfect Y' z.2).symm
  set J := Y'.map fst with hJ
  have hrange : (fst.comp Y'.subtype).range = J := by
    rw [MonoidHom.range_comp, range_subtype]
  let eJ : Y' ≃* J := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hJp : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hJs : J.IsSubnormal := hY's.map (fun x => ⟨(x, 1), rfl⟩)
  have hJne : J ≠ ⊥ := by
    intro hbot
    apply hY
    rw [eq_bot_iff]
    intro y hy
    have h1 : eJ (eY ⟨y, hy⟩) = 1 := by
      have : (eJ (eY ⟨y, hy⟩) : GorensteinWalter.PGL2 K) ∈ (⊥ : Subgroup _) :=
        hbot ▸ (eJ (eY ⟨y, hy⟩)).2
      exact Subtype.ext ((mem_bot).mp this)
    have h2' : (⟨y, hy⟩ : Y) = 1 := by
      rw [← map_one eJ, ← map_one eY] at h1
      exact eY.injective (eJ.injective h1)
    exact (mem_bot).mpr (congrArg Subtype.val h2')
  have hpp := CatalogueSchreierLinearTwo.oddPrimePower_of_odd_card K hodd
  obtain ⟨h3, hJeq⟩ := GorensteinWalter.pgl2_perfect_subnormal_eq_commutator K hpp J hJne hJp hJs
  rw [GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three K hpp h3] at hJeq
  exact ⟨h3, ⟨eY.trans (eJ.trans ((MulEquiv.subgroupCongr hJeq).trans
    (MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm))⟩⟩

end Catalog7L3

end CFSG.ComponentClassification.GSThmB
