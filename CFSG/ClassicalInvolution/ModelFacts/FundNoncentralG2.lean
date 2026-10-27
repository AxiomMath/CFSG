module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralChevalley

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups commutatorElement

section G2

variable {K : Type} [Field K]

theorem g2_torus_neg_one_not_central (h2 : (2 : K) ≠ 0) (l j : Fin (Tag.rank .G2))
    (hodd : Odd (Tag.cartan .G2 l j)) :
    torusElement .G2 K l (-1) ∉ Subgroup.center (adjointGroup .G2 K) := by
  intro hc
  have h1 := commutator_torusElement_xPar_single (F := rootOperatorFamily .G2) (K := K) l j (-1) 1
  have h3 : ⁅torusElement .G2 K l (-1), xPar (rootOperatorFamily .G2) (Pi.single j 1) (1 : K)⁆ =
      1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hc _).symm
  rw [h3] at h1
  have h4 : (((-1 : Kˣ) ^ Tag.cartan .G2 l j : Kˣ) : K) = -1 := by
    rw [hodd.neg_one_zpow]
    simp
  rw [h4, ← xPar_zero (F := rootOperatorFamily .G2) (Pi.single j 1 : Fin (Tag.rank .G2) → ℤ)] at h1
  have h5 := xPar_injective (F := rootOperatorFamily .G2) (K := K) (isRoot_single .G2 j) h1
  apply h2
  linear_combination h5

theorem g2_exists_odd_cartan (l : Fin 2) : ∃ j : Fin 2, Odd (Tag.cartan .G2 l j) := by
  revert l
  rw [Fin.forall_fin_two]
  exact ⟨⟨1, by rw [g2_cartan_zero_one]; exact ⟨-1, by norm_num⟩⟩,
    ⟨0, by rw [g2_cartan_one_zero]; exact ⟨-2, by norm_num⟩⟩⟩

theorem g2_eq_one_of_mem_center_of_mem_rankOne (l : Fin (Tag.rank .G2))
    {r : adjointGroup .G2 K} (hrc : r ∈ Subgroup.center (adjointGroup .G2 K))
    (hrl : r ∈ rankOne (rootGroup (rootOperatorFamily .G2) K) l) : r = 1 := by
  obtain ⟨φ, hφ, hup, hlow⟩ := g2_exists_sl2_hom (K := K) l
  have hup' : ∀ c, φ (sl2Upper c) = xPar (rootOperatorFamily .G2) (Pi.single l 1) c := fun c => by
    rw [hup, xPar_simple]
  have hlow' : ∀ c, φ (sl2Lower c) = xPar (rootOperatorFamily .G2) (-Pi.single l 1) c :=
    fun c => by rw [hlow, xPar_neg_simple]
  have hrange : r ∈ φ.range := by
    refine (sup_le ?_ ?_ : rankOne (rootGroup (rootOperatorFamily .G2) K) l ≤ φ.range) hrl
    · intro g hg
      obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_simple (rootOperatorFamily .G2) hg
      exact ⟨sl2Upper c, hup c⟩
    · intro g hg
      obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_neg_simple (rootOperatorFamily .G2) hg
      exact ⟨sl2Lower c, hlow c⟩
  refine eq_one_of_mem_center_of_param hφ (fun h2 hcen => ?_) hrc hrange
  have hw : ∀ t : Kˣ, CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily .G2)) l t =
      φ (wS t) := fun t => weylElement_eq_map (D := g2Datum K) hup' hlow' t
  have e1 : CFSG.LieType.Chevalley.weylElement .G2 K l = φ (wS 1) := by
    rw [weylElement_eq_xPar (rootOperatorFamily .G2) l, hw]
  have e2 : torusElement .G2 K l (-1) = (φ (wS (1 : Kˣ) * wS (1 : Kˣ)))⁻¹ := by
    have h1 := weylElement_xPar (F := rootOperatorFamily .G2) (K := K) l (-1)
    have h2' : wS (-1 : Kˣ) = (wS (1 : Kˣ))⁻¹ :=
      eq_inv_of_mul_eq_one_right wS_one_mul_wS_neg_one
    rw [hw, e1, h2', map_inv] at h1
    rw [map_mul, mul_inv_rev]
    exact eq_mul_inv_of_mul_eq h1.symm
  obtain ⟨j, hj⟩ := g2_exists_odd_cartan l
  have hnc := g2_torus_neg_one_not_central h2 l j hj
  rw [e2] at hnc
  exact hnc (inv_mem hcen)

end G2

theorem eq_one_of_mem_center_G2 (n p e : ℕ) (hp : p.Prime) (hfund : IsFundTag .G2)
    (hadm : StatedLieAdmissible .G2 n p e)
    {R : Subgroup (modelUniv .G2 n p e hp).K}
    (hR : R ∈ fundamentalSubgroups .G2 (modelUniv .G2 n p e hp).D)
    {r : (modelUniv .G2 n p e hp).K} (hrR : r ∈ R)
    (hrc : r ∈ Subgroup.center (modelUniv .G2 n p e hp).K) : r = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact eq_one_of_mem_center_of_all_nodes .G2 n p e hp hfund hadm
    (fun k r hr hrk => g2_eq_one_of_mem_center_of_mem_rankOne (K := GaloisField p e) k hr hrk)
    hR hrR hrc

end CFSG.ClassicalInvolution.ModelFacts
