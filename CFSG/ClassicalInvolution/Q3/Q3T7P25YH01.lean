module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjMain
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

open scoped MatrixGroups
open CFSG.ClassicalInvolution.Q3.Q3T6

open Matrix in
noncomputable def slMapEquivThree {R S : Type} [CommRing R] [CommRing S] (r : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) where
  toFun := SpecialLinearGroup.map (r : R →+* S)
  invFun := SpecialLinearGroup.map (r.symm : S →+* R)
  left_inv x := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  right_inv x := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  map_mul' x y := map_mul _ x y

theorem sl2PerfectAut3 (P : Subgroup (MulAut SL(2, GaloisField 3 1))) (hP : ⁅P, P⁆ = P) :
    2 * Nat.card P ≤ Nat.card SL(2, GaloisField 3 1) := by
  obtain ⟨r⟩ := Q3Z.nonempty_ringEquiv_galoisField_three
  let Φ : SL(2, ZMod 3) ≃* SL(2, GaloisField 3 1) := slMapEquivThree r
  have hc : Nat.card (MulAut SL(2, GaloisField 3 1)) = 24 := by
    rw [← sl2Three_card_mulAut]
    exact Nat.card_congr (MulAut.congr Φ.symm).toEquiv
  have hSL : Nat.card SL(2, GaloisField 3 1) = 24 := by
    rw [← Aut.sl2Three_natCard]
    exact Nat.card_congr Φ.symm.toEquiv
  have hs : Group.IsSolvable (MulAut SL(2, GaloisField 3 1)) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hc]; norm_num)
  have hsP : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective P.subtype_injective
  have hbot : P = ⊥ := by
    by_contra hne
    have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := P)
    have hcP : commutator P = ⊤ := by
      apply Subgroup.map_injective P.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        hP]
    rw [hcP] at hlt
    exact lt_irrefl _ hlt
  rw [hbot, Subgroup.card_bot, hSL]
  norm_num

end CFSG.ClassicalInvolution.Q3.Q3T7P25
