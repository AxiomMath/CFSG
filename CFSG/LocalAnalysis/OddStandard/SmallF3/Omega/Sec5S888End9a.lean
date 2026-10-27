module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallCover
public import CFSG.GH74.Generic.S45.LKCent

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

private noncomputable def slEquivOfRingEquiv {K K' : Type*} [Field K] [Field K']
    (ρ : K ≃+* K') : SL(2, K) ≃* SL(2, K') where
  toFun := Matrix.SpecialLinearGroup.map ρ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map ρ.symm.toRingHom
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  map_mul' := (Matrix.SpecialLinearGroup.map ρ.toRingHom).map_mul

theorem double_cover_sl2 {Pb L : Type} [Group Pb] [Finite Pb] [Group L] (η : Pb →* L)
    (hη : Function.Surjective η) (hcard : Nat.card η.ker = 2) (hcen : η.ker ≤ center Pb)
    (hcomm : η.ker ≤ commutator Pb) {p n : ℕ} [Fact p.Prime] (hp : p ≠ 2) (h5 : 5 ≤ p ^ n)
    (e : L ≃* PSL(2, GaloisField p n)) : Nonempty (Pb ≃* SL(2, GaloisField p n)) := by
  classical
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h5
  have hcardGF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  haveI : Group.IsPerfect (PSL(2, GaloisField p n)) :=
    CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three (GaloisField p n)
      (by rw [hcardGF]; omega)
  haveI hLperf : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hPbperf : Group.IsPerfect Pb := by
    refine ⟨?_⟩
    have hmap : (commutator Pb).map η = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective η hη, ← _root_.commutator_def]
      exact hLperf.commutator_eq_top
    have hthis := Subgroup.comap_map_eq_self (f := η) (H := commutator Pb) hcomm
    rw [hmap, Subgroup.comap_top] at hthis
    exact hthis.symm
  obtain ⟨_, _, K, _, _, hK, ⟨eK⟩⟩ :=
    CFSG.ComponentClassification.CatFactsSmall.exists_sl2_equiv_of_perfect hPbperf hη hcen hcard hp
      (CFSG.GH74.Generic.S45.lieModel_of_mulEquiv_psl2 p n h5 e)
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  have hcardEq : Fintype.card K = Fintype.card (GaloisField p n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hcardGF]
  exact ⟨eK.trans (slEquivOfRingEquiv (FiniteField.ringEquivOfCardEq hcardEq))⟩

end CFSG.OddStandard.SmallF3.Omega
