module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open Matrix

theorem closure_unitary_eq_statedSU (n : ℕ) :
    Subgroup.closure {A : GL (Fin n) (GaloisField 2 2) |
      (Matrix.of fun i j => (A : Matrix (Fin n) (Fin n) (GaloisField 2 2)) j i ^ 2) *
          (A : Matrix (Fin n) (Fin n) (GaloisField 2 2)) = 1 ∧
        GeneralLinearGroup.det A = 1} = StatedSU n 2 (GaloisField 2 2) := by
  unfold StatedSU
  congr 1
  ext A
  simp only [Set.mem_ofPred_eq]
  rw [and_comm]
  refine and_congr ?_ Iff.rfl
  rw [← GeneralLinearGroup.val_det_apply, Units.val_eq_one]

theorem timmesfeldPSU_eq_map (n : ℕ) :
    timmesfeldPSU n = (StatedSU n 2 (GaloisField 2 2)).map ProjGenLinGroup.mk := by
  unfold timmesfeldPSU
  rw [closure_unitary_eq_statedSU]

noncomputable def timmesfeldPSUEquivStatedProj (n : ℕ) :
    timmesfeldPSU n ≃* StatedProj (StatedSU n 2 (GaloisField 2 2)) := by
  set H := StatedSU n 2 (GaloisField 2 2) with hH
  let f : H →* ProjGenLinGroup (Fin n) (GaloisField 2 2) :=
    (ProjGenLinGroup.mk : GL (Fin n) (GaloisField 2 2) →* _).domRestrict H
  have hker : f.ker = (StatedScalars (Fin n) (GaloisField 2 2)).subgroupOf H := by
    rw [MonoidHom.ker_domRestrict]
    congr 1
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact QuotientGroup.ker_mk' _
  have hrange : (timmesfeldPSU n : Subgroup _) = f.range := by
    rw [timmesfeldPSU_eq_map, MonoidHom.domRestrict_range]
  exact (MulEquiv.subgroupCongr hrange).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))

theorem lieModel_psu_two_of_mulEquiv {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (e : G ≃* timmesfeldPSU n) : LieModel G .PSU n 2 1 := by
  refine Or.inl ⟨by simp [classicalTags], ⟨Nat.prime_two, le_rfl, by omega, ?_⟩,
    GaloisField 2 2, inferInstance, inferInstance, ?_,
    ⟨e.trans (timmesfeldPSUEquivStatedProj n)⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · rw [GaloisField.card 2 2 (by norm_num)]
    norm_num

end CFSG.GF2Type
