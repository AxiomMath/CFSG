module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.OpenTranslation

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Open CFSG.Fischer

noncomputable abbrev localSU : Subgroup (GL (Fin 6) (GaloisField 2 2)) :=
  fischerMatrixGroup fun A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2) =>
    A.det = 1 ∧ ∀ x y, fischerHermitianF4 6 (A.mulVec x) (A.mulVec y) = fischerHermitianF4 6 x y

theorem fischerHermitianF4_six_eq (x y : Fin 6 → GaloisField 2 2) :
    fischerHermitianF4 6 x y = hermitian 1 x y := by
  rw [hermitian_one]; rfl

theorem localSU_eq_SU_one : localSU = SU (1 : Matrix (Fin 6) (Fin 6) K) := by
  rw [SU_one_eq]
  unfold localSU fischerMatrixGroup fischerEUSU
  congr 1

noncomputable def localPSUEquiv :
    localSU ⧸ Subgroup.center localSU ≃* PSU (1 : Matrix (Fin 6) (Fin 6) K) :=
  quotientCenterCongr (MulEquiv.subgroupCongr localSU_eq_SU_one)

theorem localPSUEquiv_mk (h : localSU) :
    localPSUEquiv (QuotientGroup.mk h) =
      QuotientGroup.mk (⟨h, localSU_eq_SU_one ▸ h.2⟩ : SU (1 : Matrix (Fin 6) (Fin 6) K)) := by
  unfold localPSUEquiv
  rw [quotientCenterCongr_mk]
  rfl

theorem psu6Input : PSU6Input := by
  intro G _ D hP d hd hU
  obtain ⟨φ, hφ⟩ := hU
  refine ⟨hP, d, hd, 1, isNondegenerateHermitian_one, φ.trans localPSUEquiv, ?_⟩
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h, ⟨v, ⟨hv0, hvv⟩, hvx⟩, hgh⟩ := (hφ g).1 hg
    refine ⟨⟨h, localSU_eq_SU_one ▸ h.2⟩, ?_, v, hv0, ?_, ?_⟩
    · show _ = localPSUEquiv (φ g)
      rw [hgh, localPSUEquiv_mk]
    · rw [← fischerHermitianF4_six_eq]; exact hvv
    · intro x
      rw [← fischerHermitianF4_six_eq]
      exact hvx x
  · rintro ⟨u, rfl, v, hv0, hvv, hux⟩
    let h : localSU := ⟨u, localSU_eq_SU_one.symm ▸ u.2⟩
    have hT : (h : GL (Fin 6) (GaloisField 2 2)) ∈ fischerTransvections (fischerHermitianF4 6)
        fun v => v ≠ 0 ∧ fischerHermitianF4 6 v v = 0 := by
      refine ⟨v, ⟨hv0, ?_⟩, fun x => ?_⟩
      · rw [fischerHermitianF4_six_eq]; exact hvv
      · rw [fischerHermitianF4_six_eq]; exact hux x
    refine ⟨φ.symm (QuotientGroup.mk h), (hφ _).2 ⟨h, hT, by rw [MulEquiv.apply_symm_apply]⟩, ?_⟩
    show localPSUEquiv (φ (φ.symm _)) = _
    rw [MulEquiv.apply_symm_apply, localPSUEquiv_mk]

end CFSG.Fischer.Classification
