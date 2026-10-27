module

public import CFSG.Blueprint.Catalog

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {K K' : Type} [Field K] [Field K']

@[expose] def glMapEquiv (φ : K ≃+* K') :
    Matrix.GeneralLinearGroup (Fin 4) K ≃* Matrix.GeneralLinearGroup (Fin 4) K' :=
  Units.mapEquiv (φ.mapMatrix : Matrix (Fin 4) (Fin 4) K ≃+* Matrix (Fin 4) (Fin 4) K').toMulEquiv

theorem coe_glMapEquiv (φ : K ≃+* K') (g : Matrix.GeneralLinearGroup (Fin 4) K) :
    ((glMapEquiv φ g : Matrix.GeneralLinearGroup (Fin 4) K') : Matrix (Fin 4) (Fin 4) K') =
      (g : Matrix (Fin 4) (Fin 4) K).map φ :=
  rfl

theorem suzukiS_map (a : ℕ) (φ : K ≃+* K') (u v : K) :
    (suzukiS a u v).map φ = suzukiS a (φ u) (φ v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN, map_add, map_mul, map_pow]

theorem suzukiD_map (a : ℕ) (φ : K ≃+* K') (l : Kˣ) :
    (suzukiD a l).map φ = suzukiD a (Units.map (φ : K →* K') l) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiD, Matrix.diagonal]

theorem suzukiW_map (φ : K ≃+* K') : (suzukiW K).map φ = suzukiW K' := by
  ext i j
  simp only [suzukiW, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem suzukiGroup_map_glMapEquiv (a : ℕ) (φ : K ≃+* K') :
    (suzukiGroup a K).map (glMapEquiv φ : _ →* Matrix.GeneralLinearGroup (Fin 4) K') =
      suzukiGroup a K' := by
  rw [suzukiGroup, suzukiGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (glMapEquiv φ g : Matrix.GeneralLinearGroup (Fin 4) K') ∈ _
    rcases hg with ⟨u, v, h⟩ | ⟨l, h⟩ | h
    · exact Or.inl ⟨φ u, φ v, by rw [coe_glMapEquiv, h, suzukiS_map]⟩
    · exact Or.inr (Or.inl ⟨Units.map (φ : K →* K') l, by rw [coe_glMapEquiv, h, suzukiD_map]⟩)
    · exact Or.inr (Or.inr (by rw [coe_glMapEquiv, h, suzukiW_map]))
  · intro hg
    refine ⟨(glMapEquiv φ).symm g, ?_, by simp⟩
    have key : ((glMapEquiv φ).symm g : Matrix (Fin 4) (Fin 4) K).map φ =
        (g : Matrix (Fin 4) (Fin 4) K') := by
      rw [← coe_glMapEquiv, MulEquiv.apply_symm_apply]
    have hinj : Function.Injective fun A : Matrix (Fin 4) (Fin 4) K => A.map φ :=
      fun A B hAB => by
        ext i j
        have := congrFun (congrFun hAB i) j
        simpa using this
    rcases hg with ⟨u, v, h⟩ | ⟨l, h⟩ | h
    · refine Or.inl ⟨φ.symm u, φ.symm v, hinj ?_⟩
      simp only
      rw [key, h, suzukiS_map, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    · refine Or.inr (Or.inl ⟨Units.map (φ.symm : K' →* K) l, hinj ?_⟩)
      simp only
      rw [key, h, suzukiD_map]
      congr 1
      ext
      simp
    · refine Or.inr (Or.inr (hinj ?_))
      simp only
      rw [key, h, suzukiW_map]

@[expose] def suzukiGroupMapEquiv (a : ℕ) (φ : K ≃+* K') : suzukiGroup a K ≃* suzukiGroup a K' :=
  ((glMapEquiv φ).subgroupMap (suzukiGroup a K)).trans
    (MulEquiv.subgroupCongr (suzukiGroup_map_glMapEquiv a φ))

end CFSG.Blueprint.EvenSource
