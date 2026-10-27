module

public import CFSG.Adapters.TauCetiExceptional.FrameworkClosure
public import CFSG.Adapters.TauCetiExceptional.BigCellCore
public import CFSG.Adapters.TauCetiExceptional.MinusculeE6
public import CFSG.Adapters.TauCetiExceptional.MinusculeE7
public import TauCeti.Algebra.Lie.E7.Minuscule.Generation

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti
  TauCeti.UniversalEnvelopingAlgebra WithConv

universe u w

theorem aeval_eq_evalMat {A : Type*} [CommRing A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A)
    (P : MvPolynomial (Fin n × Fin n) ℤ) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2) P = BigCell.evalMat M P := by
  rw [MvPolynomial.aeval_def, algebraMap_int_eq]
  rfl

theorem fracVanishingIdeal_le_kostantGeneratedDefiningIdeal {L : Type u} [LieRing L]
    [LieAlgebra ℚ L] {I : Type w} {κ : Type*} {V : Type} [AddCommGroup V] [Module ℚ V]
    (e : I → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ M)
    (S : Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ] ℚ)))
    (hS : ∀ (i : I) (c : ℚ), (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) n).symm
      (kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm (Multiplicative.ofAdd c))) ∈ S) :
    fracVanishingIdeal (R := ℤ) (K := ℚ) S ≤ kostantGeneratedDefiningIdeal e h ρ M hM hnil b := by
  rw [le_kostantGeneratedDefiningIdeal_iff]
  intro j x hx
  rw [RingHom.mem_ker]
  apply symmetricAlgebra_eq_zero_of_forall_rat
  intro c
  have hv : ((GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) n).symm
      (kostantRootSubgroupMatrix e h ρ M hM j (hnil j) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm
          (Multiplicative.ofAdd c)))).ofConv x = 0 :=
    (mem_fracVanishingIdeal _ x).mp hx ⟨_, hS j c⟩
  have hpt := pointsMulEquiv_kostantRootSubgroupCoordinateMap e h ρ M hM j (hnil j) b ℚ
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm (Multiplicative.ofAdd c))
  rw [← hpt, GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_pointToGeneralLinear] at hv
  exact hv

@[expose] def e6RatPoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ 27 →ₐ[ℤ] ℚ)) :=
  ((e6Data_valid.minGroup ℚ).map (toMat e6Match.lab ℚ).toMonoidHom).map
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 27).symm.toMonoidHom

@[expose] def e6NativeVanishingIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ 27) :=
  fracVanishingIdeal (R := ℤ) (K := ℚ) e6RatPoints

theorem pointsMulEquiv_symm_toMat_mem_e6RatPoints
    (g : e6Data_valid.minGroup ℚ) :
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 27).symm (toMat e6Match.lab ℚ g) ∈
      e6RatPoints :=
  ⟨toMat e6Match.lab ℚ g, ⟨g, g.2, rfl⟩, rfl⟩

theorem e6NativeVanishingIdeal_le_definingIdeal :
    e6NativeVanishingIdeal ≤ E6Minuscule.definingIdeal := by
  rw [E6Minuscule.definingIdeal_eq_kostantGeneratedDefiningIdeal]
  refine fracVanishingIdeal_le_kostantGeneratedDefiningIdeal _ _ _ _ _ _ _ _ fun j c => ?_
  rw [← E6Minuscule.coe_rootSubgroupPoints]
  rcases j with i | i
  · rw [e6_rootSubgroupPoints_inl, rootUnit_eq_xu]
    exact pointsMulEquiv_symm_toMat_mem_e6RatPoints ⟨_, e6Data_valid.xu_mem ℚ _ c⟩
  · rw [e6_rootSubgroupPoints_inr, rootUnit_eq_xu]
    exact pointsMulEquiv_symm_toMat_mem_e6RatPoints ⟨_, e6Data_valid.xu_mem ℚ _ c⟩

theorem e6_evalMat_eq_zero
    (P : MvPolynomial (Fin 27 × Fin 27) ℤ)
    (hP : ∀ g : e6Data_valid.minGroup ℚ,
      BigCell.evalMat ((toMat e6Match.lab ℚ g : Matrix.GeneralLinearGroup (Fin 27) ℚ) :
        Matrix (Fin 27) (Fin 27) ℚ) P = 0)
    (A : Type*) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin 27) A)
    (hg : g ∈ E6Minuscule.points A) :
    BigCell.evalMat (g : Matrix (Fin 27) (Fin 27) A) P = 0 := by
  have hx : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 27
      (GeneralLinear.coordinateRingMap ℤ 27 P) ∈ e6NativeVanishingIdeal := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨_, ⟨g', hg', rfl⟩, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) 27).symm
      (toMat e6Match.lab ℚ g')).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat]
    exact hP ⟨g', hg'⟩
  have := (E6Minuscule.mem_points_iff A g).mp hg _ (e6NativeVanishingIdeal_le_definingIdeal hx)
  rwa [GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat] at this

@[expose] def e7RatPoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ 56 →ₐ[ℤ] ℚ)) :=
  ((e7Data_valid.minGroup ℚ).map (toMat e7Match.lab ℚ).toMonoidHom).map
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 56).symm.toMonoidHom

@[expose] def e7NativeVanishingIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ 56) :=
  fracVanishingIdeal (R := ℤ) (K := ℚ) e7RatPoints

theorem pointsMulEquiv_symm_toMat_mem_e7RatPoints
    (g : e7Data_valid.minGroup ℚ) :
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 56).symm (toMat e7Match.lab ℚ g) ∈
      e7RatPoints :=
  ⟨toMat e7Match.lab ℚ g, ⟨g, g.2, rfl⟩, rfl⟩

theorem e7NativeVanishingIdeal_le_definingIdeal :
    e7NativeVanishingIdeal ≤ E7Minuscule.definingIdeal := by
  rw [E7Minuscule.definingIdeal_eq_kostantGeneratedDefiningIdeal]
  refine fracVanishingIdeal_le_kostantGeneratedDefiningIdeal _ _ _ _ _ _ _ _ fun j c => ?_
  rw [← E7Minuscule.coe_rootSubgroupPoints]
  rcases j with i | i
  · rw [e7_rootSubgroupPoints_inl, rootUnit_eq_xu]
    exact pointsMulEquiv_symm_toMat_mem_e7RatPoints ⟨_, e7Data_valid.xu_mem ℚ _ c⟩
  · rw [e7_rootSubgroupPoints_inr, rootUnit_eq_xu]
    exact pointsMulEquiv_symm_toMat_mem_e7RatPoints ⟨_, e7Data_valid.xu_mem ℚ _ c⟩

theorem e7_evalMat_eq_zero
    (P : MvPolynomial (Fin 56 × Fin 56) ℤ)
    (hP : ∀ g : e7Data_valid.minGroup ℚ,
      BigCell.evalMat ((toMat e7Match.lab ℚ g : Matrix.GeneralLinearGroup (Fin 56) ℚ) :
        Matrix (Fin 56) (Fin 56) ℚ) P = 0)
    (A : Type*) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin 56) A)
    (hg : g ∈ E7Minuscule.points A) :
    BigCell.evalMat (g : Matrix (Fin 56) (Fin 56) A) P = 0 := by
  have hx : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 56
      (GeneralLinear.coordinateRingMap ℤ 56 P) ∈ e7NativeVanishingIdeal := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨_, ⟨g', hg', rfl⟩, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) 56).symm
      (toMat e7Match.lab ℚ g')).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat]
    exact hP ⟨g', hg'⟩
  have := (E7Minuscule.mem_points_iff A g).mp hg _ (e7NativeVanishingIdeal_le_definingIdeal hx)
  rwa [GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat] at this

end CFSG.TauCetiBridge.Minuscule
