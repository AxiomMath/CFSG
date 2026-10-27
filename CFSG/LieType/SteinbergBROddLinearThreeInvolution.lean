module

public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
public import CFSG.LieType.SteinbergBRGL2ThreeCore
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock

public section

namespace CFSG.LieType.SteinbergBR.OddLinearThreeInv

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Wreathed.OddLinearThreeCentralizerCore

variable {K : Type*} [Field K]

@[expose] noncomputable def coordEquiv {V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin 2) K V) : (V ≃ₗ[K] V) ≃* GL (Fin 2) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)

theorem det_coordEquiv {V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin 2) K V) (a : V ≃ₗ[K] V) :
    GeneralLinearGroup.det (coordEquiv b a) = LinearEquiv.det a := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, LinearEquiv.coe_det]
  exact LinearMap.det_toMatrix b (a : V →ₗ[K] V)

@[expose] noncomputable def slEquiv {V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin 2) K V) :
    (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).ker ≃* SpecialLinearGroup (Fin 2) K :=
  (((coordEquiv b).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (det_coordEquiv b a).trans ha
    · intro hg
      refine ⟨(coordEquiv b).symm g, ?_, (coordEquiv b).apply_symm_apply g⟩
      show LinearEquiv.det ((coordEquiv b).symm g) = 1
      rw [← det_coordEquiv b, MulEquiv.apply_symm_apply]
      exact hg))).trans SpecialLinearGroup.toGLKerEquiv.symm

end CFSG.LieType.SteinbergBR.OddLinearThreeInv

namespace CFSG.LieType

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Wreathed.OddLinearThreeCentralizerCore CFSG.LieType.SteinbergBR
  CFSG.LieType.SteinbergBR.OddLinearThreeInv

theorem unique_odd_linear_three_involution_centralizer_component_or_unique_core_involution
    {K : Type*} [Field K] [Finite K] (hK : Odd (Nat.card K)) (hq : 3 ≤ Nat.card K)
    (t : projectiveSL 3 K) (ht : orderOf t = 2) :
    (5 ≤ Nat.card K → ∃ J : Subgroup (Subgroup.centralizer ({t} : Set (projectiveSL 3 K))),
      J.Normal ∧ Nonempty (J ≃* SpecialLinearGroup (Fin 2) K) ∧ CFSG.IsComponent J) ∧
    (Nat.card K = 3 →
      Nonempty (Subgroup.centralizer ({t} : Set (projectiveSL 3 K)) ≃* GL (Fin 2) K) ∧
      Nat.card (Subgroup.centralizer ({t} : Set (projectiveSL 3 K))) = 48 ∧
      Nat.card (CFSG.pCore 2 (Subgroup.centralizer ({t} : Set (projectiveSL 3 K)))) = 8 ∧
      ∀ x ∈ CFSG.pCore 2 (Subgroup.centralizer ({t} : Set (projectiveSL 3 K))),
        orderOf x = 2 ↔ x = ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩) := by
  obtain ⟨z, hz, hzt, -, hdm, -, -, -, -, hsurj, hker, -⟩ :=
    odd_linear_three_involution_centralizer_core K hK hq (scalars 3 K) (scalars_le_center 3 K)
      t ht
  set φ := targetQuotientCentralizer K hK (scalars 3 K) z hz t hzt
  let b : Module.Basis (Fin 2) K (minusSpace (matrixAction K z).toLinearMap) :=
    Module.finBasisOfFinrankEq K _ hdm
  refine ⟨fun hq5 => ?_, fun hq3 => ?_⟩
  ·
    let SLk := (LinearEquiv.det : (minusSpace (matrixAction K z).toLinearMap ≃ₗ[K]
      minusSpace (matrixAction K z).toLinearMap) →* Kˣ).ker
    have hinj : Function.Injective (φ.comp SLk.subtype) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, ha⟩ h
      obtain ⟨c, hc3, -, rfl⟩ := (hker a).1 h
      have hc2 : c ^ 2 = 1 := (minus_scalar_det K hK z hz c).symm.trans ha
      have hc1 : c = 1 := by
        calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
          _ = 1 := by rw [hc3, hc2, inv_one, one_mul]
      subst hc1
      exact Subtype.ext (LinearEquiv.ext fun x => one_smul Kˣ x)
    have hJr : (φ.comp SLk.subtype).range = SLk.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    let eJ : SLk.map φ ≃* SpecialLinearGroup (Fin 2) K :=
      ((MulEquiv.subgroupCongr hJr).symm.trans (MonoidHom.ofInjective hinj).symm).trans
        (slEquiv b)
    have hnormal : (SLk.map φ).Normal := (MonoidHom.normal_ker _).map φ hsurj
    have h4 : ∃ s : Finset K, s.card = 4 := by
      have := Fintype.ofFinite K
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
      exact ⟨s, hs⟩
    exact ⟨SLk.map φ, hnormal, ⟨eJ⟩,
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eJ).2
        (CFSG.RankThree.Classical.isQuasisimple_SL2 h4), hnormal.isSubnormal⟩
  ·
    have := Fintype.ofFinite K
    have hK3 : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hq3]
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro a h
      obtain ⟨c, hc3, -, rfl⟩ := (hker a).1 h
      have hc1 : c = 1 := by
        have hpow := FiniteField.pow_card (c : K)
        rw [hK3, ← Units.val_pow_eq_pow_val, hc3, Units.val_one] at hpow
        exact Units.ext hpow.symm
      subst hc1
      exact LinearEquiv.ext fun x => one_smul Kˣ x
    let Ψ : Subgroup.centralizer ({t} : Set (projectiveSL 3 K)) ≃* GL (Fin 2) K :=
      (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm.trans (coordEquiv b)
    let eK : K ≃+* ZMod 3 := (ZMod.ringEquivOfPrime K Nat.prime_three hK3).symm
    let Θ : Subgroup.centralizer ({t} : Set (projectiveSL 3 K)) ≃* GL2Three.G23 :=
      Ψ.trans (Units.mapEquiv eK.mapMatrix.toMulEquiv)
    have hcardC : Nat.card (Subgroup.centralizer ({t} : Set (projectiveSL 3 K))) = 48 := by
      rw [Nat.card_congr Θ.toEquiv, GL2Three.card_G23]
    have hO2 : (CFSG.pCore 2 (Subgroup.centralizer ({t} : Set (projectiveSL 3 K)))).map
        Θ.toMonoidHom = GL2Three.quatQ := by
      rw [pCore_map_equiv 2 Θ, GL2Three.pCore_two_eq]
    set t' : Subgroup.centralizer ({t} : Set (projectiveSL 3 K)) :=
      ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ with ht'
    have ht'2 : orderOf t' = 2 := by rw [ht', Subgroup.orderOf_mk, ht]
    have ht'O : t' ∈ CFSG.pCore 2 (Subgroup.centralizer ({t} : Set (projectiveSL 3 K))) := by
      have hcen : Subgroup.zpowers t' ≤
          Subgroup.center (Subgroup.centralizer ({t} : Set (projectiveSL 3 K))) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
        intro c
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
      have hzp : IsPGroup 2 (Subgroup.zpowers t') :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2, pow_one])
      have hle : Subgroup.zpowers t' ≤
          CFSG.pCore 2 (Subgroup.centralizer ({t} : Set (projectiveSL 3 K))) :=
        le_sSup ⟨Subgroup.normal_of_le_center hcen, hzp⟩
      exact hle (Subgroup.mem_zpowers t')
    have hmemQ : ∀ x ∈ CFSG.pCore 2 (Subgroup.centralizer ({t} : Set (projectiveSL 3 K))),
        Θ x ∈ GL2Three.quatQ := fun x hx => hO2 ▸ Subgroup.mem_map_of_mem _ hx
    refine ⟨⟨Ψ⟩, hcardC, ?_, fun x hx => ?_⟩
    · rw [← Subgroup.card_map_of_injective (f := Θ.toMonoidHom) Θ.injective, hO2,
        GL2Three.card_quatQ]
    · have hΘt : Θ t' = -1 := (GL2Three.mem_quatQ_orderOf (hmemQ t' ht'O)).1
        (by rw [MulEquiv.orderOf_eq, ht'2])
      rw [← MulEquiv.orderOf_eq Θ, GL2Three.mem_quatQ_orderOf (hmemQ x hx), ← hΘt]
      exact Θ.injective.eq_iff

end CFSG.LieType
