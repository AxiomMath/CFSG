module
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Wreathed.CentralizerFullQuotient

public noncomputable section
namespace CFSG.Wreathed.TwoCommutingComponentCover
open scoped Classical
universe u v
variable {G : Type u} [Group G]

@[expose] def conjugatedSylow (S : Sylow 2 G) (g : G) : Sylow 2 G := g • S

@[expose] def conjugatedCoordinates {m : ℕ} (S : Sylow 2 G)
    (e : S ≃* Wreath m) (g : G) : conjugatedSylow S g ≃* Wreath m :=
  (S.equivSMul g).symm.trans e

theorem conjugated_wreathModelHom_apply {m : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath m) (g : G) (w : Wreath m) :
    wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g) w =
      g * wreathModelHom S e w * g⁻¹ := by
  rfl

theorem centralizer_map_equiv {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map phi.toMonoidHom =
      Subgroup.centralizer ({phi x} : Set H) := by
  ext h
  constructor
  · rintro ⟨a, ha, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change phi a * phi x = phi x * phi a
    simpa only [map_mul] using congrArg phi (Subgroup.mem_centralizer_singleton_iff.mp ha)
  · intro hh
    refine Subgroup.mem_map.mpr ⟨phi.symm h, ?_, phi.apply_symm_apply h⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply phi.injective
    simpa only [map_mul, phi.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp hh

@[expose] def centralizerEquiv {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃* Subgroup.centralizer ({phi x} : Set H) :=
  ((Subgroup.centralizer ({x} : Set G)).equivMapOfInjective
    phi.toMonoidHom phi.injective).trans
      (MulEquiv.subgroupCongr (centralizer_map_equiv phi x))

theorem centralizerEquiv_coe {H : Type v} [Group H] (phi : G ≃* H) (x : G)
    (c : Subgroup.centralizer ({x} : Set G)) : (centralizerEquiv phi x c : H) = phi c := rfl

theorem centralizerEquiv_symm_coe {H : Type v} [Group H] (phi : G ≃* H) (x : G)
    (c : Subgroup.centralizer ({phi x} : Set H)) :
    ((centralizerEquiv phi x).symm c : G) = phi.symm c := by
  apply phi.injective
  rw [phi.apply_symm_apply]
  have hc := congrArg Subtype.val ((centralizerEquiv phi x).apply_symm_apply c)
  exact hc

theorem centralizerEquiv_oddCore {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).map
      (centralizerEquiv phi x).toMonoidHom =
        CFSG.oddCore (Subgroup.centralizer ({phi x} : Set H)) :=
  CFSG.ComponentClassification.OddCore.equiv_invariant (centralizerEquiv phi x)

@[expose] def reducedCentralizerEquiv {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ⧸ CFSG.oddCore (Subgroup.centralizer ({x} : Set G)) ≃*
      Subgroup.centralizer ({phi x} : Set H) ⧸
        CFSG.oddCore (Subgroup.centralizer ({phi x} : Set H)) :=
  QuotientGroup.congr _ _ (centralizerEquiv phi x) (centralizerEquiv_oddCore phi x)

theorem reducedCentralizerEquiv_mk {H : Type v} [Group H] (phi : G ≃* H) (x : G)
    (c : Subgroup.centralizer ({x} : Set G)) :
    reducedCentralizerEquiv phi x (QuotientGroup.mk' (CFSG.oddCore _) c) =
      QuotientGroup.mk' (CFSG.oddCore _) (centralizerEquiv phi x c) := by
  exact QuotientGroup.congr_mk' _ _ _ _ c

theorem reducedCentralizerEquiv_symm_mk {H : Type v} [Group H] (phi : G ≃* H) (x : G)
    (c : Subgroup.centralizer ({x} : Set G)) :
    (reducedCentralizerEquiv phi x).symm
      (QuotientGroup.mk' (CFSG.oddCore _) (centralizerEquiv phi x c)) =
      QuotientGroup.mk' (CFSG.oddCore _) c := by
  rw [← reducedCentralizerEquiv_mk]
  exact MulEquiv.symm_apply_apply _ _

theorem reducedCentralizerEquiv_layer {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    (CFSG.layer (Subgroup.centralizer ({x} : Set G) ⧸
      CFSG.oddCore (Subgroup.centralizer ({x} : Set G)))).map
        (reducedCentralizerEquiv phi x).toMonoidHom =
      CFSG.layer (Subgroup.centralizer ({phi x} : Set H) ⧸
        CFSG.oddCore (Subgroup.centralizer ({phi x} : Set H))) := by
  rw [CFSG.layer_eq_componentClassification, CFSG.layer_eq_componentClassification]
  exact CFSG.ComponentClassification.Layer.equiv_invariant (reducedCentralizerEquiv phi x)

theorem fitting_map_equiv {H : Type v} [Group H] (phi : G ≃* H) :
    (CFSG.ComponentClassification.Fitting.subgroup G).map phi.toMonoidHom =
      CFSG.ComponentClassification.Fitting.subgroup H :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv phi


theorem generalizedFitting_map_equiv {H : Type v} [Group H] (phi : G ≃* H) :
    (CFSG.generalizedFitting G).map phi.toMonoidHom = CFSG.generalizedFitting H :=
  CFSG.WholeGroup.generalizedFitting_map_mulEquiv phi

@[expose] def originalConjugatedCentralizerEquiv
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    involutionCentralizer n S e ≃*
      involutionCentralizer n (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  centralizerEquiv (MulAut.conj g) (wreathModelHom S e (Original.x (2 ^ n)))

theorem originalConjugatedCentralizerEquiv_coe
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G)
    (c : involutionCentralizer n S e) :
    (originalConjugatedCentralizerEquiv n S e g c : G) = g * (c : G) * g⁻¹ := rfl

theorem originalConjugatedCentralizerEquiv_symm_coe
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G)
    (c : involutionCentralizer n (conjugatedSylow S g) (conjugatedCoordinates S e g)) :
    ((originalConjugatedCentralizerEquiv n S e g).symm c : G) =
      g⁻¹ * (c : G) * g := by
  exact centralizerEquiv_symm_coe (MulAut.conj g) _ c

theorem originalConjugatedCentralizerEquiv_oddCore
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    (centralizerOddCore n S e).map (originalConjugatedCentralizerEquiv n S e g).toMonoidHom =
      centralizerOddCore n (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  CFSG.ComponentClassification.OddCore.equiv_invariant _

@[expose] def originalConjugatedReducedEquiv
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    centralizerOddCoreQuotient n S e ≃*
      centralizerOddCoreQuotient n (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  reducedCentralizerEquiv (MulAut.conj g) (wreathModelHom S e (Original.x (2 ^ n)))

theorem originalConjugatedReducedEquiv_mk
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G)
    (c : involutionCentralizer n S e) :
    originalConjugatedReducedEquiv n S e g (centralizerOddCoreMap n S e c) =
      centralizerOddCoreMap n (conjugatedSylow S g) (conjugatedCoordinates S e g)
        (originalConjugatedCentralizerEquiv n S e g c) := by
  exact reducedCentralizerEquiv_mk _ _ _

theorem originalConjugatedReducedEquiv_symm_mk
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G)
    (c : involutionCentralizer n (conjugatedSylow S g) (conjugatedCoordinates S e g)) :
    (originalConjugatedReducedEquiv n S e g).symm
      (centralizerOddCoreMap n (conjugatedSylow S g) (conjugatedCoordinates S e g) c) =
      centralizerOddCoreMap n S e ((originalConjugatedCentralizerEquiv n S e g).symm c) := by
  have h := originalConjugatedReducedEquiv_mk n S e g
    ((originalConjugatedCentralizerEquiv n S e g).symm c)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h]
  exact MulEquiv.symm_apply_apply _ _

theorem originalConjugatedReducedEquiv_layer
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    (CFSG.layer (centralizerOddCoreQuotient n S e)).map
      (originalConjugatedReducedEquiv n S e g).toMonoidHom =
        CFSG.layer (centralizerOddCoreQuotient n
          (conjugatedSylow S g) (conjugatedCoordinates S e g)) :=
  reducedCentralizerEquiv_layer _ _

theorem originalConjugatedReducedEquiv_center [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    (centralizerFullCenterImage n hn S e).map
      (originalConjugatedReducedEquiv n S e g).toMonoidHom =
        centralizerFullCenterImage n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) := by
  rw [← centralizerOddCoreQuotient_center_eq_fullCenterImage,
    ← centralizerOddCoreQuotient_center_eq_fullCenterImage]
  exact Subgroup.map_center_eq (originalConjugatedReducedEquiv n S e g)

@[expose] def originalConjugatedFullEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    centralizerFullQuotient n hn S e ≃*
      centralizerFullQuotient n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  QuotientGroup.congr _ _ (originalConjugatedReducedEquiv n S e g)
    (originalConjugatedReducedEquiv_center n hn S e g)

theorem originalConjugatedFullEquiv_mk [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G)
    (h : centralizerOddCoreQuotient n S e) :
    originalConjugatedFullEquiv n hn S e g (centralizerFullQuotientMap n hn S e h) =
      centralizerFullQuotientMap n hn (conjugatedSylow S g) (conjugatedCoordinates S e g)
        (originalConjugatedReducedEquiv n S e g h) := by
  exact QuotientGroup.congr_mk' _ _ _ _ h

theorem originalConjugatedFullEquiv_symm_mk [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G)
    (h : centralizerOddCoreQuotient n (conjugatedSylow S g) (conjugatedCoordinates S e g)) :
    (originalConjugatedFullEquiv n hn S e g).symm
      (centralizerFullQuotientMap n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) h) =
      centralizerFullQuotientMap n hn S e ((originalConjugatedReducedEquiv n S e g).symm h) := by
  have hh := originalConjugatedFullEquiv_mk n hn S e g
    ((originalConjugatedReducedEquiv n S e g).symm h)
  rw [MulEquiv.apply_symm_apply] at hh
  rw [← hh]
  exact MulEquiv.symm_apply_apply _ _

end CFSG.Wreathed.TwoCommutingComponentCover


