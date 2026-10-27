module
public import CFSG.CharacterTheory.Wreathed.TwoCommutingComponentCoverConjugation
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient

public noncomputable section
namespace CFSG.Wreathed.TwoCommutingComponentCover
open scoped Classical
universe u
variable {G : Type u} [Group G]

theorem originalConjugatedFullEquiv_simpleLayer [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    (centralizerSimpleLayer n hn S e).map (originalConjugatedFullEquiv n hn S e g).toMonoidHom =
      centralizerSimpleLayer n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  generalizedFitting_map_equiv _

@[expose] def originalConjugatedSimpleLayerEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    centralizerSimpleLayer n hn S e ≃*
      centralizerSimpleLayer n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  ((originalConjugatedFullEquiv n hn S e g).subgroupMap (centralizerSimpleLayer n hn S e)).trans
    (MulEquiv.subgroupCongr (originalConjugatedFullEquiv_simpleLayer n hn S e g))

theorem originalConjugatedSimpleLayerEquiv_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G)
    (l : centralizerSimpleLayer n hn S e) :
    (originalConjugatedSimpleLayerEquiv n hn S e g l :
      centralizerFullQuotient n hn (conjugatedSylow S g) (conjugatedCoordinates S e g)) =
        originalConjugatedFullEquiv n hn S e g l := rfl

theorem original_conjugated_nonSym4 [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) (g : G) :
    ¬ Nonempty (centralizerFullQuotient n hn (conjugatedSylow S g)
      (conjugatedCoordinates S e g) ≃* Equiv.Perm (Fin 4)) := by
  rintro ⟨a⟩
  exact hfour ⟨(originalConjugatedFullEquiv n hn S e g).trans a⟩

theorem original_conjugated_same_PSL2_model
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) (g : G) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn (conjugatedSylow S g) (conjugatedCoordinates S e g))
        .PSL 2 p f := by
  rcases hmodel with ⟨hadm, F, hF, hfinite, hcard, ⟨a⟩⟩
  exact ⟨hadm, F, hF, hfinite, hcard,
    ⟨(originalConjugatedSimpleLayerEquiv n hn S e g).symm.trans a⟩⟩

theorem original_involution_conjugator [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2) :
    ∃ g : G, wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y := by
  have hx : orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2 :=
    (orderOf_injective _ (wreathModelHom_injective S e) _).trans
      (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (all_involutions_conjugate_of_simple_wreathed hnonab n hn S e _ y hx hy)
  exact ⟨g, hg⟩

theorem conjugated_centralizer_eq_at_y
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y) :
    involutionCentralizer n (conjugatedSylow S g) (conjugatedCoordinates S e g) =
      Subgroup.centralizer ({y} : Set G) := by
  simp only [involutionCentralizer, hxy]

@[expose] def actualReducedCentralizer (y : G) : Type u :=
  Subgroup.centralizer ({y} : Set G) ⧸ CFSG.oddCore (Subgroup.centralizer ({y} : Set G))

instance actualReducedCentralizerGroup (y : G) : Group (actualReducedCentralizer y) :=
  inferInstanceAs (Group (Subgroup.centralizer ({y} : Set G) ⧸
    CFSG.oddCore (Subgroup.centralizer ({y} : Set G))))

instance actualReducedCentralizerFinite [Finite G] (y : G) :
    Finite (actualReducedCentralizer y) :=
  inferInstanceAs (Finite (Subgroup.centralizer ({y} : Set G) ⧸
    CFSG.oddCore (Subgroup.centralizer ({y} : Set G))))

@[expose] def actualReducedMap (y : G) :
    Subgroup.centralizer ({y} : Set G) →* actualReducedCentralizer y :=
  QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({y} : Set G)))

@[expose] def actualComponentImage (y : G) (K : Subgroup G) :
    Subgroup (actualReducedCentralizer y) :=
  (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).map (actualReducedMap y)

@[expose] def conjugatedAtYCentralizerEquiv
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y) :
    involutionCentralizer n (conjugatedSylow S g) (conjugatedCoordinates S e g) ≃*
      Subgroup.centralizer ({y} : Set G) :=
  MulEquiv.subgroupCongr (conjugated_centralizer_eq_at_y n S e g y hxy)

theorem conjugatedAtYCentralizerEquiv_coe
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y)
    (c : involutionCentralizer n (conjugatedSylow S g) (conjugatedCoordinates S e g)) :
    (conjugatedAtYCentralizerEquiv n S e g y hxy c : G) = (c : G) := rfl

@[expose] def conjugatedAtYReducedEquiv
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y) :
    centralizerOddCoreQuotient n (conjugatedSylow S g) (conjugatedCoordinates S e g) ≃*
      actualReducedCentralizer y :=
  QuotientGroup.congr _ _ (conjugatedAtYCentralizerEquiv n S e g y hxy)
    (CFSG.ComponentClassification.OddCore.equiv_invariant _)

theorem conjugatedAtYReducedEquiv_mk
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y)
    (c : involutionCentralizer n (conjugatedSylow S g) (conjugatedCoordinates S e g)) :
    conjugatedAtYReducedEquiv n S e g y hxy
      (centralizerOddCoreMap n (conjugatedSylow S g) (conjugatedCoordinates S e g) c) =
      actualReducedMap y (conjugatedAtYCentralizerEquiv n S e g y hxy c) := by
  exact QuotientGroup.congr_mk' _ _ _ _ c

theorem conjugatedAtYReducedEquiv_layer
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y) :
    (CFSG.layer (centralizerOddCoreQuotient n (conjugatedSylow S g)
      (conjugatedCoordinates S e g))).map
        (conjugatedAtYReducedEquiv n S e g y hxy).toMonoidHom =
          CFSG.layer (actualReducedCentralizer y) := by
  rw [CFSG.layer_eq_componentClassification, CFSG.layer_eq_componentClassification]
  exact CFSG.ComponentClassification.Layer.equiv_invariant _

theorem conjugatedAtYCentralizerEquiv_symm_coe
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y) (c : Subgroup.centralizer ({y} : Set G)) :
    ((conjugatedAtYCentralizerEquiv n S e g y hxy).symm c : G) = (c : G) := by
  have h := conjugatedAtYCentralizerEquiv_coe n S e g y hxy
    ((conjugatedAtYCentralizerEquiv n S e g y hxy).symm c)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem conjugatedAtYReducedEquiv_symm_mk
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y) (c : Subgroup.centralizer ({y} : Set G)) :
    (conjugatedAtYReducedEquiv n S e g y hxy).symm (actualReducedMap y c) =
      centralizerOddCoreMap n (conjugatedSylow S g) (conjugatedCoordinates S e g)
        ((conjugatedAtYCentralizerEquiv n S e g y hxy).symm c) := by
  have h := conjugatedAtYReducedEquiv_mk n S e g y hxy
    ((conjugatedAtYCentralizerEquiv n S e g y hxy).symm c)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h]
  exact MulEquiv.symm_apply_apply _ _

theorem conjugatedAtYReducedEquiv_componentImage
    {G : Type} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y) (K : Subgroup G) :
    (ComponentCoveringLocal.originalImage n (conjugatedSylow S g)
      (conjugatedCoordinates S e g) K).map
        (conjugatedAtYReducedEquiv n S e g y hxy).toMonoidHom = actualComponentImage y K := by
  ext h
  constructor
  · rintro ⟨v, ⟨c, hc, rfl⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨conjugatedAtYCentralizerEquiv n S e g y hxy c, ?_, ?_⟩
    · change (conjugatedAtYCentralizerEquiv n S e g y hxy c : G) ∈ K
      rw [conjugatedAtYCentralizerEquiv_coe]
      exact hc
    · exact (conjugatedAtYReducedEquiv_mk n S e g y hxy c).symm
  · rintro ⟨c, hc, rfl⟩
    let b := (conjugatedAtYCentralizerEquiv n S e g y hxy).symm c
    refine Subgroup.mem_map.mpr ⟨centralizerOddCoreMap n (conjugatedSylow S g)
      (conjugatedCoordinates S e g) b, ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨b, ?_, rfl⟩
      change (b : G) ∈ K
      rw [conjugatedAtYCentralizerEquiv_symm_coe]
      exact hc
    · change conjugatedAtYReducedEquiv n S e g y hxy
        (centralizerOddCoreMap n (conjugatedSylow S g)
          (conjugatedCoordinates S e g) b) = actualReducedMap y c
      rw [conjugatedAtYReducedEquiv_mk]
      simp only [b, MulEquiv.apply_symm_apply]

theorem actual_y_component_cover_iff_original_conjugated
    {G : Type} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g y : G)
    (hxy : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y) {K : Subgroup G} :
    CFSG.layer (actualReducedCentralizer y) ≤ actualComponentImage y K ↔
      CFSG.layer (centralizerOddCoreQuotient n (conjugatedSylow S g)
        (conjugatedCoordinates S e g)) ≤ ComponentCoveringLocal.originalImage n
          (conjugatedSylow S g) (conjugatedCoordinates S e g) K := by
  rw [← conjugatedAtYReducedEquiv_layer n S e g y hxy,
    ← conjugatedAtYReducedEquiv_componentImage n S e g y hxy K]
  exact Subgroup.map_le_map_iff_of_injective
    (conjugatedAtYReducedEquiv n S e g y hxy).injective


theorem actual_second_involution_original_local_data
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (y : G) (hy : orderOf y = 2) (K : Subgroup G) (hyK : y ∈ K)
    (hcover : CFSG.layer (actualReducedCentralizer y) ≤ actualComponentImage y K) :
    ∃ g : G, wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y ∧
      involutionCentralizer n (conjugatedSylow S g) (conjugatedCoordinates S e g) =
        Subgroup.centralizer ({y} : Set G) ∧
      wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
        (Original.x (2 ^ n)) ∈ K ∧
      ¬ Nonempty (centralizerFullQuotient n hn (conjugatedSylow S g)
        (conjugatedCoordinates S e g) ≃* Equiv.Perm (Fin 4)) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (centralizerSimpleLayer n hn (conjugatedSylow S g) (conjugatedCoordinates S e g))
          .PSL 2 p f ∧
      CFSG.layer (centralizerOddCoreQuotient n (conjugatedSylow S g)
        (conjugatedCoordinates S e g)) ≤ ComponentCoveringLocal.originalImage n
          (conjugatedSylow S g) (conjugatedCoordinates S e g) K := by
  obtain ⟨g, hxy⟩ := original_involution_conjugator hnonab n hn S e y hy
  exact ⟨g, hxy, conjugated_centralizer_eq_at_y n S e g y hxy, hxy.symm ▸ hyK,
    original_conjugated_nonSym4 n hn S e hfour g,
    original_conjugated_same_PSL2_model n hn S e p f hmodel g,
    (actual_y_component_cover_iff_original_conjugated n S e g y hxy (K := K)).mp hcover⟩

end CFSG.Wreathed.TwoCommutingComponentCover


