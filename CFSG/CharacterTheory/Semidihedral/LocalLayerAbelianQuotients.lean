module

public import CFSG.CharacterTheory.Semidihedral.PerfectLayerNormalization

public noncomputable section

namespace CFSG.Semidihedral.LocalLayerAbelianQuotients

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.GorensteinWalter CFSG.Open
open scoped commutatorElement

universe u v

abbrev originalLayerPreimage {G : Type u} [Group G] (t : G) : Subgroup (C t) :=
  ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)

theorem originalLayerPreimage_eq_kappa_preimage {G : Type u} [Group G] (t : G) :
    originalLayerPreimage t = (CFSG.generalizedFitting (Gamma t)).comap (kappa t) := by
  rw [originalLayerPreimage, Subgroup.comap_comap, barKappa_comp_nu]

theorem coordinate_outer_quotient_isMulCommutative (F : Type v) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) :
    Nat.card (SquareClass F) = 2 ∧ IsCyclic (F ≃+* F) ∧
      IsMulCommutative (coordinateE F ⧸ specialLayer F) := by
  let : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  let e := outerQuotientEquiv F hF
  refine ⟨squareClass_card_two F hF, inferInstance, ?_⟩
  exact IsMulCommutative.of_comm fun a b => e.injective (by
    simpa only [map_mul] using mul_comm' (e a) (e b))

theorem commutator_le_kernel {D : Type u} {B : Type v} [Group D] [Group B]
    [IsMulCommutative B] (phi : D →* B) : commutator D ≤ phi.ker := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  change phi ⁅a, b⁆ = 1
  rw [map_commutatorElement, commutatorElement_def, mul_comm' (phi a) (phi b)]
  group

theorem odd_inverted_subgroup_le_kernel {D : Type u} {B : Type v} [Group D] [Group B]
    [IsMulCommutative B] (phi : D →* B) (W : Subgroup D) (hW : Odd (Nat.card W))
    (a : D) (hinv : ∀ w ∈ W, a * w * a⁻¹ = w⁻¹) : W ≤ phi.ker := by
  intro w hw
  have hconj : phi (a * w * a⁻¹) = phi w := by
    rw [map_mul, map_mul, map_inv, mul_comm' (phi a) (phi w)]
    group
  have heq : phi w = (phi w)⁻¹ :=
    hconj.symm.trans ((congrArg phi (hinv w hw)).trans (map_inv phi w))
  have hsquare : phi w ^ 2 = 1 := by
    calc
      phi w ^ 2 = phi w * (phi w)⁻¹ := by
        rw [pow_two]
        exact congrArg (fun z => phi w * z) heq
      _ = 1 := mul_inv_cancel _
  have hodd : Odd (orderOf (phi w)) :=
    hW.of_dvd_nat ((orderOf_map_dvd phi w).trans (W.orderOf_dvd_natCard hw))
  exact orderOf_eq_one_iff.mp ((Nat.coprime_two_right.mpr hodd).eq_one_of_dvd
    (orderOf_dvd_of_pow_eq_one hsquare))

theorem actual_matrix_outer_map_kernels {G : Type} [Group G]
    (t : G) (n p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (data : ActualMatrixData t n p f F A rho) :
    ∃ hF : IsOddPrimePower (Nat.card F),
      ((theta F hF).comp rho).ker = CFSG.generalizedFitting (Gamma t) ∧
      (((theta F hF).comp rho).comp (barKappa t)).ker =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ∧
      ((((theta F hF).comp rho).comp (barKappa t)).comp (nu t)).ker =
        originalLayerPreimage t ∧
      (∀ x : C t, (((theta F hF).comp rho).comp (barKappa t)).comp (nu t) x =
        theta F hF (rho (kappa t x))) := by
  let hF : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, data.field_card⟩
  have hker : ((theta F hF).comp rho).ker = CFSG.generalizedFitting (Gamma t) :=
    SameParameterRegularity.kernel_comp_eq_of_layer_image rho data.faithful
      (theta F hF) (CFSG.generalizedFitting (Gamma t))
      (data.layer_image.trans (theta_ker F hF).symm)
  have hbar : (((theta F hF).comp rho).comp (barKappa t)).ker =
      (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
    rw [← MonoidHom.comap_ker, hker]
  refine ⟨hF, hker, hbar, ?_, fun _ => rfl⟩
  rw [← MonoidHom.comap_ker, hbar]

theorem actual_matrix_layer_preimage_has_abelian_quotient {G : Type} [Group G]
    (t : G) (n p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (data : ActualMatrixData t n p f F A rho) :
    IsMulCommutative (Gamma t ⧸ CFSG.generalizedFitting (Gamma t)) ∧
      IsMulCommutative (C t ⧸ originalLayerPreimage t) ∧
      commutator (C t) ≤ originalLayerPreimage t := by
  obtain ⟨hF, hker, -, hY, -⟩ :=
    actual_matrix_outer_map_kernels t n p f hp hpodd hf F A rho data
  let : IsCyclic (F ≃+* F) := (coordinate_outer_quotient_isMulCommutative F hF).2.1
  let phi := (((theta F hF).comp rho).comp (barKappa t)).comp (nu t)
  refine ⟨SameParameterRegularity.quotient_isMulCommutative_of_kernel
    (CFSG.generalizedFitting (Gamma t)) ((theta F hF).comp rho) hker,
    SameParameterRegularity.quotient_isMulCommutative_of_kernel
      (originalLayerPreimage t) phi hY, ?_⟩
  exact hY ▸ commutator_le_kernel phi

theorem original_local_outer_action {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (rho : Gamma t →* coordinateE F)
      (hF : IsOddPrimePower (Nat.card F)),
      Nat.card F = p ^ f ∧ 5 ≤ Nat.card F ∧ Function.Injective rho ∧
      (CFSG.generalizedFitting (Gamma t)).map rho = specialLayer F ∧
      (theta F hF).ker = specialLayer F ∧
      ((theta F hF).comp rho).ker = CFSG.generalizedFitting (Gamma t) ∧
      ((((theta F hF).comp rho).comp (barKappa t)).comp (nu t)).ker =
        originalLayerPreimage t ∧
      (∀ x : C t, (((theta F hF).comp rho).comp (barKappa t)).comp (nu t) x =
        theta F hF (rho (kappa t x))) ∧
      Nat.card (SquareClass F) = 2 ∧ IsCyclic (F ≃+* F) ∧
      IsMulCommutative (coordinateE F ⧸ specialLayer F) ∧
      IsMulCommutative (Gamma t ⧸ CFSG.generalizedFitting (Gamma t)) ∧
      IsMulCommutative (C t ⧸ originalLayerPreimage t) ∧
      commutator (C t) ≤ originalLayerPreimage t := by
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ := actual_simple_layer_matrix_data
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  obtain ⟨hF, hker, -, hY, hrep⟩ :=
    actual_matrix_outer_map_kernels t n p f hp hpodd hf F A rho data
  obtain ⟨hcard, hcyclic, houter⟩ := coordinate_outer_quotient_isMulCommutative F hF
  obtain ⟨hGamma, hC, hcomm⟩ :=
    actual_matrix_layer_preimage_has_abelian_quotient t n p f hp hpodd hf F A rho data
  exact ⟨F, hfield, hfinite, rho, hF, data.field_card, data.field_card ▸ hq,
    data.faithful, data.layer_image, theta_ker F hF, hker, hY, hrep,
    hcard, hcyclic, houter, hGamma, hC, hcomm⟩

theorem original_local_layer_preimage_has_abelian_quotient_univ_zero
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    IsMulCommutative (C t ⧸ originalLayerPreimage t) ∧
      commutator (C t) ≤ originalLayerPreimage t := by
  obtain ⟨F, hfield, hfinite, rho, hF, -, -, -, -, -, -, -, -, -, -, -, -, hC, hcomm⟩ :=
    original_local_outer_action n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  exact ⟨hC, hcomm⟩

theorem original_local_layer_preimage_has_abelian_quotient
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) :
    IsMulCommutative (C t ⧸ originalLayerPreimage t) ∧
      commutator (C t) ≤ originalLayerPreimage t := by
  obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S0' : Sylow 2 G' := S0.mapSurjective (f := e.toMonoidHom) e.surjective
  let f0' : SemidihedralGroup n ≃* S0' :=
    f0.trans ((S0 : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective)
  let c := PerfectLayerNormalization.originalCentralizerEquiv e t
  let d := PerfectLayerNormalization.originalGeneralizedFittingEquiv e t
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma (e t))) := d.symm.isSimpleGroup
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg (Subgroup.map
      (PerfectLayerNormalization.originalReducedQuotientEquiv e t).toMonoidHom) hcentral
    rw [PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  obtain ⟨hC', -⟩ := original_local_layer_preimage_has_abelian_quotient_univ_zero
    n hn S0' f0' (PerfectLayerNormalization.isomorphism_transports_no_index_two e hG)
    (e t) ((e.orderOf_eq t).trans ht)
    (PerfectLayerNormalization.isomorphism_transports_nonabelian d hnonab) hcentral'
    (PerfectLayerNormalization.isomorphism_transports_noncyclic_sylows d 2 hnc)
    p f hp hpodd hf hq (PerfectLayerNormalization.original_psl_two_model_transport d p f hmodel)
  let : IsMulCommutative (C (e t) ⧸ originalLayerPreimage (e t)) := hC'
  have hY : (originalLayerPreimage t).map c.toMonoidHom = originalLayerPreimage (e t) :=
    (PerfectLayerNormalization.original_local_layer_preimages_transport e t).2
  let phi := (QuotientGroup.mk' (originalLayerPreimage (e t))).comp c.toMonoidHom
  have hker : phi.ker = originalLayerPreimage t := by
    ext x
    change c x ∈ (QuotientGroup.mk' (originalLayerPreimage (e t))).ker ↔
      x ∈ originalLayerPreimage t
    rw [QuotientGroup.ker_mk', ← hY]
    exact Subgroup.mem_map_iff_mem c.injective
  exact ⟨SameParameterRegularity.quotient_isMulCommutative_of_kernel
    (originalLayerPreimage t) phi hker, hker ▸ commutator_le_kernel phi⟩

theorem original_perfect_local_layer_preimage_has_abelian_quotient
    {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) :
    IsMulCommutative (C t ⧸ originalLayerPreimage t) ∧
      commutator (C t) ≤ originalLayerPreimage t :=
  original_local_layer_preimage_has_abelian_quotient n hn S0 f0
    Principal.RotationCongruence.index_ne_two_of_isPerfect
    t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel

theorem original_simple_local_layer_preimage_has_abelian_quotient
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) :
    IsMulCommutative (C t ⧸ originalLayerPreimage t) ∧
      commutator (C t) ≤ originalLayerPreimage t :=
  original_local_layer_preimage_has_abelian_quotient n hn S0 f0
    (Principal.index_ne_two_of_isSimpleGroup hGnonab)
    t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel

theorem original_odd_inverted_subgroup_le_layer_preimage
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (W : Subgroup (C t)) (hW : Odd (Nat.card W)) (a : C t)
    (hinv : ∀ w ∈ W, a * w * a⁻¹ = w⁻¹) : W ≤ originalLayerPreimage t := by
  let : IsMulCommutative (C t ⧸ originalLayerPreimage t) :=
    (original_local_layer_preimage_has_abelian_quotient
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel).1
  have h := odd_inverted_subgroup_le_kernel
    (QuotientGroup.mk' (originalLayerPreimage t)) W hW a hinv
  simpa only [QuotientGroup.ker_mk'] using h

theorem original_odd_inverted_ambient_subgroup_le_layer_preimage
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (W : Subgroup G) (hWC : W ≤ C t) (hW : Odd (Nat.card W)) (a : G) (ha : a ∈ C t)
    (hinv : ∀ w ∈ W, a * w * a⁻¹ = w⁻¹) :
    W ≤ (originalLayerPreimage t).map (C t).subtype := by
  let U := W.subgroupOf (C t)
  have hUodd : Odd (Nat.card U) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
    exact hW
  have hUinv : ∀ w ∈ U, (⟨a, ha⟩ : C t) * w * (⟨a, ha⟩ : C t)⁻¹ = w⁻¹ := by
    intro w hw
    apply Subtype.ext
    exact hinv w hw
  have hUY : U ≤ originalLayerPreimage t := original_odd_inverted_subgroup_le_layer_preimage
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel U hUodd ⟨a, ha⟩ hUinv
  intro w hw
  exact Subgroup.mem_map_of_mem (C t).subtype (hUY (show (⟨w, hWC hw⟩ : C t) ∈ U from hw))

end CFSG.Semidihedral.LocalLayerAbelianQuotients
