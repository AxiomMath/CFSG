module

public import CFSG.CharacterTheory.Wreathed.ComponentCoverConfinementSetup
public import CFSG.CharacterTheory.Wreathed.FullCentralizerFromProjectiveModel
public import CFSG.CharacterTheory.Semidihedral.ExchangedEigensubgroups
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.CharacterTheory.Wreathed.ComponentCoverTwoInvolutions
public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreOrder
public import CFSG.CharacterTheory.Wreathed.OriginalCoveringLocalFamilyMembers
public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelCharacterInputs
public import CFSG.CharacterTheory.Wreathed.StationaryInvertedSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.ComponentCoverConfinement

open CFSG.Assembly.LowTwoRank SmallerRecognitionOriginalField
open OriginalStationarityCoverageCriterion ComponentCoverFactorizations
open CFSG.Semidihedral CFSG.Semidihedral.ExchangedEigensubgroups

@[expose] def ExchangedDimension (p f : ℕ) : Prop :=
  ∀ (R : Type) [CommGroup R] [Finite R] [Nontrivial R] (F : Type) [Field F]
    (J : Type) [Group J] [Finite J] [Group.IsPerfect J] (ell : ℕ), ell.Prime → Odd ell →
    Nat.card F = p ^ f →
    ∀ β : J →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective β →
    β.ker ≤ Subgroup.center J → Odd (Nat.card β.ker) →
    ∀ t : J, t ∈ Subgroup.center J → orderOf t = 2 → β t = OddFieldSL2.minusIdentity F →
    ∀ ρ : J →* MulAut R, (∀ r : R, ρ t r = r⁻¹) → IsPGroup ell R →
    ∀ α : MulAut R, α ^ 2 = 1 → ∀ d : J, ρ d * α * (ρ d)⁻¹ = ρ t * α →
    ∀ ι : positiveGroup α →* OddProjectiveCoverKernel.S F, Function.Injective ι →
      ell = p ∧ Nat.card (positiveGroup α) = p ^ f

theorem exchangedDimension_of_five_lt
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hq : 5 < p ^ f) : ExchangedDimension p f := by
  intro R _ _ _ F _ J _ _ _ ell hell hellodd hF β hβ hcentral hodd t ht htorder htβ ρ hinv hR α
    hα d hexchange ι hι
  obtain ⟨hl, -, -, -, -, -, hcard, -⟩ :=
    exchanged_eigensubgroups_projective_embedding_forces_defining_square_order hp hpodd hell
      hellodd hf hF hq β hβ hcentral hodd t ht htorder htβ ρ hinv hR α hα d hexchange ι hι
  exact ⟨hl, hcard⟩

section Elements

variable {G : Type} [Group G]

theorem eq_one_of_sq_eq_one_of_odd {v : G} (hv : Odd (orderOf v)) (h : v ^ 2 = 1) : v = 1 := by
  have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hv
    exact absurd hv (by decide)

end Elements

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem lift_mem_x_and_d
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)) :
    centralInvolution n S e ∈ J ∧
      wreathModelHom S e (Original.d (2 ^ n)) ∈ J.map (involutionCentralizer n S e).subtype := by
  have hQ := LocalOddCorePerfectNormalizer.original_quaternion_le_actual_lift hnonab n hn S e
    hfour J hJM
  refine ⟨hQ (centralizerKernelInvolution_original_mem_quaternion n hn S e), ?_⟩
  have hd : wreathModelHom S e (Original.d (2 ^ n)) ∈ modelY S e :=
    Subgroup.mem_map_of_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rw [← centralizerQuaternion_map n hn S e] at hd
  exact Subgroup.map_mono hQ hd

theorem eigen_dimension
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hdim : ExchangedDimension p f)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal] [Group.IsPerfect J]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hcomm : ∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r)
    (W : Subgroup G) (hWab : IsMulCommutative W) (hW1 : W ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hellodd : Odd ell) (hWp : IsPGroup ell W)
    (hWinv : ∀ w ∈ W, wreathModelHom S e (Original.x (2 ^ n)) * w *
      (wreathModelHom S e (Original.x (2 ^ n)))⁻¹ = w⁻¹)
    (hJW : ∀ j ∈ J, (j : G) ∈ Subgroup.normalizer (W : Set G))
    (hyW : wreathModelHom S e (Original.x2 (2 ^ n)) ∈ Subgroup.normalizer (W : Set G))
    (c : G)
    (hcN : ∀ w ∈ W, w * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * w →
        c * w * c⁻¹ ∈ involutionCentralizer n S e)
    (hcM : ∀ w (hw : w ∈ W) (hwy : w * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * w),
        centralizerOddCoreMap n S e ⟨c * w * c⁻¹, hcN w hw hwy⟩ ∈
          CFSG.layer (centralizerOddCoreQuotient n S e))
    (hcker : ∀ w (hw : w ∈ W) (hwy : w * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * w),
        centralizerOddCoreMap n S e ⟨c * w * c⁻¹, hcN w hw hwy⟩ = 1 → w = 1) :
    ell = p ∧ Nat.card (W ⊓ Subgroup.centralizer
      ({wreathModelHom S e (Original.x2 (2 ^ n))} : Set G) : Subgroup G) = p ^ f := by
  set x := wreathModelHom S e (Original.x (2 ^ n)) with hxdef
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hydef
  have hp2 : p ≠ 2 := fun h => by
    rw [h] at hpodd
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  obtain ⟨F, hFf, hFfin, hcard, -, -, theta, rho, eta, hin, -, -, -⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_layer_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hp2 hf hlocal
  let : Field F := hFf
  let : Finite F := hFfin
  obtain ⟨hxJ, hdJ⟩ := lift_mem_x_and_d hnonab n hn S e hfour J hJM
  obtain ⟨dN, hdN, hdNeq⟩ := hdJ
  replace hdNeq : (dN : G) = wreathModelHom S e (Original.d (2 ^ n)) := hdNeq
  have : IsMulCommutative W := hWab
  let : CommGroup W := IsMulCommutative.instCommGroup
  have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW1
  let πJ : J →* CFSG.layer (centralizerOddCoreQuotient n S e) :=
    ((centralizerOddCoreMap n S e).comp J.subtype).codRestrict _ (fun j => by
      rw [← hJM]
      exact Subgroup.mem_map_of_mem _ j.2)
  let β : J →* Matrix.SpecialLinearGroup (Fin 2) F := eta.toMonoidHom.comp πJ
  have hβ : Function.Surjective β := by
    intro X
    have hX : ((eta.symm X : CFSG.layer (centralizerOddCoreQuotient n S e)) :
        centralizerOddCoreQuotient n S e) ∈ J.map (centralizerOddCoreMap n S e) := by
      rw [hJM]
      exact (eta.symm X).2
    obtain ⟨j, hj, hjX⟩ := hX
    refine ⟨⟨j, hj⟩, ?_⟩
    have h1 : πJ ⟨j, hj⟩ = eta.symm X := Subtype.ext hjX
    change eta (πJ ⟨j, hj⟩) = X
    rw [h1, MulEquiv.apply_symm_apply]
  have hkerR : ∀ j : J, β j = 1 → (j : involutionCentralizer n S e) ∈ centralizerOddCore n S e := by
    intro j hj
    have h1 : πJ j = 1 := eta.injective (by rw [map_one]; exact hj)
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
  have hcentral : β.ker ≤ Subgroup.center J := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro j'
    exact Subtype.ext (hcomm j' j'.2 j (hkerR j hj)).eq
  have hodd : Odd (Nat.card β.ker) := by
    have hle : β.ker.map J.subtype ≤ centralizerOddCore n S e := by
      rintro _ ⟨j, hj, rfl⟩
      exact hkerR j hj
    rw [← Subgroup.card_map_of_injective J.subtype_injective]
    exact (weakClosure_oddCore_card _).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  let t : J := ⟨centralInvolution n S e, hxJ⟩
  have ht : t ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro j
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (centralInvolution_mem_center n S e)) j)
  have htorder : orderOf t = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact CompatibleFamilies.orderOf_x S e hn
  have htβ : β t = OddFieldSL2.minusIdentity F := by
    have h1 : πJ t = ActualProjectiveLayer.centralizerActualLayerInvolution hnonab n hn S e hfour :=
      Subtype.ext rfl
    change eta (πJ t) = _
    rw [h1, hin.involution, ProjectiveSL2Cover.minusIdentity_eq_neg_one]
    rfl
  let κ : J →* Subgroup.normalizer (W : Set G) :=
    ((involutionCentralizer n S e).subtype.comp J.subtype).codRestrict _ (fun j => hJW j j.2)
  let ρ : J →* MulAut W := (Subgroup.normalizerMonoidHom W).comp κ
  have hinv : ∀ r : W, ρ t r = r⁻¹ := fun r => Subtype.ext (by
    change x * (r : G) * x⁻¹ = (r : G)⁻¹
    exact hWinv r r.2)
  let yW : Subgroup.normalizer (W : Set G) := ⟨y, hyW⟩
  let α : MulAut W := Subgroup.normalizerMonoidHom W yW
  have hα : α ^ 2 = 1 := by
    have h1 : yW ^ 2 = 1 := Subtype.ext (by
      change y ^ 2 = 1
      rw [← orderOf_dvd_iff_pow_eq_one, CompatibleFamilies.orderOf_x2 S e hn])
    change (Subgroup.normalizerMonoidHom W yW) ^ 2 = 1
    rw [← map_pow, h1, map_one]
  let dJ : J := ⟨dN, hdN⟩
  have hexchange : ρ dJ * α * (ρ dJ)⁻¹ = ρ t * α := by
    have hrel : κ dJ * yW * (κ dJ)⁻¹ = κ t * yW := Subtype.ext (by
      change (dN : G) * y * (dN : G)⁻¹ = x * y
      rw [hdNeq]
      exact InvertedLocalSylow.modelHom_d_conj_x2 S e (by omega))
    change (Subgroup.normalizerMonoidHom W) (κ dJ) * (Subgroup.normalizerMonoidHom W) yW *
        ((Subgroup.normalizerMonoidHom W) (κ dJ))⁻¹ =
      (Subgroup.normalizerMonoidHom W) (κ t) * (Subgroup.normalizerMonoidHom W) yW
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, hrel]
  have hposW : ∀ w : W, w ∈ positiveGroup α → (w : G) * y = y * w := by
    intro w hw
    have h := congrArg Subtype.val ((mem_positiveGroup α w).mp hw)
    change y * (w : G) * y⁻¹ = w at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  let ψ : positiveGroup α →* involutionCentralizer n S e :=
    ((MulAut.conj c).toMonoidHom.comp (W.subtype.comp (positiveGroup α).subtype)).codRestrict _
      (fun w => hcN (w : W) (w : W).2 (hposW w w.2))
  let φ : positiveGroup α →* CFSG.layer (centralizerOddCoreQuotient n S e) :=
    ((centralizerOddCoreMap n S e).comp ψ).codRestrict _
      (fun w => hcM (w : W) (w : W).2 (hposW w w.2))
  let ι : positiveGroup α →* OddProjectiveCoverKernel.S F :=
    (ProjectiveSL2Cover.scalarQuotient F 2).comp (eta.toMonoidHom.comp φ)
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hker : eta (φ w) ∈ (ProjectiveSL2Cover.scalarQuotient F 2).ker := hw
    rw [ProjectiveSL2Cover.scalarQuotient_two_ker] at hker
    have hsq : eta (φ w) ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hker
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        ProjectiveSL2Cover.minusIdentity_square, one_zpow]
    have hsq' : φ w ^ 2 = 1 := eta.injective (by rw [map_pow, hsq, map_one])
    have hsq'' : centralizerOddCoreMap n S e (ψ w) ^ 2 = 1 := congrArg Subtype.val hsq'
    have hwodd : Odd (orderOf ((w : W) : G)) := by
      have : Fact ell.Prime := ⟨hell⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWp
      have hWodd : Odd (Nat.card W) := by
        rw [hk]
        exact hellodd.pow
      exact hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W (w : W).2)
    have hψodd : Odd (orderOf (ψ w)) := by
      have h1 : orderOf (ψ w) = orderOf ((w : W) : G) := by
        rw [← Subgroup.orderOf_coe]
        change orderOf ((MulAut.conj c) ((w : W) : G)) = _
        exact MulEquiv.orderOf_eq _ _
      rw [h1]
      exact hwodd
    have h1 := eq_one_of_sq_eq_one_of_odd (hψodd.of_dvd_nat (orderOf_map_dvd _ _)) hsq''
    have h2 := hcker (w : W) (w : W).2 (hposW w w.2) h1
    exact Subtype.ext (Subtype.ext h2)
  obtain ⟨hl, hcardpos⟩ := hdim W F J ell hell hellodd hcard β hβ hcentral hodd t ht htorder htβ
    ρ hinv hWp α hα dJ hexchange ι hι
  refine ⟨hl, ?_⟩
  have hmap : (positiveGroup α).map W.subtype = W ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr (hposW w hw)⟩
    · rintro ⟨hzW, hzy⟩
      refine ⟨⟨z, hzW⟩, ?_, rfl⟩
      apply (mem_positiveGroup α _).mpr
      apply Subtype.ext
      change y * z * y⁻¹ = z
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hzy).symm
  rw [← hmap, Subgroup.card_map_of_injective W.subtype_injective, hcardpos]

end CFSG.Wreathed.ComponentCoverConfinement
