module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeSetting
public import CFSG.CharacterTheory.Wreathed.ComponentCoverFactorizations
public import CFSG.CharacterTheory.Wreathed.TwoCommutingComponentCoverSecondInvolution

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGQGroups CFSG.QuasiDihedralFusion

theorem le_range_of_ker_le_oddCore {J X : Type*} [Group J] [Group X] [Finite J] [Finite X]
    (φ : J →* X) (hker : φ.ker ≤ CFSG.oddCore J) (M : Subgroup X) (hM : commutator X ≤ M)
    (Λ : Subgroup (J ⧸ CFSG.oddCore J)) [Group.IsPerfect Λ] (hcard : Nat.card M ≤ Nat.card Λ) :
    M ≤ φ.range := by
  have h1 : (commutator J).map φ ≤ M := by
    rw [map_commutator_eq]
    exact (Subgroup.commutator_mono le_top le_top).trans hM
  have h2 : Λ ≤ commutator (J ⧸ CFSG.oddCore J) := by
    rw [← Subgroup.commutator_eq_self (H := Λ)]
    exact Subgroup.commutator_mono le_top le_top
  have h3 : commutator (J ⧸ CFSG.oddCore J) =
      (commutator J).map (QuotientGroup.mk' (CFSG.oddCore J)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rfl
  have h4 : Nat.card ((commutator J).map (QuotientGroup.mk' (CFSG.oddCore J))) ≤
      Nat.card ((commutator J).map φ) := by
    refine Nat.le_of_dvd Nat.card_pos ?_
    rw [← Subgroup.relIndex_ker, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
    exact Subgroup.relIndex_dvd_of_le_left _ hker
  have h5 : (commutator J).map φ = M := by
    refine Subgroup.eq_of_le_of_card_ge h1 ?_
    calc Nat.card M ≤ Nat.card Λ := hcard
      _ ≤ Nat.card (commutator (J ⧸ CFSG.oddCore J)) := Subgroup.card_le_of_le h2
      _ = Nat.card ((commutator J).map (QuotientGroup.mk' (CFSG.oddCore J))) := by rw [h3]
      _ ≤ Nat.card ((commutator J).map φ) := h4
  rw [← h5]
  exact Subgroup.map_le_range φ _

theorem exists_commuting_involutions_of_isQDGroup {H : Type*} [Group H] (hH : IsQDGroup H) :
    ∃ a b : H, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a := by
  obtain ⟨k, hk⟩ := hH.sylow
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := H)
  rcases hk with ⟨-, m, hm, hSD⟩ | ⟨hk2, hW⟩
  · obtain ⟨φ⟩ := hSD P
    have hz := CFSG.Semidihedral.z_mem_center m hm
    have hs : CFSG.Semidihedral.s m ∉ Subgroup.center (CFSG.Open.SemidihedralGroup m) := by
      intro hs
      have h := (CFSG.Semidihedral.element_mem_center_iff m hm 0 1).mp
        (CFSG.Semidihedral.s_eq_element m (by omega) ▸ hs)
      exact one_ne_zero h.1
    refine ⟨(φ (CFSG.Semidihedral.z m) : H), (φ (CFSG.Semidihedral.s m) : H), ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact CFSG.Semidihedral.orderOf_z m (by omega)
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact CFSG.Semidihedral.orderOf_s m (by omega)
    · intro h
      have h' := φ.injective (Subtype.ext h)
      exact hs (h' ▸ hz)
    · have h := Subgroup.mem_center_iff.mp hz (CFSG.Semidihedral.s m)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]
  · obtain ⟨ψ⟩ := hW P
    have hstr := wreath_center_involution_and_quaternion_coordinates k hk2
    have hx : Original.x (2 ^ k) ∈ Subgroup.center (Wreath (2 ^ k)) := by
      rw [hstr.center]
      exact (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _
    refine ⟨(ψ.symm (Original.x (2 ^ k)) : H), (ψ.symm (Original.x2 (2 ^ k)) : H),
      ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hstr.involution_orders.1
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hstr.involution_orders.2.1
    · intro h
      have h' := ψ.symm.injective (Subtype.ext h)
      exact hstr.distinct_classes.1 (h' ▸ IsConj.refl _)
    · have h := Subgroup.mem_center_iff.mp hx (Original.x2 (2 ^ k))
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]

variable {G : Type} [Group G]

def centralizerInclusion (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (y : K) (hy : (y : G) = wreathModelHom S e (Original.x (2 ^ n))) :
    Subgroup.centralizer ({y} : Set K) →* involutionCentralizer n S e :=
  (K.subtype.comp (Subgroup.centralizer ({y} : Set K)).subtype).codRestrict _ fun j => by
    change (j : G) ∈ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}
    rw [Subgroup.mem_centralizer_singleton_iff, ← hy]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp j.property)

theorem centralizerInclusion_injective (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (y : K) (hy : (y : G) = wreathModelHom S e (Original.x (2 ^ n))) :
    Function.Injective (centralizerInclusion n S e K y hy) := by
  intro a b hab
  exact Subtype.ext (Subtype.ext (congrArg (fun c : involutionCentralizer n S e => (c : G)) hab))

variable [Finite G] [IsSimpleGroup G]

open ComponentCoveringLocal FullCentralizerFromProjectiveModel in
theorem layer_le_originalImage_of_hasNormalSL2
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (y : K) (hy : (y : G) = wreathModelHom S e (Original.x (2 ^ n)))
    (hSL : HasNormalSL2 (Subgroup.centralizer ({y} : Set K) ⧸
      CFSG.oddCore (Subgroup.centralizer ({y} : Set K))) (p ^ f)) :
    CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K := by
  obtain ⟨F, _, _, hFcard, _, _, _, _, eta, _, _, _, hdata⟩ :=
    actual_projective_layer_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hp2 hf hlocal
  obtain ⟨Λ, F', _, _, -, hF'card, ⟨iΛ⟩⟩ := hSL
  let := Fintype.ofFinite F
  let := Fintype.ofFinite F'
  let σ : F' ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hFcard, hF'card])
  let E : Λ ≃* CFSG.layer (centralizerOddCoreQuotient n S e) :=
    iΛ.trans ((CFSG.ClassicalModels.specialLinearFieldEquiv σ (Fin 2)).trans eta.symm)
  have hperfM : Group.IsPerfect (CFSG.layer (centralizerOddCoreQuotient n S e)) :=
    hdata.structural.component.1.1
  have hperf : Group.IsPerfect Λ :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  let ι := centralizerInclusion n S e K y hy
  let φ := (centralizerOddCoreMap n S e).comp ι
  have hker : φ.ker ≤ CFSG.oddCore (Subgroup.centralizer ({y} : Set K)) := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    have hφ : φ.ker = (centralizerOddCore n S e).comap ι := by
      ext j
      exact QuotientGroup.eq_one_iff (ι j)
    rw [hφ]
    exact (CFSG.ComponentClassification.OddCore.odd_card
      (involutionCentralizer n S e)).of_dvd_nat
        (Subgroup.card_comap_dvd_of_injective _ ι
          (centralizerInclusion_injective n S e K y hy))
  have hrange := le_range_of_ker_le_oddCore φ hker _
    (original_derived_eq_layer hnonab n hn S e hfour p f hp hp2 hf hlocal).le Λ
    (Nat.card_congr E.toEquiv).ge
  refine hrange.trans ?_
  rw [MonoidHom.range_comp]
  apply Subgroup.map_mono
  rintro _ ⟨j, rfl⟩
  exact (j : K).property

open SmallerRecognitionOriginalField TwoCommutingComponentCover ComponentCoverFactorizations in
theorem wreathedSetting_workingHypothesisII
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) :
    (wreathedSetting n S e p f).WorkingHypothesisII := by
  intro H hH hQD
  by_contra hne
  have hO : CFSG.oddCore H ≠ ⊥ := fun h => hne (by
    rw [CFSG.ABGTheoremB.oddCoreIn, h, Subgroup.map_bot])
  obtain ⟨a, b, ha, hb, hab, hcomm⟩ := exists_commuting_involutions_of_isQDGroup hQD.1
  obtain ⟨g, hxa⟩ := original_involution_conjugator hnonab n hn S e (a : G)
    (by rw [Subgroup.orderOf_coe]; exact ha)
  have hfour' := original_conjugated_nonSym4 n hn S e hfour g
  have hlocal' := original_conjugated_same_PSL2_model n hn S e p f hlocal g
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hcover := layer_le_originalImage_of_hasNormalSL2 hnonab n hn _ _ hfour' p f hp hp2 hf
    hlocal' H a hxa.symm (hQD.2 a ha).2.2
  have hxH : wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) ∈ H := hxa ▸ a.property
  have hfac :=
    smaller_recognition_factors_every_involution_containing_component_covering_subgroup
      hnonab n hn _ _ hfour' p f hp hpodd hf hq.le hlocal' hrec H (lt_top_iff_ne_top.mpr hH)
      hxH hcover hO
  have hcent : QuotientGroup.mk' (CFSG.oddCore H) a ∈ Subgroup.center (H ⧸ CFSG.oddCore H) := by
    have h := hfac.2.1
    have hya : (⟨_, hxH⟩ : H) = a := Subtype.ext hxa
    rwa [hya] at h
  obtain ⟨c, hc⟩ := isConj_iff.mp (hQD.1.involutions_isConj a b ha hb)
  have hbar : QuotientGroup.mk' (CFSG.oddCore H) a = QuotientGroup.mk' (CFSG.oddCore H) b := by
    rw [← hc, map_mul, map_mul, map_inv, Subgroup.mem_center_iff.mp hcent, mul_inv_cancel_right]
  have hmem : a⁻¹ * b ∈ CFSG.oddCore H := QuotientGroup.eq.mp hbar
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha2])
  have horder : orderOf (a⁻¹ * b) = 2 := by
    rw [hainv]
    apply orderOf_eq_prime
    · rw [Commute.mul_pow hcomm, ha2, hb2, one_mul]
    · exact fun h => hab (hainv.symm.trans (inv_eq_of_mul_eq_one_right h))
  have hdvd := orderOf_dvd_natCard (⟨a⁻¹ * b, hmem⟩ : CFSG.oddCore H)
  rw [Subgroup.orderOf_mk, horder] at hdvd
  exact (Nat.not_even_iff_odd.mpr (CFSG.ABGTheoremB.odd_card_oddCore H))
    (even_iff_two_dvd.mpr hdvd)

end CFSG.Wreathed.OriginalAllPrime
