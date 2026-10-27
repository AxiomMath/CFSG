module

public import CFSG.CharacterTheory.Wreathed.ActualCentralizerLayer
public import CFSG.CharacterTheory.Wreathed.NoncentralScalarSylowCoverage

public noncomputable section

open scoped Classical
open CFSG.Wreathed
open CFSG.Wreathed.NoncentralScalarSylowCoverage

namespace CFSG.Wreathed.OriginalScalarSylowCoverage
universe u
variable {G : Type u} [Group G] [Finite G]

@[expose] def originalCenterQuotientEquiv
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃*
        centralizerFullQuotient n hn S e :=
  QuotientGroup.quotientMulEquivOfEq
    (centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e)

theorem original_nonfourpoint_fullCenter
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4))) :
    ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) := by
  rintro ⟨alpha⟩
  exact hfour ⟨(originalCenterQuotientEquiv n hn S e).trans alpha⟩

theorem original_wreath_center_unique_involution
    (n : ℕ) (hn : 2 ≤ n) (w : Wreath (2 ^ n))
    (horder : orderOf w = 2) (hcenter : w ∈ Subgroup.center (Wreath (2 ^ n))) :
    w = Original.x (2 ^ n) := by
  cases n with
  | zero => omega
  | succ k =>
    have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by
      rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < (2 : ℕ))]
    simpa only [Original.x_eq, hhalf] using
      unique_central_involution k w horder hcenter

theorem original_quotient_center_unique_involution
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (q : centralizerOddCoreQuotient n S e) (horder : orderOf q = 2)
    (hcenter : q ∈ Subgroup.center (centralizerOddCoreQuotient n S e)) :
    q = centralizerOddCoreMap n S e (centralInvolution n S e) := by
  rw [centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e,
    centralizerFullCenterImage_eq_modelCenter, modelCenter] at hcenter
  obtain ⟨w, hw, hvalue⟩ := Subgroup.mem_map.mp hcenter
  have hworder : orderOf w = 2 :=
    (orderOf_injective _ (wreathModelHom_injective _ _) w).symm.trans
      (hvalue.symm ▸ horder)
  have hwcenter : w ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [(wreath_center_involution_and_quaternion_coordinates n hn).center]
    exact hw
  have hx := original_wreath_center_unique_involution n hn w hworder hwcenter
  rw [← hvalue, hx, centralizerOddCoreModelHom_apply, centralizerModelHom_x]

theorem original_involution_image_order
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (v : involutionCentralizer n S e) (horder : orderOf v = 2) :
    orderOf (centralizerOddCoreMap n S e v) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← map_pow, ← horder, pow_orderOf_eq_one, map_one]
  · intro h
    have hr : v ∈ centralizerOddCore n S e :=
      (QuotientGroup.eq_one_iff (N := centralizerOddCore n S e) v).mp h
    have hdiv := (centralizerOddCore n S e).orderOf_dvd_natCard hr
    rw [horder] at hdiv
    exact (centralizerOddCore_card_odd n S e).not_two_dvd_nat hdiv

theorem original_second_involution_noncentral
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (v : involutionCentralizer n S e) (horder : orderOf v = 2)
    (hne : v ≠ centralInvolution n S e) :
    centralizerOddCoreMap n S e v ∉ Subgroup.center (centralizerOddCoreQuotient n S e) := by
  intro hcenter
  have himage := original_quotient_center_unique_involution n hn S e
    (centralizerOddCoreMap n S e v) (original_involution_image_order n S e v horder) hcenter
  have hxorder := centralizerKernelInvolution_original_order n hn S e
  have hv2 : v ^ 2 = 1 := horder ▸ pow_orderOf_eq_one v
  have hx2 : (centralInvolution n S e) ^ 2 = 1 :=
    hxorder ▸ pow_orderOf_eq_one (centralInvolution n S e)
  let r := v * centralInvolution n S e
  have hr : r ∈ centralizerOddCore n S e := by
    apply (QuotientGroup.eq_one_iff (N := centralizerOddCore n S e) r).mp
    change centralizerOddCoreMap n S e (v * centralInvolution n S e) = 1
    rw [map_mul, himage, ← pow_two, ← map_pow, hx2, map_one]
  have hcomm : Commute v (centralInvolution n S e) :=
    Subgroup.mem_center_iff.mp (centralInvolution_mem_center n S e) v
  have hr2 : r ^ 2 = 1 := by
    dsimp only [r]
    rw [hcomm.mul_pow, hv2, hx2, one_mul]
  have hrcard : r ^ Nat.card (centralizerOddCore n S e) = 1 :=
    congrArg (fun a : centralizerOddCore n S e => (a : involutionCentralizer n S e))
      (pow_card_eq_one' (x := (⟨r, hr⟩ : centralizerOddCore n S e)))
  have hrone : r = 1 :=
    (pow_eq_one_iff_of_coprime
      (Nat.coprime_two_left.mpr (centralizerOddCore_card_odd n S e))).mp ⟨hr2, hrcard⟩
  apply hne
  apply mul_inv_eq_one.mp
  rw [inv_eq_self_of_orderOf_eq_two hxorder]
  exact hrone

theorem original_scalar_Sylow_action_gives_primewise_layer_coverage
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (P : Sylow ell (centralizerOddCore n S e))
    (v : involutionCentralizer n S e) (hv : orderOf v = 2)
    (hne : v ≠ centralInvolution n S e)
    (hnormalizes : v ∈ Subgroup.normalizer (((P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)))
    (hscalar : (∀ a ∈ (P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype, v * a * v⁻¹ = a) ∨
      (∀ a ∈ (P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype, v * a * v⁻¹ = a⁻¹)) :
    (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) := by
  have hdata := wreathed_centralizer_unique_component_data hnonab n hn S e
    (original_nonfourpoint_fullCenter n hn S e hfour)
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    rw [hdata.layer]
    exact hdata.normal
  let : (show Subgroup (involutionCentralizer n S e ⧸ centralizerOddCore n S e) from
      CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    change (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal
    infer_instance
  have hquasi : CFSG.IsQuasisimple (CFSG.layer (centralizerOddCoreQuotient n S e)) := by
    rw [hdata.layer]
    exact hdata.quasisimple
  have hcentralizer : Subgroup.centralizer (CFSG.layer (centralizerOddCoreQuotient n S e) :
      Set (centralizerOddCoreQuotient n S e)) =
        Subgroup.center (centralizerOddCoreQuotient n S e) := by
    rw [hdata.layer]
    exact hdata.centralizer.trans hdata.ambient_center.symm
  exact noncentral_scalar_Sylow_action_gives_quasisimple_centralizer_coverage
      (centralizerOddCore n S e) (CFSG.layer (centralizerOddCoreQuotient n S e))
      hquasi hcentralizer hell hdiv P v hnormalizes
      (original_second_involution_noncentral n hn S e v hv hne) hscalar

theorem original_all_prime_scalar_pairs_give_layer_coverage
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    (hpairs : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∃ P : Sylow ell (centralizerOddCore n S e), ∃ v : involutionCentralizer n S e,
        orderOf v = 2 ∧ v ≠ centralInvolution n S e ∧
        v ∈ Subgroup.normalizer (((P : Subgroup (centralizerOddCore n S e)).map
          (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ∧
        ((∀ a ∈ (P : Subgroup (centralizerOddCore n S e)).map
          (centralizerOddCore n S e).subtype, v * a * v⁻¹ = a) ∨
          (∀ a ∈ (P : Subgroup (centralizerOddCore n S e)).map
            (centralizerOddCore n S e).subtype, v * a * v⁻¹ = a⁻¹))) :
    ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∃ P : Sylow ell (centralizerOddCore n S e),
        (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
          (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
          (CFSG.layer (centralizerOddCoreQuotient n S e)).comap
            (centralizerOddCoreMap n S e)).map (centralizerOddCoreMap n S e) =
              CFSG.layer (centralizerOddCoreQuotient n S e) := by
  intro ell hell hdiv
  obtain ⟨P, v, hv, hne, hnormalizes, hscalar⟩ := hpairs ell hell hdiv
  exact ⟨P, original_scalar_Sylow_action_gives_primewise_layer_coverage
    hnonab n hn S e hfour hell hdiv P v hv hne hnormalizes hscalar⟩

end CFSG.Wreathed.OriginalScalarSylowCoverage
