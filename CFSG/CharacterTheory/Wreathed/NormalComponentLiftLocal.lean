module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftGroup
public import CFSG.CharacterTheory.Wreathed.TorusSplitting

public section

open scoped Classical

namespace CFSG.Wreathed.NormalComponentLift

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.BaseFourCentralizerStructure
  CFSG.Wreathed.TorusSplitting

variable {G : Type} [Group G]

abbrev nModel (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Wreath (2 ^ n) →* involutionCentralizer n S e :=
  wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)

theorem nModel_mem_sylow (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (w : Wreath (2 ^ n)) :
    nModel n hn S e w ∈ (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) := by
  rw [← wreathModelHom_range (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)]
  exact ⟨w, rfl⟩

theorem nModel_pow_two_pow (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (w : Wreath (2 ^ n)) : ∃ k : ℕ, nModel n hn S e w ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := (centralizerSylow n hn S e).isPGroup' ⟨_, nModel_mem_sylow n hn S e w⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem centralizerOddCoreMap_nModel_injective [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective ((centralizerOddCoreMap n S e).comp (nModel n hn S e)) := by
  intro a b hab
  apply wreathModelHom_injective (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
  have h := centralizerOddCoreMap_sylow_injective n hn S e
    (a₁ := ⟨_, nModel_mem_sylow n hn S e a⟩) (a₂ := ⟨_, nModel_mem_sylow n hn S e b⟩) hab
  exact congrArg Subtype.val h

theorem x2_mul_swap_ne (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.z (2 ^ n)) ≠
      wreathModelHom S e (Original.z (2 ^ n)) * wreathModelHom S e (Original.x2 (2 ^ n)) := by
  intro h
  set s := wreathModelHom S e (Original.s (2 ^ n))
  set t := wreathModelHom S e (Original.t (2 ^ n))
  set w := wreathModelHom S e (Original.z (2 ^ n))
  have hy : wreathModelHom S e (Original.x2 (2 ^ n)) = s ^ (2 ^ n / 2) := by
    rw [Original.x2, map_pow]
  rw [hy] at h
  have hconj : w⁻¹ * s ^ (2 ^ n / 2) * w = t ^ (2 ^ n / 2) := by
    have hc := conj_pow (a := w⁻¹) (b := s) (i := 2 ^ n / 2)
    rw [inv_inv] at hc
    rw [← hc, actual_swap_conj_s S e]
  have hfix : w⁻¹ * s ^ (2 ^ n / 2) * w = s ^ (2 ^ n / 2) := by
    rw [mul_assoc, h, inv_mul_cancel_left]
  have hst : s ^ (2 ^ n / 2) = t ^ (2 ^ n / 2) := hfix.symm.trans hconj
  have hone : s ^ (2 ^ n / 2) = 1 := by
    have hd := Subgroup.disjoint_def.mp (zpowers_disjoint S e)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _)
      (hst ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers t) _)
    exact hd
  have hdvd := orderOf_dvd_of_pow_eq_one hone
  rw [actual_orderOf_s S e] at hdvd
  have hpos : 0 < 2 ^ n / 2 := Nat.div_pos (Nat.le_self_pow (by omega) 2) (by norm_num)
  have hle := Nat.le_of_dvd hpos hdvd
  have hlt : 2 ^ n / 2 < 2 ^ n := Nat.div_lt_self (by positivity) (by norm_num)
  omega

theorem d_conj_x2 (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.z (2 ^ n))) *
      wreathModelHom S e (Original.x2 (2 ^ n)) *
      (wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.z (2 ^ n)))⁻¹ =
    wreathModelHom S e (Original.x (2 ^ n)) * wreathModelHom S e (Original.x2 (2 ^ n)) := by
  set s := wreathModelHom S e (Original.s (2 ^ n))
  set t := wreathModelHom S e (Original.t (2 ^ n))
  set w := wreathModelHom S e (Original.z (2 ^ n))
  have hy : wreathModelHom S e (Original.x2 (2 ^ n)) = s ^ (2 ^ n / 2) := by
    rw [Original.x2, map_pow]
  have hx : wreathModelHom S e (Original.x (2 ^ n)) = s ^ (2 ^ n / 2) * t ^ (2 ^ n / 2) := by
    rw [Original.x, Original.a, map_pow, map_mul]
    exact (actual_s_t_commute S e).mul_pow _
  have hws : w * s * w⁻¹ = t := by
    rw [← map_inv, ← map_mul, ← map_mul, Original.z_conjugates_s]
  have hwy : w * s ^ (2 ^ n / 2) * w⁻¹ = t ^ (2 ^ n / 2) := by
    rw [← conj_pow, hws]
  have hst : Commute (s ^ (2 ^ n / 2)) (t ^ (2 ^ n / 2)) :=
    ((actual_s_t_commute S e).pow_left _).pow_right _
  have hs : s ^ (2 ^ n / 2) * s ^ (2 ^ n / 2) = 1 := by
    rw [← pow_add, show 2 ^ n / 2 + 2 ^ n / 2 = 2 ^ n by
      have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega, ← actual_orderOf_s S e, pow_orderOf_eq_one]
  rw [hy, hx]
  calc s ^ (2 ^ n / 2) * w * s ^ (2 ^ n / 2) * (s ^ (2 ^ n / 2) * w)⁻¹ =
      s ^ (2 ^ n / 2) * (w * s ^ (2 ^ n / 2) * w⁻¹) * (s ^ (2 ^ n / 2))⁻¹ := by group
    _ = s ^ (2 ^ n / 2) * t ^ (2 ^ n / 2) * (s ^ (2 ^ n / 2))⁻¹ := by rw [hwy]
    _ = t ^ (2 ^ n / 2) := by rw [hst.eq, mul_inv_cancel_right]
    _ = s ^ (2 ^ n / 2) * t ^ (2 ^ n / 2) * s ^ (2 ^ n / 2) := by
      rw [hst.eq, mul_assoc, hs, mul_one]

section Lift

variable [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
  (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
  (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))

include hnonab hfour in
theorem centralizerOddCoreMap_d_mem_layer :
    centralizerOddCoreMap n S e (nModel n hn S e (Original.d (2 ^ n))) ∈
      CFSG.layer (centralizerOddCoreQuotient n S e) := by
  have hU := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  have h1 : nModel n hn S e (Original.d (2 ^ n)) ∈ centralizerQuaternion n hn S e :=
    Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
  have h3 := Subgroup.mem_map_of_mem (centralizerOddCoreMap n S e) h1
  rw [← centralizerLiftedLayerSylow_image hnonab n hn S e hfour] at h3
  obtain ⟨u, -, hu⟩ := h3
  rw [hU.layer, ← hu]
  exact u.2

include hnonab hfour in
theorem d_mem
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hJR : J ⊓ centralizerOddCore n S e = ⊥) : nModel n hn S e (Original.d (2 ^ n)) ∈ J := by
  obtain ⟨k, hk⟩ := nModel_pow_two_pow n hn S e (Original.d (2 ^ n))
  have hmem := centralizerOddCoreMap_d_mem_layer hnonab n hn S e hfour
  rw [← hJM] at hmem
  exact mem_of_pow_two_pow hJR (centralizerOddCore_card_odd n S e) hmem hk

omit [Finite G] [IsSimpleGroup G] in
theorem x2_mem_four :
    wreathModelHom S e (Original.x2 (2 ^ n)) ∈ Subgroup.closure
      {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} :=
  Subgroup.subset_closure (Or.inl (by rw [Original.x2, map_pow]))

omit [Finite G] [IsSimpleGroup G] in
theorem nModel_d_coe :
    (nModel n hn S e (Original.d (2 ^ n)) : G) =
      wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.z (2 ^ n)) := by
  change wreathModelHom S e (Original.x2 (2 ^ n) * Original.z (2 ^ n)) = _
  rw [map_mul]

include hnonab hfour in
theorem swap_comm_torusFixedCore
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hJR : J ⊓ centralizerOddCore n S e = ⊥) :
    ∀ z ∈ torusFixedCore n S e, wreathModelHom S e (Original.z (2 ^ n)) * z =
      z * wreathModelHom S e (Original.z (2 ^ n)) := by
  rintro z ⟨⟨r, hr, rfl⟩, hzT⟩
  set y := wreathModelHom S e (Original.x2 (2 ^ n))
  set w := wreathModelHom S e (Original.z (2 ^ n))
  have hyz : y * (r : G) = r * y := (Subgroup.mem_centralizer_iff.mp hzT y (x2_mem_four n S e))
  have hdr := commute_of_inf_eq_bot hJR (d_mem hnonab n hn S e hfour J hJM hJR) hr
  have hdz : (y * w) * (r : G) = r * (y * w) := by
    rw [← nModel_d_coe n hn S e]
    exact congrArg Subtype.val hdr
  have hw : w = y⁻¹ * (y * w) := by group
  rw [hw]
  calc y⁻¹ * (y * w) * (r : G) = y⁻¹ * ((y * w) * r) := by group
    _ = y⁻¹ * (r * (y * w)) := by rw [hdz]
    _ = (y⁻¹ * r) * (y * w) := by group
    _ = (r * y⁻¹) * (y * w) := by
        rw [show y⁻¹ * (r : G) = r * y⁻¹ by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hyz, mul_assoc, mul_inv_cancel, mul_one]]
    _ = r * (y⁻¹ * (y * w)) := by group

omit [IsSimpleGroup G] in
theorem centralizerOddCoreMap_y_not_mem_center :
    centralizerOddCoreMap n S e (nModel n hn S e (Original.x2 (2 ^ n))) ∉
      Subgroup.center (centralizerOddCoreQuotient n S e) := by
  intro h
  have hc := Subgroup.mem_center_iff.mp h
    (centralizerOddCoreMap n S e (nModel n hn S e (Original.z (2 ^ n))))
  have hinj := centralizerOddCoreMap_nModel_injective n hn S e
    (a₁ := Original.z (2 ^ n) * Original.x2 (2 ^ n))
    (a₂ := Original.x2 (2 ^ n) * Original.z (2 ^ n)) (by
      simp only [MonoidHom.comp_apply, map_mul]
      exact hc)
  apply x2_mul_swap_ne n hn S e
  have := congrArg (wreathModelHom S e) hinj
  rw [map_mul, map_mul] at this
  exact this.symm

omit [IsSimpleGroup G] in
theorem orderOf_centralizerOddCoreMap_y :
    orderOf (centralizerOddCoreMap n S e (nModel n hn S e (Original.x2 (2 ^ n)))) = 2 := by
  rw [← MonoidHom.comp_apply, orderOf_injective _ (centralizerOddCoreMap_nModel_injective n hn S e),
    ← orderOf_injective _ (wreathModelHom_injective S e)]
  exact CompatibleFamilies.orderOf_x2 S e hn

end Lift

end CFSG.Wreathed.NormalComponentLift
