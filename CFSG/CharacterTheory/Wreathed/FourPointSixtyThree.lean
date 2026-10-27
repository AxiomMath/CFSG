module

public import CFSG.CharacterTheory.Wreathed.FourPointSixtyThreeSupport
public import CFSG.CharacterTheory.Wreathed.FourPointPrincipalDegrees
public import CFSG.CharacterTheory.Wreathed.FaithfulInvolutionTrace

public noncomputable section

namespace CFSG.Wreathed.FourPointSixtyThree

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour
  CFSG.Wreathed.OddNormalQuotientInvolutions

open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_odd_core_centralization_and_sixty_three_involutions
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let aN : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let C := orderFourCentralizer n S e
    n = 2 ∧ kernelCentralizer R aN = ⊤ ∧ C = N ∧
    (∀ y : N, orderOf y = 2 → ∀ r ∈ R, y * r = r * y) ∧
    (∀ y : N, orderOf y = 2 → y ∉ Subgroup.center N → (kernelCentralizer R y).index = 1) ∧
    (∃ ρR : FiniteComplexRepresentation.{0, 0} R, Module.finrank ℂ ρR.vector = 2 ∧
      MonoidHom.ker ρR.representation = ⊥) ∧
    Nat.card N = 96 * Nat.card R ∧ Nat.card G = 6048 * Nat.card R ∧ N.index = 63 ∧
    Nat.card {y : N // orderOf y = 2} = 7 ∧ Nat.card {g : G // orderOf g = 2} = 63 := by
  intro N R aN C
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, ⟨Φ, hΦ⟩, hdeg⟩ :=
    FourPointPrincipalDegrees.four_point_principal_degrees_and_original_odd_core_order hnonab 2
      hn S e alpha
  obtain ⟨⟨z, hzC, hzodd, hπz⟩, ⟨y₀, hy₀2, hy₀Φ⟩, horder, hblock⟩ := hdeg Φ hΦ
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨-, -, -, -, -, γ, hγB, hγdeg, -, hγx, hγa, -, -⟩ :=
    hblock z hzC hzodd hπz ideal basis principal hprincipal
  set x : G := wreathModelHom S e (Original.x (2 ^ 2)) with hxdef
  set a : G := wreathModelHom S e (Original.a (2 ^ 2)) with hadef
  let ρ := (basis.representation γ).representation
  have hγx' : ρ.character x = -2 := hγx
  have hγa' : ρ.character a = -2 := hγa
  have hdim6 : Module.finrank ℂ (basis.representation γ).vector = 6 := hγdeg
  have hne : (basis.representation γ).character ≠ 1 := by
    intro h
    have h1 : (basis.representation γ).character 1 = 1 := by
      rw [h]
      rfl
    rw [FiniteComplexRepresentation.character, Representation.char_one, hdim6] at h1
    norm_num at h1
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff _).mp
    (FourPointGaussianColumns.ker_eq_bot_of_character_ne_one (basis.representation γ)
      (basis.irreducible γ) hne)
  obtain ⟨-, -, hgauss⟩ :=
    FourPointGaussianColumns.four_point_global_gaussian_columns_and_conjugate_pair_dichotomy
      hnonab 2 hn S e alpha
  obtain ⟨-, -, hgauss⟩ := hgauss Φ hΦ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hxr, -⟩ :=
    hgauss y₀ hy₀2 hy₀Φ z hzC hzodd hπz ideal basis principal hprincipal Complex.I Complex.I_sq
  have hconst : ∀ r ∈ R.map N.subtype, ρ.character (x * r) = ρ.character x := by
    rintro _ ⟨r, hr, rfl⟩
    have h := hxr γ hγB r (FourPointOrderEight.odd_orderOf_of_mem_centralizerOddCore 2 S e hr)
    simp only [show r ∈ centralizerOddCore 2 S e from hr, ↓reduceIte, mul_one] at h
    have h' : ρ.character (x * r) =
        ρ.character (x * z) + (ρ.character x - ρ.character (x * z)) := h
    rw [Subgroup.coe_subtype, h']
    ring
  have ha4 : orderOf a = 2 ^ 2 := orderOf_wreathModelHom_a 2 S e
  have hxa2 : x = a ^ 2 := wreathModelHom_x_eq 2 S e
  have hx2 : orderOf x = 2 := by
    rw [hxa2, orderOf_pow_of_dvd (by norm_num) (by rw [ha4]; norm_num), ha4]
    norm_num
  have hR' : R.map N.subtype ≤ Subgroup.centralizer {x} := Subgroup.map_subtype_le R
  obtain ⟨hinvP, hfaithP, hdimP, -, htr⟩ :=
    faithful_involution_eigenspace_extremal_trace_centralization ρ hinj hx2 (R.map N.subtype)
      hR' hconst
  have hk : Module.finrank ℂ (LinearMap.ker (ρ x - 1)) = 2 := by
    rw [hdim6, hγx'] at hdimP
    have h : (Module.finrank ℂ (LinearMap.ker (ρ x - 1)) : ℂ) = 2 := by
      linear_combination hdimP / 2
    exact_mod_cast h
  have hcomm : ∀ h : N, ρ.character h = -2 → ρ.character (x * h) = -2 →
      ∀ r ∈ R, h * r = r * h := by
    intro h h1 h2 r hr
    have hnorm : (h : G) ∈ Subgroup.normalizer ((R.map N.subtype : Subgroup G) : Set G) := by
      apply Subgroup.le_normalizer_map N.subtype
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top h)
    have htrace : ‖ρ.character h + ρ.character (x * h)‖ =
        2 * (Module.finrank ℂ (LinearMap.ker (ρ x - 1)) : ℝ) := by
      rw [h1, h2, hk]
      norm_num
    have key := htr h h.2 hnorm htrace r (Subgroup.mem_map_of_mem _ hr)
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp key)
  have hxa : x * a = a⁻¹ := by
    have h4 : a ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← ha4, pow_orderOf_eq_one]
    rw [hxa2, ← pow_succ]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h4])
  have hγxa : ρ.character (x * a) = -2 := by
    rw [hxa]
    have h := finite_character_conjugate_inverse (basis.representation γ) a
    have h' : starRingEnd ℂ (ρ.character a) = ρ.character a⁻¹ := h
    rw [← h', hγa', map_neg, map_ofNat]
  have hRa : ∀ r ∈ R, aN * r = r * aN := hcomm aN hγa' hγxa
  have hker_a : kernelCentralizer R aN = ⊤ := by
    refine Subgroup.subgroupOf_eq_top.mpr fun r hr => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hRa r hr).symm
  have hCN : C = N := by
    refine le_antisymm (orderFourCentralizer_le 2 S e) fun g hg => ?_
    obtain ⟨r, hr, c, hc, hgrc⟩ := orderFour_factorization 2 hn S e ⟨g, hg⟩
    have hg' : g = (r : G) * (c : G) := congrArg Subtype.val hgrc
    have hra : (r : G) * a = a * r := (congrArg Subtype.val (hRa r hr)).symm
    have hca : (c : G) * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    change g ∈ Subgroup.centralizer {a}
    rw [Subgroup.mem_centralizer_singleton_iff, hg', mul_assoc, hca, ← mul_assoc, hra,
      mul_assoc]
  have hinvR : ∀ y : N, orderOf y = 2 → ∀ r ∈ R, y * r = r * y := by
    intro y hy r hr
    by_cases hyx : (y : G) = x
    · apply Subtype.ext
      change (y : G) * r = r * y
      rw [hyx]
      exact (Subgroup.mem_centralizer_singleton_iff.mp r.2).symm
    have hyG : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
    have hyx' : (y : G) * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp y.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hxy2 : orderOf (x * y) = 2 := by
      apply orderOf_eq_prime
      · have hx1 : x ^ 2 = 1 := by rw [← hx2, pow_orderOf_eq_one]
        have hy1 : (y : G) ^ 2 = 1 := by rw [← hyG, pow_orderOf_eq_one]
        have hcxy : Commute x (y : G) := hyx'.symm
        rw [hcxy.mul_pow, hx1, hy1, one_mul]
      · intro h1
        apply hyx
        have hxinv : x⁻¹ = x := by
          rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx2, pow_orderOf_eq_one]
        rw [← hxinv]
        exact eq_inv_of_mul_eq_one_right h1
    have hval : ∀ g : G, orderOf g = 2 → ρ.character g = -2 := fun g hg => by
      obtain ⟨c, hc⟩ := isConj_iff.mp
        (all_involutions_conjugate_of_simple_wreathed hnonab 2 hn S e x g hx2 hg)
      rw [← hc, Representation.char_conj, hγx']
    exact hcomm y (hval y hyG) (hval _ hxy2) r hr
  have hker : ∀ y : N, orderOf y = 2 → kernelCentralizer R y = ⊤ := fun y hy =>
    Subgroup.subgroupOf_eq_top.mpr fun r hr => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hinvR y hy r hr).symm
  have hplane : ∃ ρR : FiniteComplexRepresentation.{0, 0} R, Module.finrank ℂ ρR.vector = 2 ∧
      MonoidHom.ker ρR.representation = ⊥ := by
    refine exists_faithful_plane ρ (N.subtype.comp R.subtype) (LinearMap.ker (ρ x - 1))
      (fun r v hv => ?_) (fun r hr => ?_) hk
    · exact hinvP _ (Subgroup.mem_map_of_mem _ r.2) hv
    · have h := hfaithP _ (Subgroup.mem_map_of_mem _ r.2) hr
      exact Subtype.ext (Subtype.ext h)
  obtain ⟨-, -, hord⟩ :=
    FourPointPrincipalOrderScalar.four_point_actual_principal_order_scalar hnonab 2 hn S e alpha
  obtain ⟨-, hyall⟩ := hord Φ hΦ
  obtain ⟨-, hclass, -, hinvcls, hnc, -, -⟩ := hyall y₀ hy₀2 hy₀Φ
  have he : (kernelCentralizer R y₀).index = 1 := by
    rw [hker y₀ hy₀2, Subgroup.index_top]
  obtain ⟨hG, hN, hidx⟩ := horder y₀ hy₀2 hy₀Φ
  have hG' : Nat.card G = 6048 * Nat.card R * (kernelCentralizer R y₀).index ^ 2 := hG
  have hidx' : N.index = 63 * (kernelCentralizer R y₀).index ^ 2 := hidx
  rw [he] at hG' hidx' hclass
  have hN7 : Nat.card {t : N // orderOf t = 2} = 7 :=
    card_involutions_of_two_classes _ y₀ 6 hinvcls hnc hclass
  have hidx63 : N.index = 63 := by
    rw [hidx']
    norm_num
  have hG63 : Nat.card {g : G // orderOf g = 2} = 63 := by
    rw [card_involutions_of_one_class x hx2 fun g hg =>
      all_involutions_conjugate_of_simple_wreathed hnonab 2 hn S e x g hx2 hg]
    exact hidx63
  refine ⟨rfl, hker_a, hCN, hinvR, fun y hy _ => by rw [hker y hy, Subgroup.index_top], hplane,
    hN, by rw [hG']; ring, hidx63, hN7, hG63⟩

end CFSG.Wreathed.FourPointSixtyThree
