module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeFiveBalance
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralOddEigenspaceBound
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityFull
public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport
public import CFSG.CharacterTheory.Wreathed.OriginalStationarityCoverageCriterion

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.Wreathed CFSG.Assembly.LowTwoRank CFSG.TwoRankLowerBound.Helpers
  CFSG.Wreathed.OriginalStationarityCoverageCriterion

namespace Five

theorem finrank_eq_finrank_invariants_add_card_mul {G : Type*} {V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (R H : Subgroup G) (hHR : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hconst : ∀ h ∈ H, h ≠ 1 → ∀ r ∈ R, ρ.character (h * r) = ρ.character h) :
    ∃ m : ℕ, Module.finrank ℂ V =
      Module.finrank ℂ (Representation.invariants (ρ.comp R.subtype)) + Nat.card H * m := by
  classical
  let : Fintype R := Fintype.ofFinite R
  set P := CFSG.LyonsUnitaryFour.subgroupAverage ρ R with hPdef
  have hPP : P * P = P := CFSG.LyonsUnitaryFour.subgroupAverage_idempotent ρ R
  have hcomm : ∀ h ∈ H, ρ h * P = P * ρ h := by
    intro h hh
    let c : R ≃ R :=
      { toFun := fun r => ⟨h * r * h⁻¹, hHR h hh r r.2⟩
        invFun := fun r => ⟨h⁻¹ * r * h, by simpa using hHR h⁻¹ (H.inv_mem hh) r r.2⟩
        left_inv := fun r => Subtype.ext (by
          simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one])
        right_inv := fun r => Subtype.ext (by
          simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]) }
    have hsum : ∑ r : R, ρ h * ρ r = ∑ r : R, ρ r * ρ h := by
      refine Fintype.sum_equiv c _ _ fun r => ?_
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [mul_assoc, Equiv.coe_fn_mk, inv_mul_cancel, mul_one, c]
    rw [hPdef, CFSG.LyonsUnitaryFour.subgroupAverage, mul_smul_comm, smul_mul_assoc,
      Finset.mul_sum, Finset.sum_mul, hsum]
  set E := LinearMap.ker P
  have hE : ∀ h ∈ H, ∀ v ∈ E, ρ h v ∈ E := by
    intro h hh v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 := congrArg (fun T : Module.End ℂ V => T v) (hcomm h hh)
    simp only [Module.End.mul_apply, hv, map_zero] at h1
    exact h1.symm
  have htr : ∀ h (hh : h ∈ H), h ≠ 1 → LinearMap.trace ℂ E ((ρ h).restrict (hE h hh)) = 0 := by
    intro h hh h1
    set T := ρ h * (1 - P) with hTdef
    have hT : ∀ v, T v ∈ E := by
      intro v
      rw [LinearMap.mem_ker]
      have h2 : P * T = 0 := by
        rw [hTdef, ← mul_assoc, ← hcomm h hh, mul_assoc, mul_sub, mul_one, hPP, sub_self,
          mul_zero]
      exact congrArg (fun F : Module.End ℂ V => F v) h2
    have hres : (ρ h).restrict (hE h hh) = T.restrict (fun v _ => hT v) := by
      ext v
      have hv : P v = 0 := v.2
      simp only [LinearMap.coe_restrict_apply, hTdef, Module.End.mul_apply, LinearMap.sub_apply,
        Module.End.one_apply, hv, sub_zero]
    rw [hres, LinearMap.trace_restrict_eq_of_forall_mem E T hT, hTdef, mul_sub, mul_one,
      map_sub, CFSG.LyonsUnitaryFour.trace_mul_subgroupAverage]
    have hterm : ∀ r : R, ρ.character (h * (r : G)) = ρ.character h :=
      fun r => hconst h hh h1 r r.2
    rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    have hne : (Nat.card R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    exact sub_self _
  obtain ⟨m, hm⟩ :=
    CFSG.Semidihedral.Principal.CosetConstantEigenspaces.card_dvd_finrank_of_trace_eq_zero
      ρ H E hE htr
  have hrange : LinearMap.range P = Representation.invariants (ρ.comp R.subtype) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact subgroupAverage_mem_invariants ρ R v
    · intro v hv
      exact ⟨v, subgroupAverage_apply_of_mem_invariants ρ R hv⟩
  refine ⟨m, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker P, hrange, ← hm]

variable {G : Type} [Group G] [Fintype G]

theorem principal_character_mul_oddCore
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    {g : G} (hgN : g ∈ involutionCentralizer n S e) {k : ℕ} (hg2 : orderOf g ∣ 2 ^ k)
    (hg1 : g ≠ 1) {r : G}
    (hr : r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) :
    (basis.representation χ).character (g * r) = (basis.representation χ).character g := by
  have := Fact.mk Nat.prime_two
  obtain ⟨r₀, hr₀, rfl⟩ := Subgroup.mem_map.mp hr
  set ψ := (basis.representation χ).representation
  let gN : involutionCentralizer n S e := ⟨g, hgN⟩
  have hcop : Nat.Coprime (orderOf gN) (Nat.card (centralizerOddCore n S e)) := by
    rw [Subgroup.orderOf_mk]
    exact Nat.Coprime.coprime_dvd_left hg2
      ((Nat.coprime_two_left.mpr (centralizerOddCore_card_odd n S e)).pow_left k)
  obtain ⟨r', u, hu, hug⟩ := CFSG.section16_exists_centralizer_coset_conj_of_coprime
    (centralizerOddCore n S e) gN hcop ⟨r₀, hr₀⟩
  have hug' : ((u : involutionCentralizer n S e) : G) * g =
      ((r' : involutionCentralizer n S e) : G)⁻¹ * ((r₀ : G) * g) *
        ((r' : involutionCentralizer n S e) : G) := by
    simpa using congrArg Subtype.val hug
  obtain ⟨huR, hug⟩ := Subgroup.mem_inf.mp hu
  have hugc : ((u : involutionCentralizer n S e) : G) * g =
      g * ((u : involutionCentralizer n S e) : G) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hug
    simpa using congrArg Subtype.val h
  obtain ⟨X, hRX, hXC, hXn, hXcop⟩ :=
    Five.exists_balance_subgroup hnonab n hn S e hfour hmodel hgN hg2 hg1
  have huX : ((u : involutionCentralizer n S e) : G) ∈ X := by
    apply hRX
    exact ⟨⟨_, huR, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr hugc⟩
  have hconst := CFSG.Semidihedral.Principal.principal_character_coset_constant_of_normal basis
    ideal 2 principal hprincipal hχ hg2 X hXC hXn hXcop huX
  calc (basis.representation χ).character (g * (r₀ : G))
      = ψ.character ((r₀ : G) * g) := Representation.char_mul_comm ψ _ _
    _ = ψ.character (((r' : involutionCentralizer n S e) : G)⁻¹ * ((r₀ : G) * g) *
          ((r' : involutionCentralizer n S e) : G)) := by
        simpa using (Representation.char_conj ψ ((r₀ : G) * g)
          ((r' : involutionCentralizer n S e) : G)⁻¹).symm
    _ = ψ.character (g * ((u : involutionCentralizer n S e) : G)) := by rw [← hug', hugc]
    _ = (basis.representation χ).character g := hconst

theorem principal_finrank_eq_finrank_invariants_add_card_mul
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    ∃ m : ℕ, Module.finrank ℂ (basis.representation χ).vector =
      Module.finrank ℂ (Representation.invariants ((basis.representation χ).representation.comp
        ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype).subtype)) +
        Nat.card (S : Subgroup G) * m := by
  set N := involutionCentralizer n S e
  set R := centralizerOddCore n S e
  have hSN : (S : Subgroup G) ≤ N := sylow_le_involutionCentralizer n hn S e
  refine finrank_eq_finrank_invariants_add_card_mul _ (R.map N.subtype) (S : Subgroup G) ?_ ?_
  · rintro h hh _ ⟨r, hr, rfl⟩
    exact ⟨⟨h, hSN hh⟩ * r * ⟨h, hSN hh⟩⁻¹,
      (inferInstance : R.Normal).conj_mem r hr ⟨h, hSN hh⟩, rfl⟩
  · intro h hh h1 r hr
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨h, hh⟩
    have hk2 : orderOf h ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hk
    exact principal_character_mul_oddCore hnonab n hn S e hfour hmodel basis ideal principal
      hprincipal hχ (hSN hh) hk2 h1 hr

theorem exists_principal_label_finrank_eq_thirty_one
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hmodel : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    ∃ χ : basis.index, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      (basis.representation χ).character ≠ 1 ∧
      Module.finrank ℂ (basis.representation χ).vector = 31 := by
  obtain ⟨Q, A, B, D, hQ, -, -, -, hblock, -, hBdeg, -⟩ :=
    SquareRootSmallCharacterRigidity.actual_root_square_root_character_rigidity hnonab n hn S e
      hfour 5 1 Nat.prime_five (by norm_num) le_rfl hmodel ideal
  obtain ⟨hBprincipal, hBne⟩ := hblock B
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hQ31 : Q = 31 := by
    have h : (Q : ℤ) = 31 := by
      rw [hQ]
      norm_num [modFourSign]
    exact_mod_cast h
  have hBimage : (B : G → ℂ) ∈ (fun l => (basis.representation l).character) ''
      ((coefficientBlock basis (localizedComplexIntegerRing ideal) principal : Finset _) :
        Set basis.index) := by
    rw [CFSG.BlockBasics.coefficientBlock_image basis ideal principal, hprincipal]
    exact hBprincipal
  obtain ⟨χ, hχ, hχB⟩ := hBimage
  replace hχB : (basis.representation χ).character = (B : G → ℂ) := hχB
  refine ⟨χ, hχ, by rw [hχB]; exact hBne, ?_⟩
  have h1 : ((Module.finrank ℂ (basis.representation χ).vector : ℕ) : ℂ) = (31 : ℕ) := by
    rw [← Representation.char_one (basis.representation χ).representation, ← hQ31, ← hBdeg,
      ← SquareRootSmallCharacterRigidity.irreducibleDegree_cast]
    exact congrFun hχB 1
  exact_mod_cast h1

end Five

theorem wreathed_five_original_odd_core_trivial
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : p ^ f = 5)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f) :
    centralizerOddCore n S e = ⊥ := by
  obtain ⟨rfl, rfl⟩ := Five.eq_five_and_eq_one_of_pow_eq_five hq5
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨χ, hχ, hne, hdim⟩ := Five.exists_principal_label_finrank_eq_thirty_one hnonab n hn S e
    hfour hmodel basis ideal principal hprincipal
  obtain ⟨m, hm⟩ := Five.principal_finrank_eq_finrank_invariants_add_card_mul hnonab n hn S e
    hfour hmodel basis ideal principal hprincipal hχ
  have hS : Nat.card (S : Subgroup G) = 32 := by
    rw [Nat.card_congr e.toEquiv, card_wreath, Five.wreath_exponent_eq_two hnonab hfour hmodel]
    norm_num
  rw [hS] at hm
  set R := (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype
  set ρ := (basis.representation χ).representation
  have hker : R ≤ MonoidHom.ker ρ := (finrank_invariants_eq_finrank_iff ρ R).mp (by omega)
  rw [FourPointGaussianColumns.ker_eq_bot_of_character_ne_one _ (basis.irreducible χ) hne,
    le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hker
  exact hker

theorem original_all_prime_five
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : p ^ f = 5)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f) :
    OriginalAllPrimeStationarity n S e ∧ OriginalAllPrimeCoverage n S e := by
  obtain ⟨hstat, hcov, -⟩ := original_trivial_oddCore_all_prime_vacuity n S e
    (wreathed_five_original_odd_core_trivial hnonab n hn S e hfour p f hp hpodd hf hq5 hmodel)
  exact ⟨hstat, hcov⟩

end CFSG.Wreathed.OriginalAllPrime
