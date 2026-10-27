module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.BrauerPermutation
public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound
public import CFSG.CharacterTheory.Wreathed.CoprimeClassUnitRatio
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u v

namespace DoublyTransitive

section Permutation

variable {W : Type*} {Ω : Type*} [Group W] [MulAction W Ω]

theorem ofMulAction_character_eq_card_fixedBy [Fintype Ω] (w : W) :
    (Representation.ofMulAction ℂ W Ω).character w = (Nat.card (MulAction.fixedBy Ω w) : ℂ) := by
  let sigma : Equiv.Perm Ω := MulAction.toPerm w
  let T : MonoidAlgebra ℂ Ω ≃ₗ[ℂ] MonoidAlgebra ℂ Ω :=
    MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ sigma
  have hT : ∀ q, T (MonoidAlgebra.basis Ω ℂ q) = MonoidAlgebra.basis Ω ℂ (sigma q) := by
    intro q
    simp [T]
  have hmap : (Representation.ofMulAction ℂ W Ω w) = T.toLinearMap := by
    apply (MonoidAlgebra.basis Ω ℂ).ext
    intro q
    simp [T, sigma]
  change LinearMap.trace ℂ (MonoidAlgebra ℂ Ω) (Representation.ofMulAction ℂ W Ω w) = _
  rw [hmap, CFSG.Theory.Character.trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis
    (MonoidAlgebra.basis Ω ℂ) sigma T hT]
  congr 1

theorem card_fixedBy_eq_card_iff [Finite Ω] (w : W) :
    Nat.card (MulAction.fixedBy Ω w) = Nat.card Ω ↔ ∀ x : Ω, w • x = x := by
  constructor
  · intro h x
    have huniv : MulAction.fixedBy Ω w = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ Set.finite_univ
      rw [Set.ncard_univ, ← Nat.card_coe_set_eq, h]
    have hx : x ∈ MulAction.fixedBy Ω w := by
      rw [huniv]
      exact Set.mem_univ x
    exact hx
  · intro h
    have huniv : MulAction.fixedBy Ω w = Set.univ := Set.eq_univ_of_forall h
    rw [huniv, Nat.card_coe_set_eq, Set.ncard_univ]

variable [Fintype W]

theorem sum_card_fixedBy_eq_card_group [Fintype Ω] [Nonempty Ω] [MulAction.IsPretransitive W Ω] :
    ∑ w : W, Nat.card (MulAction.fixedBy Ω w) = Nat.card W := by
  let Q1 := Quotient (MulAction.orbitRel W Ω)
  let : Fintype Q1 := Fintype.ofFinite Q1
  have hQ1card : Fintype.card Q1 = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let q : Ω := Classical.choice (inferInstance : Nonempty Ω)
    refine ⟨Quotient.mk (MulAction.orbitRel W Ω) q, fun z => ?_⟩
    rw [← Quotient.out_eq z]
    apply Quotient.sound
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W q (Quotient.out z)
    exact ⟨g, hg⟩
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group W Ω
  simp only [Nat.card_eq_fintype_card]
  rw [show (∑ w : W, Fintype.card (MulAction.fixedBy Ω w)) =
    ∑ w : W, Fintype.card (MulAction.fixedBy Ω w) from rfl]
  convert h using 1
  rw [hQ1card, one_mul]

theorem sum_card_fixedBy_sq_eq_two_mul_card_group [Fintype Ω]
    [h2 : MulAction.IsMultiplyPretransitive W Ω 2] (hn : 2 ≤ Nat.card Ω) :
    ∑ w : W, Nat.card (MulAction.fixedBy Ω w) ^ 2 = 2 * Nat.card W := by
  have htrans : MulAction.IsPretransitive W Ω := MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨a, b, hab⟩ : ∃ a b : Ω, a ≠ b := by
    have : 1 < Fintype.card Ω := by rw [← Nat.card_eq_fintype_card]; omega
    exact Fintype.one_lt_card_iff.mp this
  let Q2 := Quotient (MulAction.orbitRel W (Ω × Ω))
  let : Fintype Q2 := Fintype.ofFinite Q2
  let qdiag : Q2 := Quotient.mk (MulAction.orbitRel W (Ω × Ω)) (a, a)
  let qoff : Q2 := Quotient.mk (MulAction.orbitRel W (Ω × Ω)) (a, b)
  have hall : ∀ z : Q2, z = qdiag ∨ z = qoff := by
    intro z
    rw [← Quotient.out_eq z]
    obtain ⟨x, y⟩ := Quotient.out z
    by_cases hxy : x = y
    · left
      subst hxy
      apply Quotient.sound
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W a x
      exact ⟨g, by simp [hg]⟩
    · right
      apply Quotient.sound
      obtain ⟨g, hg1, hg2⟩ := MulAction.is_two_pretransitive_iff.mp h2 hab hxy
      exact ⟨g, by simp [hg1, hg2]⟩
  have hne : qoff ≠ qdiag := by
    intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hga : g • a = a := congrArg Prod.fst hg
    have hgb : g • a = b := congrArg Prod.snd hg
    exact hab (hga.symm.trans hgb)
  have hQ2card : Fintype.card Q2 = 2 := by
    have huniv : (Finset.univ : Finset Q2) = {qoff, qdiag} := by
      ext z
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases hall z with h | h
      · exact Or.inr h
      · exact Or.inl h
    rw [← Finset.card_univ, huniv, Finset.card_pair hne]
  have hfixProd (w : W) : Fintype.card (MulAction.fixedBy (Ω × Ω) w) =
      Nat.card (MulAction.fixedBy Ω w) ^ 2 := by
    let e : MulAction.fixedBy (Ω × Ω) w ≃ MulAction.fixedBy Ω w × MulAction.fixedBy Ω w :=
      { toFun := fun x => (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
        invFun := fun x => ⟨(x.1.1, x.2.1), Prod.ext x.1.2 x.2.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    rw [Fintype.card_congr e, Fintype.card_prod, ← Nat.card_eq_fintype_card, pow_two]
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group W (Ω × Ω)
  simp only [hfixProd] at h
  rw [h, hQ2card, Nat.card_eq_fintype_card]

theorem prime_dvd_card_fixedBy_of_not_dvd_index [Finite Ω] [MulAction.IsPretransitive W Ω]
    (p : ℕ) [Fact p.Prime] (hp : p ∣ Nat.card Ω) (g : W)
    (hg : ¬ p ∣ (Subgroup.centralizer ({g} : Set W)).index) :
    p ∣ Nat.card (MulAction.fixedBy Ω g) := by
  have hpp : p.Prime := Fact.out
  let S : Sylow p (Subgroup.centralizer ({g} : Set W)) := Classical.ofNonempty
  let P : Subgroup W := (S : Subgroup _).map (Subgroup.centralizer ({g} : Set W)).subtype
  have hPC : P ≤ Subgroup.centralizer ({g} : Set W) := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := S.isPGroup'.map _
  let F : SubMulAction P Ω :=
    { carrier := MulAction.fixedBy Ω g
      smul_mem' := fun y x hx => by
        have hcomm : (y : W) * g = g * y := Subgroup.mem_centralizer_singleton_iff.mp (hPC y.2)
        change g • ((y : W) • x) = (y : W) • x
        rw [← mul_smul, ← hcomm, mul_smul, hx] }
  have hmod := hPp.card_modEq_card_fixedPoints F
  have hempty : Nat.card (MulAction.fixedPoints P F) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨x, hx⟩
    have hle : P ≤ MulAction.stabilizer W (x : Ω) := by
      intro y hy
      have e := congrArg Subtype.val (hx ⟨y, hy⟩)
      exact e
    have hPcard :
        Nat.card P = p ^ padicValNat p (Nat.card (Subgroup.centralizer ({g} : Set W))) := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Sylow.card_eq_multiplicity,
        Nat.factorization_def _ hpp]
    have hW : Nat.card (Subgroup.centralizer ({g} : Set W)) *
        (Subgroup.centralizer ({g} : Set W)).index = Nat.card W := Subgroup.card_mul_index _
    have hvalW : padicValNat p (Nat.card W) =
        padicValNat p (Nat.card (Subgroup.centralizer ({g} : Set W))) := by
      rw [← hW, padicValNat.mul Nat.card_pos.ne' (Subgroup.index_ne_zero_of_finite),
        padicValNat.eq_zero_of_not_dvd hg, add_zero]
    have hstab : Nat.card (MulAction.stabilizer W (x : Ω)) * Nat.card Ω = Nat.card W := by
      rw [← MulAction.index_stabilizer_of_transitive (x := (x : Ω)) (G := W)]
      exact Subgroup.card_mul_index _
    have hdvd : p ^ (padicValNat p (Nat.card W) + 1) ∣ Nat.card W := by
      rw [pow_succ, hvalW, ← hPcard, ← hstab]
      exact mul_dvd_mul (Subgroup.card_dvd_of_le hle) hp
    exact pow_succ_padicValNat_not_dvd Nat.card_pos.ne' hdvd
  rw [hempty] at hmod
  exact (Nat.modEq_zero_iff_dvd.mp hmod)

end Permutation

end DoublyTransitive

open DoublyTransitive

theorem doubly_transitive_prime_divisible_degree_principal_augmentation
    {W : Type u} [Group W] [Fintype W] {Ω : Type v} [Fintype Ω] [MulAction W Ω]
    [MulAction.IsMultiplyPretransitive W Ω 2] (hn : 2 ≤ Nat.card Ω)
    (basis : FiniteIrreducibleCharacterBasis W) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (hp : p ∣ Nat.card Ω) :
    ∃ χ : basis.index,
      (∀ w : W, (basis.representation χ).character w =
        (Nat.card (MulAction.fixedBy Ω w) : ℂ) - 1) ∧
      (basis.representation χ).IsIrreducible ∧
      (∀ w : W, ∃ z : ℤ, (basis.representation χ).character w = z) ∧
      χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      Module.finrank ℂ (basis.representation χ).vector = Nat.card Ω - 1 ∧
      MonoidHom.ker (basis.representation χ).representation = (MulAction.toPermHom W Ω).ker := by
  have htrans : MulAction.IsPretransitive W Ω := MulAction.isPretransitive_of_is_two_pretransitive
  have hΩne : Nonempty Ω := by
    have : 0 < Nat.card Ω := by omega
    exact (Nat.card_pos_iff.mp this).1
  let perm : FiniteComplexRepresentation.{u, v} W :=
    { vector := MonoidAlgebra ℂ Ω, representation := Representation.ofMulAction ℂ W Ω }
  have hperm : ∀ w, perm.character w = (Nat.card (MulAction.fixedBy Ω w) : ℂ) :=
    fun w => ofMulAction_character_eq_card_fixedBy w
  choose m hm using characterPairing_basis_natural basis perm
  have hexp : ∀ w, perm.character w =
      ∑ θ, (m θ : ℂ) * (basis.representation θ).character w := by
    intro w
    have e := congrFun (character_eq_sum_multiplicity basis perm) w
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm] using e
  have hcardW : (Nat.card W : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hm1 : m principal = 1 := by
    have e : characterPairing perm.character (basis.representation principal).character = 1 := by
      unfold characterPairing
      simp only [hperm, hprincipal, Pi.one_apply, mul_one]
      have hsum := sum_card_fixedBy_eq_card_group (W := W) (Ω := Ω)
      rw [show (∑ w : W, (Nat.card (MulAction.fixedBy Ω w) : ℂ)) = (Nat.card W : ℂ) by
        exact_mod_cast hsum]
      field_simp
    rw [hm principal] at e
    exact_mod_cast e
  have hnorm : ∑ θ, m θ ^ 2 = 2 := by
    have e1 : characterPairing perm.character perm.character = 2 := by
      unfold characterPairing
      simp only [hperm, MulAction.fixedBy_inv]
      have hsum := sum_card_fixedBy_sq_eq_two_mul_card_group (W := W) (Ω := Ω) hn
      have hsumC : (∑ w : W, (Nat.card (MulAction.fixedBy Ω w) : ℂ) *
          (Nat.card (MulAction.fixedBy Ω w) : ℂ)) = 2 * (Nat.card W : ℂ) := by
        have h' : ∑ w : W, Nat.card (MulAction.fixedBy Ω w) * Nat.card (MulAction.fixedBy Ω w) =
            2 * Nat.card W := by simpa only [pow_two] using hsum
        exact_mod_cast h'
      rw [hsumC]
      field_simp
    have e2 : characterPairing perm.character perm.character = ∑ θ, (m θ : ℂ) * m θ := by
      have hfun : perm.character =
          fun w => ∑ θ, (m θ : ℂ) * (basis.representation θ).character w := funext hexp
      calc characterPairing perm.character perm.character
          = characterPairing (fun w => ∑ θ, (m θ : ℂ) * (basis.representation θ).character w)
              perm.character := by rw [← hfun]
        _ = ∑ θ, (m θ : ℂ) * characterPairing (basis.representation θ).character
              perm.character := characterPairing_expansion_left _ _ _
        _ = ∑ θ, (m θ : ℂ) * m θ :=
            Finset.sum_congr rfl fun θ _ => by rw [characterPairing_comm, hm θ]
    rw [e2] at e1
    have e3 : ((∑ θ, m θ ^ 2 : ℕ) : ℂ) = 2 := by
      push_cast
      simpa only [pow_two] using e1
    exact_mod_cast e3
  have hrest : ∑ θ ∈ Finset.univ.erase principal, m θ ^ 2 = 1 := by
    have e := Finset.add_sum_erase Finset.univ (fun θ => m θ ^ 2) (Finset.mem_univ principal)
    rw [hm1, hnorm] at e
    omega
  obtain ⟨θ₀, hθ₀mem, hθ₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [hrest]; norm_num : ∑ θ ∈ Finset.univ.erase principal, m θ ^ 2 ≠ 0)
  have hθ₀p : θ₀ ≠ principal := Finset.ne_of_mem_erase hθ₀mem
  have hθ₀1 : m θ₀ = 1 := by
    have hle : m θ₀ ^ 2 ≤ 1 := hrest ▸ Finset.single_le_sum (f := fun θ => m θ ^ 2)
      (fun _ _ => Nat.zero_le _) hθ₀mem
    have hpos : 0 < m θ₀ := Nat.pos_of_ne_zero fun h => hθ₀ne (by simp [h])
    nlinarith
  have hzero : ∀ θ, θ ≠ principal → θ ≠ θ₀ → m θ = 0 := by
    intro θ h1 h2
    have e := Finset.add_sum_erase (Finset.univ.erase principal) (fun θ => m θ ^ 2) hθ₀mem
    rw [hrest, hθ₀1] at e
    have hsum0 : ∑ θ ∈ (Finset.univ.erase principal).erase θ₀, m θ ^ 2 = 0 := by
      simp only [one_pow] at e
      omega
    have hmem : θ ∈ (Finset.univ.erase principal).erase θ₀ := by simp [h1, h2]
    exact pow_eq_zero_iff two_ne_zero |>.mp ((Finset.sum_eq_zero_iff.mp hsum0) θ hmem)
  have hchar : ∀ w, (basis.representation θ₀).character w =
      (Nat.card (MulAction.fixedBy Ω w) : ℂ) - 1 := by
    intro w
    have e := hexp w
    rw [hperm w, ← Finset.sum_subset (Finset.subset_univ ({principal, θ₀} : Finset basis.index))
      (fun θ _ hθ => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hθ
        rw [hzero θ hθ.1 hθ.2, Nat.cast_zero, zero_mul]),
      Finset.sum_pair hθ₀p.symm, hm1, hθ₀1, hprincipal] at e
    simp only [Nat.cast_one, one_mul, Pi.one_apply] at e
    linear_combination -e
  have hfix1 : Nat.card (MulAction.fixedBy Ω (1 : W)) = Nat.card Ω :=
    (card_fixedBy_eq_card_iff (1 : W)).mpr fun x => one_smul W x
  have hdeg1 : (basis.representation θ₀).character 1 = (Nat.card Ω : ℂ) - 1 := by
    rw [hchar 1, hfix1]
  have hfin : Module.finrank ℂ (basis.representation θ₀).vector = Nat.card Ω - 1 := by
    have e : ((Module.finrank ℂ (basis.representation θ₀).vector : ℕ) : ℂ) =
        ((Nat.card Ω - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ Nat.card Ω), Nat.cast_one, ← hdeg1]
      exact (Representation.char_one _).symm
    exact_mod_cast e
  have hker : MonoidHom.ker (basis.representation θ₀).representation =
      (MulAction.toPermHom W Ω).ker := by
    apply le_antisymm
    · intro w hw
      rw [MonoidHom.mem_ker] at hw ⊢
      have hval : (basis.representation θ₀).character w =
          (basis.representation θ₀).character 1 := by
        have h1 : (basis.representation θ₀).representation 1 = 1 := map_one _
        change LinearMap.trace ℂ _ ((basis.representation θ₀).representation w) =
          LinearMap.trace ℂ _ ((basis.representation θ₀).representation 1)
        rw [hw, h1]
      rw [hchar w, hchar 1, hfix1] at hval
      have hcard : Nat.card (MulAction.fixedBy Ω w) = Nat.card Ω := by
        have e : (Nat.card (MulAction.fixedBy Ω w) : ℂ) = Nat.card Ω := by
          linear_combination hval
        exact_mod_cast e
      have hall := (card_fixedBy_eq_card_iff w).mp hcard
      ext x
      simpa using hall x
    · refine CFSG.LyonsUnitaryFour.le_ker_of_character_eq_degree _ _ fun h hh => ?_
      rw [MonoidHom.mem_ker] at hh
      have hall : ∀ x : Ω, h • x = x := fun x => by
        have e := congrArg (fun σ : Equiv.Perm Ω => σ x) hh
        simpa using e
      change (basis.representation θ₀).character h = (basis.representation θ₀).character 1
      rw [hchar h, hchar 1, hfix1, (card_fixedBy_eq_card_iff h).mpr hall]
  have hblock : θ₀ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    rw [coefficientBlock_mem_iff, sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
    apply centralCharacterResidueHom_eq_of_class_values
    intro c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk g)
      with hv
    set k := (Subgroup.centralizer ({g} : Set W)).index with hk
    have hval : ∀ label, (localCentralCharacterHom basis ideal label v : ℂ) =
        (k : ℂ) * (basis.representation label).character g /
          (basis.representation label).character 1 := fun label =>
      CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis g label
    have hωp : localCentralCharacterHom basis ideal principal v =
        (k : localizedComplexIntegerRing ideal) := by
      apply Subtype.ext
      rw [hval, hprincipal]
      simp
    have hn1 : (Nat.card Ω : ℂ) - 1 ≠ 0 := by
      intro h
      have h' : (Nat.card Ω : ℂ) = 1 := by linear_combination h
      have h'' : Nat.card Ω = 1 := by exact_mod_cast h'
      omega
    have hO : ((Nat.card Ω : localizedComplexIntegerRing ideal) - 1) *
        localCentralCharacterHom basis ideal θ₀ v =
        (k : localizedComplexIntegerRing ideal) *
          ((Nat.card (MulAction.fixedBy Ω g) : localizedComplexIntegerRing ideal) - 1) := by
      apply Subtype.ext
      push_cast
      rw [hval, hchar g, hdeg1]
      field_simp
    have hres := congrArg (localizedComplexIntegerResidue ideal) hO
    rw [map_mul, map_mul, map_sub, map_sub, map_one, map_natCast, map_natCast,
      map_natCast] at hres
    have hn0 : ((Nat.card Ω : ℕ) : ComplexAlgebraicIntegers ⧸ ideal) = 0 :=
      (CharP.cast_eq_zero_iff _ p _).mpr hp
    have hkey : ((k : ℕ) : ComplexAlgebraicIntegers ⧸ ideal) *
        ((Nat.card (MulAction.fixedBy Ω g) : ℕ) : ComplexAlgebraicIntegers ⧸ ideal) = 0 := by
      by_cases hkp : p ∣ k
      · rw [(CharP.cast_eq_zero_iff _ p k).mpr hkp, zero_mul]
      · rw [(CharP.cast_eq_zero_iff _ p _).mpr
          (prime_dvd_card_fixedBy_of_not_dvd_index p hp g hkp), mul_zero]
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal v) =
      localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal θ₀ v)
    rw [hωp, map_natCast]
    rw [hn0] at hres
    linear_combination hres + hkey
  refine ⟨θ₀, hchar, basis.irreducible θ₀, fun w => ⟨(Nat.card (MulAction.fixedBy Ω w) : ℤ) - 1,
    by rw [hchar w]; push_cast; ring⟩, hblock, hfin, hker⟩

end CFSG.Semidihedral.Principal
