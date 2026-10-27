module

public import CFSG.CharacterTheory.Wreathed.FourPointCompleteModel
public import CFSG.CharacterTheory.Wreathed.InvolutionInducedCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointPrincipalOrderScalar

open Equiv CFSG.Wreathed CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.OddNormalQuotientInvolutions
  CFSG.Wreathed.InvolutionInducedCharacters

theorem twoUnit_not_isSquare : ¬ IsSquare twoUnit := by
  rintro ⟨r, hr⟩
  have h := congrArg (fun v : (ZMod 3)ˣ => (v : ZMod 3)) hr
  simp only [Units.val_mul, twoUnit_val] at h
  have key : ∀ z : ZMod 3, (2 : ZMod 3) ≠ z * z := by decide
  exact key _ h

theorem sum_inflated_block {K Q : Type} [Group K] [Fintype K] [Group Q] [Fintype Q]
    (basisK : FiniteIrreducibleCharacterBasis K) (basisQ : FiniteIrreducibleCharacterBasis Q)
    (π : K →* Q) (hπ : Function.Surjective π) (B : Finset basisK.index)
    (hB : ∀ χ, χ ∈ B ↔ ∃ θ : basisQ.index,
      (basisK.representation χ).character = (basisQ.representation θ).character ∘ π)
    (hB' : ∀ θ : basisQ.index, ∃ χ ∈ B,
      (basisK.representation χ).character = (basisQ.representation θ).character ∘ π)
    (F : (K → ℂ) → ℂ) :
    ∑ χ ∈ B, F (basisK.representation χ).character =
      ∑ θ, F ((basisQ.representation θ).character ∘ π) := by
  classical
  choose g hgB hg using hB'
  have hginj : Function.Injective g := by
    intro θ θ' h
    apply basisQ.distinct
    funext q
    obtain ⟨k, rfl⟩ := hπ q
    have h1 := congrFun (hg θ) k
    have h2 := congrFun (hg θ') k
    rw [h] at h1
    simp only [Function.comp_apply] at h1 h2
    change (basisQ.representation θ).character (π k) = (basisQ.representation θ').character (π k)
    rw [← h1, h2]
  have himage : B = Finset.univ.image g := by
    ext χ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hχ
      obtain ⟨θ, hθ⟩ := (hB χ).mp hχ
      exact ⟨θ, basisK.distinct ((hg θ).trans hθ.symm)⟩
    · rintro ⟨θ, rfl⟩
      exact hgB θ
  rw [himage, Finset.sum_image fun θ _ θ' _ h => hginj h]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [hg θ]

theorem four_point_actual_principal_order_scalar {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let H := centralizerOddCoreQuotient n S e
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let st : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let xN : N := centralInvolution n S e
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let iF := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let y₀ : W := u ^ 2 * iF (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3))
    n = 2 ∧ (∃ Φ : W ≃* H, Φ (u ^ 2) = π st) ∧
    ∀ Φ : W ≃* H, Φ (u ^ 2) = π st →
      (∃ y : N, orderOf y = 2 ∧ π y = Φ y₀) ∧
      ∀ y : N, orderOf y = 2 → π y = Φ y₀ →
        let eR : ℕ := (kernelCentralizer R y).index
        let c : ℕ := Nat.card N
        c = 96 * Nat.card R ∧ Nat.card (ConjClasses.mk y).carrier = 6 * eR ∧
        Nat.card (Subgroup.centralizer {π y}) = 16 ∧
        (∀ t : N, orderOf t = 2 ↔ t = xN ∨ IsConj y t) ∧ ¬ IsConj xN y ∧
        IsConj y (xN * y) ∧
        ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
          (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
          (_ : (basis.representation principal).character = 1),
          (Nat.card G : ℂ) * ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
              principal,
            (basis.representation χ).character x ^ 3 / (basis.representation χ).character 1 =
            16 * c * (6 * eR) ^ 2 ∧
          16 * c * (6 * eR) ^ 2 = 55296 * Nat.card R * eR ^ 2 ∧
          ∀ (basisN : FiniteIrreducibleCharacterBasis N) (principalN : basisN.index)
            (_ : (basisN.representation principalN).character = 1),
            (∀ χ, χ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN ↔
              R ≤ MonoidHom.ker (basisN.representation χ).representation) ∧
            (coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN).card =
              16 := by
  intro H N R π st xN x W u iF y₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  obtain ⟨Φ₀, hΦ₀, -⟩ := exists_four_point_model_equiv hnonab n hn S e alpha
  refine ⟨hn2, ⟨Φ₀, hΦ₀⟩, ?_⟩
  intro Φ hΦ
  subst hn2
  have hbot : ∀ σ ∈ (⊥ : Subgroup (ZMod 3 ≃+* ZMod 3)),
      σ ((twoUnit : (ZMod 3)ˣ) : ZMod 3) = twoUnit := by
    intro σ hσ
    rw [Subgroup.mem_bot] at hσ
    subst hσ
    rfl
  let Φ' : SemilinearExtension (ZMod 3) twoUnit (2 ^ 2) (wreathModulus_pos 2)
      (wreathModulus_even hn) ⊥ hbot ≃* involutionCentralizer 2 S e ⧸ centralizerOddCore 2 S e :=
    (semidirectBotEquiv _).symm.trans Φ
  have hΦ'inl : ∀ w, Φ' (SemidirectProduct.inl w) = Φ w := by
    intro w
    change Φ ((semidirectBotEquiv _).symm (SemidirectProduct.inl w)) = Φ w
    congr 1
    exact (semidirectBotEquiv _).symm_apply_eq.mpr rfl
  have hst2 : st ^ 2 = xN := by
    apply Subtype.ext
    change (wreathModelHom S e (Original.a (2 ^ 2))) ^ 2 = wreathModelHom S e (Original.x (2 ^ 2))
    rw [← map_pow]
    rfl
  have hΦ' : Φ' (SemidirectProduct.inl (cyclicGenerator (ZMod 3) twoUnit (2 ^ 2)
      (wreathModulus_pos 2) (wreathModulus_even hn) ^ (2 ^ 2))) =
      QuotientGroup.mk' (centralizerOddCore 2 S e)
        ⟨wreathModelHom S e (Original.x (2 ^ 2)),
          Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
    rw [hΦ'inl]
    change Φ (u ^ 4) = π xN
    have hu4 : u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
    rw [hu4, map_pow, hΦ, ← map_pow, hst2]
  have hR : Odd (Nat.card (centralizerOddCore 2 S e)) := centralizerOddCore_card_odd 2 S e
  have hII := actual_centralizer_involution_induced_characters_and_principal_order_identity
    hnonab 2 hn S e (centralizerOddCore 2 S e) hR (F := ZMod 3) (p := 3) (f := 1)
    Nat.prime_three (by decide) le_rfl (by simp) twoUnit twoUnit_not_isSquare ⊥ hbot
    (by simp) Φ' hΦ'
  have hpow : (2 : ℕ) ^ 2 / 4 = 1 := by norm_num
  simp only [hpow, pow_one] at hII
  obtain ⟨hyex, hII⟩ := hII
  have hy₀ : ∀ v, v = Φ' (SemidirectProduct.inl (cyclicGenerator (ZMod 3) twoUnit (2 ^ 2)
      (wreathModulus_pos 2) (wreathModulus_even hn) ^ 2 *
      specialInclusion (ZMod 3) twoUnit (2 ^ 2) (wreathModulus_pos 2) (wreathModulus_even hn)
        (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3)))) ↔ v = Φ y₀ := by
    intro v
    rw [hΦ'inl]
    rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy2, hyΦ⟩ := hyex
    exact ⟨y, hy2, (hy₀ _).mp hyΦ⟩
  intro y hy2 hyΦ eR c
  obtain ⟨⟨hclasses, hxy, hc, hcent, hcls, hxyconj⟩, -, horder⟩ :=
    hII y hy2 ((hy₀ _).mpr hyΦ)
  have hq : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  have hd : Nat.card (⊥ : Subgroup (ZMod 3 ≃+* ZMod 3)) = 1 := by simp
  have hε : (if Nat.card (ZMod 3) % 4 = 1 then (1 : ℤ) else -1) = -1 := by rw [hq]; rfl
  rw [hq, hd] at hc
  rw [hε, hq] at hcls hcent
  have hc96 : c = 96 * Nat.card R := by
    change Nat.card N = _
    rw [hc]
    norm_num
    ring
  have hA : (Nat.card (ConjClasses.mk y).carrier : ℤ) = 6 * eR := by
    rw [hcls]
    simp only [eR]
    ring
  have hAℕ : Nat.card (ConjClasses.mk y).carrier = 6 * eR := by exact_mod_cast hA
  have hQ := odd_normal_quotient_involution_classes_and_centralizers R hR
  have hfib : Nat.card (Subgroup.centralizer {y}) =
      Nat.card (kernelCentralizer R y) * Nat.card (Subgroup.centralizer {π y}) :=
    (hQ.2.2 (π y) y hy2 rfl).2.2.1
  have hcentH : Nat.card (Subgroup.centralizer {π y}) = 16 := by
    have h1 : ((Nat.card (kernelCentralizer R y) * Nat.card (Subgroup.centralizer {π y}) : ℕ) : ℤ)
        = Nat.card (kernelCentralizer R y) * 16 := by
      rw [← hfib, hcent]
      norm_num
      ring
    have hpos : 0 < Nat.card (kernelCentralizer R y) := Nat.card_pos
    have h2 : Nat.card (kernelCentralizer R y) * Nat.card (Subgroup.centralizer {π y}) =
        Nat.card (kernelCentralizer R y) * 16 := by exact_mod_cast h1
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  refine ⟨hc96, hAℕ, hcentH, hclasses, hxy, hxyconj, ?_⟩
  intro ideal _ _ basis principal hprincipal
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisH
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalH
  have hFP := fun (basisN : FiniteIrreducibleCharacterBasis N) (principalN : basisN.index)
      (hprincipalN : (basisN.representation principalN).character = 1) =>
    four_point_actual_centralizer_complete_model_and_principal_block hnonab 2 hn S e alpha ideal
      basisH principalH hprincipalH basisN principalN hprincipalN
  obtain ⟨basisN⟩ := finiteIrreducibleCharacterBasis_exists (G := N)
  obtain ⟨principalN, hprincipalN⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisN
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalN
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinflI, hinflE, -, -, -⟩ :=
    hFP basisN principalN hprincipalN
  have hloc := horder ideal basis principal hprincipal basisN principalN hprincipalN
  obtain ⟨-, -, hz1, -, -⟩ := hloc
  have hAC : (((kernelCentralizer R y).index * Nat.card (ZMod 3) *
      (Nat.card (ZMod 3) + if Nat.card (ZMod 3) % 4 = 1 then (1 : ℤ) else -1) : ℤ) : ℂ) =
      6 * eR := by
    rw [hε, hq]
    push_cast
    simp only [eR]
    ring
  have hx2N : orderOf xN = 2 := (hclasses xN).mpr (Or.inl rfl)
  have hπsurj : Function.Surjective π := centralizerOddCoreMap_surjective 2 S e
  have hcen : π xN ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨g, rfl⟩ := hπsurj h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hinvH : orderOf (π xN) = 2 := orderOf_mk_eq_two R hR hx2N
  have helH : orderOf (π y) = 2 := orderOf_mk_eq_two R hR hy2
  have hconjH : IsConj (π xN * π y) (π y) := by
    have h := MonoidHom.map_isConj π hxyconj
    rw [map_mul] at h
    exact h.symm
  obtain ⟨-, hweighted⟩ := CFSG.Wreathed.central_involution_conjugate_product_weighted_character_sum
    basisH (π xN) (π y) hcen hinvH helH hconjH (6 * eR : ℂ)
  have hlocal : ∑ ψ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN,
      (basisN.representation ψ).character xN / (basisN.representation ψ).character 1 *
        ((basisN.representation ψ).character xN +
          (6 * eR : ℂ) * (basisN.representation ψ).character y) ^ 2 =
      (6 * eR : ℂ) ^ 2 * 16 := by
    rw [sum_inflated_block basisN basisH π hπsurj _ hinflI hinflE
      (fun f => f xN / f 1 * (f xN + (6 * eR : ℂ) * f y) ^ 2)]
    simp only [Function.comp_apply, map_one]
    rw [hweighted, hcentH]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hz1, hAC]
    calc (Nat.card N : ℂ) * _ = (c : ℂ) * ((6 * eR : ℂ) ^ 2 * 16) := by
          congr 1
      _ = _ := by ring
  · rw [hc96]
    ring
  · intro basisN' principalN' hprincipalN'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hker, -, -, -, hcard16, -⟩ :=
      hFP basisN' principalN' hprincipalN'
    exact ⟨hker, hcard16⟩


end CFSG.Wreathed.FourPointPrincipalOrderScalar
