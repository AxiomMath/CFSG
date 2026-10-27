module

public import CFSG.CharacterTheory.Wreathed.InvolutionInducedCharactersSupport
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearInvolutionClasses
public import CFSG.CharacterTheory.Wreathed.ConditionalCompatibleModelData
public import CFSG.CharacterTheory.OddOrderBasics.Induction
public import CFSG.CharacterTheory.CentralInvolutionParity
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralPrincipalInducedFamily
public import CFSG.CharacterTheory.Wreathed.CentralSylowPowerQuotients
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.InvolutionInducedCharacters

open CFSG.Wreathed CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.OddNormalQuotientInvolutions
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2Abelianization
  Matrix

theorem basis_character_mem_blocksIrr' {A : Type} [Group A] [Fintype A]
    (basis : FiniteIrreducibleCharacterBasis A) (l : basis.index) :
    (basis.representation l).character ∈ BlocksIrr A :=
  ⟨(basis.representation l).vector, inferInstance, inferInstance, inferInstance,
    (basis.representation l).representation, basis.irreducible l, rfl⟩

theorem actual_centralizer_involution_induced_characters_and_principal_order_identity_of_one_class
    {G : Type} [Group G] [Fintype G]
    (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (R : Subgroup (involutionCentralizer n S e)) [R.Normal] (hR : Odd (Nat.card R))
    {F : Type} [Field F] [Fintype F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (b : Fˣ) (hb : ¬ IsSquare b)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (hd : Odd (Nat.card Sigma))
    (Φ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* involutionCentralizer n S e ⧸ R)
    (hΦ : Φ (SemidirectProduct.inl (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) ^ (2 ^ n))) = QuotientGroup.mk' R
        ⟨wreathModelHom S e (Original.x (2 ^ n)),
          Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    let m : ℕ := 2 ^ n
    let N : Subgroup G := involutionCentralizer n S e
    let x : G := wreathModelHom S e (Original.x m)
    let xN : N := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    let π : N →* N ⧸ R := QuotientGroup.mk' R
    let H := SemilinearExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma
    let ι : CentralExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) →* H :=
      SemidirectProduct.inl
    let u := cyclicGenerator F b m (wreathModulus_pos n) (wreathModulus_even hn)
    let y₀ := (u ^ 2) ^ (m / 4) *
      specialInclusion F b m (wreathModulus_pos n) (wreathModulus_even hn) (weyl F)
    let q : ℕ := Nat.card F
    let d : ℕ := Nat.card Sigma
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    (∃ y : N, orderOf y = 2 ∧ π y = Φ (ι y₀)) ∧
    ∀ y : N, orderOf y = 2 → π y = Φ (ι y₀) →
      let A : ℤ := (kernelCentralizer R y).index * q * (q + ε)
      let c : ℕ := Nat.card N
      ((∀ t : N, orderOf t = 2 ↔ t = xN ∨ IsConj y t) ∧ ¬ IsConj xN y ∧
        c = Nat.card R * m * d * q * (q ^ 2 - 1) ∧
        (Nat.card (Subgroup.centralizer {y}) : ℤ) =
          Nat.card (kernelCentralizer R y) * m * d * (q - ε) ∧
        (Nat.card (ConjClasses.mk y).carrier : ℤ) = A ∧ IsConj y (xN * y)) ∧
      (∀ (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ)
          (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd d),
        let Ξ : Fin m → Fin d → H → ℂ := fun r s h =>
          (linearCharacter F b m (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma σ₀
            hgen ζm ζd hζm hζd r s h : ℂ) * (fixedPointCount H (Omega F) h - 1)
        let ψ : Fin m → Fin d → N → ℂ := fun r s g => Ξ r s (Φ.symm (π g))
        let Γ : Fin m → Fin d → G → ℂ := fun r s => inducedFunction N (ψ r s)
        ∀ r s, (∃ data : FiniteComplexRepresentation.{0, 0} G, data.character = Γ r s) ∧
          Γ r s 1 = (q : ℂ) * N.index ∧ Γ r s x = q + ε * (-1) ^ r.val * A ∧
          BlocksInnerProduct (Γ r s) 1 = 0) ∧
      ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
        [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
        (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
        (_ : (basis.representation principal).character = 1)
        (basisN : FiniteIrreducibleCharacterBasis N) (principalN : basisN.index)
        (_ : (basisN.representation principalN).character = 1),
        let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
        let B₀N := coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN
        let rhs : N → ℂ := fun z => (c : ℂ) * ∑ ψ ∈ B₀N,
          ((basisN.representation ψ).character xN + A * (basisN.representation ψ).character y) ^ 2 *
            (basisN.representation ψ).character (xN * z) / (basisN.representation ψ).character 1
        (∀ z : N, Odd (orderOf z) →
          (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basis.representation χ).character x ^ 2 *
            (basis.representation χ).character (x * z) / (basis.representation χ).character 1 =
          rhs z) ∧
        (∀ ψ ∈ B₀N, (basisN.representation ψ).character xN /
            (basisN.representation ψ).character 1 = 1 ∨
          (basisN.representation ψ).character xN / (basisN.representation ψ).character 1 = -1) ∧
        (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basis.representation χ).character x ^ 3 /
            (basis.representation χ).character 1 =
          (c : ℂ) * ∑ ψ ∈ B₀N, (basisN.representation ψ).character xN /
            (basisN.representation ψ).character 1 *
              ((basisN.representation ψ).character xN +
                A * (basisN.representation ψ).character y) ^ 2 ∧
        (∀ ψ ∈ B₀N, R ≤ MonoidHom.ker (basisN.representation ψ).representation ∧
          ∃! ξ : H → ℂ, ξ ∈ BlocksIrr H ∧
            (basisN.representation ψ).character = fun g => ξ (Φ.symm (π g))) ∧
        ∀ z z' : N, Odd (orderOf z) → Odd (orderOf z') → π z = π z' → rhs z = rhs z' := by
  intro m N x xN π H ι u y₀ q d ε
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm4 : 4 ∣ m := ⟨2 ^ (n - 2), by
    simp only [m]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega⟩
  have hSL := semilinear_involution_classes_and_augmentation_values hp hpodd hf hcard b hb m
    (wreathModulus_pos n) (wreathModulus_even hn) hm4 Sigma hSigma hd
  obtain ⟨-, -, -, hιy₀ord, hinvH, -, hxy₀, hcardH, hcentH, hclassH, hyconj, -, -, -, hchar⟩ :=
    hSL
  have hxN : (xN : G) = x := rfl
  have hxc : xN ∈ Subgroup.center N := Subgroup.mem_center_iff.mpr fun g => Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hx2 : orderOf x = 2 := by
    have ha : orderOf (wreathModelHom S e (Original.a (2 ^ n))) = 2 ^ n :=
      orderOf_wreathModelHom_a n S e
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hhalf : 2 ^ n / 2 = 2 ^ k := by
      rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hdvd : 2 ^ k ∣ orderOf (wreathModelHom S e (Original.a (2 ^ n))) := by
      rw [ha, hk]
      exact pow_dvd_pow 2 k.le_succ
    have hxa := wreathModelHom_x_eq n S e
    change orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2
    rw [hxa, hhalf, orderOf_pow_of_dvd (by positivity) hdvd, ha, hk, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hx2N : orderOf xN = 2 := by rw [← Subgroup.orderOf_coe, hxN, hx2]
  have hxΦ : π xN = Φ (ι (u ^ m)) := hΦ.symm
  have hQ := odd_normal_quotient_involution_classes_and_centralizers R hR
  have hyexists : ∃ y : N, orderOf y = 2 ∧ π y = Φ (ι y₀) := by
    have h2 : orderOf (Φ (ι y₀)) = 2 := by rw [MulEquiv.orderOf_eq]; exact hιy₀ord
    obtain ⟨t, ht, htv⟩ := hQ.2.1 _ h2
    exact ⟨t, ht, htv⟩
  refine ⟨hyexists, ?_⟩
  intro y hy2 hyΦ A c
  obtain ⟨hclasses, hxy⟩ := involutions_of_quotient_model R hR Φ hinvH hxy₀ hxc hx2N hxΦ hy2 hyΦ
  have hfib := hQ.2.2 (π y) y hy2 rfl
  have hcentΦ : Nat.card (Subgroup.centralizer {π y}) =
      Nat.card (Subgroup.centralizer {ι y₀}) := by
    rw [hyΦ]
    refine Nat.card_congr ((Equiv.subtypeEquiv Φ.toEquiv ?_).symm)
    intro h
    simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv, ← map_mul, Φ.injective.eq_iff]
  have hclassΦ : Nat.card (ConjClasses.mk (π y)).carrier =
      Nat.card {h : H // IsConj (ι y₀) h} := by
    rw [hyΦ]
    have hcarrier : (ConjClasses.mk (Φ (ι y₀))).carrier = {v | IsConj (Φ (ι y₀)) v} := by
      ext v
      simp only [ConjClasses.mem_carrier_iff_mk_eq, Set.mem_ofPred_eq]
      exact ⟨fun h' => ConjClasses.mk_eq_mk_iff_isConj.mp h'.symm,
        fun h' => (ConjClasses.mk_eq_mk_iff_isConj.mpr h').symm⟩
    rw [hcarrier]
    change Nat.card {v // IsConj (Φ (ι y₀)) v} = _
    refine Nat.card_congr ((Equiv.subtypeEquiv Φ.toEquiv ?_).symm)
    intro h
    constructor
    · intro h'
      have := MonoidHom.map_isConj Φ.toMonoidHom h'
      simpa using this
    · intro h'
      have := MonoidHom.map_isConj Φ.symm.toMonoidHom h'
      simpa using this
  have hcardA : (Nat.card (ConjClasses.mk y).carrier : ℤ) = A := by
    rw [hfib.2.2.2.1]
    push_cast
    rw [hclassΦ, hclassH]
    simp only [A]
    ring
  have hxyconj : IsConj y (xN * y) := by
    have hcomm : Commute xN y := (Subgroup.mem_center_iff.mp hxc y).symm
    have hxsq : xN ^ 2 = 1 := by
      have h := pow_orderOf_eq_one xN
      rwa [hx2N] at h
    have hysq : y ^ 2 = 1 := by
      have h := pow_orderOf_eq_one y
      rwa [hy2] at h
    have hxinv : xN⁻¹ = xN := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hxsq]
    have hne : xN * y ≠ 1 := by
      intro h
      have hy : y = xN := by
        rw [← hxinv]
        exact eq_inv_of_mul_eq_one_right h
      apply hxy
      rw [hy]
      exact IsConj.refl _
    have hord : orderOf (xN * y) = 2 := by
      apply orderOf_eq_prime
      · rw [hcomm.mul_pow, hxsq, hysq, one_mul]
      · exact hne
    apply isConj_of_isConj_mk R hR hy2 hord
    have hπxy : π (xN * y) = Φ (ι (u ^ m * y₀)) := by
      rw [map_mul, hxΦ, hyΦ, ← map_mul, ← map_mul]
    rw [hπxy, hyΦ]
    exact MonoidHom.map_isConj (Φ.toMonoidHom.comp ι) hyconj
  have hfusion := hinv
  have hconjG : ∀ h : N, IsConj (xN : G) (h : G) ↔ h = xN ∨ IsConj y h := by
    intro h
    constructor
    · intro h'
      apply (hclasses h).mp
      obtain ⟨g, hg⟩ := isConj_iff.mp h'
      rw [← Subgroup.orderOf_coe, ← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hxN, hx2]
    · rintro (rfl | h')
      · exact IsConj.refl _
      · have hyG : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy2]
        exact (hfusion x (y : G) hx2 hyG).trans (MonoidHom.map_isConj N.subtype h')
  have hcardAC : (Nat.card (ConjClasses.mk y).carrier : ℂ) = A := by exact_mod_cast hcardA
  have hq1 : (q : ℂ) ≠ 1 := by
    have hp3 : 3 ≤ p := by
      obtain ⟨k, hk⟩ := hpodd
      have := hp.two_le
      omega
    have hq3 : 3 ≤ q := by
      change 3 ≤ Nat.card F
      rw [hcard]
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf
    exact_mod_cast (show q ≠ 1 by omega)
  refine ⟨⟨hclasses, hxy, ?_, ?_, hcardA, hxyconj⟩, ?_, ?_⟩
  ·
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [show Nat.card (N ⧸ R) = Nat.card H from Nat.card_congr Φ.toEquiv.symm, hcardH] at h1
    change Nat.card N = _
    rw [h1]
    ring
  ·
    rw [hfib.2.2.1]
    push_cast
    rw [hcentΦ, hcentH]
    ring
  ·
    intro σ₀ hgen ζm ζd hζm hζd Ξ ψ Γ r s
    obtain ⟨-, -, hΞirr, hval, -⟩ := hchar σ₀ hgen ζm ζd hζm hζd
    have hsurj : Function.Surjective (Φ.symm.toMonoidHom.comp π) :=
      Φ.symm.surjective.comp (QuotientGroup.mk'_surjective R)
    have hψirr : ψ r s ∈ BlocksIrr N :=
      CFSG.Semidihedral.Principal.comp_mem_blocksIrr (Φ.symm.toMonoidHom.comp π) hsurj
        (hΞirr r s).1
    have hψclass : ∀ g h : N, ψ r s (g * h * g⁻¹) = ψ r s h := by
      obtain ⟨V, i1, i2, i3, ρ, -, hρ⟩ := hψirr
      intro g h
      rw [← hρ]
      exact Representation.char_conj ρ h g
    have hψx : ψ r s xN = q := by
      change Ξ r s (Φ.symm (π xN)) = q
      rw [hxΦ, MulEquiv.symm_apply_apply]
      exact (hval r s).2.2.1
    have hψy : ψ r s y = ε * (-1) ^ r.val := by
      change Ξ r s (Φ.symm (π y)) = _
      rw [hyΦ, MulEquiv.symm_apply_apply]
      exact (hval r s).2.2.2
    have hψ1 : ψ r s 1 = q := by
      change Ξ r s (Φ.symm (π 1)) = q
      rw [map_one, map_one]
      exact (hΞirr r s).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨V, i1, i2, i3, ρ, -, hρ⟩ := hψirr
      obtain ⟨W, iW1, iW2, iW3, σ, hσ⟩ :=
        (CFSG.OddOrderBasics.induction_preserves_characters N).1 V ρ
      refine ⟨{ vector := W, representation := σ }, ?_⟩
      change σ.character = inducedFunction N (ψ r s)
      rw [hσ, hρ]
    · change inducedFunction N (ψ r s) 1 = _
      rw [(CFSG.OddOrderBasics.induced_class_function_identities N).2.2.1, hψ1]
      ring
    · change inducedFunction N (ψ r s) (xN : G) = _
      rw [inducedFunction_two_classes N rfl hconjG (fun h => hxy h.symm) (ψ r s) hψclass, hψx,
        hψy, hcardAC]
      ring
    · change BlocksInnerProduct (inducedFunction N (ψ r s)) 1 = 0
      rw [CFSG.blocksInnerProduct_inducedFunction_left N (ψ r s) 1 (fun _ _ => rfl)]
      have hone : (1 : N → ℂ) ∈ BlocksIrr N :=
        ⟨(principalFiniteComplexRepresentation N).vector, inferInstance, inferInstance,
          inferInstance, (principalFiniteComplexRepresentation N).representation,
          principalFiniteComplexRepresentation_isIrreducible N,
          principalFiniteComplexRepresentation_character N⟩
      have h := CFSG.blocksInnerProduct_irreducible ⟨ψ r s, hψirr⟩ ⟨1, hone⟩
      have hne : (⟨ψ r s, hψirr⟩ : BlocksIrr N) ≠ ⟨1, hone⟩ := by
        intro heq
        have h1 := congrFun (congrArg Subtype.val heq) 1
        simp only [Pi.one_apply] at h1
        rw [hψ1] at h1
        exact hq1 h1
      rw [ite_eq_right hne] at h
      exact h
  ·
    intro ideal _ _ basis principal hprincipal basisN principalN hprincipalN B₀ B₀N rhs
    have hxx : x * x = 1 := by
      rw [← pow_two, ← hx2, pow_orderOf_eq_one]
    have hEH : CFSG.LyonsUnitaryFour.extendedCentralizer x ≤ N := by
      intro g hg
      change g⁻¹ * x * g = x ∨ g⁻¹ * x * g = x⁻¹ at hg
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      rw [hxinv, or_self] at hg
      change g ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * x = g * (g⁻¹ * x * g) := by rw [hg]
        _ = x * g := by group
    have hu : orderOf (xN : G) ∣ 2 ^ 1 := by rw [hxN, hx2, pow_one]
    have hOF := CFSG.LyonsUnitaryFour.brauer_principal_order_formula basis ideal 2 principal
      hprincipal hxx hxx N xN 1 hu hEH basisN principalN hprincipalN
    have hcw : ∀ ψ : basisN.index,
        CFSG.LyonsUnitaryFour.classWeight N (basisN.representation ψ).character x =
          (c : ℂ)⁻¹ * ((basisN.representation ψ).character xN +
            A * (basisN.representation ψ).character y) := by
      intro ψ
      rw [classWeight_two_classes N hconjG (fun h => hxy h.symm) _
        (fun g h => Representation.char_conj _ h g), hcardAC]
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hparity := CFSG.CentralInvolution.central_involution_character_parity xN hxc hx2N
    have hsign : ∀ ψ : basisN.index,
        ((basisN.representation ψ).character xN / (basisN.representation ψ).character 1 = 1 ∨
          (basisN.representation ψ).character xN / (basisN.representation ψ).character 1 = -1) ∧
        ∀ h, (basisN.representation ψ).character (h * xN) =
          (basisN.representation ψ).character xN / (basisN.representation ψ).character 1 *
            (basisN.representation ψ).character h := fun ψ =>
      ⟨(hparity.1 _ (basis_character_mem_blocksIrr' basisN ψ)).1,
        (hparity.1 _ (basis_character_mem_blocksIrr' basisN ψ)).2.1⟩
    have hmain : ∀ z : N, Odd (orderOf z) →
        (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basis.representation χ).character x ^ 2 *
          (basis.representation χ).character (x * z) / (basis.representation χ).character 1 =
        rhs z := by
      intro z hz
      have h := hOF.1 z z.2 (Nat.coprime_two_left.mpr hz)
      have hl : ∀ χ ∈ B₀, (basis.representation χ).character x ^ 2 *
          (basis.representation χ).character (x * z) / (basis.representation χ).character 1 =
          (basis.representation χ).character x * (basis.representation χ).character x *
            (basis.representation χ).character ((xN * z : N) : G) /
              (basis.representation χ).character 1 := fun χ _ => by
        rw [Subgroup.coe_mul, hxN]
        ring
      rw [Finset.sum_congr rfl hl, h]
      simp only [rhs, hcw]
      change (c : ℂ) * c * c * _ = _
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      field_simp
    have : Fintype (N ⧸ R) := Fintype.ofFinite _
    obtain ⟨qBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := N ⧸ R)
    obtain ⟨qPrincipal, hqPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
      qBasis (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
    rw [principalFiniteComplexRepresentation_character] at hqPrincipal
    have hR2 : ¬ 2 ∣ Nat.card R := fun h =>
      (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr h)
    have hinfl := CFSG.Semidihedral.Principal.normal_prime_kernel_principal_block_inflation
      basisN ideal 2 R hR2 qBasis principalN hprincipalN qPrincipal hqPrincipal
    have hθ : ∀ ψ ∈ B₀N, ∃ θ : qBasis.index, (basisN.representation ψ).character =
        (qBasis.representation θ).character ∘ QuotientGroup.mk' R := fun ψ hψ => by
      obtain ⟨θ, -, hθ⟩ := (hinfl.1 ψ).mp hψ
      exact ⟨θ, hθ⟩
    refine ⟨hmain, fun ψ _ => (hsign ψ).1, ?_, ?_, ?_⟩
    · have h := hmain 1 (by rw [orderOf_one]; exact odd_one)
      have hlhs : ∑ χ ∈ B₀, (basis.representation χ).character x ^ 3 /
          (basis.representation χ).character 1 =
          ∑ χ ∈ B₀, (basis.representation χ).character x ^ 2 *
            (basis.representation χ).character (x * ((1 : N) : G)) /
              (basis.representation χ).character 1 :=
        Finset.sum_congr rfl fun χ _ => by rw [Subgroup.coe_one, mul_one]; ring
      rw [hlhs, h]
      simp only [rhs, mul_one]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      ring
    · intro ψ hψ
      obtain ⟨θ, hθψ⟩ := hθ ψ hψ
      refine ⟨(hinfl.2.2.2 ψ).mpr ⟨θ, hθψ⟩, ?_⟩
      refine ⟨fun h => (qBasis.representation θ).character (Φ h), ⟨?_, ?_⟩, ?_⟩
      · exact CFSG.Semidihedral.Principal.comp_mem_blocksIrr Φ.toMonoidHom Φ.surjective
          (basis_character_mem_blocksIrr' qBasis θ)
      · rw [hθψ]
        funext g
        simp only [Function.comp_apply, MulEquiv.apply_symm_apply]
        rfl
      · rintro ξ ⟨-, hξ⟩
        funext h
        obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective R (Φ h)
        have h1 := congrFun hξ g
        have h2 := congrFun hθψ g
        simp only [Function.comp_apply] at h1 h2
        change (QuotientGroup.mk' R) g = _ at hg
        rw [hg, MulEquiv.symm_apply_apply] at h1
        rw [← h1, h2]
        change (qBasis.representation θ).character (QuotientGroup.mk' R g) = _
        rw [hg]
    · intro z z' _ _ hzz'
      simp only [rhs]
      congr 1
      refine Finset.sum_congr rfl fun ψ hψ => ?_
      obtain ⟨θ, hθψ⟩ := hθ ψ hψ
      have hcomm : ∀ w : N, xN * w = w * xN := fun w =>
        (Subgroup.mem_center_iff.mp hxc w).symm
      have hzeq : (basisN.representation ψ).character z =
          (basisN.representation ψ).character z' := by
        rw [hθψ]
        simp only [Function.comp_apply]
        exact congrArg _ hzz'
      rw [hcomm z, hcomm z', (hsign ψ).2 z, (hsign ψ).2 z', hzeq]


theorem actual_centralizer_involution_induced_characters_and_principal_order_identity
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (R : Subgroup (involutionCentralizer n S e)) [R.Normal] (hR : Odd (Nat.card R))
    {F : Type} [Field F] [Fintype F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (b : Fˣ) (hb : ¬ IsSquare b)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (hd : Odd (Nat.card Sigma))
    (Φ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* involutionCentralizer n S e ⧸ R)
    (hΦ : Φ (SemidirectProduct.inl (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) ^ (2 ^ n))) = QuotientGroup.mk' R
        ⟨wreathModelHom S e (Original.x (2 ^ n)),
          Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    let m : ℕ := 2 ^ n
    let N : Subgroup G := involutionCentralizer n S e
    let x : G := wreathModelHom S e (Original.x m)
    let xN : N := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    let π : N →* N ⧸ R := QuotientGroup.mk' R
    let H := SemilinearExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma
    let ι : CentralExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) →* H :=
      SemidirectProduct.inl
    let u := cyclicGenerator F b m (wreathModulus_pos n) (wreathModulus_even hn)
    let y₀ := (u ^ 2) ^ (m / 4) *
      specialInclusion F b m (wreathModulus_pos n) (wreathModulus_even hn) (weyl F)
    let q : ℕ := Nat.card F
    let d : ℕ := Nat.card Sigma
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    (∃ y : N, orderOf y = 2 ∧ π y = Φ (ι y₀)) ∧
    ∀ y : N, orderOf y = 2 → π y = Φ (ι y₀) →
      let A : ℤ := (kernelCentralizer R y).index * q * (q + ε)
      let c : ℕ := Nat.card N
      ((∀ t : N, orderOf t = 2 ↔ t = xN ∨ IsConj y t) ∧ ¬ IsConj xN y ∧
        c = Nat.card R * m * d * q * (q ^ 2 - 1) ∧
        (Nat.card (Subgroup.centralizer {y}) : ℤ) =
          Nat.card (kernelCentralizer R y) * m * d * (q - ε) ∧
        (Nat.card (ConjClasses.mk y).carrier : ℤ) = A ∧ IsConj y (xN * y)) ∧
      (∀ (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ)
          (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd d),
        let Ξ : Fin m → Fin d → H → ℂ := fun r s h =>
          (linearCharacter F b m (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma σ₀
            hgen ζm ζd hζm hζd r s h : ℂ) * (fixedPointCount H (Omega F) h - 1)
        let ψ : Fin m → Fin d → N → ℂ := fun r s g => Ξ r s (Φ.symm (π g))
        let Γ : Fin m → Fin d → G → ℂ := fun r s => inducedFunction N (ψ r s)
        ∀ r s, (∃ data : FiniteComplexRepresentation.{0, 0} G, data.character = Γ r s) ∧
          Γ r s 1 = (q : ℂ) * N.index ∧ Γ r s x = q + ε * (-1) ^ r.val * A ∧
          BlocksInnerProduct (Γ r s) 1 = 0) ∧
      ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
        [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
        (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
        (_ : (basis.representation principal).character = 1)
        (basisN : FiniteIrreducibleCharacterBasis N) (principalN : basisN.index)
        (_ : (basisN.representation principalN).character = 1),
        let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
        let B₀N := coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN
        let rhs : N → ℂ := fun z => (c : ℂ) * ∑ ψ ∈ B₀N,
          ((basisN.representation ψ).character xN + A * (basisN.representation ψ).character y) ^ 2 *
            (basisN.representation ψ).character (xN * z) / (basisN.representation ψ).character 1
        (∀ z : N, Odd (orderOf z) →
          (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basis.representation χ).character x ^ 2 *
            (basis.representation χ).character (x * z) / (basis.representation χ).character 1 =
          rhs z) ∧
        (∀ ψ ∈ B₀N, (basisN.representation ψ).character xN /
            (basisN.representation ψ).character 1 = 1 ∨
          (basisN.representation ψ).character xN / (basisN.representation ψ).character 1 = -1) ∧
        (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basis.representation χ).character x ^ 3 /
            (basis.representation χ).character 1 =
          (c : ℂ) * ∑ ψ ∈ B₀N, (basisN.representation ψ).character xN /
            (basisN.representation ψ).character 1 *
              ((basisN.representation ψ).character xN +
                A * (basisN.representation ψ).character y) ^ 2 ∧
        (∀ ψ ∈ B₀N, R ≤ MonoidHom.ker (basisN.representation ψ).representation ∧
          ∃! ξ : H → ℂ, ξ ∈ BlocksIrr H ∧
            (basisN.representation ψ).character = fun g => ξ (Φ.symm (π g))) ∧
        ∀ z z' : N, Odd (orderOf z) → Odd (orderOf z') → π z = π z' → rhs z = rhs z' :=
  actual_centralizer_involution_induced_characters_and_principal_order_identity_of_one_class
    (simple_wreathed_one_involution_class_and_local_S3 hnonab n hn S e).2.2.1 n hn S e R hR hp
    hpodd hf hcard b hb Sigma hSigma hd Φ hΦ

end CFSG.Wreathed.InvolutionInducedCharacters
