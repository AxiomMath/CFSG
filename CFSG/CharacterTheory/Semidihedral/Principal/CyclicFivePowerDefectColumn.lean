module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicFivePowerDefectColumnSupport
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterProjectionPairing

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers FivePowerColumn

universe u

theorem cyclic_five_power_alternating_five_centralizer_generator_supported_defect_column
    {G : Type u} [Group G] [Fintype G] [Fact (Nat.Prime 5)]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 5] (a : ℕ) (_ha : 1 ≤ a)
    (W : Subgroup G) [IsCyclic W] (hWcard : Nat.card W = 5 ^ a) (J : Subgroup G)
    (hdisj : W ⊓ J = ⊥)
    (hsup : W ⊔ J = Subgroup.centralizer (W : Set G))
    (hJ : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (hJH : ∀ h ∈ Subgroup.normalizer (W : Set G), ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hinv : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (label : basis.index) (hlabel : coefficientBlockDefect basis ideal 5 label W) :
    let θ : J → ℂ := fun j => (Nat.card (MulAction.fixedBy (Sylow 5 J) j) : ℂ) - 1
    let b : Set (Subgroup.centralizer (W : Set G) → ℂ) := {f | ∃ μ : W →* ℂˣ,
      ∀ (k : Subgroup.centralizer (W : Set G)) (w : W) (j : J), (k : G) = w * j →
        f k = μ w * θ j}
    (∀ basisJ : FiniteIrreducibleCharacterBasis J,
      (∃ l : basisJ.index, (basisJ.representation l).character = θ) ∧
      ∀ l : basisJ.index, Module.finrank ℂ (basisJ.representation l).vector = 5 →
        (basisJ.representation l).character = θ) ∧
    θ 1 = 5 ∧
    (∃ c₀ : localBasis.index,
      (fun l => (localBasis.representation l).character) ''
          (coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀ :
            Set localBasis.index) = b ∧
      ∀ c : localBasis.index,
        brauerNormalizerCharacterResidueHom ideal 5 W (IsPGroup.of_card hWcard)
            (Subgroup.centralizer (W : Set G)) le_rfl (Subgroup.centralizer_le_normalizer _)
            localBasis c = centralCharacterResidueHom basis ideal label ↔
          c ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀) ∧
    (∀ other : basis.index, coefficientBlockDefect basis ideal 5 other W →
      other ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label) ∧
    ∀ t ∈ J, orderOf t = 2 → ∀ lam : W →* ℂˣ, orderOf lam = 5 →
      (∃ ψ : Subgroup.centralizer (W : Set G) → ℂ,
        ∀ (k : Subgroup.centralizer (W : Set G)) (w : W) (j : J), (k : G) = w * j →
          ψ k = θ j * ((lam w : ℂ) - 1)) ∧
      ∀ ψ : Subgroup.centralizer (W : Set G) → ℂ,
        (∀ (k : Subgroup.centralizer (W : Set G)) (w : W) (j : J), (k : G) = w * j →
          ψ k = θ j * ((lam w : ℂ) - 1)) →
        let A := inducedFunction (Subgroup.centralizer (W : Set G)) ψ
        A ∈ coefficientVirtualLattice basis
            (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ∧
        characterPairing A A = 3 ∧
        (∀ g : G, A g ≠ 0 → ∀ x y : G, x * y = g → Commute x y →
          (∃ e : ℕ, orderOf x = 5 ^ e) → ¬ 5 ∣ orderOf y →
            ∃ w ∈ W, Subgroup.zpowers w = W ∧ IsConj x w) ∧
        (∃ s : Finset basis.index, s.card = 3 ∧ ∀ χ : basis.index,
          (χ ∈ s → characterPairing A (basis.representation χ).character = 1 ∨
              characterPairing A (basis.representation χ).character = -1) ∧
          (χ ∉ s → characterPairing A (basis.representation χ).character = 0)) ∧
        ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
          characterPairing A (basis.representation χ).character =
            ((5 : ℂ) ^ a)⁻¹ * ∑ w : W, (basis.representation χ).character (t * w) *
              (starRingEnd ℂ (lam w : ℂ) - 1) := by
  intro θ b
  obtain ⟨e⟩ := hJ
  have hWp : IsPGroup 5 W := IsPGroup.of_card hWcard
  have hWK : W ≤ Subgroup.centralizer (W : Set G) := left_le_centralizer hsup
  have hJK : J ≤ Subgroup.centralizer (W : Set G) := right_le_centralizer hsup
  have hWab : ∀ x ∈ W.subgroupOf (Subgroup.centralizer (W : Set G)),
      ∀ y ∈ W.subgroupOf (Subgroup.centralizer (W : Set G)), Commute x y := fun x hx y _ =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp y.2 x hx)
  have hWJ : ∀ x ∈ W.subgroupOf (Subgroup.centralizer (W : Set G)),
      ∀ y ∈ J.subgroupOf (Subgroup.centralizer (W : Set G)), Commute x y := fun x hx y hy =>
    Subtype.ext (commute_of_mem hsup hx hy)
  have hdisj' : W.subgroupOf (Subgroup.centralizer (W : Set G)) ⊓
      J.subgroupOf (Subgroup.centralizer (W : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ W ⊓ J := ⟨hx.1, hx.2⟩
    rw [hdisj, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hsup' : W.subgroupOf (Subgroup.centralizer (W : Set G)) ⊔
      J.subgroupOf (Subgroup.centralizer (W : Set G)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hWK hJK, hsup, Subgroup.subgroupOf_self]
  obtain ⟨basisW⟩ := finiteIrreducibleCharacterBasis_exists
    (G := W.subgroupOf (Subgroup.centralizer (W : Set G)))
  obtain ⟨basisJ⟩ := finiteIrreducibleCharacterBasis_exists
    (G := J.subgroupOf (Subgroup.centralizer (W : Set G)))
  obtain ⟨-, -, -, -, -, -, -, c₀, himage', -, -, huniq⟩ :=
    abelian_five_kernel_alternating_five_unique_defect_block
      (W.subgroupOf (Subgroup.centralizer (W : Set G)))
      (J.subgroupOf (Subgroup.centralizer (W : Set G))) hWab hWp.comap_subtype hWJ hdisj' hsup'
      ⟨(Subgroup.subgroupOfEquivOfLe hJK).trans e⟩ ideal basisW basisJ localBasis
  have himage : (fun l => (localBasis.representation l).character) ''
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀ :
        Set localBasis.index) = b := by
    rw [himage']
    exact kernelBlock_eq hsup e hWab basisW
  obtain ⟨hfiber, huniqB⟩ := brauer_fiber_eq basis ideal W hWp hWK localBasis c₀ huniq hlabel
  refine ⟨fun basisJ => ⟨FiveKernel.exists_label_sylowAugmentation e basisJ,
    fun l hl => FiveKernel.eq_sylowAugmentation_of_five_dvd e basisJ l (by rw [hl])⟩,
    FiveKernel.sylowAugmentation_one e, ⟨c₀, himage, hfiber⟩, huniqB, ?_⟩
  intro t htJ ht lam hlam
  have hlam5 : lam ^ 5 = 1 := hlam ▸ pow_orderOf_eq_one lam
  have hlam1 : lam ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hlam
    norm_num at hlam
  have hlam2 : lam ^ 2 ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hlam] at h'
    norm_num at h'
  have hlaminv : lam⁻¹ ≠ 1 := by
    intro h
    apply hlam1
    ext w
    have h' := DFunLike.congr_fun h w
    simp only [MonoidHom.inv_apply, MonoidHom.one_apply, inv_eq_one] at h'
    rw [h', MonoidHom.one_apply]
  have hgen : ∀ w : W, lam w ≠ 1 → Subgroup.zpowers (w : G) = W :=
    zpowers_eq_of_ne_one W a hWcard lam hlam5
  have hθord : ∀ j j' : J, orderOf j = orderOf j' → θ j = θ j' := fun j j' h =>
    sylowAugmentation_eq_of_orderOf_eq e e h
  have hθ5 : ∀ j : J, θ j ≠ 0 → Nat.Coprime 5 (orderOf j) := fun j h =>
    coprime_of_sylowAugmentation_ne_zero e h
  have hθt : θ ⟨t, htJ⟩ = 1 :=
    FiveKernel.sylowAugmentation_of_orderOf_two e (by rw [Subgroup.orderOf_mk]; exact ht)
  have hsum60 : ∑ j : J, θ j * θ j⁻¹ = 60 := sum_sylowAugmentation_mul_inv e
  have hWord : ∀ x : W, orderOf (x : G) ∣ 5 ^ a := fun x => by
    rw [Subgroup.orderOf_coe, ← hWcard]
    exact orderOf_dvd_natCard x
  have hS : ∀ c ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀,
      ∃ μ : W →* ℂˣ, ∀ (k : Subgroup.centralizer (W : Set G)) (w : W) (j : J),
        (k : G) = w * j → (localBasis.representation c).character k = μ w * θ j := by
    intro c hc
    have hmem : (localBasis.representation c).character ∈ b := by
      rw [← himage]
      exact ⟨c, hc, rfl⟩
    exact hmem
  have hlabelOf : ∀ μ : W →* ℂˣ,
      ∃ l ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀,
        ∀ (k : Subgroup.centralizer (W : Set G)) (w : W) (j : J), (k : G) = w * j →
          (localBasis.representation l).character k = μ w * θ j := by
    intro μ
    have hmem : (fun k => (μ ((prodEquiv hsup hdisj).symm k).1 : ℂ) *
        θ ((prodEquiv hsup hdisj).symm k).2) ∈ b := by
      refine ⟨μ, fun k w j hk => ?_⟩
      beta_reduce
      rw [prodEquiv_symm_apply hsup hdisj hk]
    rw [← himage] at hmem
    obtain ⟨l, hl, hlf⟩ := hmem
    refine ⟨l, hl, fun k w j hk => ?_⟩
    have h := congrFun hlf k
    beta_reduce at h
    rw [h, prodEquiv_symm_apply hsup hdisj hk]
  refine ⟨⟨fun k => θ ((prodEquiv hsup hdisj).symm k).2 *
    ((lam ((prodEquiv hsup hdisj).symm k).1 : ℂ) - 1), fun k w j hk => ?_⟩, ?_⟩
  · beta_reduce
    rw [prodEquiv_symm_apply hsup hdisj hk]
  intro ψ hψ
  dsimp only
  set A := inducedFunction (Subgroup.centralizer (W : Set G)) ψ with hA
  obtain ⟨llam, hllam, hllamχ⟩ := hlabelOf lam
  obtain ⟨l1, hl1, hl1χ⟩ := hlabelOf 1
  have hψeq : ψ = (localBasis.representation llam).character -
      (localBasis.representation l1).character := by
    funext k
    obtain ⟨w, j, hk⟩ := exists_eq_mul hsup hdisj k
    rw [Pi.sub_apply, hψ k w j hk, hllamχ k w j hk, hl1χ k w j hk, MonoidHom.one_apply,
      Units.val_one]
    ring
  have hψspan : ψ ∈ coefficientCharacterSpace localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) c₀) := by
    rw [hψeq]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨llam, hllam, rfl⟩)
      (Submodule.subset_span ⟨l1, hl1, rfl⟩)
  have hAclass : ∀ x g : G, A (g * x * g⁻¹) = A x := fun x g => inducedFunction_conjugate _ _ x g
  have hfrob : ∀ f : G → ℂ, (∀ x g : G, f (g * x * g⁻¹) = f x) →
      characterPairing A f = characterPairing ψ (fun k : Subgroup.centralizer (W : Set G) => f k) :=
    fun f hf => characterPairing_inducedFunction_left _ ψ f hf
  have hint : ∀ χ : basis.index, ∃ z : ℤ,
      characterPairing A (basis.representation χ).character = z := by
    intro χ
    have hAeq : A = (coinducedFiniteComplexRepresentation (Subgroup.centralizer (W : Set G))
        (localBasis.representation llam)).character -
        (coinducedFiniteComplexRepresentation (Subgroup.centralizer (W : Set G))
          (localBasis.representation l1)).character := by
      rw [hA, hψeq, CyclicInversion.inducedFunction_sub]
      funext g
      rw [Pi.sub_apply, Pi.sub_apply, coinducedFiniteComplexRepresentation_character,
        coinducedFiniteComplexRepresentation_character]
    obtain ⟨m₁, hm₁⟩ := CyclicInversion.character_pairing_nat basis
      (coinducedFiniteComplexRepresentation _ (localBasis.representation llam)) χ
    obtain ⟨m₂, hm₂⟩ := CyclicInversion.character_pairing_nat basis
      (coinducedFiniteComplexRepresentation _ (localBasis.representation l1)) χ
    refine ⟨(m₁ : ℤ) - m₂, ?_⟩
    rw [hAeq, characterPairing_sub_left, hm₁, hm₂]
    push_cast
    ring
  choose z hz using hint
  have hBr₀ := (hfiber c₀).mpr (coefficientBlock_self_mem _ _ _)
  have hsection : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∀ w : W, Subgroup.zpowers (w : G) = W → ∀ j : J, Nat.Coprime 5 (orderOf j) →
        (basis.representation χ).character ((w : G) * j) =
          θ j * (basis.representation χ).character ((w : G) * t) := by
    intro χ hχ w hw j hj
    have hρj : Nat.Coprime 5 (orderOf (⟨j, hJK j.2⟩ : Subgroup.centralizer (W : Set G))) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
      exact hj
    have hρt : Nat.Coprime 5 (orderOf (⟨t, hJK htJ⟩ : Subgroup.centralizer (W : Set G))) := by
      rw [Subgroup.orderOf_mk, ht]
      norm_num
    have h1 := character_eq_projection basis ideal W hWp hw localBasis label c₀ hfiber hχ
      ⟨j, hJK j.2⟩ (prodEquiv hsup hdisj (w, j)) hρj rfl
    have h2 := character_eq_projection basis ideal W hWp hw localBasis label c₀ hfiber hχ
      ⟨t, hJK htJ⟩ (prodEquiv hsup hdisj (w, ⟨t, htJ⟩)) hρt rfl
    have h3 := apply_eq_of_mem_span localBasis _ θ ⟨t, htJ⟩ hθt hS
      (characterSubsetProjection_mem localBasis _ (fun h => (basis.representation χ).character h))
      (k := prodEquiv hsup hdisj (w, j)) (k' := prodEquiv hsup hdisj (w, ⟨t, htJ⟩)) rfl rfl
    calc (basis.representation χ).character ((w : G) * j)
        = (basis.representation χ).character (prodEquiv hsup hdisj (w, j)) := rfl
      _ = θ j * (basis.representation χ).character (prodEquiv hsup hdisj (w, ⟨t, htJ⟩)) := by
        rw [h1, h3, h2]
      _ = θ j * (basis.representation χ).character ((w : G) * t) := rfl
  have hvanish : ∀ χ ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      characterPairing A (basis.representation χ).character = 0 := by
    intro χ hχ
    rw [hfrob _ (fun x g => Representation.char_conj _ x g),
      coefficientCharacterSpace_pairing_projection_right localBasis _ ψ _ hψspan]
    apply characterPairing_zero_of_inverse_support {k | ψ k ≠ 0}
    · intro k hk
      by_contra h
      exact hk h
    · intro k hk
      obtain ⟨w, j, hkwj⟩ := exists_eq_mul hsup hdisj k
      have hk' : ψ k ≠ 0 := hk
      rw [hψ k w j hkwj] at hk'
      have hj0 : θ j ≠ 0 := left_ne_zero_of_mul hk'
      have hw1 : lam w ≠ 1 := fun h =>
        right_ne_zero_of_mul hk' (by rw [h, Units.val_one, sub_self])
      have hw' : Subgroup.zpowers (w : G)⁻¹ = W := by
        rw [Subgroup.zpowers_inv]
        exact hgen w hw1
      have hρ : Nat.Coprime 5
          (orderOf (⟨(j : G)⁻¹, hJK (J.inv_mem j.2)⟩ : Subgroup.centralizer (W : Set G))) := by
        rw [Subgroup.orderOf_mk, orderOf_inv, Subgroup.orderOf_coe]
        exact hθ5 j hj0
      exact projection_eq_zero basis ideal W hWp hw' localBasis label c₀ hBr₀ hχ _ k⁻¹ hρ (by
        rw [Subgroup.coe_inv, hkwj, mul_inv_rev,
          ← (commute_of_mem hsup (W.inv_mem w.2) (J.inv_mem j.2)).eq])
  have hcoeff : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      characterPairing A (basis.representation χ).character =
        ((5 : ℂ) ^ a)⁻¹ * ∑ w : W, (basis.representation χ).character (t * w) *
          (starRingEnd ℂ (lam w : ℂ) - 1) := by
    intro χ hχ
    rw [hfrob _ (fun x g => Representation.char_conj _ x g)]
    unfold characterPairing
    rw [sum_centralizer hsup hdisj, card_centralizer_eq hsup hdisj, hWcard,
      FiveKernel.card_eq_sixty e]
    have hterm : ∀ (w : W) (j : J), ψ (prodEquiv hsup hdisj (w, j)) *
        (basis.representation χ).character
          (((prodEquiv hsup hdisj (w, j))⁻¹ : Subgroup.centralizer (W : Set G)) : G) =
        θ j * θ j⁻¹ * (((lam w : ℂ) - 1) *
          (basis.representation χ).character ((w : G)⁻¹ * t)) := by
      intro w j
      rw [hψ _ w j rfl, coe_prodEquiv_inv hsup hdisj]
      by_cases hw1 : lam w = 1
      · rw [hw1, Units.val_one, sub_self]
        ring
      by_cases hj0 : θ j = 0
      · rw [hj0]
        ring
      have hw' : Subgroup.zpowers ((w⁻¹ : W) : G) = W := by
        rw [Subgroup.coe_inv, Subgroup.zpowers_inv]
        exact hgen w hw1
      have hj' : Nat.Coprime 5 (orderOf j⁻¹) := by
        rw [orderOf_inv]
        exact hθ5 j hj0
      have h := hsection χ hχ w⁻¹ hw' j⁻¹ hj'
      rw [Subgroup.coe_inv, Subgroup.coe_inv] at h
      rw [h]
      ring
    simp_rw [hterm]
    have hinner : ∀ w : W, ∑ j : J, θ j * θ j⁻¹ * (((lam w : ℂ) - 1) *
        (basis.representation χ).character ((w : G)⁻¹ * t)) =
        60 * (((lam w : ℂ) - 1) * (basis.representation χ).character ((w : G)⁻¹ * t)) := by
      intro w
      rw [← Finset.sum_mul, hsum60]
    rw [Finset.sum_congr rfl fun w _ => hinner w, ← Finset.mul_sum]
    have hreindex : ∑ w : W, ((lam w : ℂ) - 1) *
        (basis.representation χ).character ((w : G)⁻¹ * t) =
        ∑ w : W, (basis.representation χ).character (t * w) *
          (starRingEnd ℂ (lam w : ℂ) - 1) := by
      refine Fintype.sum_equiv (Equiv.inv W) _ _ fun w => ?_
      rw [Equiv.inv_apply, conj_eq_inv W lam hlam5, inv_inv, Subgroup.coe_inv,
        ← (commute_of_mem hsup (W.inv_mem w.2) htJ).eq]
      ring
    rw [hreindex]
    push_cast
    field_simp
  have hnorm : characterPairing A A = 3 := by
    rw [hfrob A hAclass]
    unfold characterPairing
    rw [sum_centralizer hsup hdisj, card_centralizer_eq hsup hdisj, hWcard,
      FiveKernel.card_eq_sixty e]
    have hterm : ∀ (w : W) (j : J), ψ (prodEquiv hsup hdisj (w, j)) *
        A (((prodEquiv hsup hdisj (w, j))⁻¹ : Subgroup.centralizer (W : Set G)) : G) =
        θ j * θ j⁻¹ * (((lam w : ℂ) - 1) * (((lam w⁻¹ : ℂ) - 1) + ((lam w : ℂ) - 1))) := by
      intro w j
      rw [hψ _ w j rfl, coe_prodEquiv_inv hsup hdisj]
      by_cases hw1 : lam w = 1
      · rw [hw1, Units.val_one, sub_self]
        ring
      by_cases hj0 : θ j = 0
      · rw [hj0]
        ring
      have hw' : Subgroup.zpowers ((w⁻¹ : W) : G) = W := by
        rw [Subgroup.coe_inv, Subgroup.zpowers_inv]
        exact hgen w hw1
      have hj' : Nat.Coprime 5 (orderOf j⁻¹) := by
        rw [orderOf_inv]
        exact hθ5 j hj0
      have h := induced_apply_generator hsup hdisj a hWcard hindex hJH hinv θ hθord hθ5 lam hgen
        ψ hψ hw' hj'
      rw [inv_inv, Subgroup.coe_inv, Subgroup.coe_inv] at h
      rw [hA, h, hθord j⁻¹ j (orderOf_inv j)]
      ring
    simp_rw [hterm]
    have hinner : ∀ w : W, ∑ j : J, θ j * θ j⁻¹ *
        (((lam w : ℂ) - 1) * (((lam w⁻¹ : ℂ) - 1) + ((lam w : ℂ) - 1))) =
        60 * (3 - 3 * (lam w : ℂ) + ((lam ^ 2) w : ℂ) - ((lam⁻¹) w : ℂ)) := by
      intro w
      rw [← Finset.sum_mul, hsum60]
      have hne : (lam w : ℂ) ≠ 0 := Units.ne_zero _
      simp only [map_inv, Units.val_inv_eq_inv_val, MonoidHom.pow_apply, MonoidHom.inv_apply,
        Units.val_pow_eq_pow_val]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun w _ => hinner w, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_linear W lam,
      sum_linear W (lam ^ 2), sum_linear W lam⁻¹, ite_eq_right hlam1, ite_eq_right hlam2,
      ite_eq_right hlaminv]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      hWcard]
    push_cast
    field_simp
    ring
  have hsupport : ∀ g : G, A g ≠ 0 → ∀ x y : G, x * y = g → Commute x y →
      (∃ e : ℕ, orderOf x = 5 ^ e) → ¬ 5 ∣ orderOf y →
        ∃ w ∈ W, Subgroup.zpowers w = W ∧ IsConj x w := by
    intro g hg x y hxy hcomm hx hy
    obtain ⟨c, -, hc⟩ : ∃ c ∈ (Finset.univ : Finset G),
        (if hmem : c⁻¹ * g * c ∈ Subgroup.centralizer (W : Set G) then
          ψ ⟨c⁻¹ * g * c, hmem⟩ else 0) ≠ 0 := by
      by_contra! hall
      apply hg
      rw [hA]
      unfold inducedFunction
      rw [Finset.sum_eq_zero (fun c _ => hall c (Finset.mem_univ c)), mul_zero]
    by_cases hmem : c⁻¹ * g * c ∈ Subgroup.centralizer (W : Set G)
    swap
    · rw [dite_eq_right hmem] at hc
      exact absurd rfl hc
    rw [dite_eq_left hmem] at hc
    obtain ⟨w, j, hk⟩ := exists_eq_mul hsup hdisj ⟨_, hmem⟩
    rw [hψ _ w j hk] at hc
    have hj0 : θ j ≠ 0 := left_ne_zero_of_mul hc
    have hw1 : lam w ≠ 1 := fun h =>
      right_ne_zero_of_mul hc (by rw [h, Units.val_one, sub_self])
    obtain ⟨n, hn⟩ := hx
    have h1 : orderOf (c⁻¹ * x * c) ∣ 5 ^ n := by rw [orderOf_conj, hn]
    have h2 : Nat.Coprime 5 (orderOf (c⁻¹ * y * c)) := by
      rw [orderOf_conj]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hy
    have h3 : Commute (c⁻¹ * x * c) (c⁻¹ * y * c) := by
      have h := hcomm.map (MulAut.conj c⁻¹).toMonoidHom
      simpa using h
    have h5 : Nat.Coprime 5 (orderOf (j : G)) := by
      rw [Subgroup.orderOf_coe]
      exact hθ5 j hj0
    have hprod : (c⁻¹ * x * c) * (c⁻¹ * y * c) = (w : G) * j := by
      rw [← hk]
      change _ = c⁻¹ * g * c
      rw [← hxy]
      group
    obtain ⟨hxw, -⟩ := CFSG.LyonsUnitaryFour.primary_factorization_unique h1 h2 h3 (hWord w) h5
      (commute_of_mem hsup w.2 j.2) hprod
    exact ⟨w, w.2, hgen w hw1, isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hxw⟩⟩
  have hnormZ : ∑ χ, z χ * z χ = 3 := by
    have h := CyclicInversion.characterPairing_eq_sum_coefficients basis A A hAclass hAclass z z
      hz hz
    rw [hnorm] at h
    exact_mod_cast h.symm
  obtain ⟨s, hs, hsχ⟩ := exists_support_of_sum_mul_self_eq_three z hnormZ
  refine ⟨CyclicInversion.mem_coefficientVirtualLattice basis _ A hAclass z hz fun χ hχ => ?_,
    hnorm, hsupport, ⟨s, hs, fun χ => ⟨fun h => ?_, fun h => ?_⟩⟩, hcoeff⟩
  · have h := hvanish χ hχ
    rw [hz χ] at h
    exact_mod_cast h
  · rcases (hsχ χ).1 h with h' | h'
    · left
      rw [hz χ, h']
      norm_num
    · right
      rw [hz χ, h']
      norm_num
  · rw [hz χ, (hsχ χ).2 h]
    norm_num

end CFSG.Semidihedral.Principal
