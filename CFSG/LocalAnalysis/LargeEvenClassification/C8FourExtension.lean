module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourPrimitiveSaving
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourAmbientConditions
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionCertificate
public import CFSG.LocalAnalysis.LargeEvenClassification.LargeExponentFourGenerators

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] noncomputable def c8FourConjugationAction {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (coordinates : Additive A ≃+ CyclicPair 2 4) : S →* C8FourCode :=
  (c8FourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
    (MulAut.conjNormal (H := A))

theorem c8FourConjugationAction_ker {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (coordinates : Additive A ≃+ CyclicPair 2 4) :
    (c8FourConjugationAction A hcommutative coordinates).ker = A := by
  let e := c8FourAutomorphismEquiv hcommutative coordinates
  have hk : (MulAut.conjNormal (H := A)).ker = A :=
    (conjNormal_ker_eq_centralizer A).trans hselfCentralizing
  ext s
  change e (MulAut.conjNormal (H := A) s) = 1 ↔ s ∈ A
  rw [← map_one e, e.injective.eq_iff]
  exact (Subgroup.ext_iff.mp hk s)

theorem c8Four_subgroup_action_kernel {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (U : Subgroup S) :
    ((c8FourConjugationAction A hcommutative coordinates).comp U.subtype).rangeRestrict.ker =
      A.comap U.subtype := by
  rw [MonoidHom.ker_rangeRestrict]
  change (c8FourConjugationAction A hcommutative coordinates).ker.comap U.subtype = _
  rw [c8FourConjugationAction_ker A hcommutative hselfCentralizing coordinates]

theorem c8Four_coordinate_generator_rank {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) (hcommutative : IsMulCommutative A)
    (coordinates : Additive A ≃+ CyclicPair 2 4) : pGeneratorRank 2 A = 2 := by
  let pairs : A ≃* Multiplicative (ZMod 8) × Multiplicative (ZMod 4) :=
    (AddEquiv.toMultiplicativeRight coordinates).trans (MulEquiv.prodMultiplicative _ _)
  have hcard := binary_rank_two_frattini_quotient_card hpgroup A hcommutative
    (by decide : 0 < 3) (by decide : 0 < 2) pairs
  change Nat.log 2 (Nat.card (A ⧸ frattini A)) = 2
  rw [hcard]
  decide

theorem c8_four_subgroup_central_primitive_square {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (U : Subgroup S)
    (g : C8FourCode)
    (hg : g ∈ ((c8FourConjugationAction A hcommutative coordinates).comp U.subtype).range)
    (hsquare : g ^ 2 = 1) (hne : g ≠ 1) (hkernel : c8FourNormKernel g)
    (himage : c8FourNormDoubles g)
    (hcentral : ∀ s : S, Commute g (c8FourConjugationAction A hcommutative coordinates s)) :
    ∃ u : U, ∃ a : A, (a : S) = (u : S) ^ 2 ∧
      (∀ b : A, a ≠ b ^ 2) ∧
      c8FourApply g (coordinates (Additive.ofMul a)) = coordinates (Additive.ofMul a) := by
  obtain ⟨u, hu⟩ := hg
  obtain ⟨a, ha, hprimitive, hfixed⟩ := c8_four_central_action_primitive_square A
    hcommutative hselfCentralizing hnoEight coordinates g hsquare hne hkernel himage
    hcentral u.val hu
  exact ⟨u, a, ha, hprimitive, hfixed⟩

theorem c8_four_subgroup_kernel_primitive_square {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (U : Subgroup S)
    (g : C8FourCode)
    (hg : g ∈ ((c8FourConjugationAction A hcommutative coordinates).comp U.subtype).range)
    (hsquare : g ^ 2 = 1) (hne : g ≠ 1) (hkernel : c8FourNormKernel g)
    (himage : c8FourNormDoubles g)
    (hcentral : ∀ s : S, Commute g (c8FourConjugationAction A hcommutative coordinates s)) :
    let action := (c8FourConjugationAction A hcommutative coordinates).comp U.subtype
    let quotient := action.rangeRestrict
    ∀ embedding : quotient.ker →* A,
      (∀ b : quotient.ker, (embedding b : S) = b.val.val) →
      ∃ u : U, ∃ b : quotient.ker, (b : U) = u ^ 2 ∧
        (∀ a : A, embedding b ≠ a ^ 2) ∧
        c8FourApply g (coordinates (Additive.ofMul (embedding b))) =
          coordinates (Additive.ofMul (embedding b)) := by
  intro action quotient embedding hembedding
  obtain ⟨u, a, ha, hprimitive, hfixed⟩ := c8_four_subgroup_central_primitive_square A
    hcommutative hselfCentralizing hnoEight coordinates U g hg hsquare hne hkernel himage hcentral
  have hmem : u ^ 2 ∈ quotient.ker := by
    rw [c8Four_subgroup_action_kernel A hcommutative hselfCentralizing coordinates U]
    change (u.val ^ 2 : S) ∈ A
    exact ha ▸ a.property
  let b : quotient.ker := ⟨u ^ 2, hmem⟩
  have hb : embedding b = a := by
    apply Subtype.ext
    exact (hembedding b).trans ha.symm
  refine ⟨u, b, rfl, ?_, ?_⟩
  · rw [hb]
    exact hprimitive
  · rw [hb]
    exact hfixed

theorem c8_four_subgroup_kernel_two_primitive_squares {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (U : Subgroup S)
    (g h : C8FourCode)
    (hg : g ∈ ((c8FourConjugationAction A hcommutative coordinates).comp U.subtype).range)
    (hh : h ∈ ((c8FourConjugationAction A hcommutative coordinates).comp U.subtype).range)
    (hgsquare : g ^ 2 = 1) (hgne : g ≠ 1) (hgkernel : c8FourNormKernel g)
    (hgimage : c8FourNormDoubles g)
    (hgcentral : ∀ s : S, Commute g (c8FourConjugationAction A hcommutative coordinates s))
    (hhsquare : h ^ 2 = 1) (hhne : h ≠ 1) (hhkernel : c8FourNormKernel h)
    (hhimage : c8FourNormDoubles h)
    (hhcentral : ∀ s : S, Commute h (c8FourConjugationAction A hcommutative coordinates s))
    (hseparate : ∀ x y : CyclicPair 2 4,
      c8FourApply g x = x → c8FourApply h y = y →
      c8FourBinaryCoordinates x ≠ 0 → c8FourBinaryCoordinates y ≠ 0 →
      c8FourBinaryCoordinates x ≠ c8FourBinaryCoordinates y) :
    let action := (c8FourConjugationAction A hcommutative coordinates).comp U.subtype
    let quotient := action.rangeRestrict
    ∀ embedding : quotient.ker →* A,
      (∀ b : quotient.ker, (embedding b : S) = b.val.val) →
      ∃ u₀ u₁ : U, ∃ b₀ b₁ : quotient.ker, (b₀ : U) = u₀ ^ 2 ∧ (b₁ : U) = u₁ ^ 2 ∧
        c8FourBinaryHom coordinates (embedding b₀) ≠ 1 ∧
        c8FourBinaryHom coordinates (embedding b₁) ≠ 1 ∧
        c8FourBinaryHom coordinates (embedding b₀) ≠
          c8FourBinaryHom coordinates (embedding b₁) := by
  intro action quotient embedding hembedding
  obtain ⟨u₀, b₀, hsquare₀, hprimitive₀, hfixed₀⟩ :=
    c8_four_subgroup_kernel_primitive_square A hcommutative hselfCentralizing hnoEight
      coordinates U g hg hgsquare hgne hgkernel hgimage hgcentral embedding hembedding
  obtain ⟨u₁, b₁, hsquare₁, hprimitive₁, hfixed₁⟩ :=
    c8_four_subgroup_kernel_primitive_square A hcommutative hselfCentralizing hnoEight
      coordinates U h hh hhsquare hhne hhkernel hhimage hhcentral embedding hembedding
  have h₀ := c8FourBinaryHom_primitive coordinates (embedding b₀) hprimitive₀
  have h₁ := c8FourBinaryHom_primitive coordinates (embedding b₁) hprimitive₁
  refine ⟨u₀, u₁, b₀, b₁, hsquare₀, hsquare₁, h₀, h₁, ?_⟩
  change c8FourBinaryCoordinates (coordinates (Additive.ofMul (embedding b₀))) ≠ 0 at h₀
  change c8FourBinaryCoordinates (coordinates (Additive.ofMul (embedding b₁))) ≠ 0 at h₁
  intro heq
  exact hseparate _ _ hfixed₀ hfixed₁ h₀ h₁ (congrArg Multiplicative.toAdd heq)

theorem c8_four_coordinate_four_generators_of_central_square_witnesses
    {S : Type*} [Group S] [Finite S] (hpgroup : IsPGroup 2 S)
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (U : Subgroup S) :
    let ambientAction := c8FourConjugationAction A hcommutative coordinates
    let action := ambientAction.comp U.subtype
    let Q := action.range
    pGeneratorRank 2 Q ≤ 4 →
    (pGeneratorRank 2 Q = 3 → ∃ g : C8FourCode, g ∈ Q ∧ g ^ 2 = 1 ∧ g ≠ 1 ∧
      c8FourNormKernel g ∧ c8FourNormDoubles g ∧
      ∀ s : S, Commute g (ambientAction s)) →
    (pGeneratorRank 2 Q = 4 → ∃ g h : C8FourCode,
      (g ∈ Q ∧ g ^ 2 = 1 ∧ g ≠ 1 ∧ c8FourNormKernel g ∧ c8FourNormDoubles g ∧
        ∀ s : S, Commute g (ambientAction s)) ∧
      (h ∈ Q ∧ h ^ 2 = 1 ∧ h ≠ 1 ∧ c8FourNormKernel h ∧ c8FourNormDoubles h ∧
        ∀ s : S, Commute h (ambientAction s)) ∧
      ∀ x y : CyclicPair 2 4, c8FourApply g x = x → c8FourApply h y = y →
        c8FourBinaryCoordinates x ≠ 0 → c8FourBinaryCoordinates y ≠ 0 →
        c8FourBinaryCoordinates x ≠ c8FourBinaryCoordinates y) →
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  intro ambientAction action Q hQrank hthree hfour
  let : CommGroup A := { (inferInstance : Group A) with
    mul_comm := @mul_comm' _ _ hcommutative }
  let quotient := action.rangeRestrict
  have hkernel : quotient.ker = A.comap U.subtype :=
    c8Four_subgroup_action_kernel A hcommutative hselfCentralizing coordinates U
  let embedding : quotient.ker →* A := {
    toFun b := ⟨b.val.val, hkernel.le b.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hinjective : Function.Injective embedding := by
    intro b c h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => a.val) h
  have hembedding (b : quotient.ker) : (embedding b : S) = b.val.val := rfl
  have hcriticalThree (hrank : pGeneratorRank 2 Q = 3) :
      ∃ u : U, ∃ b : quotient.ker, (b : U) = u ^ 2 ∧ ∀ a : A, embedding b ≠ a ^ 2 := by
    obtain ⟨g, hg, hsquare, hne, hkernel, himage, hcentral⟩ := hthree hrank
    obtain ⟨u, b, hbsquare, hprimitive, _⟩ :=
      c8_four_subgroup_kernel_primitive_square A hcommutative hselfCentralizing hnoEight
        coordinates U g hg hsquare hne hkernel himage hcentral embedding hembedding
    exact ⟨u, b, hbsquare, hprimitive⟩
  have hcriticalFour (hrank : pGeneratorRank 2 Q = 4) :
      ∃ u₀ u₁ : U, ∃ b₀ b₁ : quotient.ker, (b₀ : U) = u₀ ^ 2 ∧ (b₁ : U) = u₁ ^ 2 ∧
        c8FourBinaryHom coordinates (embedding b₀) ≠ 1 ∧
        c8FourBinaryHom coordinates (embedding b₁) ≠ 1 ∧
        c8FourBinaryHom coordinates (embedding b₀) ≠
          c8FourBinaryHom coordinates (embedding b₁) := by
    obtain ⟨g, h, ⟨hg, hgsquare, hgne, hgkernel, hgimage, hgcentral⟩,
      ⟨hh, hhsquare, hhne, hhkernel, hhimage, hhcentral⟩, hseparate⟩ := hfour hrank
    exact c8_four_subgroup_kernel_two_primitive_squares A hcommutative hselfCentralizing hnoEight
      coordinates U g h hg hh hgsquare hgne hgkernel hgimage hgcentral
      hhsquare hhne hhkernel hhimage hhcentral hseparate embedding hembedding
  exact abelian_kernel_four_action_primitive_squares_four_generators (hpgroup.to_subgroup U)
    (hpgroup.to_subgroup A) quotient action.rangeRestrict_surjective embedding hinjective
    (c8Four_coordinate_generator_rank hpgroup A hcommutative coordinates).le hQrank
    (c8FourBinaryHom coordinates) hcriticalThree hcriticalFour

theorem c8FourActionDistinctFixedLines_nonzero_ne {g h : C8FourCode}
    (hgh : c8FourActionDistinctFixedLines g h) (x y : CyclicPair 2 4)
    (hx : c8FourApply g x = x) (hy : c8FourApply h y = y)
    (hxzero : c8FourBinaryCoordinates x ≠ 0) (hyzero : c8FourBinaryCoordinates y ≠ 0) :
    c8FourBinaryCoordinates x ≠ c8FourBinaryCoordinates y := by
  exact card_two_addSubgroup_nonzero_ne (c8FourActionFixedParity g)
    (c8FourActionFixedParity h) hgh.1 hgh.2.1 hgh.2.2 _ _
    ((c8FourActionFixedParity_mem g _).mpr ⟨x, hx, rfl⟩)
    ((c8FourActionFixedParity_mem h _).mpr ⟨y, hy, rfl⟩) hxzero hyzero

theorem c8FourActionPrimitive_square_witness {S : Type*} [Group S]
    (action : S →* C8FourCode) (Q : Subgroup C8FourCode) (g : C8FourCode)
    (hg : c8FourActionPrimitive action.range Q g) :
    g ∈ Q ∧ g ^ 2 = 1 ∧ g ≠ 1 ∧ c8FourNormKernel g ∧ c8FourNormDoubles g ∧
      ∀ s : S, Commute g (action s) := by
  exact ⟨hg.1, hg.2.2.1.2, hg.2.2.1.1, hg.2.2.2.1,
    c8FourActionNormImage_doubles hg.2.2.2.2,
    fun s => hg.2.1.2 (action s) ⟨s, rfl⟩⟩

theorem c8_four_coordinate_four_generators_of_action_witnesses
    {S : Type*} [Group S] [Finite S] (hpgroup : IsPGroup 2 S)
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (U : Subgroup S) :
    let ambientAction := c8FourConjugationAction A hcommutative coordinates
    let Q := (ambientAction.comp U.subtype).range
    pGeneratorRank 2 Q ≤ 4 →
    (pGeneratorRank 2 Q = 3 → ∃ g, c8FourActionPrimitive ambientAction.range Q g) →
    (pGeneratorRank 2 Q = 4 → ∃ g h, c8FourActionPrimitive ambientAction.range Q g ∧
      c8FourActionPrimitive ambientAction.range Q h ∧ c8FourActionDistinctFixedLines g h) →
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  intro ambientAction Q hQrank hthree hfour
  apply c8_four_coordinate_four_generators_of_central_square_witnesses hpgroup A hcommutative
    hselfCentralizing hnoEight coordinates U hQrank
  · intro hrank
    obtain ⟨g, hg⟩ := hthree hrank
    exact ⟨g, c8FourActionPrimitive_square_witness ambientAction Q g hg⟩
  · intro hrank
    obtain ⟨g, h, hg, hh, hgh⟩ := hfour hrank
    exact ⟨g, h, c8FourActionPrimitive_square_witness ambientAction Q g hg,
      c8FourActionPrimitive_square_witness ambientAction Q h hh,
      c8FourActionDistinctFixedLines_nonzero_ne hgh⟩

theorem c8_four_coordinate_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4) (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  let ambientAction := c8FourConjugationAction A hcommutative coordinates
  let H := ambientAction.range
  let Q := (ambientAction.comp U.subtype).range
  have hH : c8FourActionAdmissible H :=
    c8_four_ambient_action_admissible A hcommutative hselfCentralizing hnoEight coordinates
  have hQH : Q ≤ H := by
    rintro g ⟨u, rfl⟩
    exact ⟨u.val, rfl⟩
  obtain ⟨hbound, hthree, hfour⟩ := c8Four_action_exhaustion H hH Q hQH
  exact c8_four_coordinate_four_generators_of_action_witnesses hpgroup A hcommutative
    hselfCentralizing hnoEight coordinates U hbound hthree hfour

theorem rank_two_c8_four_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : A ≃* Multiplicative (ZMod 8) × Multiplicative (ZMod 4))
    (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  let : CommGroup A := { (inferInstance : Group A) with
    mul_comm := @mul_comm' _ _ hcommutative }
  exact c8_four_coordinate_four_generators hpgroup A hcommutative hselfCentralizing hnoEight
    (rankTwoAddCoordinates (upper := 3) (lower := 2) coordinates) U

theorem rank_two_c8_four_ambient_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : A ≃* Multiplicative (ZMod 8) × Multiplicative (ZMod 4))
    (U : Subgroup S) : ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  classical
  obtain ⟨X, hX, hcard⟩ := rank_two_c8_four_four_generators hpgroup A hcommutative
    hselfCentralizing hnoEight coordinates U
  refine ⟨X.image U.subtype, Finset.card_image_le.trans hcard, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hX, Subgroup.map_top]
  exact U.range_subtype

end CFSG.LargeEvenClassification.Helpers
