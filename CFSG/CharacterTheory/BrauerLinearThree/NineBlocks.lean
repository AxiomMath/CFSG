module

public import CFSG.CharacterTheory.BrauerLinearThree.NineCharacter
public import CFSG.CharacterTheory.BrauerLinearThree.NineDegree
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.FreeSix

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
theorem fourV_le_cT : fourV φ ≤ cT J := by
  rw [fourV, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · rw [hx]
    exact element_mem_centralizer_zpowers J
  · rw [Set.mem_singleton_iff.mp hx]
    exact mem_centralizer_zpowers_iff.mpr (J_commute_invJ₁ φ)

omit [Finite F] in
theorem centralizer_fourV_le_cT : Subgroup.centralizer (fourV φ : Set G) ≤ cT J := by
  intro x hx
  exact mem_centralizer_zpowers_iff.mpr ((mem_centralizer_fourV φ).mp hx).1

omit [Finite F] in
theorem oddTorus_le_cT : oddTorus φ ≤ cT J :=
  (oddTorus_le_centralizer_fourV φ).trans (centralizer_fourV_le_cT φ)

omit [Finite F] in
theorem invJ₁_mem_cT : invJ₁ φ ∈ cT J := mem_centralizer_zpowers_iff.mpr (J_commute_invJ₁ φ)

omit [Finite F] in
theorem swapW_mem_cT : swapW φ ∈ cT J :=
  mem_centralizer_zpowers_iff.mpr (linearCentralizerHom_commute φ swapGL)

omit [Finite F] in
theorem coe_mem_centralizer_fourV (x : Subgroup.centralizer
    (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J))) :
    ((x : cT J) : G) ∈ Subgroup.centralizer (fourV φ : Set G) := by
  rw [mem_centralizer_fourV]
  refine ⟨(mem_centralizer_zpowers_iff.mp (x : cT J).2), ?_⟩
  have h := mem_centralizer_zpowers_iff.mp x.2
  exact congrArg Subtype.val h

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem closure_pair_eq_subgroupOf :
    Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
      ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)) = (fourV φ).subgroupOf (cT J) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx, SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact J_mem_fourV φ
    · rw [Set.mem_singleton_iff.mp hx, SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact invJ₁_mem_fourV φ
  · intro x hx
    rw [Subgroup.mem_subgroupOf, mem_fourV φ hZ hZodd h2 hJ] at hx
    have hJm : (⟨J, element_mem_centralizer_zpowers J⟩ : cT J) ∈
        Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
          ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hJ₁m : (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) ∈
        Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
          ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rcases hx with hx | hx | hx | hx
    · rw [show x = 1 from Subtype.ext hx]
      exact Subgroup.one_mem _
    · rw [show x = ⟨J, _⟩ from Subtype.ext hx]
      exact hJm
    · rw [show x = ⟨invJ₁ φ, _⟩ from Subtype.ext hx]
      exact hJ₁m
    · rw [show x = ⟨J, element_mem_centralizer_zpowers J⟩ *
          ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ from Subtype.ext (hx.trans (invJ₂_eq φ hZ hZodd h2 hJ))]
      exact Subgroup.mul_mem _ hJm hJ₁m

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem eq_or_eq_of_mem_linearOrbit {μ ν : oddTorus φ →* ℂˣ}
    (hν : ν ∈ linearOrbit (oddTorus φ) μ ((cT J ⊓ mV (fourV φ) : Subgroup G) : Set G)) :
    ν = μ ∨ ∀ e e' : oddTorus φ, (e' : G) = (swapW φ)⁻¹ * e * swapW φ → ν e = μ e' := by
  obtain ⟨x, hx, hνx⟩ := hν
  obtain ⟨hxC, hxM⟩ := hx
  have hxJ : J * x = x * J := mem_centralizer_zpowers_iff.mp hxC
  rcases mem_dV_or_swapW_mul_mem_dV φ hZ hZodd h2 hJ hxJ hxM with hD | hD
  · left
    refine MonoidHom.ext fun e => hνx e e ?_
    have hc := commute_of_mem_centralizer_fourV φ hZ hZodd h2 hD
      (oddTorus_le_centralizer_fourV φ e.2)
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  · right
    intro e e' he'
    apply hνx
    rw [he']
    set d := swapW φ * x with hd
    have hx' : x = swapW φ * d := by rw [hd, ← mul_assoc, swapW_mul_self, one_mul]
    have hWe : swapW φ * ↑e * swapW φ ∈ Subgroup.centralizer (fourV φ : Set G) := by
      have h := inv_mul_mul_mem_centralizer_fourV φ
        (swapW_mem_normalizer_fourV φ hZ hZodd h2 hJ) (oddTorus_le_centralizer_fourV φ e.2)
      rwa [swapW_inv] at h
    have hc := commute_of_mem_centralizer_fourV φ hZ hZodd h2 hD hWe
    rw [hx', _root_.mul_inv_rev, swapW_inv]
    calc swapW φ * ↑e * swapW φ = d⁻¹ * (d * (swapW φ * ↑e * swapW φ)) := by group
      _ = d⁻¹ * ((swapW φ * ↑e * swapW φ) * d) := by rw [hc]
      _ = d⁻¹ * swapW φ * ↑e * (swapW φ * d) := by group

omit [Finite F] in
@[expose] noncomputable def swapConjOdd : oddTorus φ →* oddTorus φ where
  toFun e := ⟨(swapW φ)⁻¹ * e * swapW φ, by
    obtain ⟨a, b, he⟩ := (mem_oddTorus φ).mp e.2
    rw [mem_oddTorus]
    refine ⟨b, a, ?_⟩
    rw [he, swapW_inv, swapW, ← map_mul, ← map_mul, swapGL_mul_diagGL, mul_assoc,
      swapGL_mul_self, mul_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite F] in
theorem coe_swapConjOdd (e : oddTorus φ) :
    (swapConjOdd φ e : G) = (swapW φ)⁻¹ * e * swapW φ := rfl

omit [Finite F] in
@[expose] noncomputable def centralizerInvJ₁Hom :
    Subgroup.centralizer (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J)) →*
      Subgroup.centralizer (fourV φ : Set G) where
  toFun x := ⟨((x : cT J) : G), coe_mem_centralizer_fourV φ x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

include hZ hZodd h2 hJ in
theorem exists_block_four_characters [Fintype G] (hq : Nat.card F % 4 = 3)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisC : FiniteIrreducibleCharacterBasis (cT J)) (label : basisC.index)
    (hD : coefficientBlockDefect basisC ideal 2 label ((fourV φ).subgroupOf (cT J)))
    (μ : oddTorus φ →* ℂˣ) (ν : Subgroup.centralizer (fourV φ : Set G) →* ℂˣ)
    (hν : ∀ (x : Subgroup.centralizer (fourV φ : Set G)) (v : G) (e : oddTorus φ),
      v ∈ fourV φ → (x : G) = v * e → ν x = μ e)
    (horbit : (linearOrbit (oddTorus φ) μ
      ((cT J ⊓ mV (fourV φ) : Subgroup G) : Set G)).ncard = 2)
    (hs : IsPGroup 2 (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J)))
    (basisCs : FiniteIrreducibleCharacterBasis (Subgroup.centralizer
      (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J))))
    {dec : DecidablePred fun n => ∃ ν' ∈ linearOrbit (oddTorus φ) μ
      ((cT J ⊓ mV (fourV φ) : Subgroup G) : Set G),
        AffordsInflation basisCs (fun x => ((x : cT J) : G)) (fourV φ) ν' n}
    (hfib : brauerFiberBlocks basisC ideal 2 ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ hs basisCs label =
      (@Finset.filter _ _ dec Finset.univ).image
        (coefficientBlock basisCs (localizedComplexIntegerRing ideal))) :
    ∃ (θ : Fin 4 → basisC.index) (f : ℕ), Function.Injective θ ∧
      coefficientBlock basisC (localizedComplexIntegerRing ideal) label =
        Finset.univ.image θ ∧
      0 < f ∧ (∀ i, Module.finrank ℂ (basisC.representation (θ i)).vector = f) ∧
      ((basisC.representation (θ 0)).character
          ⟨J, element_mem_centralizer_zpowers J⟩ = f ∧
        (basisC.representation (θ 1)).character
          ⟨J, element_mem_centralizer_zpowers J⟩ = f ∧
        (basisC.representation (θ 2)).character
          ⟨J, element_mem_centralizer_zpowers J⟩ = -(f : ℂ) ∧
        (basisC.representation (θ 3)).character
          ⟨J, element_mem_centralizer_zpowers J⟩ = -(f : ℂ)) ∧
      ((basisC.representation (θ 0)).character ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ = 2 ∧
        (basisC.representation (θ 1)).character ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ = -2 ∧
        (basisC.representation (θ 2)).character ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ = 0 ∧
        (basisC.representation (θ 3)).character ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ = 0) ∧
      (∀ x, x ∉ involutionLocalSection J →
        ((basisC.representation (θ 0)).character + (basisC.representation (θ 1)).character -
          (basisC.representation (θ 2)).character - (basisC.representation (θ 3)).character) x =
            0) ∧
      coefficientCharacterSpace basisC
          (coefficientBlock basisC (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (involutionLocalSection J) =
        Submodule.span ℂ {(basisC.representation (θ 0)).character +
          (basisC.representation (θ 1)).character - (basisC.representation (θ 2)).character -
            (basisC.representation (θ 3)).character} := by
  have hEC := oddTorus_le_cT φ
  have hWM := swapW_mem_normalizer_fourV φ hZ hZodd h2 hJ
  have hcl := closure_pair_eq_subgroupOf φ hZ hZodd h2 hJ
  let eE : (oddTorus φ).subgroupOf (cT J) ≃* oddTorus φ := Subgroup.subgroupOfEquivOfLe hEC
  have heE : ∀ e, (eE e : G) = ((e : cT J) : G) := fun e => rfl
  let μ' : (oddTorus φ).subgroupOf (cT J) →* ℂˣ := μ.comp eE.toMonoidHom
  let μ₁ : oddTorus φ →* ℂˣ := μ.comp (swapConjOdd φ)
  let μ₁' : (oddTorus φ).subgroupOf (cT J) →* ℂˣ := μ₁.comp eE.toMonoidHom
  let ν₀ := ν.comp (centralizerInvJ₁Hom φ)
  let ν₁ := (ν.comp (dConj hWM)).comp (centralizerInvJ₁Hom φ)
  obtain ⟨n₀, hn₀⟩ := exists_label_of_hom basisCs ν₀
  obtain ⟨n₁, hn₁⟩ := exists_label_of_hom basisCs ν₁
  have hVmem : ∀ v : cT J,
      v ∈ Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
        ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)) ↔ (v : G) ∈ fourV φ := by
    intro v
    rw [hcl, Subgroup.mem_subgroupOf]
  have hWv : ∀ v ∈ fourV φ, (swapW φ)⁻¹ * v * swapW φ ∈ fourV φ := by
    intro v hv
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hWM) v).mp hv
    rwa [inv_inv] at h
  have hdec : ∀ x : Subgroup.centralizer
      (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J)),
      ∃ v ∈ fourV φ, ∃ e : oddTorus φ, ((x : cT J) : G) = v * e := by
    intro x
    obtain ⟨v, hv, e, he, hx⟩ := exists_mul_of_mem_centralizer_fourV φ hZ hZodd h2 hJ hq
      (coe_mem_centralizer_fourV φ x)
    exact ⟨v, hv, ⟨e, he⟩, hx⟩
  have hν₀ : ∀ (x : Subgroup.centralizer
      (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J))) (v : G)
      (e : oddTorus φ), v ∈ fourV φ → ((x : cT J) : G) = v * e → ν₀ x = μ e :=
    fun x v e hv hx => hν (centralizerInvJ₁Hom φ x) v e hv hx
  have hν₁ : ∀ (x : Subgroup.centralizer
      (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J))) (v : G)
      (e : oddTorus φ), v ∈ fourV φ → ((x : cT J) : G) = v * e → ν₁ x = μ₁ e := by
    intro x v e hv hx
    refine hν _ ((swapW φ)⁻¹ * v * swapW φ) (swapConjOdd φ e) (hWv v hv) ?_
    change (swapW φ)⁻¹ * ((x : cT J) : G) * swapW φ = _
    rw [hx, coe_swapConjOdd]
    group
  have hμmem : μ ∈ linearOrbit (oddTorus φ) μ ((cT J ⊓ mV (fourV φ) : Subgroup G) : Set G) :=
    ⟨1, Subgroup.one_mem _, fun e e' he' => by
      rw [show e' = e from Subtype.ext (by rw [he']; group)]⟩
  have hμ₁mem : μ₁ ∈ linearOrbit (oddTorus φ) μ ((cT J ⊓ mV (fourV φ) : Subgroup G) : Set G) :=
    ⟨swapW φ, ⟨swapW_mem_cT φ, hWM⟩, fun e e' he' => by
      change μ (swapConjOdd φ e) = μ e'
      rw [show swapConjOdd φ e = e' from Subtype.ext he'.symm]⟩
  have horbit' : ∀ ν' ∈ linearOrbit (oddTorus φ) μ
      ((cT J ⊓ mV (fourV φ) : Subgroup G) : Set G), ν' = μ ∨ ν' = μ₁ := by
    intro ν' hν'
    rcases eq_or_eq_of_mem_linearOrbit φ hZ hZodd h2 hJ hν' with h | h
    · exact Or.inl h
    · exact Or.inr (MonoidHom.ext fun e => h e (swapConjOdd φ e) rfl)
  have hμne : μ₁' ≠ μ' := by
    intro h
    have h' : μ₁ = μ := by
      refine MonoidHom.ext fun e => ?_
      have := congrArg (fun χ : (oddTorus φ).subgroupOf (cT J) →* ℂˣ => χ (eE.symm e)) h
      simpa [μ₁', μ'] using this
    have hsub : linearOrbit (oddTorus φ) μ ((cT J ⊓ mV (fourV φ) : Subgroup G) : Set G) ⊆
        {μ} := by
      intro ν' hν'
      rcases horbit' ν' hν' with h1 | h1
      · exact h1
      · rw [h1, h']; rfl
    have := Set.ncard_le_ncard hsub (Set.finite_singleton μ)
    rw [horbit, Set.ncard_singleton] at this
    omega
  have hfilter : (@Finset.filter _ _ dec Finset.univ) = {n₀, n₁} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨ν', hν', hn⟩
      rcases horbit' ν' hν' with h | h
      · left
        apply basisCs.distinct
        funext x
        obtain ⟨v, hv, e, hx⟩ := hdec x
        change (basisCs.representation n).character x = (basisCs.representation n₀).character x
        rw [hn x v e hv hx, hn₀, h, hν₀ x v e hv hx]
      · right
        apply basisCs.distinct
        funext x
        obtain ⟨v, hv, e, hx⟩ := hdec x
        change (basisCs.representation n).character x = (basisCs.representation n₁).character x
        rw [hn x v e hv hx, hn₁, h, hν₁ x v e hv hx]
    · rintro (h | h) <;> rw [h]
      · exact ⟨μ, hμmem, fun x v e hv hx => by rw [hn₀, hν₀ x v e hv hx]⟩
      · exact ⟨μ₁, hμ₁mem, fun x v e hv hx => by rw [hn₁, hν₁ x v e hv hx]⟩
  have hfiber : brauerFiberBlocks basisC ideal 2 ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ hs basisCs label =
      {coefficientBlock basisCs (localizedComplexIntegerRing ideal) n₀,
        coefficientBlock basisCs (localizedComplexIntegerRing ideal) n₁} := by
    rw [hfib, hfilter, Finset.image_insert, Finset.image_singleton]
  have htcent : ∀ g : cT J,
      g * ⟨J, element_mem_centralizer_zpowers J⟩ =
        ⟨J, element_mem_centralizer_zpowers J⟩ * g :=
    fun g => Subtype.ext (mem_centralizer_zpowers_iff.mp g.2).symm
  have ht : orderOf
      (⟨J, element_mem_centralizer_zpowers J⟩ : cT J) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hJ
  have hs2 : orderOf (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) = 2 := by
    rw [Subgroup.orderOf_mk]; exact orderOf_invJ₁ φ hZ h2
  have hst : (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) ≠
      ⟨J, element_mem_centralizer_zpowers J⟩ :=
    fun h => J_ne_invJ₁ φ hZ h2 (congrArg Subtype.val h).symm
  have hEodd : Odd (Nat.card ((oddTorus φ).subgroupOf (cT J))) := by
    rw [Nat.card_congr eE.toEquiv]
    exact odd_card_oddTorus φ h2 hq
  have hED : (oddTorus φ).subgroupOf (cT J) ≤ Subgroup.centralizer
      (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J)) := by
    intro e he
    rw [mem_centralizer_zpowers_iff]
    apply Subtype.ext
    exact ((mem_centralizer_fourV φ).mp (oddTorus_le_centralizer_fourV φ he)).2
  have hDVE : ∀ x ∈ Subgroup.centralizer
      (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J)),
      ∃ v ∈ Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
        ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)),
        ∃ e ∈ (oddTorus φ).subgroupOf (cT J), x = v * e := by
    intro x hx
    obtain ⟨v, hv, e, hxe⟩ := hdec ⟨x, hx⟩
    refine ⟨⟨v, fourV_le_cT φ hv⟩, (hVmem _).mpr hv, ⟨e, hEC e.2⟩, e.2, ?_⟩
    exact Subtype.ext hxe
  have hVE : Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
      ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)) ⊓ (oddTorus φ).subgroupOf (cT J) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2'⟩ := Subgroup.mem_inf.mp hx
    have hmem : (x : G) ∈ fourV φ ⊓ oddTorus φ := Subgroup.mem_inf.mpr ⟨(hVmem x).mp h1, h2'⟩
    rw [fourV_inf_oddTorus φ hZ hZodd h2 hJ hq, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
  have hyV : (⟨swapW φ, swapW_mem_cT φ⟩ : cT J) ∈ Subgroup.normalizer
      (Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
        ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)) : Set (cT J)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hVmem, hVmem]
    exact Subgroup.mem_normalizer_iff.mp hWM h
  have hys : (⟨swapW φ, swapW_mem_cT φ⟩ : cT J) * ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ *
      (⟨swapW φ, swapW_mem_cT φ⟩ : cT J)⁻¹ =
        ⟨J, element_mem_centralizer_zpowers J⟩ *
          ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ := by
    apply Subtype.ext
    change swapW φ * invJ₁ φ * (swapW φ)⁻¹ = J * invJ₁ φ
    rw [swapW_conj_invJ₁, invJ₂_eq φ hZ hZodd h2 hJ]
  have hμ₁ : ∀ e e' : (oddTorus φ).subgroupOf (cT J),
      (e' : cT J) = (⟨swapW φ, swapW_mem_cT φ⟩ : cT J)⁻¹ * e * ⟨swapW φ, swapW_mem_cT φ⟩ →
        μ₁' e = μ' e' := by
    intro e e' he'
    change μ (swapConjOdd φ (eE e)) = μ (eE e')
    congr 1
    apply Subtype.ext
    rw [coe_swapConjOdd, heE, heE, he']
    rfl
  have hν₀' : ∀ (x : Subgroup.centralizer
      (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J))) (v : cT J)
      (e : (oddTorus φ).subgroupOf (cT J)),
      v ∈ Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
        ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)) → (x : cT J) = v * e → ν₀ x = μ' e := by
    intro x v e hv hx
    exact hν₀ x v (eE e) ((hVmem v).mp hv) (by rw [hx]; rfl)
  have hν₁' : ∀ (x : Subgroup.centralizer
      (Subgroup.zpowers (⟨invJ₁ φ, invJ₁_mem_cT φ⟩ : cT J) : Set (cT J))) (v : cT J)
      (e : (oddTorus φ).subgroupOf (cT J)),
      v ∈ Subgroup.closure ({⟨J, element_mem_centralizer_zpowers J⟩,
        ⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J)) → (x : cT J) = v * e → ν₁ x = μ₁' e := by
    intro x v e hv hx
    exact hν₁ x v (eE e) ((hVmem v).mp hv) (by rw [hx]; rfl)
  rw [← hcl] at hD
  obtain ⟨θ, f, hθinj, hθb, hf, hdeg, ht0, ht1, ht2, ht3, hs0, hs1, hs2', hs3, -, -, hsupp, -, -,
      hspan, -, -⟩ :=
    central_involution_two_linear_local_blocks_four_characters_and_section_line basisC ideal
      ⟨J, element_mem_centralizer_zpowers J⟩
      ⟨invJ₁ φ, invJ₁_mem_cT φ⟩ htcent ht hs2 hst hs basisCs ((oddTorus φ).subgroupOf (cT J))
      hEodd hED hDVE hVE ⟨swapW φ, swapW_mem_cT φ⟩ hyV hys μ' μ₁' hμ₁ hμne ν₀ ν₁ hν₀' hν₁'
      n₀ n₁ hn₀ hn₁ label hD hfiber
  exact ⟨θ, f, hθinj, hθb, hf, hdeg, ⟨ht0, ht1, ht2, ht3⟩, ⟨hs0, hs1, hs2', hs3⟩, hsupp, hspan⟩

omit [Finite F] in
@[expose] noncomputable def cTHom : GL (Fin 2) F →* cT J :=
  (linearCentralizerHom φ).codRestrict _ fun A =>
    mem_centralizer_zpowers_iff.mpr (linearCentralizerHom_commute φ A)

omit [Finite F] in
theorem cTHom_surjective : Function.Surjective (cTHom φ) := by
  intro x
  obtain ⟨A, hA⟩ := exists_linearCentralizerHom_eq φ (mem_centralizer_zpowers_iff.mp x.2)
  exact ⟨A, Subtype.ext hA⟩

omit [Finite F] in
theorem ker_cTHom : (cTHom φ).ker = Z := by
  ext A
  rw [MonoidHom.mem_ker, ← linearCentralizerHom_eq_one_iff φ]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

include hZ hZodd h2 hJ in
theorem not_dvd_finrank_of_defect_fourV [Fintype G] (hq : Nat.card F % 4 = 3) (p f : ℕ)
    (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisC : FiniteIrreducibleCharacterBasis (cT J)) (label : basisC.index)
    (hD : coefficientBlockDefect basisC ideal 2 label ((fourV φ).subgroupOf (cT J)))
    (θ : basisC.index)
    (hθ : θ ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) label) :
    ¬ p ∣ Module.finrank ℂ (basisC.representation θ).vector := by
  have hV := isKleinFour_fourV φ hZ h2 hJ
  have hcardV : Nat.card ((fourV φ).subgroupOf (cT J)) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fourV_le_cT φ)).toEquiv,
      IsKleinFour.card_four (G := fourV φ)]
    rfl
  obtain ⟨-, -, hall⟩ :=
    block_class_defect_witness_character_degree_dvd basisC ideal 2 label _ hD
  obtain ⟨-, hdvd⟩ := hall 2 hcardV
  have hθdvd := hdvd θ hθ
  have h16 : 2 ^ 4 ∣ Nat.card (cT J) := by
    have e : cT J = Subgroup.centralizer ({J} : Set G) := centralizer_zpowers_eq J
    rw [e]
    have hc := card_centralizer_J φ
    have hodd := odd_card_F h2
    obtain ⟨k, hk⟩ : 4 ∣ Nat.card F + 1 := by omega
    obtain ⟨k', hk'⟩ : 2 ∣ Nat.card F - 1 := by obtain ⟨j, hj⟩ := hodd; omega
    have h16' : 2 ^ 4 ∣ Nat.card (Subgroup.centralizer ({J} : Set G)) * Nat.card Z := by
      rw [hc, hk, hk']
      exact ⟨Nat.card F * k' ^ 2 * k, by ring⟩
    exact (Nat.Coprime.dvd_mul_right (Nat.Coprime.pow_left 4
      (Nat.coprime_two_left.mpr hZodd))).mp h16'
  have hv : 4 ≤ padicValNat 2 (Nat.card (cT J)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp h16
  have h4 : 4 ∣ Module.finrank ℂ (basisC.representation θ).vector :=
    (pow_dvd_pow 2 (show 2 ≤ padicValNat 2 (Nat.card (cT J)) - 2 by omega)).trans hθdvd
  exact not_dvd_of_four_dvd_of_mem_blocksIrr hZ hZodd h2 (cTHom φ) (cTHom_surjective φ)
    (ker_cTHom φ) hq p f hp hf hF _
    ⟨(basisC.representation θ).vector, inferInstance, inferInstance, inferInstance,
      (basisC.representation θ).representation, basisC.irreducible θ, rfl⟩ _
    (Representation.char_one _) h4

include hZ hZodd h2 hJ in
theorem exists_inflation_of_mem_linearOrbit [Finite G] (hq : Nat.card F % 4 = 3)
    (ω : Subgroup.centralizer (fourV φ : Set G) →* ℂˣ)
    (hωV : ∀ x : Subgroup.centralizer (fourV φ : Set G), (x : G) ∈ fourV φ → ω x = 1)
    {μ' : oddTorus φ →* ℂˣ}
    (hμ' : μ' ∈ linearOrbit (oddTorus φ) (ω.comp (Subgroup.inclusion
      (oddTorus_le_centralizer_fourV φ))) (mV (fourV φ) : Set G)) :
    ∃ ν : Subgroup.centralizer (fourV φ : Set G) →* ℂˣ,
      ∀ (x : Subgroup.centralizer (fourV φ : Set G)) (v : G) (e : oddTorus φ),
        v ∈ fourV φ → (x : G) = v * e → ν x = μ' e := by
  have hV := isKleinFour_fourV φ hZ h2 hJ
  have hED := oddTorus_le_centralizer_fourV φ
  have hDVE : ∀ x ∈ dV (fourV φ), ∃ v ∈ fourV φ, ∃ e ∈ oddTorus φ, x = v * e :=
    fun x hx => exists_mul_of_mem_centralizer_fourV φ hZ hZodd h2 hJ hq hx
  have hEodd := odd_card_oddTorus φ h2 hq
  obtain ⟨m, hm, hνm⟩ := hμ'
  refine ⟨ω.comp (dConj hm), fun x v e hv hx => ?_⟩
  have hv' : m⁻¹ * v * m ∈ fourV φ := by
    have h' := (Subgroup.mem_normalizer_iff.mp ((mV (fourV φ)).inv_mem hm) v).mp hv
    rwa [inv_inv] at h'
  have he' : m⁻¹ * (e : G) * m ∈ oddTorus φ := by
    have h' := conj_mem_of_mem hV hED hDVE hEodd ((mV (fourV φ)).inv_mem hm) e.2
    rwa [inv_inv] at h'
  have hsplit : dConj hm x = (⟨m⁻¹ * v * m, le_dV hV hv'⟩ : dV (fourV φ)) *
      ⟨m⁻¹ * e * m, hED he'⟩ := by
    apply Subtype.ext
    change m⁻¹ * (x : G) * m = m⁻¹ * v * m * (m⁻¹ * e * m)
    rw [hx]
    group
  rw [MonoidHom.comp_apply, hsplit, map_mul, hωV _ hv', one_mul,
    hνm e ⟨m⁻¹ * e * m, he'⟩ rfl]
  rfl

omit [Finite F] in
theorem card_centralizer_invJ₁_cT :
    Nat.card (Subgroup.centralizer ({⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J))) =
      Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({invJ₁ φ} : Set G) : Subgroup G) := by
  have hmap : (Subgroup.centralizer ({⟨invJ₁ φ, invJ₁_mem_cT φ⟩} : Set (cT J))).map
      (cT J).subtype = Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({invJ₁ φ} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_centralizer_zpowers_iff.mp y.2).symm, congrArg Subtype.val hy⟩
    · rintro ⟨hxJ, hx₁⟩
      exact ⟨⟨x, mem_centralizer_zpowers_iff.mpr hxJ.symm⟩, Subtype.ext hx₁, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective (cT J).subtype_injective]

omit [Finite F] in
theorem eq_one_or_eq_of_mem_zpowers {g y : G} (hg : orderOf g = 2)
    (hy : y ∈ Subgroup.zpowers g) : y = 1 ∨ y = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hg]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    simp only [Nat.cast_ofNat, h, zpow_zero]
  · right
    simp only [Nat.cast_ofNat, h, zpow_one]

end CFSG.BrauerLinearThree
