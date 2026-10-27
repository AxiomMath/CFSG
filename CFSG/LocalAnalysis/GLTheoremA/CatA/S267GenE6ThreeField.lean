module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenE6ThreeLang
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyTwistedE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RationalComponentEq

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Generic

variable {G : Type*} [Group G]

theorem eq_of_isComponentOf_of_le {A B X : Subgroup G} [Finite X] (hA : IsComponentOf A X)
    (hB : IsComponentOf B X) (hle : A ≤ B) : A = B := by
  by_contra hne
  have h := commutator_eq_bot_of_isComponentOf_ne_of_finite hA hB hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact not_le_centralizer_self_of_isQuasisimple hA.2.2 (h.trans (Subgroup.centralizer_le hle))

theorem fixSubgroup_conj_mul (ψ β : MulAut G) :
    fixSubgroup (ψ * β * ψ⁻¹) = (fixSubgroup β).map ψ.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map, mem_fixSubgroup]
  constructor
  · intro hy
    refine ⟨ψ⁻¹ y, (mem_fixSubgroup).2 ?_, by simp⟩
    have h : ψ (β (ψ⁻¹ y)) = y := hy
    apply ψ.injective
    rw [h]
    simp
  · rintro ⟨c, hc, rfl⟩
    have hc' : β c = c := (mem_fixSubgroup).1 hc
    simp [MulAut.mul_apply, hc']

private theorem commutator_self_of_top {A : Subgroup G} (h : commutator ↥A = ⊤) : ⁅A, A⁆ = A := by
  have h1 : ⁅A, A⁆ = Subgroup.map A.subtype ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h1, ← commutator_def, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem map_eq_of_isComponentOf_conj [Finite G] {γ δ ψ : MulAut G} (hψ : ψ * γ * ψ⁻¹ = δ)
    {J N : Subgroup G} (hJ : IsComponentOf J (fixSubgroup γ)) (hN : IsComponentOf N (fixSubgroup δ))
    (hperf : ∀ P : Subgroup G, P ≤ fixSubgroup δ → ⁅P, P⁆ = P → P ≤ N) :
    J.map ψ.toMonoidHom = N := by
  have hJ' : IsComponentOf (J.map ψ.toMonoidHom) (fixSubgroup δ) := by
    rw [← hψ, fixSubgroup_conj_mul]
    exact isComponentOf_map_of_injective _ ψ.injective hJ
  exact eq_of_isComponentOf_of_le hJ' hN
    (hperf _ hJ'.1 (commutator_self_of_top hJ'.2.2.1))

theorem fix_of_map_eq {E : Subgroup (MulAut G)} {J N : Subgroup G} {ψ : MulAut G}
    (hJfix : ∀ x ∈ E, ∀ c ∈ J, x c = c) (hN : J.map ψ.toMonoidHom = N) :
    ∀ x ∈ E, ∀ c ∈ N, (ψ * x * ψ⁻¹) c = c := by
  intro x hx c hc
  rw [← hN] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp [MulAut.mul_apply, hJfix x hx j hj]

theorem card_lt_of_conj_le_zpowers {E : Subgroup (MulAut G)} {ψ δ : MulAut G}
    (hle : ∀ x ∈ E, ψ * x * ψ⁻¹ ∈ Subgroup.zpowers δ) (hδ : Nat.card (Subgroup.zpowers δ) = 3)
    (hcard : Nat.card E = 3 ^ 2) : False := by
  have hmap : E.map (MulAut.conj ψ).toMonoidHom ≤ Subgroup.zpowers δ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  haveI : Finite (Subgroup.zpowers δ) := Nat.finite_of_card_ne_zero (by rw [hδ]; norm_num)
  have h := Subgroup.card_le_of_le hmap
  rw [Subgroup.card_map_of_injective (MulAut.conj ψ).injective, hcard] at h
  omega

end Generic

section Untwisted

variable
  {K : Type} [Field K] [Finite K]

private theorem exists_fixed_structure_e6 (τ : Tag) (σ : K ≃+* K) :
    ∃ ι : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K, Function.Injective ι ∧
      ι.range ≤ fixSubgroup (entrywiseAdjointAut τ σ) ∧
      ∃ _ : (ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))).Normal,
      Group.IsSolvable (↥(fixSubgroup (entrywiseAdjointAut τ σ)) ⧸
        ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))) ∧
      ∀ x : adjointGroup τ K, x ∈ ι.range ↔ (x : ModGL τ K) ∈ fixedFieldImage τ σ := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, -, hJnormal, hcomm⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hΓnorm : entrywiseFixedGroup τ σ ≤
      Subgroup.normalizer (fixedFieldImage τ σ : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 hJnormal
  have hfix : ∀ x : adjointGroup τ K,
      x ∈ fixSubgroup (entrywiseAdjointAut τ σ) ↔
        (x : ModGL τ K) ∈ entrywiseFixedGroup τ σ := fun x => by
    rw [mem_fixSubgroup, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨x.2, (coe_entrywiseAdjointAut τ σ x).symm.trans (congrArg Subtype.val h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut τ σ x).trans h)
  let ι : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K :=
    ((baseChangeGL (τ := τ) (fixSubfield σ).subtype).comp
      (adjointGroup τ (fixSubfield σ)).subtype).codRestrict (adjointGroup τ K)
      fun u => CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ u.2
  have hι : ∀ u, (ι u : ModGL τ K) =
      baseChangeGL (fixSubfield σ).subtype (u : ModGL τ (fixSubfield σ)) := fun _ => rfl
  have hrange : ∀ x : adjointGroup τ K,
      x ∈ ι.range ↔ (x : ModGL τ K) ∈ fixedFieldImage τ σ := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, (hι u).symm⟩
    · rintro ⟨u, hu, hux⟩
      exact ⟨⟨u, hu⟩, Subtype.ext (by rw [hι]; exact hux)⟩
  have hJle : ι.range ≤ fixSubgroup (entrywiseAdjointAut τ σ) := fun x hx =>
    (hfix x).2 (hJΓ ((hrange x).1 hx))
  have hJn : (ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hrange, hrange]
    exact Subgroup.mem_normalizer_iff.1 (hΓnorm ((hfix g).1 hg)) (h : ModGL τ K)
  have hsol : Group.IsSolvable
      (↥(fixSubgroup (entrywiseAdjointAut τ σ)) ⧸
        ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    have hx : ((x : adjointGroup τ K) : ModGL τ K) ∈ entrywiseFixedGroup τ σ :=
      (hfix x.1).1 x.2
    have hy : ((y : adjointGroup τ K) : ModGL τ K) ∈ entrywiseFixedGroup τ σ :=
      (hfix y.1).1 y.2
    have hq := hcomm (QuotientGroup.mk ⟨_, hx⟩) (QuotientGroup.mk ⟨_, hy⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      hrange]
    exact hq
  exact ⟨ι, fun a b hab => Subtype.ext (hinj (by rw [← hι a, ← hι b, hab])), hJle, hJn, hsol,
    hrange⟩

private theorem exists_conj_eq_entrywiseAdjointAut_e6 (τ : Tag) {p : ℕ} (hp : p.Prime)
    (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσp : σ ^ p = 1)
    (hα : (MulAut.conj g * exactNormalAut τ K a σ 0) ^ p = 1) :
    ∃ ψ : MulAut (adjointGroup τ K),
      ψ * (MulAut.conj g * exactNormalAut τ K a σ 0) * ψ⁻¹ = entrywiseAdjointAut τ σ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hK4 : 4 ≤ Nat.card K := four_le_card_of_ne_one hℓ n.pos hK hσ
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ
  let w : inndiagGroup τ K := ⟨(g : ModGL τ K) * rootDiagUnit τ a,
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)⟩
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (adjointGroup τ K),
      α = MulAut.conj g * exactNormalAut τ K a σ 0 := ⟨_, rfl⟩
  rw [← hαdef] at hα ⊢
  have hαeq : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (w : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
        (w : ModGL τ K)⁻¹ := by
    intro h
    rw [hαdef, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero]
    simp only [w, mul_inv_rev, one_mul, inv_one, mul_one]
    group
  let ιC : adjointGroup τ K → inndiagGroup τ K := fun h => ⟨h, adjointGroup_le_inndiagGroup h.2⟩
  obtain ⟨X, hXdef⟩ : ∃ X : MulAut (inndiagGroup τ K),
      X = MulAut.conj w * inndiagFieldAut τ K σ := ⟨_, rfl⟩
  have hX1 : ∀ h : adjointGroup τ K, X (ιC h) = ιC (α h) := fun h => Subtype.ext (by
    rw [hXdef, MulAut.mul_apply, MulAut.conj_apply]
    change (w : ModGL τ K) * (inndiagFieldAut τ K σ (ιC h) : ModGL τ K) * (w : ModGL τ K)⁻¹ = _
    rw [hαeq]
    rfl)
  have hXk : ∀ (k : ℕ) (h : adjointGroup τ K), (X ^ k) (ιC h) = ιC ((α ^ k) h) := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ', MulAut.mul_apply, ih, hX1, pow_succ', MulAut.mul_apply]
  have hXp : X ^ p = 1 := by
    refine MulEquiv.ext fun γ => ?_
    rw [MulAut.one_apply]
    obtain ⟨β, hβdef⟩ : ∃ β : MulAut (inndiagGroup τ K), β = X ^ p := ⟨_, rfl⟩
    rw [← hβdef]
    have hβι : ∀ h : adjointGroup τ K, β (ιC h) = ιC h := fun h => by
      rw [hβdef, hXk, hα, MulAut.one_apply]
    have hz : ∀ h ∈ adjointGroup τ K, ((γ⁻¹ * β γ : inndiagGroup τ K) : ModGL τ K) * h =
        h * ((γ⁻¹ * β γ : inndiagGroup τ K) : ModGL τ K) := by
      intro h hh
      have hh' : (γ : ModGL τ K) * h * (γ : ModGL τ K)⁻¹ ∈ adjointGroup τ K :=
        conj_mem_adjointGroup_of_mem_inndiag γ.2 hh
      have e2 : β (γ * ιC ⟨h, hh⟩ * γ⁻¹) = β γ * ιC ⟨h, hh⟩ * (β γ)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hβι]
      have e3 : γ * ιC ⟨h, hh⟩ * γ⁻¹ = ιC ⟨_, hh'⟩ := rfl
      rw [e3, hβι] at e2
      have e4 : (γ : ModGL τ K) * h * (γ : ModGL τ K)⁻¹ =
          (β γ : ModGL τ K) * h * (β γ : ModGL τ K)⁻¹ := congrArg Subtype.val e2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (γ : ModGL τ K)⁻¹ * (β γ : ModGL τ K) * h =
          (γ : ModGL τ K)⁻¹ * ((β γ : ModGL τ K) * h * (β γ : ModGL τ K)⁻¹) *
            (β γ : ModGL τ K) := by group
        _ = (γ : ModGL τ K)⁻¹ * ((γ : ModGL τ K) * h * (γ : ModGL τ K)⁻¹) *
            (β γ : ModGL τ K) := by rw [e4]
        _ = h * ((γ : ModGL τ K)⁻¹ * (β γ : ModGL τ K)) := by group
    have h1 := eq_one_of_commute_adjointGroup hK4 (γ⁻¹ * β γ).2 hz
    exact (inv_mul_eq_one.1 (Subtype.ext h1)).symm
  obtain ⟨g', hg'⟩ := exists_conj_eq_inndiagFieldAut (τ := τ) n.pos hK hp σ hord w
    (by rw [← hXdef]; exact hXp)
  refine ⟨inndiagConj τ K g', MulEquiv.ext fun h => Subtype.ext ?_⟩
  have e1 := congrArg (fun φ : MulAut (inndiagGroup τ K) => (φ (ιC h) : ModGL τ K)) hg'
  rw [← hXdef] at e1
  have hc1 : ∀ u : adjointGroup τ K,
      (MulAut.conj g') (ιC u) = ιC (inndiagConj τ K g' u) := fun u => Subtype.ext rfl
  have hc2 : ∀ u : adjointGroup τ K,
      (MulAut.conj g')⁻¹ (ιC u) = ιC ((inndiagConj τ K g')⁻¹ u) := fun u => by
    rw [← map_inv, ← map_inv]
    exact Subtype.ext rfl
  simp only [MulAut.mul_apply] at e1 ⊢
  rw [hc2, hX1, hc1] at e1
  exact e1

theorem e6Three_not_common_component_of_not_le_inndiag
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : ¬ E ≤ e6Inndiag K) (J : Subgroup (adjointGroup Tag.E6 K)) :
    ¬ ∀ x ∈ E, x ≠ 1 → IsComponentOf J (fixSubgroup x) := by
  classical
  intro hall
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  obtain ⟨Θ, -, hΘ, hker, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6
    (Or.inl rfl) K
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨β, hβE, hβΘ⟩ : ∃ β ∈ E, Θ β ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hd
    intro α hα
    obtain ⟨g, a, hga⟩ := (hker α).1 (hno α hα)
    have e : α = MulAut.conj g * rootDiagAutHom Tag.E6 K a := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [hga h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
      change _ = (g : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 a * h * (rootDiagUnit Tag.E6 a)⁻¹) *
        (g : ModGL Tag.E6 K)⁻¹
      group
    rw [e, e6Inndiag]
    exact Subgroup.mul_mem_sup ⟨g, rfl⟩ ⟨a, rfl⟩
  have hβ3 : β ^ 3 = 1 := hE.2 β hβE
  obtain ⟨g, a, σ, ε, hform⟩ := hnf β
  have hΘβ := hΘ β g a σ ε hform
  have hΘp : Θ β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  rw [hΘβ] at hΘp
  have hσ3 : σ ^ 3 = 1 := by simpa using congrArg Prod.fst hΘp
  have hε0 : (ε : ℕ) = 0 := by
    have h2 : (Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE Tag.E6))) ^ 3 = 1 :=
      congrArg Prod.snd hΘp
    rw [← ofAdd_nsmul, ofAdd_eq_one] at h2
    have hεp : exactE Tag.E6 ∣ 3 * (ε : ℕ) := by
      rw [← ZMod.natCast_eq_zero_iff]
      simpa using h2
    have hcop : Nat.Coprime (exactE Tag.E6) 3 :=
      (Nat.coprime_primes Nat.prime_two Nat.prime_three).2 (by norm_num)
    exact Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_left hεp) ε.2
  rw [hε0] at hform
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hβΘ
    rw [hΘβ, hε0]
    rfl
  have hβe : β = MulAut.conj g * exactNormalAut Tag.E6 K a σ 0 :=
    eq_conj_mul_exactNormalAut_of_apply hform
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_e6 Tag.E6 Nat.prime_three g a σ hσ1 hσ3
    (by rw [← hβe]; exact hβ3)
  rw [← hβe] at hψ
  obtain ⟨ι, hι, hNC, hNn, hsol, hrange⟩ := exists_fixed_structure_e6 Tag.E6 σ
  have hNq : CFSG.Open.IsQuasisimple ι.range := by
    let e₁ : adjointGroup Tag.E6 (fixSubfield σ) ≃* ι.range := MonoidHom.ofInjective hι
    have hq₀ := CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 (fixSubfield σ)
    let e₂ : adjointGroup Tag.E6 (fixSubfield σ) ⧸
        Subgroup.center (adjointGroup Tag.E6 (fixSubfield σ)) ≃*
          adjointGroup Tag.E6 (fixSubfield σ) :=
      (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot_field Tag.E6 _)).trans
        QuotientGroup.quotientBot
    let f := e₂.trans e₁
    have hJs : IsSimpleGroup ι.range :=
      CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq₀ f.symm
    obtain ⟨-, -, hnc⟩ := hq₀
    have hnc' : ∃ a b : ι.range, a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ := hnc
      refine ⟨f x, f y, fun h => hxy (f.injective ?_)⟩
      rw [map_mul, map_mul]
      exact h
    have hq := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup
      hJs hnc'
    exact ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hNcomp : IsComponentOf ι.range (fixSubgroup (entrywiseAdjointAut Tag.E6 σ)) :=
    ⟨hNC, .step hNC hNn (.refl _), hNq⟩
  have hJfix : ∀ x ∈ E, ∀ c ∈ J, x c = c := fun x hx c hc => by
    by_cases hx1 : x = 1
    · rw [hx1, MulAut.one_apply]
    · exact (mem_fixSubgroup).1 ((hall x hx hx1).1 hc)
  have hβ1 : β ≠ 1 := fun h => hβΘ (by rw [h, map_one])
  have hJN := map_eq_of_isComponentOf_conj hψ (hall β hβE hβ1) hNcomp fun P hPC hP =>
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hNC
      hsol hPC hP
  have hfixN := fix_of_map_eq hJfix hJN
  refine card_lt_of_conj_le_zpowers (ψ := ψ) (δ := entrywiseAdjointAut Tag.E6 σ)
    (fun x hx => FieldGraphFieldPointwise.mem_zpowers_of_forall_fixedFieldImage σ
      fun j hj => hfixN x hx j ((hrange j).2 hj)) ?_ hcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers,
    CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut Tag.E6.rank_pos σ,
    orderOf_eq_prime hσ3 hσ1]

end Untwisted

section Twisted


open CFSG.RankThree.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge
  CFSG.HardMathSupport.Lang.Coordinator in
theorem twE6Three_not_common_component_of_not_le_inndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hd : ¬ E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (J : Subgroup (twistedE6RootGroup K σ)) :
    ¬ ∀ x ∈ E, x ≠ 1 → IsComponentOf J (fixSubgroup x) := by
  classical
  intro hall
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  obtain ⟨β, hβE, hβΘ⟩ : ∃ β ∈ E, Θ β ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hd
    intro α hα
    rw [← hker]
    exact hno α hα
  have hβ3 : β ^ 3 = 1 := hE.2 β hβE
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨d, hd3, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    twisted_E6_field_descent_data_of_prime_order hℓ hf K hK2f σ hσ Θ hΘ Nat.prime_three
      (by norm_num) β hβ3 hβΘ
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ
    (by omega : 1 ≤ 2 * f) hK2f
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = ℓ ^ (2 * d * 3) := by
    rw [hK2f, hd3]
    ring_nf
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * 3) := fun c => by
    rw [hσ, hd3, mul_comm]
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, -, hJC, hδord, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd1
      (le_refl 3) (by decide) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  have hfixpow := twistedE6_zpowers_of_fixes hℓ hd1 (le_refl 3) (by decide) K hKdp κ hκ σ hσdp
    (fixSubfieldRestrict T κ) hσ₀ ε hε
  set J₀ := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ) with hJ₀
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδ
  have hΓ : fixSubgroup δ =
      MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id (twistedE6RootGroup K σ)) := rfl
  have hNC : J₀.subgroupOf (twistedE6RootGroup K σ) ≤ fixSubgroup δ := by
    rw [hΓ, ← hder]
    exact Subgroup.commutator_le_self _
  have hNn : ((J₀.subgroupOf (twistedE6RootGroup K σ)).subgroupOf (fixSubgroup δ)).Normal := by
    rw [hΓ, ← hder]
    have h := Subgroup.normal_subgroupOf_commutator_sup
      (MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id (twistedE6RootGroup K σ)))
      (MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id (twistedE6RootGroup K σ)))
    rwa [sup_idem] at h
  have eJC : J₀.subgroupOf (twistedE6RootGroup K σ) ≃* J₀ := Subgroup.subgroupOfEquivOfLe hJC
  have hNq : CFSG.Open.IsQuasisimple (J₀.subgroupOf (twistedE6RootGroup K σ)) := by
    have hJs : IsSimpleGroup (J₀.subgroupOf (twistedE6RootGroup K σ)) := eJC.isSimpleGroup
    have hq := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup
      hJs (by
        by_contra hcon
        push Not at hcon
        apply hncJ
        intro a b
        apply eJC.symm.injective
        rw [map_mul, map_mul]
        exact hcon _ _)
    exact ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hNcomp : IsComponentOf (J₀.subgroupOf (twistedE6RootGroup K σ)) (fixSubgroup δ) :=
    ⟨hNC, .step hNC hNn (.refl _), hNq⟩
  have hγE : β ^ r ∈ E := pow_mem hβE r
  have hγ1 : β ^ r ≠ 1 := fun h => hβΘ (by rw [← hrs, h, one_pow, map_one])
  have hJfix : ∀ x ∈ E, ∀ c ∈ J, x c = c := fun x hx c hc => by
    by_cases hx1 : x = 1
    · rw [hx1, MulAut.one_apply]
    · exact (mem_fixSubgroup).1 ((hall x hx hx1).1 hc)
  have hJN := map_eq_of_isComponentOf_conj hψ (hall _ hγE hγ1) hNcomp fun P hPC hP => by
    have hPC' : P ≤ MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id (twistedE6RootGroup K σ)) :=
      hPC
    calc P = ⁅P, P⁆ := hP.symm
      _ ≤ _ := Subgroup.commutator_mono hPC' hPC'
      _ = _ := hder
  have hfixN := fix_of_map_eq hJfix hJN
  refine card_lt_of_conj_le_zpowers (ψ := ψ) (δ := δ)
    (fun x hx => hfixpow _ fun c hc => hfixN x hx c (Subgroup.mem_subgroupOf.2 hc)) ?_ hcard
  rw [Nat.card_zpowers, hδord]

end Twisted

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
