module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerAction
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.LieType.Chevalley.CLSEvenE6AllInvolutionFourGroup

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)
open CFSG.LieType.Chevalley.E6GraphFullCoset (IsOrdinaryDiagGraph)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped Pointwise

section General

variable {M : Type*} [Group M]

theorem card_centralizer_conj (φ β : M) :
    Nat.card (centralizer ({φ * β * φ⁻¹} : Set M)) = Nat.card (centralizer ({β} : Set M)) := by
  have h : (centralizer ({β} : Set M)).map (MulAut.conj φ).toMonoidHom =
      centralizer ({φ * β * φ⁻¹} : Set M) := by
    ext x
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      calc φ * y * φ⁻¹ * (φ * β * φ⁻¹) = φ * (y * β) * φ⁻¹ := by group
        _ = φ * (β * y) * φ⁻¹ := by rw [hy]
        _ = φ * β * φ⁻¹ * (φ * y * φ⁻¹) := by group
    · intro hx
      refine ⟨φ⁻¹ * x * φ, ?_, by group⟩
      calc φ⁻¹ * x * φ * β = φ⁻¹ * (x * (φ * β * φ⁻¹)) * φ := by group
        _ = φ⁻¹ * ((φ * β * φ⁻¹) * x) * φ := by rw [hx]
        _ = β * (φ⁻¹ * x * φ) := by group
  rw [← h, card_map_of_injective (f := (MulAut.conj φ).toMonoidHom) (MulAut.conj φ).injective]

variable {C : Type*} [Group C]

theorem mulAut_mul_conj_mul_inv' (β : MulAut C) (c : C) :
    β * MulAut.conj c * β⁻¹ = MulAut.conj (β c) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem card_centralizer_dvd_card_eqLocus_mul_card_outer (hZ : center C = ⊥) (β : MulAut C) :
    Nat.card (centralizer ({β} : Set (MulAut C))) ∣
      Nat.card (MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id C)) *
        Nat.card (OuterAutomorphisms.Outer C) := by
  set Z := centralizer ({β} : Set (MulAut C))
  set π : Z →* OuterAutomorphisms.Outer C :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner C)).comp Z.subtype with hπ
  have hinj := mulAut_conj_injective_of_center hZ
  have hmemZ : ∀ c : C, MulAut.conj c ∈ Z ↔ β c = c := fun c => by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : β * MulAut.conj c * β⁻¹ = MulAut.conj c := by rw [← h]; group
      rw [mulAut_mul_conj_mul_inv'] at h'
      exact hinj h'
    · intro h
      have h' : β * MulAut.conj c * β⁻¹ = MulAut.conj c := by
        rw [mulAut_mul_conj_mul_inv', h]
      calc MulAut.conj c * β = β * MulAut.conj c * β⁻¹ * β := by rw [h']
        _ = β * MulAut.conj c := by group
  have hker : Nat.card π.ker = Nat.card (MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id C)) := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun c : MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id C) =>
        (⟨⟨MulAut.conj (c : C), (hmemZ c).2 c.2⟩, ?_⟩ : π.ker)) ⟨?_, ?_⟩)).symm
    · rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact ⟨c, rfl⟩
    · intro a b h
      have h' := congrArg (fun z : π.ker => ((z : Z) : MulAut C)) h
      exact Subtype.ext (hinj h')
    · rintro ⟨⟨z, hz⟩, hzk⟩
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hzk
      obtain ⟨c, hc⟩ := hzk
      have hcZ : MulAut.conj c ∈ Z := by
        rw [show MulAut.conj c = z from hc]
        exact hz
      refine ⟨⟨c, (hmemZ c).1 hcZ⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hc)
  have hrange : Nat.card π.range ∣ Nat.card (OuterAutomorphisms.Outer C) := by
    rw [← card_top (G := OuterAutomorphisms.Outer C)]
    exact card_dvd_of_le le_top
  rw [← card_ker_mul_card_range π, hker]
  exact Nat.mul_dvd_mul_left _ hrange

theorem conj_mem_centralizer_singleton_iff (hZ : center C = ⊥) (β : MulAut C) (c : C) :
    MulAut.conj c ∈ centralizer ({β} : Set (MulAut C)) ↔ β c = c := by
  have hinj := mulAut_conj_injective_of_center hZ
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : β * MulAut.conj c * β⁻¹ = MulAut.conj c := by rw [← h]; group
    rw [mulAut_mul_conj_mul_inv'] at h'
    exact hinj h'
  · intro h
    have h' : β * MulAut.conj c * β⁻¹ = MulAut.conj c := by
      rw [mulAut_mul_conj_mul_inv', h]
    calc MulAut.conj c * β = β * MulAut.conj c * β⁻¹ * β := by rw [h']
      _ = β * MulAut.conj c := by group

theorem factorization_two_mul_odd {m n : ℕ} (hm : m ≠ 0) (hn : Odd n) :
    (m * n).factorization 2 = m.factorization 2 := by
  rw [Nat.factorization_mul hm hn.pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.2 hn)
      (even_iff_two_dvd.2 h)), add_zero]

theorem odd_two_pow_pow_sub_one {e k : ℕ} (he : e ≠ 0) (hk : k ≠ 0) : Odd ((2 ^ e) ^ k - 1) := by
  have hev : Even ((2 ^ e) ^ k) := (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, he⟩, hk⟩)
  exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.2 (by positivity)) hev odd_one

theorem odd_two_pow_pow_add_one {e k : ℕ} (he : e ≠ 0) (hk : k ≠ 0) : Odd ((2 ^ e) ^ k + 1) :=
  (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, he⟩, hk⟩).add_one

theorem one_ne_ofAdd_one_zmod_two : (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd 1 := by
  decide

end General

@[expose] def fixSubgroup {C : Type*} [Group C] (β : MulAut C) : Subgroup C :=
  MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id C)

@[expose] def OuterFixBoundsE6 (K : Type) [Field K] (f : ℕ) : Prop :=
  (∀ η : MulAut (adjointGroup TwistTag.E6.tag K),
    (∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) →
    (Nat.card (fixSubgroup η)).factorization 2 ≤ 24 * f + f.factorization 2) ∧
  (∀ (η : MulAut (adjointGroup TwistTag.E6.tag K))
    (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K),
    (∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) →
    (Nat.card (fixSubgroup (MulAut.conj ⟨_, ht⟩ * η))).factorization 2 ≤
      24 * f + f.factorization 2) ∧
  (∀ σ : K ≃+* K, σ ^ 2 = 1 → σ ≠ 1 →
    (Nat.card (fixSubgroup (entrywiseAdjointAut TwistTag.E6.tag σ))).factorization 2 ≤
      24 * f + f.factorization 2) ∧
  (∀ σ : K ≃+* K, σ ^ 2 = 1 → σ ≠ 1 →
    (Nat.card (fixSubgroup (diagramConjAut TwistTag.E6 K *
      entrywiseAdjointAut TwistTag.E6.tag σ))).factorization 2 ≤ 24 * f + f.factorization 2)

theorem outer_involution_cases_E6 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup TwistTag.E6.tag K)) (hα : α ^ 2 = 1)
    (hαo : α ∉ OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag K)) :
    (∃ η : MulAut (adjointGroup TwistTag.E6.tag K),
      (∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) ∧
      ((∃ φ : MulAut (adjointGroup TwistTag.E6.tag K), φ * α * φ⁻¹ = η) ∨
        ∃ (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K)
          (φ : MulAut (adjointGroup TwistTag.E6.tag K)),
          φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η)) ∨
    ∃ σ : K ≃+* K, σ ^ 2 = 1 ∧ σ ≠ 1 ∧
      ((∃ φ : MulAut (adjointGroup TwistTag.E6.tag K),
          φ * α * φ⁻¹ = entrywiseAdjointAut TwistTag.E6.tag σ) ∨
        ∃ φ : MulAut (adjointGroup TwistTag.E6.tag K),
          φ * α * φ⁻¹ = diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨Θ, -, hΘ, -, hinv, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have hΘα := hΘ α g a σ ε hga
  have hε2 : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε2 with h0 | h1
    ·
      exfalso
      refine hαo (EvenE6AllInvolution.mem_inner_of_conj_mul_rootDiagAut (τ := TwistTag.E6.tag)
        hK hf g a ?_ hα)
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
          (h : ModGL TwistTag.E6.tag K) = h := Units.ext (entrywise_id _)
      rw [hga h, h0, exactQ_zero, e1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
      group
    · obtain ⟨ht, η, hη, hconj, hiff, -, -⟩ :=
        (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 K hK
      have hdiag : IsOrdinaryDiagGraph K α := by
        rw [hiff Θ hΘ, hΘα, h1, Nat.cast_one]
      refine Or.inl ⟨η, hη, ?_⟩
      rcases hconj α hdiag hα with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
      · exact Or.inl ⟨φ, hφ⟩
      · exact Or.inr ⟨ht, φ, hφ⟩
  · have hσ2 : σ ^ 2 = 1 := hinv α g a σ ε hga hα
    obtain ⟨⟨e, he⟩, hσc, -⟩ := hfield 2 f Nat.prime_two hf hK σ hσ2 hσ1
    have he1 : 1 ≤ e := by omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show f / 2 = e by omega]
    obtain ⟨hQ1, hQP⟩ :=
      even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ'
    refine Or.inr ⟨σ, hσ2, hσ1, ?_⟩
    rcases hε2 with h0 | h1
    ·
      obtain ⟨_, -, hdesc⟩ := hQ1 TwistTag.E6.tag
      obtain ⟨-, hdα⟩ := hdesc g a
      have hαform : ∀ u, (α u : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag a * Units.map (entrywiseHom σ.toRingHom)
            (u : ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro u
        rw [hga u, h0, exactQ_zero, mul_one, inv_one, mul_one]
      obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα)
      exact Or.inl ⟨ψ, MulEquiv.ext fun u => Subtype.ext (by
        rw [hψ u, coe_entrywiseAdjointAut])⟩
    ·
      obtain ⟨_, -, hdesc⟩ := hQP
      obtain ⟨-, hdα⟩ := hdesc g a
      have hαform : ∀ u, (α u : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
            Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro u
        rw [hga u, h1]
        rfl
      obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα)
      exact Or.inr ⟨ψ, MulEquiv.ext fun u => Subtype.ext (by
        rw [hψ u, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut])⟩

theorem factorization_card_adjointGroup {τ : Tag} {K : Type} [Field K] [Finite K] {p f : ℕ}
    [hp : Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ f) :
    (Nat.card (adjointGroup τ K)).factorization p =
      f * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  obtain ⟨-, hind⟩ := isPGroup_and_not_dvd_index (τ := τ) (K := K) p
    posUnipotent_le_adjointGroup card_posUnipotent
  have hind0 : ((posUnipotent τ K).subgroupOf (adjointGroup τ K)).index ≠ 0 := fun h =>
    hind (h ▸ dvd_zero p)
  rw [← card_mul_index ((posUnipotent τ K).subgroupOf (adjointGroup τ K)),
    card_subgroupOf_of_le posUnipotent_le_adjointGroup, card_posUnipotent, hK, ← pow_mul,
    Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hind0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hind, add_zero]

theorem factorization_card_fixSubgroup_graph_E6 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (η : MulAut (adjointGroup TwistTag.E6.tag K))
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) :
    (Nat.card (fixSubgroup η)).factorization 2 = 24 * f := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hfix : fixSubgroup η =
      (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subgroupOf
        (adjointGroup TwistTag.E6.tag K) := by
    rw [twistedFixedGroup_subgroupOf]
    unfold fixSubgroup
    congr 1
    refine MonoidHom.ext fun g => Subtype.ext ?_
    rw [MulEquiv.coe_toMonoidHom, hη, coe_twistC, twistHom_apply]
    congr 2
    exact (Units.ext (entrywise_id _)).symm
  obtain ⟨-, -, -, -, ⟨Ψ, -⟩, -⟩ := even_E6_pure_graph_fixed_group_exact_F4 K hK2
  rw [hfix, card_subgroupOf_of_le (twistedFixedGroup_le_adjointGroup _ _ _),
    Nat.card_congr Ψ.toEquiv, factorization_card_adjointGroup hK,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4, mul_comm]

theorem factorization_card_fixSubgroup_field_E6 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    (Nat.card (fixSubgroup (entrywiseAdjointAut TwistTag.E6.tag σ))).factorization 2 =
      18 * f := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨⟨e, he⟩, -, hcardk⟩ := hfield 2 f Nat.prime_two hf hK σ hσ2 hσ1
  have hfe : f / 2 = e := by omega
  have he1 : 1 ≤ e := by omega
  set k := fixSubfield σ with hkdef
  have hk : Nat.card k = 2 ^ e := by
    rw [← hfe, ← hcardk]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => Iff.rfl)
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two he1 hk
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  set C := adjointGroup TwistTag.E6.tag K
  set Γ := entrywiseFixedGroup TwistTag.E6.tag σ
  set J := fixedFieldImage TwistTag.E6.tag σ
  set H := entrywiseFixedTorus TwistTag.E6.tag σ
  have hFδ : fixSubgroup (entrywiseAdjointAut TwistTag.E6.tag σ) = Γ.subgroupOf C := by
    ext g
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  obtain ⟨-, -, -, hJΓ, hΓ, -, -⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup TwistTag.E6.tag K σ
  have hΓC : Γ ≤ C := inf_le_left
  have hHΓ : H ≤ Γ := entrywiseFixedTorus_le
  set J' := J.subgroupOf Γ
  have hsurj : Function.Surjective ((QuotientGroup.mk' J').comp (Subgroup.inclusion hHΓ)) := by
    intro x
    obtain ⟨⟨γ, hγ⟩, rfl⟩ := QuotientGroup.mk'_surjective J' x
    have hγ' : γ ∈ (H : Set (ModGL TwistTag.E6.tag K)) * (J : Set (ModGL TwistTag.E6.tag K)) := by
      rw [← hΓ]
      exact hγ
    obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hγ'
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.2 ?_
    change (h : ModGL TwistTag.E6.tag K)⁻¹ * (h * j) ∈ J
    rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact hj
  have hind : J'.index ∣ Nat.card H := by
    rw [Subgroup.index]
    exact card_dvd_of_surjective _ hsurj
  have hHodd : ¬ 2 ∣ Nat.card H := by
    intro h2
    have hHT : Nat.card H ∣ Nat.card (torusGroup Tag.E6 K) := card_dvd_of_le inf_le_left
    have hT := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E6 (K := K)
    have hodd : Odd ((Nat.card K - 1) ^ 6) := by
      refine Odd.pow ?_
      rw [hK]
      have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      obtain ⟨m, hm⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
      rw [hm, pow_succ]
      exact ⟨2 ^ m - 1, by have : 1 ≤ 2 ^ m := Nat.one_le_two_pow; omega⟩
    have h2T : 2 ∣ (Nat.card K - 1) ^ 6 := by
      rw [← hT]
      exact Dvd.dvd.mul_right (h2.trans hHT) _
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2T)
  have hind2 : ¬ 2 ∣ J'.index := fun h => hHodd (h.trans hind)
  have hind0 : J'.index ≠ 0 := fun h => hind2 (h ▸ dvd_zero 2)
  have hJcard : Nat.card J' = Nat.card (adjointGroup Tag.E6 k) := by
    rw [card_subgroupOf_of_le hJΓ]
    exact (Nat.card_congr (fixedFieldImageEquiv σ).toEquiv).symm
  have hJ0 : Nat.card J' ≠ 0 := Nat.card_pos.ne'
  rw [hFδ, card_subgroupOf_of_le hΓC, ← card_mul_index J', Nat.factorization_mul hJ0 hind0,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hind2, add_zero, hJcard,
    factorization_card_adjointGroup hk, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E6]
  omega

theorem factorization_card_fixSubgroup_graphField_E6 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    (Nat.card (fixSubgroup (diagramConjAut TwistTag.E6 K *
      entrywiseAdjointAut TwistTag.E6.tag σ))).factorization 2 ≤ 18 * f := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨⟨e, he⟩, hσc, -⟩ := hfield 2 f Nat.prime_two hf hK σ hσ2 hσ1
  have hfe : f / 2 = e := by omega
  have he1 : 1 ≤ e := by omega
  have he0 : e ≠ 0 := by omega
  have hK' : Nat.card K = (2 ^ e) ^ 2 := by rw [hK, he, ← pow_mul, mul_comm, two_mul]
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ e := fun c => by
    change σ c = _
    rw [hσc, hfe]
  set C := adjointGroup TwistTag.E6.tag K
  have hfix : fixSubgroup (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) =
      (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K σ.toRingHom).subgroupOf C := by
    rw [twistedFixedGroup_subgroupOf]
    unfold fixSubgroup
    congr 1
    refine MonoidHom.ext fun g => Subtype.ext ?_
    rw [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, coe_diagramConjAut, coe_twistC,
      twistHom_apply, coe_entrywiseAdjointAut]
  set Ω := AlgebraicClosure K
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : ExpChar Ω 2 := ExpChar.prime Nat.prime_two
  set Fr : Ω →+* Ω := iterateFrobenius Ω 2 e
  have hFr : ∀ c, Fr c = c ^ 2 ^ e := fun c => iterateFrobenius_def 2 e c
  obtain ⟨-, -, -, -, -, hcard, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order Nat.prime_two he1 K hK'
      σ.toRingHom hσ' Ω Fr hFr
  have hcomp : (algebraMap K Ω).comp σ.toRingHom = Fr.comp (algebraMap K Ω) :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hσ', hFr, map_pow]
  have hle : (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K Ω)) ≤ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 Ω Fr := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hgC, hgF⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨baseChangeGL_mem_adjointGroup _ hgC, ?_⟩
    change twistHom TwistTag.E6 Ω Fr (baseChangeGL (algebraMap K Ω) g) =
      baseChangeGL (algebraMap K Ω) g
    rw [twistHom_baseChangeGL _ hcomp]
    exact congrArg _ hgF
  have hdvd : Nat.card (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K σ.toRingHom) ∣
      Nat.card (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 Ω Fr) := by
    rw [← card_map_of_injective (f := baseChangeGL (algebraMap K Ω))
      (baseChangeGL_injective (algebraMap K Ω))]
    exact card_dvd_of_le hle
  rw [hcard] at hdvd
  have o12 := odd_two_pow_pow_sub_one he0 (k := 12) (by norm_num)
  have o9 := odd_two_pow_pow_add_one he0 (k := 9) (by norm_num)
  have o8 := odd_two_pow_pow_sub_one he0 (k := 8) (by norm_num)
  have o6 := odd_two_pow_pow_sub_one he0 (k := 6) (by norm_num)
  have o5 := odd_two_pow_pow_add_one he0 (k := 5) (by norm_num)
  have o2 := odd_two_pow_pow_sub_one he0 (k := 2) (by norm_num)
  have p36 : (2 ^ e) ^ 36 ≠ 0 := by positivity
  have n1 := mul_ne_zero p36 o12.pos.ne'
  have n2 := mul_ne_zero n1 o9.pos.ne'
  have n3 := mul_ne_zero n2 o8.pos.ne'
  have n4 := mul_ne_zero n3 o6.pos.ne'
  have n5 := mul_ne_zero n4 o5.pos.ne'
  have n6 := mul_ne_zero n5 o2.pos.ne'
  have hfac := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' n6).2 hdvd 2
  rw [factorization_two_mul_odd n5 o2, factorization_two_mul_odd n4 o5,
    factorization_two_mul_odd n3 o6, factorization_two_mul_odd n2 o8,
    factorization_two_mul_odd n1 o9, factorization_two_mul_odd p36 o12, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hfac
  rw [hfix, card_subgroupOf_of_le (twistedFixedGroup_le_adjointGroup _ _ _)]
  omega

noncomputable abbrev graphFixedJ (K : Type) [Field K] : Subgroup (ModGL TwistTag.E6.tag K) :=
  (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K (RingHom.id K)).map (baseChangeGL (RingHom.id K))

theorem factorization_card_fixSubgroup_secondGraph_E6 {f : ℕ}
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (η : MulAut (adjointGroup TwistTag.E6.tag K))
    (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K)
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) :
    (Nat.card (fixSubgroup (MulAut.conj ⟨_, ht⟩ * η))).factorization 2 ≤
      24 * f + f.factorization 2 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hZ : center (adjointGroup TwistTag.E6.tag K) = ⊥ := center_adjointGroup_eq_bot_field _ K
  have hinj := mulAut_conj_injective_of_center hZ
  have hSG : E6SecondGraphFull.SecondGraphFullCentralizer (adjointGroup TwistTag.E6.tag K)
      (graphFixedJ K) (diagramMap TwistTag.E6 K) (pinnedX TwistTag.E6.tag K e6HighestRoot 1)
      (E6SecondGraphFull.embeddedFieldAut (RingHom.id K)) :=
    E6SecondGraphFull.secondGraphFullCentralizer_adjointGroup hf K hK
  obtain ⟨htJ, hJC, η', hη', -, res, -, hker, hrange, huniq, -, -, -⟩ := hSG
  have hηη' : η = η' := MulEquiv.ext fun h => Subtype.ext ((hη h).trans (hη' h).symm)
  have hξ : MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag K) * η =
      MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η' := by
    rw [hηη']
  rw [hξ]
  have hP2 : diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K = 1 := by
    rw [← sq]
    exact diagramMap_pow_order TwistTag.E6 K
  have hη'2 : η' * η' = 1 := MulEquiv.ext fun h => Subtype.ext (by
    rw [MulAut.mul_apply, hη', hη', MulAut.one_apply]
    calc diagramMap TwistTag.E6 K * (diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 K)⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ =
          (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K) * (h : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K)⁻¹ := by group
      _ = h := by rw [hP2]; group)
  have hη'I : η' ∉ OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag K) := by
    rintro ⟨c, hc⟩
    obtain ⟨Θ, -, hΘ, hΘker, -, -⟩ :=
      ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
    obtain ⟨-, -, -, -, hiff, -, -⟩ :=
      (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 K hK
    have hdiag : IsOrdinaryDiagGraph K η' :=
      ⟨1, 1, one_mem _, fun h => by rw [hη', rootDiagUnit_one]; group⟩
    have hΘη := (hiff Θ hΘ η').1 hdiag
    have hΘc : Θ (MulAut.conj c) = 1 := (hΘker _).2 ⟨c, 1, fun h => by
      rw [rootDiagUnit_one, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group⟩
    rw [hc] at hΘc
    rw [hΘc] at hΘη
    have h2 := congrArg Prod.snd hΘη
    exact one_ne_ofAdd_one_zmod_two h2
  have hmemZ : ∀ c : fixSubgroup (MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η'), MulAut.conj (c : adjointGroup TwistTag.E6.tag K) ∈
      centralizer ({(MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η')} : Set (MulAut (adjointGroup TwistTag.E6.tag K))) := fun c =>
    (conj_mem_centralizer_singleton_iff hZ (MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η') c).2 c.2
  let ψ : fixSubgroup (MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η') →* centralizer ({(MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η')} : Set (MulAut (adjointGroup TwistTag.E6.tag K))) :=
    MonoidHom.codRestrict ((MulAut.conj : adjointGroup TwistTag.E6.tag K →* MulAut _).comp
      (fixSubgroup (MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η')).subtype) _ hmemZ
  let φ : fixSubgroup (MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η') →* MulAut (graphFixedJ K) := res.comp ψ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hk : ψ c ∈ res.ker := hc
    have hk' : (ψ c : MulAut (adjointGroup TwistTag.E6.tag K)) ∈ zpowers η' :=
      hker ▸ ⟨ψ c, hk, rfl⟩
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hk'
    have hn' : (ψ c : MulAut (adjointGroup TwistTag.E6.tag K)) = 1 ∨
        (ψ c : MulAut (adjointGroup TwistTag.E6.tag K)) = η' := by
      rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
      · left
        rw [← hn, zpow_mul, zpow_two, hη'2, one_zpow]
      · right
        rw [← hn, zpow_add, zpow_mul, zpow_two, hη'2, one_zpow, one_mul, zpow_one]
    have hcc : (ψ c : MulAut (adjointGroup TwistTag.E6.tag K)) =
        MulAut.conj (c : adjointGroup TwistTag.E6.tag K) := rfl
    rcases hn' with h1 | h1
    · rw [hcc, ← map_one MulAut.conj] at h1
      exact Subtype.ext (hinj h1)
    · exact absurd ⟨(c : adjointGroup TwistTag.E6.tag K), by rw [← hcc, h1]⟩ hη'I
  have hφr : φ.range ≤ res.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨ψ x, rfl⟩
  have hcard1 : Nat.card (fixSubgroup (MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag K) * η')) ∣ Nat.card res.range := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
    exact card_dvd_of_le hφr
  have hbij : Nat.card res.range =
      Nat.card (centralizer ({(⟨_, htJ⟩ : graphFixedJ K)} : Set (graphFixedJ K))) *
        Nat.card (K ≃+* K) := by
    rw [← Nat.card_prod]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun p : centralizer ({(⟨_, htJ⟩ : graphFixedJ K)} : Set (graphFixedJ K)) × (K ≃+* K) =>
        (⟨MulAut.conj (p.1 : graphFixedJ K) * E6SecondGraphFull.embeddedFieldAut (RingHom.id K) p.2,
          (hrange _).2 ⟨p.1, mem_centralizer_singleton_iff.1 p.1.2, p.2, rfl⟩⟩ : res.range))
      ⟨?_, ?_⟩)).symm
    · rintro ⟨x, φ₁⟩ ⟨y, φ₂⟩ h
      obtain ⟨h1, h2⟩ := huniq x y φ₁ φ₂ (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext h1) h2
    · rintro ⟨α, hα⟩
      obtain ⟨x, hx, φ₁, rfl⟩ := (hrange α).1 hα
      exact ⟨(⟨x, mem_centralizer_singleton_iff.2 hx⟩, φ₁), rfl⟩
  have hJ : (Nat.card (graphFixedJ K)).factorization 2 = 24 * f := by
    obtain ⟨-, -, -, -, ⟨Ψ, -⟩, -⟩ := even_E6_pure_graph_fixed_group_exact_F4 K hK2
    rw [graphFixedJ, map_baseChangeGL_id, Nat.card_congr Ψ.toEquiv, factorization_card_adjointGroup hK,
      CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4, mul_comm]
  have hCJ : (Nat.card (centralizer ({(⟨_, htJ⟩ : graphFixedJ K)} :
      Set (graphFixedJ K)))).factorization 2 ≤ 24 * f := by
    have hd := card_dvd_of_le
      (le_top (a := centralizer ({(⟨_, htJ⟩ : graphFixedJ K)} : Set (graphFixedJ K))))
    rw [card_top] at hd
    have hJ0 : Nat.card (graphFixedJ K) ≠ 0 := Nat.card_pos.ne'
    rw [← hJ]
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hJ0).2 hd 2
  have hAut : Nat.card (K ≃+* K) = f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have hf0 : f ≠ 0 := by omega
  have hR0 : Nat.card res.range ≠ 0 := Nat.card_pos.ne'
  have h1 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hR0).2 hcard1 2
  rw [hbij, hAut, Nat.factorization_mul Nat.card_pos.ne' hf0, Finsupp.add_apply] at h1
  omega

theorem outerTwoPartBoundE6_of_fixBounds {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (hfix : OuterFixBoundsE6 K f) : OuterTwoPartBoundE6 K f := by
  intro α hα2 hαo
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  change MulAut (adjointGroup TwistTag.E6.tag K) at α
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  have hZ : center (adjointGroup TwistTag.E6.tag K) = ⊥ := center_adjointGroup_eq_bot_field _ K
  have hfin : Finite (adjointGroup TwistTag.E6.tag K) := by
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    infer_instance
  have key : ∀ β₀ : MulAut (adjointGroup TwistTag.E6.tag K),
      (∃ φ, φ * α * φ⁻¹ = β₀) →
      (Nat.card (fixSubgroup β₀)).factorization 2 ≤ 24 * f + f.factorization 2 →
      ¬ 2 ^ (26 * f) ∣ Nat.card (centralizer ({α} : Set (MulAut (adjointGroup TwistTag.E6.tag K)))) := by
    rintro β₀ ⟨φ, rfl⟩ hb hdvd
    rw [← card_centralizer_conj φ α] at hdvd
    have h1 := card_centralizer_dvd_card_eqLocus_mul_card_outer hZ (φ * α * φ⁻¹)
    have h2 := (ordinary_E_outer_order_Cartan_divisor TwistTag.E6.tag (Or.inl rfl) Nat.prime_two hf
      K hK 3 2 (Or.inl ⟨rfl, rfl, rfl⟩)).1
    have h3 : 2 ^ (26 * f) ∣ Nat.card (fixSubgroup (φ * α * φ⁻¹)) * (3 * 2 * f) :=
      hdvd.trans (h1.trans (Nat.mul_dvd_mul_left _ h2))
    have hF0 : Nat.card (fixSubgroup (φ * α * φ⁻¹)) ≠ 0 := Nat.card_pos.ne'
    have hf0 : f ≠ 0 := by omega
    have h6f : 3 * 2 * f ≠ 0 := by positivity
    have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (mul_ne_zero hF0 h6f)).1 h3
    rw [Nat.factorization_mul hF0 h6f, Finsupp.add_apply,
      Nat.factorization_mul (by norm_num : 3 * 2 ≠ 0) hf0, Finsupp.add_apply] at h4
    have h32 : (3 * 2 : ℕ).factorization 2 = 1 := by
      rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by decide)]
    rw [h32] at h4
    have hlt : f.factorization 2 < f := Nat.factorization_lt 2 hf0
    omega
  obtain ⟨hη, hξ, hσ, hγσ⟩ := hfix
  rcases outer_involution_cases_E6 hf K hK α hα hαo with
    ⟨η, hηdef, ⟨φ, hφ⟩ | ⟨ht, φ, hφ⟩⟩ | ⟨σ, hσ2, hσ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩
  · exact key η ⟨φ, hφ⟩ (hη η hηdef)
  · exact key _ ⟨φ, hφ⟩ (hξ η ht hηdef)
  · exact key _ ⟨φ, hφ⟩ (hσ σ hσ2 hσ1)
  · exact key _ ⟨φ, hφ⟩ (hγσ σ hσ2 hσ1)

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem forall_inner_E6 (hset : CFSG.EvenSmallLie.StandardSetting G L)
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ g : G, g⁻¹ * t * g ≠ t → g⁻¹ * t * g ∈ L ⊔ zpowers t →
      ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ := by
  refine forall_inner_E6_of_outer hset K hK e ht hKt (outerTwoPartBoundE6_of_fixBounds hf K hK
    ⟨fun η hη => ?_, fun η ht hη => factorization_card_fixSubgroup_secondGraph_E6 hf K hK η ht hη,
      fun σ hσ2 hσ1 => ?_, fun σ hσ2 hσ1 => ?_⟩)
  · rw [factorization_card_fixSubgroup_graph_E6 hf K hK η hη]
    omega
  · rw [factorization_card_fixSubgroup_field_E6 hf K hK σ hσ2 hσ1]
    omega
  · have := factorization_card_fixSubgroup_graphField_E6 hf K hK σ hσ2 hσ1
    omega

end Inner

end CFSG.SeitzReduction.E6Pilot
