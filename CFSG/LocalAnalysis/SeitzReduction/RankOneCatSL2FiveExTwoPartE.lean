module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

@[expose] def E6GraphTwoPartInput (p f k : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup TwistTag.E6.tag K)) (g : adjointGroup TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → Kˣ),
      (∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹) → orderOf α = 2 →
      2 ^ k ∣ Nat.card (fixedSubgroup α)

@[expose] def E7InnerTwoPartInput (p f k : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup .E7 K)) (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
      (∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) =
        (g : ModGL .E7 K) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ *
          (g : ModGL .E7 K)⁻¹) → orderOf α = 2 →
      2 ^ k ∣ Nat.card (fixedSubgroup α)

@[expose] def TrialityInnerTwoPartInput (p f k : ℕ) : Prop :=
  ∀ (J : Type) [Group J], LieModel J .trialityD4 0 p f → ∀ α : MulAut J, orderOf α = 2 →
    α ∈ (MulAut.conj : J →* MulAut J).range → 2 ^ k ∣ Nat.card (fixedSubgroup α)

@[expose] def TwistedE6InnerTwoPartInput (p f k : ℕ) : Prop :=
  ∀ (J : Type) [Group J], LieModel J .twistedE6 0 p f → ∀ α : MulAut J, orderOf α = 2 →
    α ∈ (MulAut.conj : J →* MulAut J).range → 2 ^ k ∣ Nat.card (fixedSubgroup α)

namespace FiveEx

theorem commutator_self_le {M : Type} [Group M] (H : Subgroup M) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun _ h₁ _ h₂ =>
    H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)

end FiveEx

section Proofs

open FiveEx in
theorem two_pow_six_dvd_card_fixed_E6_or_graph {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (β : MulAut (adjointGroup TwistTag.E6.tag K)) (hβ : orderOf β = 2) :
    2 ^ 6 ∣ Nat.card (fixedSubgroup β) ∨
      ∃ (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ),
        ∀ h : adjointGroup TwistTag.E6.tag K, (β h : ModGL TwistTag.E6.tag K) =
          (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
            diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹ := by
  have hf := one_le_of_card hK
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hKodd := odd_card hp hp2 hK
  have h1 : ∀ x : ModGL Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ2
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.isLt
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε with hε | hε
    · have h := two_pow_dvd_card_fixed_innerDiag (Or.inr (Or.inr (Or.inl rfl))) hKodd
        bE6_mul_cartan ⟨1, rfl⟩ (two_dvd_sub_one hKodd) (g := g) (a := a)
        (fun h => by rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]) hβ2
      exact Or.inl h
    · exact Or.inr ⟨g, a, fun h => (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)⟩
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    left
    rcases hε with hε | hε
    · exact two_pow_six_dvd_card_fixed_field (t := .E6) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hp
        hp2 he hKe σ hσc (g := g) (a := a)
        (fun h => by rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]) hβ2
    · obtain ⟨-, β', hβ', hβα⟩ :=
        exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
      obtain ⟨-, hconj⟩ := hβα g a
      obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj β (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl))
        ((sq β).symm.trans hβ2)
      have hβfix : (fixedSubgroup β').map (adjointGroup TwistTag.E6.tag K).subtype =
          twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
        ext y
        simp only [Subgroup.mem_map, twistedFixedGroup, Subgroup.mem_inf]
        constructor
        · rintro ⟨u, hu, rfl⟩
          refine ⟨u.2, ?_⟩
          change twistHom TwistTag.E6 K σ.toRingHom (u : ModGL TwistTag.E6.tag K) = u
          rw [twistHom_apply, ← hβ' u]
          exact congrArg Subtype.val hu
        · rintro ⟨hyG, hyσ⟩
          refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
          change (β' ⟨y, hyG⟩ : ModGL TwistTag.E6.tag K) = y
          rw [hβ']
          change twistHom TwistTag.E6 K σ.toRingHom y = y at hyσ
          rw [twistHom_apply] at hyσ
          exact hyσ
      let e₂ : ↥(fixedSubgroup β') ≃* ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) :=
        (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
          (MulEquiv.subgroupCongr hβfix)
      have hc : Nat.card (fixedSubgroup β) =
          Nat.card (twistedFixedGroup TwistTag.E6 K σ.toRingHom) :=
        Nat.card_congr (e₁.trans e₂).toEquiv
      rw [hc]
      have hL : LieModel (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ.toRingHom))
          .twistedE6 0 p (f / 2) :=
        Or.inr (Or.inl ⟨rfl, by decide, ⟨hp, he, rfl⟩, K, inferInstance, inferInstance, hKe,
          σ.toRingHom, hσc, ⟨MulEquiv.refl _⟩⟩)
      exact ((two_pow_six_dvd_card_of_lieModel (by decide) hp2 hL).trans
        (Subgroup.card_quotient_dvd_card _)).trans
          (Subgroup.card_dvd_of_le (FiveEx.commutator_self_le _))

open FiveEx in
theorem involutionTwoPart_E7 {K : Type} [Field K] [Finite K] {p f k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hk : k ≤ 6) (hinner : E7InnerTwoPartInput p f k) :
    InvolutionTwoPart (adjointGroup .E7 K) k := by
  intro β hβ
  have hf := one_le_of_card hK
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have h1 : ∀ x : ModGL Tag.E7 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ : ∀ ε : Fin (exactE Tag.E7), exactQ Tag.E7 K ε = 1 := fun _ => rfl
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ2
  by_cases hσ1 : σ = 1
  · subst hσ1
    exact hinner K hK β g a (fun h => by rw [hgaσ h, hQ, h1, mul_one, inv_one, mul_one]) hβ
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    exact (pow_dvd_pow 2 hk).trans (two_pow_six_dvd_card_fixed_field (t := .E7)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hp hp2 he hKe σ hσc (g := g) (a := a)
      (fun h => by rw [hgaσ h, hQ, mul_one, inv_one, mul_one]) hβ2)

theorem excTwoPartInput_E7_of_inner {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≤ 6)
    (hinner : E7InnerTwoPartInput p f k) : ExcTwoPartInput .E7 p f k :=
  excTwoPartInput_of_adjointGroup (τ := .E7) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ hK => involutionTwoPart_E7 hp hp2 hK hk hinner

theorem two_pow_six_dvd_card_fixed_trialityD4_outer {J : Type} [Group J] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : LieModel J .trialityD4 0 p f) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    2 ^ 6 ∣ Nat.card (fixedSubgroup α) := by
  have hadm := SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hm
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  set C := graphFixedRootGroup TwistTag.D4 M σ.toRingHom with hCdef
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hβo : β ∉ (MulAut.conj : C →* MulAut C).range := by
    change MulAut.congr e α ∉ ComponentClassification.OuterAutomorphisms.inner C
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨-, hex, ⟨Θ, hΘ, -, hker, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf M hM σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hex β
  have hΘβ : Θ β = δ := hΘ β g δ hgδ
  rcases hinv β hβ2 with h1 | ⟨⟨e', he'⟩, hδc⟩
  · exact absurd (hker ▸ (MonoidHom.mem_ker.mpr h1)) hβo
  have he1 : 1 ≤ e' := by omega
  have hδ : ∀ c, δ c = c ^ p ^ (3 * e') := fun c => by
    rw [← hΘβ, hδc, show 3 * f / 2 = 3 * e' by omega]
  have hr : IsPrimePow (p ^ e') := hp.isPrimePow.pow (by omega)
  have hro : Odd (p ^ e') := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hM3 : Nat.card M = (p ^ f) ^ 3 := hM
  have hM6 : Nat.card M = (p ^ e') ^ 6 := by
    rw [hM3, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hσ2 : ∀ c, σ c = c ^ ((p ^ e') ^ 2) := fun c => by
    rw [hσ, show f = e' * 2 by omega, pow_mul]
  have hδ3 : ∀ c, δ c = c ^ ((p ^ e') ^ 3) := fun c => by
    rw [hδ, ← pow_mul, mul_comm]
  have hα2 : (MulAut.conj g * fieldActor σ δ) ^ 2 = 1 := hgδ ▸ hβ2
  obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components hr hro M hM6 σ
    hσ2 δ hδ3 g hα2
  have hM6' : Nat.card M = p ^ (3 * e' * 2) := by
    rw [hM3, ← pow_mul]
    congr 1
    omega
  have hσ' : ∀ c, σ c = c ^ p ^ (e' * 2) := fun c => by
    rw [hσ, show f = e' * 2 by omega]
  obtain ⟨-, -, hk, hres, -, hJC, hfixJ, -, -, -⟩ :=
    RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hp he1
      (le_refl 2) (by norm_num : Nat.Coprime 2 3) M hM6' σ hσ' δ hδ
  have hc : MulAut.congr ψ β = fieldActor σ δ := by
    rw [show MulAut.congr ψ β = ψ * β * ψ⁻¹ from MulEquiv.ext fun _ => rfl, hgδ]
    exact hψ
  have hF : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      (trialityFieldImage σ δ).subgroupOf C := by
    change _ = (trialityFieldImage σ δ).comap C.subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  have hFc : fixedSubgroup (MulAut.congr ψ β) = (trialityFieldImage σ δ).subgroupOf C := by
    rw [hc, hF]
  let Ψ : fixedSubgroup α ≃* trialityFieldImage σ δ :=
    ((ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv e α).trans
      (ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv ψ β)).trans
      ((MulEquiv.subgroupCongr hFc).trans (Subgroup.subgroupOfEquivOfLe hJC))
  have hk' : Nat.card (fixSubfield δ) = (p ^ e') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ) c = c ^ ((p ^ e') ^ 2) :=
    fun c => Subtype.ext (by rw [hres c, hσ2, SubmonoidClass.coe_pow])
  let e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
  have hY := LieType.CurtisTits.lieModel_of_mulEquiv e₁
    (ComponentClassification.CatLeafProof.lieModel_graphFixedRootGroup_trialityD4_odd hp hp2 he1
      hk' (fixSubfieldRestrict σ δ) (Or.inr hσ₀))
  rw [Nat.card_congr Ψ.toEquiv]
  exact two_pow_six_dvd_card_of_lieModel (by decide) hp2 hY

end Proofs

end CFSG.SeitzReduction.RankOne
