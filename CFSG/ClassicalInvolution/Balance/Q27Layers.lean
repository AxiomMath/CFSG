module

public import CFSG.ClassicalInvolution.Balance.Q27PairData
public import CFSG.ClassicalInvolution.Balance.Q27ThreeD4Model
public import CFSG.ClassicalInvolution.Balance.LayerGenerationHybrid
public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.LieType.Steinberg.TwistedD4 (fixedField)
open scoped MatrixGroups

section Model

variable {p f : ℕ} [hp : Fact p.Prime]

theorem false_of_member_pair_trialityD4 {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    (ht : t = .trialityD4) {n e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p e)
    (hf : 3 * e = f) {G : Type} [Group G] [Finite G] {a : G}
    (ψ : (modelUniv t n p e hp.out).K →* OddQuot a)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp.out).K)
    {R₁ R₂ : Subgroup (modelUniv t n p e hp.out).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D)
    {z₁ z₂ : OddQuot a} (hz₁ : z₁ ∈ R₁.map ψ) (hz₂ : z₂ ∈ R₂.map ψ)
    (hc₂ : ∀ y ∈ R₂.map ψ, z₂ * y = y * z₂) (hc₂₁ : ∀ y ∈ R₂.map ψ, z₁ * y = y * z₁)
    (hK₂ : ∃ K₂ : Subgroup G, K₂ ≤ Subgroup.centralizer ({a} : Set G) ∧
      Nonempty (↥K₂ ⧸ classicalInvolutionOddCore ↥K₂ ≃* SL(2, GaloisField p f)) ∧
      modOdd a K₂ = R₂.map ψ)
    {F : Subgroup (OddQuot a)} (hF2 : ∀ g ∈ F, g * g = 1)
    (hfaith : ∀ g ∈ F, g ≠ 1 → ¬ ∀ x ∈ ψ.range, g * x = x * g) {f₁ f₂ : OddQuot a}
    (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) (hf₁1 : f₁ ≠ 1) (hf₂1 : f₂ ≠ 1) (hf₁₂ : f₁ ≠ f₂)
    (hact₁ : ∀ y ∈ ψ.range, f₁ * y * f₁⁻¹ = z₁ * y * z₁⁻¹)
    (hact₂ : ∀ y ∈ ψ.range, f₂ * y * f₂⁻¹ = z₂ * y * z₂⁻¹) : False := by
  subst ht
  obtain ⟨K₂, hK₂a, hK₂e, hK₂R⟩ := hK₂
  have he : 1 ≤ e := hadm.2.1
  have hperf₂ : ⁅R₂, R₂⁆ = R₂ := by
    rcases fundamental_trialityD4_perfect_or_long hadm R₂ hR₂ with h | ⟨ι, hι⟩
    · exact commutator_self_eq_of_le h
    · exfalso
      obtain ⟨ψ', hψ'⟩ := exists_surjective_of_modOdd hK₂a hK₂e (ψ.comp ι)
        (by rw [MonoidHom.range_comp, hι, hK₂R])
      have hle := Nat.card_le_card_of_surjective ψ' hψ'
      have hFix : Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) = p ^ e :=
        ModelFacts.card_fixedField_iterateFrobenius he
      have hGF : Nat.card (GaloisField p f) = p ^ f :=
        GaloisField.card p f (by omega)
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFix, hGF] at hle
      have h2 : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
      have hpf : p ^ f = (p ^ e) ^ 3 := by rw [← hf, pow_mul']
      rw [hpf] at hle
      generalize p ^ e = q at h2 hle
      have h3 : q * (q ^ 2 - 1) ≤ q * q ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have h4 : 2 ≤ (q ^ 3) ^ 2 - 1 := by
        have : 4 ≤ q ^ 2 := by nlinarith
        have : q ^ 2 ≤ (q ^ 3) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
        omega
      have h5 : q ^ 3 * 2 ≤ q ^ 3 * ((q ^ 3) ^ 2 - 1) := Nat.mul_le_mul_left _ h4
      have h6 : 0 < q ^ 3 := by positivity
      nlinarith
  exact false_of_commuting_pair_trialityD4 hp2 hadm ψ hker hR₁ hperf₂ hz₁ hz₂ hc₂ hc₂₁ hF2
    hfaith hf₁ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂

end Model

section Layers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem LayerGenerationLie.of_hybrid_free (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationHybrid p)
    (hM : MemberFamily p f Ω A 𝒦) (hT : IndepTripleOn p f Ω A) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) : LayerGenerationLie Ω A a := by
  intro L hL hlie hjoin F₀ hF
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  obtain ⟨D⟩ := hIH {a} hnc
  obtain ⟨D', hcomp, -⟩ := lieDecomposition_localSystem_comp hp2 h0 hA1 hq hΩ D
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : CFSG.Open.IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hT.isElemAbelian.2 x hx
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcommL
  · obtain ⟨j, hj⟩ := hcomp i
    have hQ : D'.Q i = (componentHom hΩ D j).range := hj.symm
    by_cases h3 : p ^ D.exp j = 3
    · exfalso
      rw [hQ] at hF
      obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
      have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
        intro g hg
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact comm_of_sq_eq_one hA2 (hF₀A hg) ha
      have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => hA2 g (hF₀A hg)
      obtain ⟨R₁, hR₁, R₂, hR₂, z₁, hz₁, z₂, hz₂, hc₁, hc₂, hc₁₂, hc₂₁, hK₂, f₁, hf₁, f₂, hf₂,
        hf₁1, hf₂1, hf₁₂, hact₁, hact₂⟩ := exists_pair_frame_data_members hΩ hT ha ha1 D j hF₀A
          h4 hfaith
      have hexp : D.tag j = .trialityD4 ∧ 3 * D.exp j = f := by
        rcases D.exp_eq j with h | h
        · exfalso
          rw [h] at h3
          omega
        · exact h
      exact false_of_member_pair_trialityD4 hexp.1 hp2 (D.admissible j) hexp.2 (componentHom hΩ D j)
        (componentHom_ker_le_center hΩ D j) hR₁ hR₂ hz₁ hz₂ hc₂ hc₂₁ hK₂
        (F := modOdd a F₀) (modOdd_sq_eq_one hA2 hF₀A) hfaith hf₁ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂
    · have h5 : 5 ≤ p ^ D.exp j :=
        five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq j).imp id And.right) h3
      rcases hmodel (D.tag j) (D.rank j) (D.exp j) (D.isFundTag j) (D.admissible j) hp2 h5 with
        hA | ⟨hG2, hD4, hB⟩
      · rw [hQ] at hF hL ⊢
        obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
        obtain ⟨R₁, hR₁, R₂, hR₂, z₁, hz₁, z₂, hz₂, hc₁, hc₂, hc₁₂, hc₂₁, f₁, hf₁, f₂, hf₂, hf₁1,
          hf₂1, hf₁₂, hact₁, hact₂⟩ := exists_pair_frame_data hΩ hT ha ha1 D j hF₀A h4 hfaith
        have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
          intro g hg
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact comm_of_sq_eq_one hA2 (hF₀A hg) ha
        have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => hA2 g (hF₀A hg)
        exact OddCentralizerFree.of_le_layers (hA (OddQuot a) (componentHom hΩ D j)
          (componentHom_ker_le_center hΩ D j) hL R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂ hc₁ hc₂ hc₁₂ hc₂₁
          (modOdd a F₀) (by rw [card_modOdd_of_exponent_two hFC hF2, h4])
          (modOdd_sq_eq_one hA2 hF₀A) hFn hfaith f₁ hf₁ f₂ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂)
      · have hsingle : FundamentalSingleClass (D.tag j) (compModel D j).D :=
          ModelFacts.fundamentalSingleClass (D.tag j) (D.rank j) p (D.exp j) Fact.out
            (D.isFundTag j) (D.admissible j) hG2 hD4
        have hperf : ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, ⁅R, R⁆ = R :=
          fun R hR => commutator_self_eq_of_le (ModelFacts.fundPerfect_core (D.tag j) (D.rank j)
            p (D.exp j) hp2 (D.isFundTag j) (D.admissible j) (by omega) R hR)
        exact hF.oddCentralizerFree_of_centralizedGenerated hA2
          (InClass.isInvolutionMember hΩ hq) hL hlie
          (centralizedGeneratedAt_of_commutingFundamental hΩ hM ha ha1 D j hsingle hperf hB hQ
            (fun K hK => modOdd_le_or_commutes D' i hK) hF)
  · exfalso
    have hcommL' : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy => hcommL x hx y (hjoin hy)
    have hq2 := hL'.2.2
    have : Group.IsPerfect ↥L := ⟨hq2.1⟩
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq2.2
    have : Nontrivial ↥L :=
      (QuotientGroup.mk_surjective :
        Function.Surjective (QuotientGroup.mk : ↥L → ↥L ⧸ Subgroup.center ↥L)).nontrivial
    exact Group.IsPerfect.not_isMulCommutative ↥L
      ⟨⟨fun x y => Subtype.ext (hcommL' x x.2 y y.2)⟩⟩

theorem componentLayersAt_of_hybrid_free [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hM : MemberFamily p f Ω A 𝒦) (hT : IndepTripleOn p f Ω A)
    (hmodel : LayerGenerationHybrid p) : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a :=
  fun _ ha ha1 =>
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponent L)
    (fun _ hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponent_le_join hp2 h0
      fundamentalWholeA1 hΩ hIH (not_subset_center_of_ne_one hnab ha1) hL)
    (LayerGenerationLie.of_hybrid_free hp2 h0 fundamentalWholeA1 hq hΩ hIH hmodel hM hT ha
      (not_subset_center_of_ne_one hnab ha1))

end Layers

section Triangle

variable {p f : ℕ} [Fact p.Prime]

theorem triangleLayers_of_hybrid_free (hmodel : LayerGenerationHybrid p) :
    Theorem5.TriangleLayers p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  exact componentLayersAt_of_hybrid_free hnab hp2 hq ModelFacts.modelClauseZero hΩ
    (localLieSystems_of_citBelowU hΩ hBelow) (Theorem5.memberFamily_of_indepTripleOn hp2 hf hA) hA
    hmodel

theorem bootTriple_of_hybrid_noF3 (hmodel : LayerGenerationHybrid p)
    (htri : Theorem5.ConnectedTrianglesExist p f)
    (hcov9 : p ^ f = 9 → Theorem5.ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    CoreAssembly.BootTriple p f :=
  Theorem5.bootTriple_of_triangleLayers_noCover (triangleLayers_of_hybrid_free hmodel) htri hcov9
    hexotic

end Triangle

end CFSG.ClassicalInvolution.Balance.Q27
