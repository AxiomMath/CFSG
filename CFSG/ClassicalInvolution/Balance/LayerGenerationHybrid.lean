module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayers
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalAll
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPair
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairBridge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTripleFinal

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.Assembly.LowTwoRank

section Statement

@[expose] def LayerGenerationPairOr (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  LayerGenerationPairAt t n p e Fact.out ∨
    (t ≠ .G2 ∧ t ≠ .trialityD4 ∧ ModelFacts.CommutingFundamentalGeneration p t n e)

@[expose] def LayerGenerationHybrid (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), IsFundTag t → StatedLieAdmissible t n p e → p ≠ 2 →
    5 ≤ p ^ e → LayerGenerationPairOr p t n e

variable {p : ℕ} [Fact p.Prime]

theorem LayerGenerationHybrid.of_pair (h : LayerGenerationPair) : LayerGenerationHybrid p :=
  fun t n e hfund hadm hp2 h5 => Or.inl (h t n p e Fact.out hfund hadm hp2 h5)

theorem LayerGenerationHybrid.of_commuting (hB : ModelFacts.CommutingFundamentalFactsFive p)
    (hG2 : ∀ n e, StatedLieAdmissible .G2 n p e → 5 ≤ p ^ e →
      LayerGenerationPairAt .G2 n p e Fact.out)
    (hD4 : ∀ n e, StatedLieAdmissible .trialityD4 n p e → 5 ≤ p ^ e →
      LayerGenerationPairAt .trialityD4 n p e Fact.out) :
    LayerGenerationHybrid p := by
  intro t n e hfund hadm hp2 h5
  by_cases h1 : t = .G2
  · subst h1
    exact Or.inl (hG2 n e hadm h5)
  by_cases h2 : t = .trialityD4
  · subst h2
    exact Or.inl (hD4 n e hadm h5)
  exact Or.inr ⟨h1, h2, hB t n e hfund hadm h5⟩

end Statement

section Subgroup

variable {X : Type} [Group X] [Finite X]

theorem pair_generation_in_subgroup_at {t : StatedLieTag} {n p e : ℕ} {hp : p.Prime}
    (hmodel : LayerGenerationPairAt t n p e hp) {Y : Subgroup X}
    (ψ : (modelUniv t n p e hp).K →* X) (hψY : ψ.range ≤ Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K)
    (hcomp : CFSG.IsComponent (ψ.range.subgroupOf Y))
    {R₁ R₂ : Subgroup (modelUniv t n p e hp).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e hp).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups t (modelUniv t n p e hp).D) {z₁ z₂ : X}
    (hz₁ : z₁ ∈ R₁.map ψ) (hz₂ : z₂ ∈ R₂.map ψ) (hc₁ : ∀ y ∈ R₁.map ψ, z₁ * y = y * z₁)
    (hc₂ : ∀ y ∈ R₂.map ψ, z₂ * y = y * z₂) (hc₁₂ : ∀ y ∈ R₁.map ψ, z₂ * y = y * z₂)
    (hc₂₁ : ∀ y ∈ R₂.map ψ, z₁ * y = y * z₁) {F : Subgroup X} (hFY : F ≤ Y)
    (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFN : F ≤ Subgroup.normalizer (ψ.range : Set X))
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) {f₁ f₂ : X} (hf₁ : f₁ ∈ F)
    (hf₂ : f₂ ∈ F) (hf₁1 : f₁ ≠ 1) (hf₂1 : f₂ ≠ 1) (hf₁₂ : f₁ ≠ f₂)
    (hact₁ : ∀ y ∈ ψ.range, f₁ * y * f₁⁻¹ = z₁ * y * z₁⁻¹)
    (hact₂ : ∀ y ∈ ψ.range, f₂ * y * f₂⁻¹ = z₂ * y * z₂⁻¹) :
    ψ.range ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X) := by
  set ψ' : (modelUniv t n p e hp).K →* ↥Y := ψ.codRestrict Y (fun x => hψY ⟨x, rfl⟩) with hψ'
  have hrange : ψ'.range = ψ.range.subgroupOf Y := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hker' : ψ'.ker ≤ Subgroup.center (modelUniv t n p e hp).K := fun x hx =>
    hker (MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
  have hcomp' : CFSG.IsComponent ψ'.range := by
    rw [hrange]
    exact hcomp
  have hcomapmap : ∀ R : Subgroup (modelUniv t n p e hp).K,
      (R.map ψ).comap Y.subtype = R.map ψ' := by
    intro R
    ext y
    constructor
    · rintro ⟨r, hr, hry⟩
      exact ⟨r, hr, Subtype.ext hry⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hr, rfl⟩
  have hMY : ∀ R : Subgroup (modelUniv t n p e hp).K, R.map ψ ≤ Y := fun R =>
    (Subgroup.map_le_range _ _).trans hψY
  have hz₁Y : z₁ ∈ Y := hMY R₁ hz₁
  have hz₂Y : z₂ ∈ Y := hMY R₂ hz₂
  have hz₁' : (⟨z₁, hz₁Y⟩ : ↥Y) ∈ R₁.map ψ' := by
    rw [← hcomapmap]
    exact hz₁
  have hz₂' : (⟨z₂, hz₂Y⟩ : ↥Y) ∈ R₂.map ψ' := by
    rw [← hcomapmap]
    exact hz₂
  have hF'4 : Nat.card (F.subgroupOf Y) = 4 := by
    rw [← hF4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFY).toEquiv
  have hF'2 : ∀ f ∈ F.subgroupOf Y, f * f = 1 := fun f hf => Subtype.ext (hF2 f.1 hf)
  have hF'N : F.subgroupOf Y ≤ Subgroup.normalizer (ψ'.range : Set ↥Y) := fun f hf => by
    rw [hrange, Subgroup.mem_normalizer_iff]
    intro h
    exact Subgroup.mem_normalizer_iff.mp (hFN (show f.1 ∈ F from hf)) h.1
  have hfaith' : ∀ f ∈ F.subgroupOf Y, f ≠ 1 → ¬ ∀ x ∈ ψ'.range, f * x = x * f := by
    intro f hf hf1 hc
    refine hfaith f.1 (show f.1 ∈ F from hf) (fun h => hf1 (Subtype.ext h)) fun x hx => ?_
    have hx' : (⟨x, hψY hx⟩ : ↥Y) ∈ ψ'.range := by
      rw [hrange]
      exact hx
    exact congrArg Subtype.val (hc _ hx')
  have hψ'mem : ∀ y : ↥Y, y ∈ ψ'.range → y.1 ∈ ψ.range := fun y hy => by
    rw [hrange] at hy
    exact hy
  have hKG := hmodel ↥Y ψ' hker' hcomp' R₁ hR₁ R₂ hR₂ ⟨z₁, hz₁Y⟩ hz₁' ⟨z₂, hz₂Y⟩ hz₂'
    (fun y hy => Subtype.ext (hc₁ y.1 (by rw [← hcomapmap] at hy; exact hy)))
    (fun y hy => Subtype.ext (hc₂ y.1 (by rw [← hcomapmap] at hy; exact hy)))
    (fun y hy => Subtype.ext (hc₁₂ y.1 (by rw [← hcomapmap] at hy; exact hy)))
    (fun y hy => Subtype.ext (hc₂₁ y.1 (by rw [← hcomapmap] at hy; exact hy)))
    (F.subgroupOf Y) hF'4 hF'2 hF'N hfaith' ⟨f₁, hFY hf₁⟩ hf₁ ⟨f₂, hFY hf₂⟩ hf₂
    (fun h => hf₁1 (congrArg Subtype.val h)) (fun h => hf₂1 (congrArg Subtype.val h))
    (fun h => hf₁₂ (congrArg Subtype.val h))
    (fun y hy => Subtype.ext (hact₁ y.1 (hψ'mem y hy)))
    (fun y hy => Subtype.ext (hact₂ y.1 (hψ'mem y hy)))
  have hle : (⨆ f ∈ F.subgroupOf Y, ⨆ (_ : f ≠ 1), centralizerLayer f) ≤
      (⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X)).comap Y.subtype := by
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({f} : Set ↥Y) := Subgroup.map_subtype_le _ hx
    have hcomm' : x * f = f * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hf1' : (f : X) ≠ 1 := fun h => hf1 (Subtype.ext h)
    have hmem : (x : X) ∈ Y ⊓ Subgroup.centralizer ({f.1} : Set X) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm')⟩
    have hsub : (Y ⊓ Subgroup.centralizer ({f.1} : Set X)) ≤
        ⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X) :=
      le_iSup₂_of_le f.1 (show f.1 ∈ F from hf) (le_iSup_of_le hf1' le_rfl)
    exact hsub hmem
  intro x hx
  have hx' : (⟨x, hψY hx⟩ : ↥Y) ∈ ψ'.range := by
    rw [hrange]
    exact hx
  exact hle (hKG hx')

end Subgroup

section Layers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem LayerGenerationLie.of_hybrid (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationHybrid p)
    (hM : MemberFamily p f Ω A 𝒦) (hT : IndepTripleOn p f Ω A) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hF3 : NoComponentOverF3 p f Ω a) :
    LayerGenerationLie Ω A a := by
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
    have h5 : 5 ≤ p ^ D.exp j :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq j).imp id And.right) (hF3 D j)
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
        fun R hR => commutator_self_eq_of_le (ModelFacts.fundPerfect_core (D.tag j) (D.rank j) p
          (D.exp j) hp2 (D.isFundTag j) (D.admissible j) (by omega) R hR)
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

theorem componentLayersAt_of_hybrid_of_noF3 [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hM : MemberFamily p f Ω A 𝒦) (hT : IndepTripleOn p f Ω A)
    (hmodel : LayerGenerationHybrid p)
    (hF3 : ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f Ω a) :
    ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a := fun a ha ha1 =>
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponentBig L)
    (fun _ hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig hp2 h0 fundamentalWholeA1 hq hΩ
      hIH (not_subset_center_of_ne_one hnab ha1) (hF3 a ha ha1) hL)
    (LayerGenerationLie.of_hybrid hp2 h0 fundamentalWholeA1 hq hΩ hIH hmodel hM hT ha
      (not_subset_center_of_ne_one hnab ha1) (hF3 a ha ha1)).toBig

end Layers

section Generation

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {a : G} {𝒦 : Set (Subgroup G)}

theorem generation_of_hybrid (hmodel : LayerGenerationHybrid p) (hp2 : p ≠ 2)
    (hΩ : InClass p f Ω) (hM : MemberFamily p f Ω A 𝒦) (hT : IndepTripleOn p f Ω A)
    (ha : a ∈ A) (ha1 : a ≠ 1) (hAY : A ≤ centLayer Ω a) (Dsys : LocalLieSystemAt p f Ω a)
    (j : Fin Dsys.card) (h5 : 5 ≤ p ^ Dsys.exp j)
    (D : LieDecomposition (memberImages Ω a) (memberJoin Ω a)) (i : D.ι)
    (hj : D.Q i = (componentHom hΩ Dsys j).range) {F' : Subgroup G}
    (hF' : F' ∈ CFSG.Open.signalizerFunctorEk 2 2 A)
    (hfaith : ∀ x ∈ modOdd a F', x ≠ 1 → ¬ ∀ y ∈ D.Q i, x * y = y * x) :
    D.Q i ≤ ⨆ g ∈ modOdd a F', ⨆ (_ : g ≠ 1),
      memberJoin Ω a ⊓ Subgroup.centralizer ({g} : Set (OddQuot a)) := by
  have hF'A : F' ≤ A := hF'.1
  have hel := hT.isElemAbelian
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hel.2 x hx
  have hF'2 : ∀ x ∈ F', x * x = 1 := fun x hx => hA2 x (hF'A hx)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hel.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, ha⟩))
  have hF'4 : Nat.card F' = 4 := by
    rw [hF'.2]
    norm_num
  have hFb4 : Nat.card (modOdd a F') = 4 := by
    rw [card_modOdd_of_exponent_two (hF'A.trans hAC) hF'2, hF'4]
  have hFbJ : modOdd a F' ≤ memberJoin Ω a := modOdd_le_memberJoin (hF'A.trans hAY)
  have hFbN : modOdd a F' ≤
      Subgroup.normalizer ((D.Q i : Subgroup (OddQuot a)) : Set (OddQuot a)) :=
    hFbJ.trans (le_normalizer_of_normal_subgroupOf (D.le_join i) (D.normal_subgroupOf i))
  have hcompY : CFSG.IsComponent ((D.Q i).subgroupOf (memberJoin Ω a)) := by
    have : ((D.Q i).subgroupOf (memberJoin Ω a)).Normal := D.normal_subgroupOf i
    have hqs : CFSG.Open.IsQuasisimple ↥((D.Q i).subgroupOf (memberJoin Ω a)) :=
      Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe (D.le_join i))
        (D.quasisimple i)
    rw [CFSG.isComponent_iff_open]
    exact ⟨le_top, isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf, hqs⟩
  have hQY : (componentHom hΩ Dsys j).range ≤ memberJoin Ω a := hj ▸ D.le_join i
  rcases hmodel (Dsys.tag j) (Dsys.rank j) (Dsys.exp j) (Dsys.isFundTag j) (Dsys.admissible j)
    hp2 h5 with hA | ⟨hG2, hD4, hB⟩
  · obtain ⟨R₁, hR₁, R₂, hR₂, z₁, hz₁, z₂, hz₂, hc₁, hc₂, hc₁₂, hc₂₁, f₁, hf₁, f₂, hf₂, hf₁1,
      hf₂1, hf₁₂, hact₁, hact₂⟩ := exists_pair_frame_data hΩ hT ha ha1 Dsys j hF'A hF'4
        (by rw [← hj]; exact hfaith)
    rw [hj] at hFbN hfaith hcompY ⊢
    exact pair_generation_in_subgroup_at hA (componentHom hΩ Dsys j) hQY
      (componentHom_ker_le_center hΩ Dsys j) hcompY hR₁ hR₂ hz₁ hz₂ hc₁ hc₂ hc₁₂ hc₂₁ hFbJ hFb4
      (modOdd_sq_eq_one hA2 hF'A) hFbN hfaith hf₁ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂
  · have hsingle : FundamentalSingleClass (Dsys.tag j) (compModel Dsys j).D :=
      ModelFacts.fundamentalSingleClass (Dsys.tag j) (Dsys.rank j) p (Dsys.exp j) Fact.out
        (Dsys.isFundTag j) (Dsys.admissible j) hG2 hD4
    have hperf : ∀ R ∈ fundamentalSubgroups (Dsys.tag j) (compModel Dsys j).D, ⁅R, R⁆ = R :=
      fun R hR => commutator_self_eq_of_le (ModelFacts.fundPerfect_core (Dsys.tag j) (Dsys.rank j)
        p (Dsys.exp j) hp2 (Dsys.isFundTag j) (Dsys.admissible j) (by omega) R hR)
    exact le_iSup_centralizer_of_centralizedGeneratedAt
      (centralizedGeneratedAt_of_commutingFundamental hΩ hM ha ha1 Dsys j hsingle hperf hB hj
        (fun K hK => modOdd_le_or_commutes D i hK) ⟨hF'A, hF'4, hFbN, hfaith⟩)

theorem centralizerGenerationModOTwo_of_hybrid_of_noF3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationHybrid p)
    (hM : MemberFamily p f Ω A 𝒦) (hT : IndepTripleOn p f Ω A) (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hF3 : NoComponentOverF3 p f Ω a) :
    CentralizerGenerationModOTwo Ω A a := by
  classical
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (A : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAY : A ≤ centLayer Ω a := by
    rw [hM.generate, Subgroup.closure_le]
    rintro z ⟨K, hK, hz⟩
    obtain ⟨-, -, -, hKA⟩ := hM.involution K hK
    exact le_centLayer ⟨hM.subset hK, hcen hKA⟩ hz.mem
  obtain ⟨Dsys⟩ := hIH {a} hnc
  obtain ⟨D, hcompD, hbigD⟩ := lieDecomposition_localSystem_comp hp2 h0 hA1 hq hΩ Dsys
  have hD := hbigD (hF3 Dsys)
  refine centralizerGenerationModOTwo_of_components hΩ.conjInvariant hM.elem hM.card ha ha1 hAY D
    fun i F' hF' hfaith => ?_
  rcases hD i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | _
  · exfalso
    have hr1 : RankOneAt Ω a (D.Q i) := by
      refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
      obtain ⟨j, hj⟩ := D.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
      · exact Or.inr fun x hx y hy => D.commute j i hji x (hj hx) y hy
    have hF'A : F' ≤ A := hF'.1
    have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
      rw [← pow_two]
      exact hM.elem.2 x hx
    have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, ha⟩))
    have hcard : 1 < Nat.card (modOdd a F') := by
      rw [card_modOdd_of_exponent_two (hF'A.trans hAC) fun x hx => hA2 x (hF'A hx), hF'.2]
      norm_num
    have : Nontrivial (modOdd a F') := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨x, hx1⟩ := exists_ne (1 : modOdd a F')
    obtain ⟨k, hk, hkx⟩ := mem_modOdd_iff.mp x.2
    refine hfaith x x.2 (fun h => hx1 (Subtype.ext h)) fun y hy => ?_
    rw [← hkx]
    exact oddQuotMk_centralizes_of_memberFamily hM ha (Or.inr hr1) (hF'A hk) _ y hy
  · obtain ⟨j, hj⟩ := hcompD i
    have h5 : 5 ≤ p ^ Dsys.exp j :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((Dsys.exp_eq j).imp id And.right) (hF3 Dsys j)
    exact generation_of_hybrid hmodel hp2 hΩ hM hT ha ha1 hAY Dsys j h5 D i hj.symm hF' hfaith

end Generation

section BootTriple

variable {p f : ℕ} [Fact p.Prime]

theorem bootTriple_of_hybrid_final' (hmodel : LayerGenerationHybrid p)
    (hcover : p ≠ 2 → 5 ≤ p ^ f → FrameCoverage p f) (hexotic : ExoticLeviBlock p f)
    (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hT, hM⟩ := exists_indepTripleOn hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hF3' : ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f (CoreAssembly.conjClass K) a :=
    fun a ha ha1 => by
      by_cases h27 : p ^ f = 27
      · exact hF3 h27 G hnab K z hz hBelow hconn A hM a ha ha1
      · exact NoComponentOverF3.of_ne_27 a hq h27
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily_of_layers_exotic' hnab hp2
    hq hΩ (CoreAssembly.exists_single_class K) hIH (omegaConnected_of_deltaConnected hconn) hM
    (twoClassInvolutionsConj p) (hcover hp2 hq G hnab K z hz hBelow hconn A hM)
    (componentLayersAt_of_hybrid_of_noF3 hnab hp2 hq ModelFacts.modelClauseZero hΩ hIH hM hT
      hmodel hF3')
    (fun a ha hfa => by
      obtain ⟨K', -, hK'⟩ := hfa
      exact centralizerGenerationModOTwo_of_hybrid_of_noF3 hp2 hq
        ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hmodel hM hT ha
        (not_subset_center_of_ne_one hnab hK'.ne_one) (hF3' a ha hK'.ne_one))
    hexotic
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

end BootTriple

end CFSG.ClassicalInvolution.Balance.Bootstrap
