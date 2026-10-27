module

public import CFSG.ClassicalInvolution.Balance.Q27FuzzyModel
public import CFSG.ClassicalInvolution.Balance.Q27Layers
public import CFSG.ClassicalInvolution.Balance.Theorem5Fuzzy

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5 (FuzzyFrameOn MemberClass FuzzyFrameBalance)
open scoped commutatorElement MatrixGroups

section Pair

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem secToral_exists_pair_frame_data_members {A : Subgroup G} {S : Set G} (hs : SecData p f a Φ)
    (T : SecToral Φ a A S) (ha1 : a ≠ 1) (D : LocalLieSystemAt p f Φ a) (j : Fin D.card)
    {L : Subgroup (OddQuot a)} (hL : L = (secComponentHom hs.normalizes D j).range)
    (hdich : ∀ K ∈ centMembers Φ a, modOdd a K ≤ L ∨
      ∀ x ∈ modOdd a K, ∀ y ∈ L, x * y = y * x)
    {F₀ : Subgroup G} (hF : IsFaithfulFourGroupAt A a L F₀) :
    ∃ R₁ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
    ∃ R₂ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
    ∃ z₁ ∈ R₁.map (secComponentHom hs.normalizes D j),
    ∃ z₂ ∈ R₂.map (secComponentHom hs.normalizes D j),
      (∀ y ∈ R₁.map (secComponentHom hs.normalizes D j), z₁ * y = y * z₁) ∧
      (∀ y ∈ R₂.map (secComponentHom hs.normalizes D j), z₂ * y = y * z₂) ∧
      (∀ y ∈ R₁.map (secComponentHom hs.normalizes D j), z₂ * y = y * z₂) ∧
      (∀ y ∈ R₂.map (secComponentHom hs.normalizes D j), z₁ * y = y * z₁) ∧
      (∃ K₂ : Subgroup G, K₂ ≤ Subgroup.centralizer ({a} : Set G) ∧
        Nonempty (↥K₂ ⧸ classicalInvolutionOddCore ↥K₂ ≃* SL(2, GaloisField p f)) ∧
        modOdd a K₂ = R₂.map (secComponentHom hs.normalizes D j)) ∧
      ∃ f₁ ∈ modOdd a F₀, ∃ f₂ ∈ modOdd a F₀, f₁ ≠ 1 ∧ f₂ ≠ 1 ∧ f₁ ≠ f₂ ∧
        (∀ y ∈ (secComponentHom hs.normalizes D j).range, f₁ * y * f₁⁻¹ = z₁ * y * z₁⁻¹) ∧
        (∀ y ∈ (secComponentHom hs.normalizes D j).range, f₂ * y * f₂⁻¹ = z₂ * y * z₂⁻¹) := by
  classical
  obtain ⟨hF₀A, hF₀4, -, hfaith⟩ := hF
  have hAC : ∀ g ∈ A, g ∈ Subgroup.centralizer ({a} : Set G) := fun g hg => T.mem_centralizer hg
  set B : Subgroup G := A ⊓ ((Subgroup.centralizer (L : Set (OddQuot a))).comap
    (oddQuotMk a)).map (Subgroup.centralizer ({a} : Set G)).subtype with hB
  have hBmem : ∀ (g : G) (hg : g ∈ A), g ∈ B ↔
      ∀ y ∈ L, oddQuotMk a ⟨g, hAC g hg⟩ * y = y * oddQuotMk a ⟨g, hAC g hg⟩ := by
    intro g hg
    constructor
    · rintro ⟨-, ⟨c, hc, hcg⟩⟩ y hy
      have hcg' : c = ⟨g, hAC g hg⟩ := Subtype.ext hcg
      subst hcg'
      exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm
    · intro h
      exact ⟨hg, ⟨⟨g, hAC g hg⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => (h y hy).symm,
        rfl⟩⟩
  have haB : a ∈ B := (hBmem a T.mem).mpr fun y _ => oddQuotMk_central (hAC a T.mem) y
  have hne1 : ∀ (g : G) (hg : g ∈ A), g ≠ 1 → oddQuotMk a ⟨g, hAC g hg⟩ ≠ 1 :=
      fun g hg hg1 h => by
    have hsq : (⟨g, hAC g hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hAC g hg⟩ = 1 :=
      Subtype.ext (T.sq hg)
    exact hg1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  have hFB : ∀ f₀ ∈ F₀, f₀ ∈ B → f₀ = 1 := by
    intro f₀ hf₀ hfB
    by_contra hne
    have hf₀A := hF₀A hf₀
    exact hfaith _ (oddQuotMk_mem_modOdd hf₀ (hAC f₀ hf₀A)) (hne1 f₀ hf₀A hne)
      ((hBmem f₀ hf₀A).mp hfB)
  obtain ⟨x, hxS, y, hyS, hxB, hyB, hxyB, hrep⟩ :=
    exists_pair_in_subgroup (fun g hg => T.sq hg) (fun g hg h hh => T.comm hg hh) T.card T.subset
      T.generate T.mem haB ha1 hF₀A hF₀4 hFB
  have hxA : x ∈ A := T.subset hxS
  have hyA : y ∈ A := T.subset hyS
  obtain ⟨Kx, hKxΦ, hKxa, hxc, hKxcomm⟩ := T.member x hxS
  obtain ⟨Ky, hKyΦ, hKya, hyc, hKycomm⟩ := T.member y hyS
  have hinL : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) → ∀ z ∈ A,
      IsCentralInvolution K z → z ∉ B → modOdd a K ≤ L := by
    intro K hK hKa z hzA hz hzB
    rcases hdich K ⟨hK, hKa⟩ with h | h
    · exact h
    · exfalso
      apply hzB
      exact (hBmem z hzA).mpr fun y hy => h _ (oddQuotMk_mem_modOdd hz.mem (hAC z hzA)) y hy
  subst hL
  obtain ⟨Rx, hRx, hRxK⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hKxΦ, hKxa⟩
    (hinL Kx hKxΦ hKxa x hxA hxc hxB)
  obtain ⟨Ry, hRy, hRyK⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hKyΦ, hKya⟩
    (hinL Ky hKyΦ hKya y hyA hyc hyB)
  have hsqA : ∀ (g : G) (hg : g ∈ A),
      oddQuotMk a ⟨g, hAC g hg⟩ * oddQuotMk a ⟨g, hAC g hg⟩ = 1 := by
    intro g hg
    rw [← map_mul]
    have : (⟨g, hAC g hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hAC g hg⟩ = 1 :=
      Subtype.ext (T.sq hg)
    rw [this, map_one]
  refine ⟨Rx, hRx, Ry, hRy, oddQuotMk a ⟨x, hAC x hxA⟩, ?_, oddQuotMk a ⟨y, hAC y hyA⟩, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRxK]
    exact oddQuotMk_mem_modOdd hxc.mem _
  · rw [hRyK]
    exact oddQuotMk_mem_modOdd hyc.mem _
  · rw [hRxK]
    intro y' hy'
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
    rw [← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext (hxc.central _ hk))
  · rw [hRyK]
    intro y' hy'
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
    rw [← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext (hyc.central _ hk))
  · rw [hRxK]
    exact hKxcomm y (hAC y hyA) hyA
  · rw [hRyK]
    exact hKycomm x (hAC x hxA) hxA
  · obtain ⟨zy, hzy⟩ := hs.member Ky hKyΦ
    exact ⟨Ky, hKya, hzy.nonempty_equiv, hRyK.symm⟩
  ·
    have hact : ∀ (g : G) (hgA : g ∈ A) (zg : G) (hzgA : zg ∈ A), g * zg ∈ B →
        ∀ y' ∈ (secComponentHom hs.normalizes D j).range,
          oddQuotMk a ⟨g, hAC g hgA⟩ * y' * (oddQuotMk a ⟨g, hAC g hgA⟩)⁻¹ =
          oddQuotMk a ⟨zg, hAC zg hzgA⟩ * y' * (oddQuotMk a ⟨zg, hAC zg hzgA⟩)⁻¹ := by
      intro g hgA zg hzgA hgB y' hy'
      have hgsq := hsqA g hgA
      have hB' := (hBmem (g * zg) (A.mul_mem hgA hzgA)).mp hgB y' hy'
      have h3 : oddQuotMk a ⟨g * zg, hAC _ (A.mul_mem hgA hzgA)⟩ =
          oddQuotMk a ⟨g, hAC g hgA⟩ * oddQuotMk a ⟨zg, hAC zg hzgA⟩ := by
        rw [← map_mul]
        rfl
      rw [h3] at hB'
      set u := oddQuotMk a ⟨g, hAC g hgA⟩ with hu
      set w := oddQuotMk a ⟨zg, hAC zg hzgA⟩ with hw
      have hu' : u * w * y' * (u * w)⁻¹ = y' := by
        rw [hB']
        group
      have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hgsq
      calc u * y' * u⁻¹ = u * (u * w * y' * (u * w)⁻¹) * u⁻¹ := by rw [hu']
        _ = (u * u) * w * y' * w⁻¹ * (u⁻¹ * u⁻¹) := by group
        _ = w * y' * w⁻¹ := by
          rw [hgsq, hui, hgsq]
          group
    obtain ⟨f₁, hf₁F, hf₁1, hf₁B⟩ := hrep x (Or.inl rfl)
    obtain ⟨f₂, hf₂F, hf₂1, hf₂B⟩ := hrep y (Or.inr (Or.inl rfl))
    have hf₁A := hF₀A hf₁F
    have hf₂A := hF₀A hf₂F
    have hact₁ := hact f₁ hf₁A x hxA hf₁B
    have hact₂ := hact f₂ hf₂A y hyA hf₂B
    refine ⟨oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩, oddQuotMk_mem_modOdd hf₁F _,
      oddQuotMk a ⟨f₂, hAC f₂ hf₂A⟩, oddQuotMk_mem_modOdd hf₂F _, hne1 f₁ hf₁A hf₁1,
      hne1 f₂ hf₂A hf₂1, ?_, hact₁, hact₂⟩
    intro heq
    apply hxyB
    rw [hBmem _ (A.mul_mem hxA hyA)]
    intro y' hy'
    set z₁ := oddQuotMk a ⟨x, hAC x hxA⟩ with hz₁
    set z₂ := oddQuotMk a ⟨y, hAC y hyA⟩ with hz₂
    have hz₁sq : z₁ * z₁ = 1 := hsqA x hxA
    have hz₂sq : z₂ * z₂ = 1 := hsqA y hyA
    have e1 := hact₁ y' hy'
    have e2 := hact₂ y' hy'
    rw [heq] at e1
    have e3 : z₁ * y' * z₁⁻¹ = z₂ * y' * z₂⁻¹ := e1.symm.trans e2
    have hc12 : z₁ * z₂ = z₂ * z₁ := by
      rw [hz₁, hz₂, ← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (T.comm hxA hyA))
    have hz₂i : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂sq
    have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁sq
    have h3 : oddQuotMk a ⟨x * y, hAC _ (A.mul_mem hxA hyA)⟩ = z₁ * z₂ := by
      rw [hz₁, hz₂, ← map_mul]
      rfl
    rw [h3]
    have e4 : z₂ * (z₁ * y' * z₁) * z₂ = y' := by
      have e3' : z₁ * y' * z₁ = z₂ * y' * z₂ := by
        simpa only [hz₁i, hz₂i] using e3
      rw [e3']
      calc z₂ * (z₂ * y' * z₂) * z₂ = (z₂ * z₂) * y' * (z₂ * z₂) := by group
        _ = y' := by rw [hz₂sq]; group
    have e5 : (z₂ * z₁) * y' * (z₁ * z₂) = y' := by
      calc (z₂ * z₁) * y' * (z₁ * z₂) = z₂ * (z₁ * y' * z₁) * z₂ := by group
        _ = y' := e4
    have e6 : (z₂ * z₁) * y' = y' * (z₂ * z₁) := by
      calc (z₂ * z₁) * y' = (z₂ * z₁) * y' * (z₁ * z₂) * (z₁ * z₂)⁻¹ := by group
        _ = y' * (z₁ * z₂)⁻¹ := by rw [e5]
        _ = y' * (z₂ * z₁) := by rw [mul_inv_rev, hz₁i, hz₂i]
    rw [hc12]
    exact e6

end Pair

section Quasi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem isQuasisimple_modOdd_free (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} (hK : K ∈ Φ) :
    CFSG.Open.IsQuasisimple ↥(modOdd a K) := by
  have hKm : K ∈ centMembers Φ a := ⟨hK, hs.le K hK⟩
  set Y := centralizingLayer Φ {a} with hY
  have hKY : K ≤ Y := le_centralizingLayer hKm
  have hfam : modOddIn Y K ∈ localFamily Φ a := ⟨K.subgroupOf Y, ⟨K, hKm, hKY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental _ hfam
  have h1 : modOdd a K = R.map (secComponentHom hs.normalizes D i) := by
    rw [← map_sectionQuotientHom_modOddIn hs.normalizes hKm, hKR]
    exact Subgroup.map_map _ _ _
  obtain ⟨z, hz⟩ := hs.member K hK
  exact isQuasisimple_member_image hp2 hq (D.isFundTag i) (D.admissible i)
    (fieldCase_of_exp_eq hp2 hq (D.exp_eq i)) (secComponentHom hs.normalizes D i)
    (secComponentHom_ker_le_center hs.normalizes D i) hR (hs.le K hK) hz.nonempty_equiv h1

end Quasi

section Layers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem layerGenerationLie_sec_hybrid_free {A : Subgroup G} {S : Set G} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hBelow : CITBelowU p f (Nat.card G))
    (hs : SecData p f a Φ) (T : SecToral Φ a A S) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hmodel : LayerGenerationHybrid p) : LayerGenerationLie Φ A a := by
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  have hΦ : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) →
      IsInvolutionMember (modOdd a K) := fun K hK _ => by
    obtain ⟨z, hz⟩ := hs.member K hK
    exact isInvolutionMember_modOdd_of_isSectionMember hz hq
  unfold LayerGenerationLie LayerGenerationOn
  intro L hL hlie hjoin F₀ hF
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
  obtain ⟨D', hD'Q, -⟩ := hs.lieDecomposition_comp hp2 h0 fundamentalWholeA1 hq Dsys
  have : (memberJoin Φ a).Normal := memberJoin_normal_of_normalizes hs.normalizes
  have hL' : CFSG.Open.IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · obtain ⟨j, hj⟩ := hD'Q i
    have hQ : D'.Q i = (secComponentHom hs.normalizes Dsys j).range := hj.symm
    by_cases h3 : p ^ Dsys.exp j = 3
    · exfalso
      obtain ⟨R₁, hR₁, R₂, hR₂, z₁, hz₁, z₂, hz₂, hc₁, hc₂, hc₁₂, hc₂₁, hK₂, f₁, hf₁, f₂, hf₂,
        hf₁1, hf₂1, hf₁₂, hact₁, hact₂⟩ := secToral_exists_pair_frame_data_members hs T ha1 Dsys j
          hQ (fun K hK => modOdd_le_or_commutes D' i hK) hF
      rw [hQ] at hF
      obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
      have hexp : Dsys.tag j = .trialityD4 ∧ 3 * Dsys.exp j = f := by
        rcases Dsys.exp_eq j with h | h
        · exfalso
          rw [h] at h3
          omega
        · exact h
      exact false_of_member_pair_trialityD4 hexp.1 hp2 (Dsys.admissible j) hexp.2
        (secComponentHom hs.normalizes Dsys j)
        (secComponentHom_ker_le_center hs.normalizes Dsys j) hR₁ hR₂ hz₁ hz₂ hc₂ hc₂₁ hK₂
        (F := modOdd a F₀) (modOdd_sq_eq_one (fun x hx => T.sq hx) hF₀A) hfaith hf₁ hf₂ hf₁1
        hf₂1 hf₁₂ hact₁ hact₂
    · have h5 : 5 ≤ p ^ Dsys.exp j :=
        five_le_pow_of_ne_three Fact.out hp2 hq ((Dsys.exp_eq j).imp id And.right) h3
      rcases hmodel (Dsys.tag j) (Dsys.rank j) (Dsys.exp j) (Dsys.isFundTag j)
        (Dsys.admissible j) hp2 h5 with hA | ⟨hG2, hD4, hB⟩
      · obtain ⟨R₁, hR₁, R₂, hR₂, z₁, hz₁, z₂, hz₂, hc₁, hc₂, hc₁₂, hc₂₁, f₁, hf₁, f₂, hf₂, hf₁1,
          hf₂1, hf₁₂, hact₁, hact₂⟩ := T.exists_pair_frame_data hs ha1 Dsys j hQ
          (fun K hK => modOdd_le_or_commutes D' i hK) hF
        rw [hQ] at hF hL ⊢
        obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
        have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := fun g hg =>
          T.mem_centralizer (hF₀A hg)
        have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => T.sq (hF₀A hg)
        exact OddCentralizerFree.of_le_layers (hA (OddQuot a)
          (secComponentHom hs.normalizes Dsys j)
          (secComponentHom_ker_le_center hs.normalizes Dsys j) hL R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂
          hc₁ hc₂ hc₁₂ hc₂₁ (modOdd a F₀) (by rw [card_modOdd_of_exponent_two hFC hF2, h4])
          (modOdd_sq_eq_one (fun x hx => T.sq hx) hF₀A) hFn hfaith f₁ hf₁ f₂ hf₂ hf₁1 hf₂1 hf₁₂
          hact₁ hact₂)
      · have hsingle : FundamentalSingleClass (Dsys.tag j) (compModel Dsys j).D :=
          ModelFacts.fundamentalSingleClass (Dsys.tag j) (Dsys.rank j) p (Dsys.exp j) Fact.out
            (Dsys.isFundTag j) (Dsys.admissible j) hG2 hD4
        have hperf : ∀ R ∈ fundamentalSubgroups (Dsys.tag j) (compModel Dsys j).D, ⁅R, R⁆ = R :=
          fun R hR => commutator_self_eq_of_le (ModelFacts.fundPerfect_core (Dsys.tag j)
            (Dsys.rank j) p (Dsys.exp j) hp2 (Dsys.isFundTag j) (Dsys.admissible j) (by omega) R
            hR)
        exact oddCentralizerFree_of_centralizedGenerated_sec (fun x hx => T.sq hx) hΦ hL hlie hF
          (T.centralizedGeneratedAt hs ha1 Dsys j hsingle hperf hB hQ
            (fun K hK => modOdd_le_or_commutes D' i hK) hF)
  · exfalso
    exact not_commutes_self_of_isQuasisimple hL'.2.2 fun x hx y hy => hcomm x hx y (hjoin hy)

theorem componentLayersAt_sec_hybrid_free {A : Subgroup G} {S : Set G} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hBelow : CITBelowU p f (Nat.card G))
    (hs : SecData p f a Φ) (T : SecToral Φ a A S) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hmodel : LayerGenerationHybrid p) : ComponentLayersAt Φ A a :=
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponent L)
    (fun _ hL => hs.trichotomy hp2 h0 fundamentalWholeA1 hq hBelow hnc hL)
    (layerGenerationLie_sec_hybrid_free hp2 hq h0 hBelow hs T hnc hmodel)

end Layers

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {J₁ J₂ J₃ : Subgroup G}
  {z₁ z₂ z₃ : G}

theorem axisTriangle_rankThreeBalance_hybrid_free [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hBelow : CITBelowU p f (Nat.card G))
    (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) (hne₁₂ : z₁ ≠ z₂) (hne₁₃ : z₁ ≠ z₃)
    (hne₂₃ : z₂ ≠ z₃) (hind : z₁ * z₂ ≠ z₃) (hmodel : LayerGenerationHybrid p) :
    RankThreeBalance (triangleAxis z₁ z₂ z₃) := by
  have hcard := hT.card_axis hne₁₂ hne₁₃ hne₂₃ hind
  refine ⟨hT.isElemAbelian, hcard, hT.weakBalanced hnab hp2 hq h0 hA1 hBelow, ?_⟩
  refine twoBalancedWrt_of_secToral (S := {z₁, z₂, z₃}) hT.isElemAbelian fun a ha ha1 => ?_
  have hs := hT.secData ha
  have hnc := not_subset_center_of_ne_one hnab ha1
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
  have hqs : ∀ K ∈ triangleSecFamily J₁ J₂ J₃ a, CFSG.Open.IsQuasisimple ↥(modOdd a K) :=
    fun K hK => isQuasisimple_modOdd_free hs Dsys hp2 hq hK
  have T := hT.secToral ha hcard hqs
  exact ⟨_, T, componentLayersAt_sec_hybrid_free hp2 hq h0 hBelow hs T hnc hmodel⟩

theorem rankThreeBalance_of_fuzzyFrameOn_hybrid_free [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hBelow : CITBelowU p f (Nat.card G)) {Ω : Set (Subgroup G)} {A : Subgroup G}
    (hA : FuzzyFrameOn p f Ω A) (hmodel : LayerGenerationHybrid p) : RankThreeBalance A := by
  obtain ⟨J₁, J₂, J₃, z₁, z₂, z₃, h1, h2, h3, hT, hne12, hne13, hne23, hind, hax⟩ :=
    hA.exists_axisTriangle
  have hB := axisTriangle_rankThreeBalance_hybrid_free hnab hp2 hq ModelFacts.modelClauseZero
    fundamentalWholeA1 hBelow hT hne12 hne13 hne23 hind hmodel
  rwa [hax] at hB

theorem fuzzyFrameBalance_of_hybrid_free {𝒞 : MemberClass} (hmodel : LayerGenerationHybrid p) :
    FuzzyFrameBalance p f 𝒞 := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind A hA
  exact rankThreeBalance_of_fuzzyFrameOn_hybrid_free hnab hp2 hq hBelow hA hmodel

end Triangle

end CFSG.ClassicalInvolution.Balance.Q27
