module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationSimple
import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusModels
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.Balance.BootstrapGeneration

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Statement

variable {X : Type*} [Group X]

@[expose] def frameGroup (𝓜 : Set (Subgroup X)) : Subgroup X :=
  Subgroup.closure {z | ∃ M ∈ 𝓜, z ∈ M ∧ z * z = 1 ∧ z ≠ 1 ∧ ∀ s ∈ M, s * z = z * s}

theorem frameGroup_le {𝓜 : Set (Subgroup X)} {L : Subgroup X} (h : ∀ M ∈ 𝓜, M ≤ L) :
    frameGroup 𝓜 ≤ L := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z ⟨M, hM, hzM, -⟩
  exact h M hM hzM

end Statement

@[expose] def LayerGenerationTriple : Prop :=
  ∀ (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime), IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → CFSG.IsComponent ψ.range →
      ∀ 𝓜 : Set (Subgroup X),
        (∀ M ∈ 𝓜, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, M = R.map ψ) →
        (∀ M ∈ 𝓜, ∀ M' ∈ 𝓜, M ≠ M' → ∀ x ∈ M, ∀ y ∈ M', x * y = y * x) →
        ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
          F ≤ Subgroup.normalizer (ψ.range : Set X) →
          (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
          (∀ f ∈ F, ∃ x ∈ frameGroup 𝓜, ∀ y ∈ ψ.range, f * y * f⁻¹ = x * y * x⁻¹) →
            ψ.range ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f

theorem layerGenerationTriple_of_model (h : LayerGenerationModel) : LayerGenerationTriple := by
  intro t n p e hp hfund hadm hp2 h5 X _ _ ψ hker hcomp 𝓜 h𝓜 _ F h4 h2 hN hf hact
  by_cases hsl : t = .PSL ∧ n = 2
  · exfalso
    obtain ⟨f₀, hf₀, hf₀1⟩ : ∃ f₀ ∈ F, f₀ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      rw [(Subgroup.eq_bot_iff_forall F).2 hcon, Subgroup.card_bot] at h4
      omega
    obtain ⟨x, hx, hxy⟩ := hact f₀ hf₀
    have hcent : ∀ y ∈ ψ.range, x * y = y * x := by
      refine Subgroup.closure_induction (p := fun x _ => ∀ y ∈ ψ.range, x * y = y * x)
        ?_ ?_ ?_ ?_ hx
      · rintro z ⟨M, hM, hzM, -, -, hzc⟩ y hy
        obtain ⟨R, hR, rfl⟩ := h𝓜 M hM
        have hRtop := fundamentalWholeA1 t n p e hp hfund hadm hsl R hR
        have hy' : y ∈ R.map ψ := by
          rw [hRtop, Subgroup.map_top]
          exact hy
        exact (hzc y hy').symm
      · intro y _
        simp
      · intro a b _ _ ha hb y hy
        rw [mul_assoc, hb y hy, ← mul_assoc, ha y hy, mul_assoc]
      · intro a _ ha y hy
        exact (Commute.inv_left (show Commute a y from ha y hy)).eq
    refine hf f₀ hf₀ hf₀1 fun y hy => ?_
    have h1 : f₀ * y * f₀⁻¹ = y := by
      rw [hxy y hy, hcent y hy, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hK := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n p e hp hfund hadm
  have hn : t = .PSL → 3 ≤ n := fun ht => by
    have h2n : 2 ≤ n := by
      subst ht
      exact hadm.2.2.1
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · exact absurd ⟨ht, by omega⟩ hsl
    · exact h3
  have hLq : CFSG.Open.IsQuasisimple ↥ψ.range := ((CFSG.isComponent_iff_open _).mp hcomp).2.2
  have hψ1 : ∃ x, ψ.rangeRestrict x ≠ 1 := by
    have : Nontrivial (↥ψ.range ⧸ Subgroup.center ↥ψ.range) := hLq.2.toNontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥ψ.range ⧸ Subgroup.center ↥ψ.range)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := ψ.rangeRestrict_surjective u
    refine ⟨x, fun h1 => hy ?_⟩
    rw [h1]
    rfl
  have hbig : IsOddLieComponentBig ψ.range :=
    isOddLieComponentBig_of_surjective hK.1 ψ.rangeRestrict ψ.rangeRestrict_surjective hψ1 hp2 h5 hn
      (isFundTag_mem_tags hfund) hK.2
  exact h X ψ.range hcomp hbig F h4 h2 hN hf

section Abstract

variable {X : Type} [Group X]

theorem exists_action_of_generators {L T : Subgroup X} (hTL : T ≤ L) {Z : Set X}
    (hZ : ∀ z ∈ Z, (∀ y ∈ L, z * y = y * z) ∨ z ∈ T) {g : X} (hg : g ∈ Subgroup.closure Z) :
    ∃ x ∈ T, ∀ y ∈ L, g * y * g⁻¹ = x * y * x⁻¹ := by
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
    rcases hZ z hz with hc | hzT
    · refine ⟨1, Subgroup.one_mem _, fun y hy => ?_⟩
      rw [hc y hy, mul_assoc, mul_inv_cancel, mul_one]
      simp
    · exact ⟨z, hzT, fun y _ => rfl⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun y _ => by simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨x₁, hx₁, h₁⟩ := iha
    obtain ⟨x₂, hx₂, h₂⟩ := ihb
    refine ⟨x₁ * x₂, Subgroup.mul_mem _ hx₁ hx₂, fun y hy => ?_⟩
    have hx₂L : x₂ ∈ L := hTL hx₂
    have hy' : x₂ * y * x₂⁻¹ ∈ L := L.mul_mem (L.mul_mem hx₂L hy) (L.inv_mem hx₂L)
    calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = a * (x₂ * y * x₂⁻¹) * a⁻¹ := by rw [h₂ y hy]
      _ = x₁ * (x₂ * y * x₂⁻¹) * x₁⁻¹ := h₁ _ hy'
      _ = x₁ * x₂ * y * (x₁ * x₂)⁻¹ := by group
  | inv a _ iha =>
    obtain ⟨x, hx, h⟩ := iha
    refine ⟨x⁻¹, Subgroup.inv_mem _ hx, fun y hy => ?_⟩
    have hxL : x ∈ L := hTL hx
    have hy' : x⁻¹ * y * x ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hxL) hy) hxL
    have h3 := h _ hy'
    have h4 : a * (x⁻¹ * y * x) * a⁻¹ = y := by
      rw [h3]
      group
    calc a⁻¹ * y * a⁻¹⁻¹ = a⁻¹ * (a * (x⁻¹ * y * x) * a⁻¹) * a := by
          rw [h4]
          group
      _ = x⁻¹ * y * x⁻¹⁻¹ := by group

end Abstract

section Triple

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def IndepTripleOn (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Prop :=
  ∃ (K : Fin 3 → Subgroup G) (z : Fin 3 → G),
    (∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i)) ∧
    (∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) ∧
    A = Subgroup.closure (Set.range z) ∧ CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 8

variable {Ω : Set (Subgroup G)}

theorem triple_centralizes {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) (m : Fin 3) :
    K m ≤ Subgroup.centralizer ((Subgroup.closure (Set.range z) : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hsub : Set.range z ⊆ ((Subgroup.centralizer ({k} : Set G) : Subgroup G) : Set G) := by
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    by_cases hmj : m = j
    · subst hmj
      exact (hK m).2.isCentralInvolution.central k hk
    · exact (hcomm m j hmj k hk (z j) (hK j).2.isCentralInvolution.mem).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.closure_le _).mpr hsub hx)

theorem modOdd_commute {a : G} {H₁ H₂ : Subgroup G} (h : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x)
    {x y : OddQuot a} (hx : x ∈ modOdd a H₁) (hy : y ∈ modOdd a H₂) : x * y = y * x := by
  obtain ⟨k₁, hk₁, rfl⟩ := mem_modOdd_iff.mp hx
  obtain ⟨k₂, hk₂, rfl⟩ := mem_modOdd_iff.mp hy
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h _ hk₁ _ hk₂)

end Triple

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem exists_fundamental_of_mem_memberImages (hΩ : InClass p f Ω) {a : G}
    (D : LocalLieSystemAt p f Ω a) {M : Subgroup (OddQuot a)} (hM : M ∈ memberImages Ω a) :
    ∃ (j : Fin D.card) (R : Subgroup (compModel D j).K),
      R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D ∧
        M = R.map (componentHom hΩ D j) := by
  have hΨ : Subgroup.map (layerQuotientHom hΩ.conjInvariant a) ''
      oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) (centralizingLayer Ω {a})) =
      memberImages Ω a := map_layerQuotientHom_family hΩ.conjInvariant
  rw [← hΨ] at hM
  obtain ⟨L', hL', rfl⟩ := hM
  obtain ⟨j, R, hR, rfl⟩ := D.fundamental L' hL'
  exact ⟨j, R, hR, Subgroup.map_map R (layerQuotientHom hΩ.conjInvariant a) (D.hom j)⟩

theorem exists_frame_data (hΩ : InClass p f Ω) (hT : IndepTripleOn p f Ω A) {a : G} (ha : a ∈ A)
    (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) :
    ∃ 𝓜 : Set (Subgroup (OddQuot a)),
      (∀ M ∈ 𝓜, ∃ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
        M = R.map (componentHom hΩ D j)) ∧
      (∀ M ∈ 𝓜, ∀ M' ∈ 𝓜, M ≠ M' → ∀ x ∈ M, ∀ y ∈ M', x * y = y * x) ∧
      ∀ k : ↥(Subgroup.centralizer ({a} : Set G)), (k : G) ∈ A →
        ∃ x ∈ frameGroup 𝓜, ∀ y ∈ (componentHom hΩ D j).range,
          oddQuotMk a k * y * (oddQuotMk a k)⁻¹ = x * y * x⁻¹ := by
  classical
  obtain ⟨K, z, hK, hcomm, rfl, hel, -⟩ := hT
  have hKA := triple_centralizes (p := p) (f := f) hK hcomm
  have hAcomm : ∀ {x y : G}, x ∈ Subgroup.closure (Set.range z) →
      y ∈ Subgroup.closure (Set.range z) → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hx⟩ : Subgroup.closure (Set.range z)) ⟨_, hy⟩)
  have hz2 : ∀ m, z m * z m = 1 := fun m => by
    have := pow_orderOf_eq_one (z m)
    rwa [(hK m).2.orderOf_eq_two, pow_two] at this
  have hzC : ∀ m, z m ∈ Subgroup.centralizer ({a} : Set G) := fun m =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hAcomm (Subgroup.subset_closure ⟨m, rfl⟩) ha)
  have hclo : Subgroup.closure (Set.range z) ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨m, rfl⟩; exact hzC m)
  have hKC : ∀ m, K m ≤ Subgroup.centralizer ({a} : Set G) := fun m =>
    (hKA m).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hKb : ∀ m, modOdd a (K m) ∈ memberImages Ω a := fun m => ⟨K m, ⟨(hK m).1, hKC m⟩, rfl⟩
  have hzb2 : ∀ m, oddQuotMk a ⟨z m, hzC m⟩ * oddQuotMk a ⟨z m, hzC m⟩ = 1 := by
    intro m
    rw [← map_mul]
    have : (⟨z m, hzC m⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z m, hzC m⟩ = 1 :=
      Subtype.ext (hz2 m)
    rw [this, map_one]
  have hAZ : ∀ g : G, g ∈ Subgroup.closure (Set.range z) →
      ∀ hgC : g ∈ Subgroup.centralizer ({a} : Set G), oddQuotMk a ⟨g, hgC⟩ ∈
        Subgroup.closure (Set.range fun m => oddQuotMk a ⟨z m, hzC m⟩) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem w hw =>
      intro hwC
      obtain ⟨m, rfl⟩ := hw
      exact Subgroup.subset_closure ⟨m, rfl⟩
    | one =>
      intro hgC
      have : (⟨1, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul g₁ g₂ h₁ h₂ ih₁ ih₂ =>
      intro hgC
      have : (⟨g₁ * g₂, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) =
          ⟨g₁, hclo h₁⟩ * ⟨g₂, hclo h₂⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ (ih₁ (hclo h₁)) (ih₂ (hclo h₂))
    | inv g₁ h₁ ih₁ =>
      intro hgC
      have : (⟨g₁⁻¹, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = ⟨g₁, hclo h₁⟩⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ (ih₁ (hclo h₁))
  refine ⟨{M | (∃ m, M = modOdd a (K m)) ∧ ∃ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
    M = R.map (componentHom hΩ D j)}, fun M hM => hM.2, ?_, ?_⟩
  · rintro M ⟨⟨m, rfl⟩, -⟩ M' ⟨⟨m', rfl⟩, -⟩ hne x hx y hy
    have hmm : m ≠ m' := fun h => hne (by rw [h])
    exact modOdd_commute (hcomm m m' hmm) hx hy
  · intro k hk
    refine exists_action_of_generators (L := (componentHom hΩ D j).range) ?_ ?_
      (hAZ k.1 hk k.2)
    · refine frameGroup_le fun M hM => ?_
      obtain ⟨R, -, rfl⟩ := hM.2
      exact Subgroup.map_le_range _ _
    · rintro w ⟨m, hm⟩
      have hwm : w = oddQuotMk a ⟨z m, hzC m⟩ := hm.symm
      subst hwm
      by_cases hcase : ∃ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
          modOdd a (K m) = R.map (componentHom hΩ D j)
      · by_cases hz1 : oddQuotMk a ⟨z m, hzC m⟩ = 1
        · left
          intro y _
          rw [hz1, one_mul, mul_one]
        · right
          refine Subgroup.subset_closure ⟨modOdd a (K m), ⟨⟨m, rfl⟩, hcase⟩,
            oddQuotMk_mem_modOdd (hK m).2.mem (hzC m), hzb2 m, hz1, ?_⟩
          intro s hs
          obtain ⟨k', hk', rfl⟩ := mem_modOdd_iff.mp hs
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext ((hK m).2.isCentralInvolution.central (k' : G) hk').symm
      · left
        obtain ⟨j', R, hR, hKR⟩ := exists_fundamental_of_mem_memberImages hΩ D (hKb m)
        have hjj : j' ≠ j := by
          rintro rfl
          exact hcase ⟨R, hR, hKR⟩
        intro y hy
        obtain ⟨y₀, rfl⟩ := hy
        have hzK : oddQuotMk a ⟨z m, hzC m⟩ ∈ modOdd a (K m) :=
          oddQuotMk_mem_modOdd (hK m).2.mem (hzC m)
        rw [hKR] at hzK
        obtain ⟨r, -, hrz⟩ := hzK
        rw [← hrz]
        have h1 := map_mul (layerQuotientHom hΩ.conjInvariant a) (D.hom j' r) (D.hom j y₀)
        have h2 := map_mul (layerQuotientHom hΩ.conjInvariant a) (D.hom j y₀) (D.hom j' r)
        have h3 := congrArg (layerQuotientHom hΩ.conjInvariant a) (D.commute j' j hjj r y₀)
        exact h1.symm.trans (h3.trans h2)

end Frame

section Layers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

omit [Finite G] in
theorem IndepTripleOn.isElemAbelian (hT : IndepTripleOn p f Ω A) : CFSG.Open.IsElemAbelian 2 A := by
  obtain ⟨-, -, -, -, -, h, -⟩ := hT
  exact h

theorem LayerGenerationLie.of_triple (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationTriple) (hT : IndepTripleOn p f Ω A)
    {a : G} (ha : a ∈ A) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hF3 : NoComponentOverF3 p f Ω a) : LayerGenerationLie Ω A a := by
  intro L hL _ hjoin F₀ hF
  obtain ⟨D⟩ := hIH {a} hnc
  obtain ⟨D', hcomp, -⟩ := lieDecomposition_localSystem_comp hp2 h0 hA1 hq hΩ D
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : CFSG.Open.IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcommL
  · obtain ⟨j, hj⟩ := hcomp i
    have hQ : D'.Q i = (componentHom hΩ D j).range := hj.symm
    rw [hQ] at hF hL ⊢
    obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
    obtain ⟨𝓜, h𝓜f, h𝓜c, hact⟩ := exists_frame_data hΩ hT ha D j
    have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
      rw [← pow_two]
      exact hT.isElemAbelian.2 x hx
    have h5 : 5 ≤ p ^ D.exp j :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq j).imp id And.right) (hF3 D j)
    have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_sq_eq_one hA2 (hF₀A hg) ha
    have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => hA2 g (hF₀A hg)
    exact OddCentralizerFree.of_le_layers (hmodel (D.tag j) (D.rank j) p (D.exp j) Fact.out
      (D.isFundTag j) (D.admissible j) hp2 h5 (OddQuot a) (componentHom hΩ D j)
      (componentHom_ker_le_center hΩ D j) hL 𝓜 h𝓜f h𝓜c (modOdd a F₀)
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) (modOdd_sq_eq_one hA2 hF₀A) hFn hfaith
      (by
        rintro _ ⟨k, hk, rfl⟩
        exact hact k (hF₀A hk)))
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

theorem componentLayersAt_of_triple_of_noF3 [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hT : IndepTripleOn p f Ω A) (hmodel : LayerGenerationTriple)
    (hF3 : ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f Ω a) :
    ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a := fun a ha ha1 =>
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponentBig L)
    (fun _ hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig hp2 h0 fundamentalWholeA1 hq hΩ
      hIH (not_subset_center_of_ne_one hnab ha1) (hF3 a ha ha1) hL)
    (LayerGenerationLie.of_triple hp2 h0 fundamentalWholeA1 hq hΩ hIH hmodel hT ha
      (not_subset_center_of_ne_one hnab ha1) (hF3 a ha ha1)).toBig

end Layers

section Subgroup

variable {X : Type} [Group X] [Finite X]

theorem triple_generation_in_subgroup (hmodel : LayerGenerationTriple) {t : StatedLieTag}
    {n p e : ℕ} {hp : p.Prime} (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) {Y : Subgroup X} (ψ : (modelUniv t n p e hp).K →* X)
    (hψY : ψ.range ≤ Y) (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K)
    (hcomp : CFSG.IsComponent (ψ.range.subgroupOf Y)) {𝓜 : Set (Subgroup X)}
    (h𝓜 : ∀ M ∈ 𝓜, ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, M = R.map ψ)
    (hcomm : ∀ M ∈ 𝓜, ∀ M' ∈ 𝓜, M ≠ M' → ∀ x ∈ M, ∀ y ∈ M', x * y = y * x)
    {F : Subgroup X} (hFY : F ≤ Y) (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFN : F ≤ Subgroup.normalizer (ψ.range : Set X))
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (hact : ∀ f ∈ F, ∃ x ∈ frameGroup 𝓜, ∀ y ∈ ψ.range, f * y * f⁻¹ = x * y * x⁻¹) :
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
  have hMle : ∀ M ∈ 𝓜, M ≤ Y := fun M hM => by
    obtain ⟨R, -, rfl⟩ := h𝓜 M hM
    exact (Subgroup.map_le_range _ _).trans hψY
  set 𝓜' : Set (Subgroup ↥Y) := (fun M => M.comap Y.subtype) '' 𝓜 with h𝓜'
  have hlift : ∀ x ∈ frameGroup 𝓜, ∃ x' ∈ frameGroup 𝓜', (x' : X) = x := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ x' ∈ frameGroup 𝓜', (x' : X) = x)
      ?_ ?_ ?_ ?_ hx
    · rintro z ⟨M, hM, hzM, hz2, hz1, hzc⟩
      refine ⟨⟨z, hMle M hM hzM⟩, Subgroup.subset_closure
        ⟨M.comap Y.subtype, ⟨M, hM, rfl⟩, hzM, Subtype.ext hz2,
          fun h => hz1 (congrArg Subtype.val h), fun s hs => Subtype.ext (hzc (s : X) hs)⟩, rfl⟩
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · rintro a b _ _ ⟨a', ha', rfl⟩ ⟨b', hb', rfl⟩
      exact ⟨a' * b', Subgroup.mul_mem _ ha' hb', rfl⟩
    · rintro a _ ⟨a', ha', rfl⟩
      exact ⟨a'⁻¹, Subgroup.inv_mem _ ha', rfl⟩
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
  have hact' : ∀ f ∈ F.subgroupOf Y, ∃ x ∈ frameGroup 𝓜', ∀ y ∈ ψ'.range,
      f * y * f⁻¹ = x * y * x⁻¹ := by
    intro f hf
    obtain ⟨x, hx, hxy⟩ := hact f.1 (show f.1 ∈ F from hf)
    obtain ⟨x', hx', rfl⟩ := hlift x hx
    refine ⟨x', hx', fun y hy => Subtype.ext ?_⟩
    rw [hrange] at hy
    exact hxy y.1 hy
  have hKG := hmodel t n p e hp hfund hadm hp2 h5 ↥Y ψ' hker' hcomp' 𝓜'
    (by
      rintro _ ⟨M, hM, rfl⟩
      obtain ⟨R, hR, rfl⟩ := h𝓜 M hM
      exact ⟨R, hR, hcomapmap R⟩)
    (by
      rintro _ ⟨M, hM, rfl⟩ _ ⟨M', hM', rfl⟩ hne x hx y hy
      have hMM' : M ≠ M' := fun h => hne (by rw [h])
      exact Subtype.ext (hcomm M hM M' hM' hMM' x.1 hx y.1 hy))
    (F.subgroupOf Y) hF'4 hF'2 hF'N hfaith' hact'
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

section Generation

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {a : G}

theorem generation_of_triple (hmodel : LayerGenerationTriple) (hp2 : p ≠ 2)
    (hΩ : InClass p f Ω) (hT : IndepTripleOn p f Ω A) (ha : a ∈ A) (hAY : A ≤ centLayer Ω a)
    (Dsys : LocalLieSystemAt p f Ω a) (j : Fin Dsys.card) (h5 : 5 ≤ p ^ Dsys.exp j)
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
  have hFb4 : Nat.card (modOdd a F') = 4 := by
    rw [card_modOdd_of_exponent_two (hF'A.trans hAC) hF'2, hF'.2]
    norm_num
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
  obtain ⟨𝓜, h𝓜f, h𝓜c, hact⟩ := exists_frame_data hΩ hT ha Dsys j
  rw [hj] at hFbN hfaith hcompY ⊢
  exact triple_generation_in_subgroup hmodel (Dsys.isFundTag j) (Dsys.admissible j) hp2 h5
    (componentHom hΩ Dsys j) hQY (componentHom_ker_le_center hΩ Dsys j) hcompY h𝓜f h𝓜c hFbJ hFb4
    (modOdd_sq_eq_one hA2 hF'A) hFbN hfaith
    (by
      rintro _ ⟨k, hk, rfl⟩
      exact hact k (hF'A hk))

end Generation

end CFSG.ClassicalInvolution.Balance.Bootstrap
