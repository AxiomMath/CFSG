module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersPair
public import CFSG.ClassicalInvolution.Balance.BootstrapBootTriple
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Helpers

theorem pos_of_five_le_pow {p f : ℕ} (hq : 5 ≤ p ^ f) : 0 < f :=
  Nat.pos_of_ne_zero (by rintro rfl; simp at hq)

theorem not_commutes_self_of_isQuasisimple {X : Type*} [Group X] {L : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥L) : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
  intro h
  have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
  obtain ⟨u, hu⟩ := exists_ne (1 : ↥L ⧸ Subgroup.center ↥L)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  apply hu
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (h g g.2 x x.2)

theorem commutator_self_eq_of_le {X : Type*} [Group X] {R : Subgroup X} (h : R ≤ ⁅R, R⁆) :
    ⁅R, R⁆ = R :=
  le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
    R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)) h

omit [Finite G] in
theorem modOdd_le_or_commutes {a : G} {Y : Subgroup (OddQuot a)}
    (D' : LieDecomposition (memberImages Ω a) Y) (i : D'.ι)
    {K : Subgroup G} (hK : K ∈ centMembers Ω a) :
    modOdd a K ≤ D'.Q i ∨ ∀ x ∈ modOdd a K, ∀ y ∈ D'.Q i, x * y = y * x := by
  obtain ⟨i', hi'⟩ := D'.exists_le (modOdd a K) ⟨K, hK, rfl⟩
  by_cases hii' : i' = i
  · subst hii'
    exact Or.inl hi'
  · exact Or.inr fun x hx y hy => D'.commute i' i hii' x (hi' hx) y hy

omit [Finite G] in
theorem le_iSup_centralizer_of_centralizedGeneratedAt {a : G} {F₀ : Subgroup G}
    {L : Subgroup (OddQuot a)} (h : CentralizedGeneratedAt Ω a F₀ L) :
    L ≤ ⨆ g ∈ modOdd a F₀, ⨆ (_ : g ≠ 1),
      memberJoin Ω a ⊓ Subgroup.centralizer ({g} : Set (OddQuot a)) := by
  refine h.trans (iSup₂_le fun K hKΩ => iSup_le fun hKC => iSup_le fun hex =>
    iSup_le fun _ => ?_)
  obtain ⟨g, hg, hg1, hcen⟩ := hex
  have hKJ : modOdd a K ≤ memberJoin Ω a :=
    le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) K ⟨hKΩ, hKC⟩
  exact le_iSup₂_of_le g hg (le_iSup_of_le hg1 (le_inf hKJ hcen))

end Helpers

section Component

variable {a : G}

theorem component_le_modOdd_of_gen {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (haA : a ∈ A) (ha1 : a ≠ 1) (hAY : A ≤ centLayer Ω a)
    {Q : Subgroup (OddQuot a)} (hQJ : Q ≤ memberJoin Ω a)
    (hQN : (Q.subgroupOf (memberJoin Ω a)).Normal)
    (hgen : ∀ F' : Subgroup G, F' ≤ A → Nat.card F' = 4 →
      (∀ x ∈ modOdd a F', x ≠ 1 → ¬ ∀ y ∈ Q, x * y = y * x) →
        Q ≤ ⨆ g ∈ modOdd a F', ⨆ (_ : g ≠ 1),
          memberJoin Ω a ⊓ Subgroup.centralizer ({g} : Set (OddQuot a))) :
    Q ≤ modOdd a (⨆ F ∈ signalizerFunctorEk 2 2 A,
      (Subgroup.centralizer (F : Set G) ⊓ centLayer Ω a)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set Y : Subgroup G := centLayer Ω a with hY
  set J : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 A,
    (Subgroup.centralizer (F : Set G) ⊓ Y) with hJ
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hA.2 x hx
  have hAC : A ≤ C := fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, haA⟩))
  have haC : a ∈ C := hAC haA
  have hJmem : ∀ (F : Subgroup G), F ∈ signalizerFunctorEk 2 2 A → ∀ (y : G),
      y ∈ Subgroup.centralizer (F : Set G) → y ∈ Y → y ∈ J := fun F hF y hyF hyY =>
    (le_iSup₂ (f := fun (F : Subgroup G) (_ : F ∈ signalizerFunctorEk 2 2 A) =>
      Subgroup.centralizer (F : Set G) ⊓ Y) F hF) ⟨hyF, hyY⟩
  set Z : Subgroup G := A ⊓ ((Subgroup.centralizer (Q : Set (OddQuot a))).comap
    (oddQuotMk a)).map C.subtype with hZ
  have hZmem : ∀ x : ↥C, (x : G) ∈ A → oddQuotMk a x ∈ Subgroup.centralizer (Q : Set (OddQuot a)) →
      (x : G) ∈ Z := fun x hxA hx => ⟨hxA, ⟨x, hx, rfl⟩⟩
  have hZcent : ∀ (g : G) (hgC : g ∈ C), g ∈ Z → ∀ y ∈ Q,
      oddQuotMk a ⟨g, hgC⟩ * y = y * oddQuotMk a ⟨g, hgC⟩ := by
    rintro g hgC ⟨-, ⟨c, hc, rfl⟩⟩ y hy
    exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm
  by_cases hF : ∃ F ∈ signalizerFunctorEk 2 2 A, F ≤ Z
  ·
    obtain ⟨F, hFE, hFZ⟩ := hF
    intro q hq
    obtain ⟨y, hyC, hyY, hyF, hyq⟩ := exists_lift_centralizer (E := F)
      (fun e he => hA2 e (hFE.1 he)) (hFE.1.trans hAY) (hQJ hq)
      (fun e he heC => hZcent e heC (hFZ he) q hq)
    exact ⟨⟨y, hyC⟩, hJmem F hFE y hyF hyY, hyq⟩
  ·
    obtain ⟨F', hF'E, hF'Z⟩ := exists_four_subgroup_inf_eq_bot hA hcard inf_le_left hF
    have hF'A : F' ≤ A := hF'E.1
    have hF'2 : ∀ x ∈ F', x * x = 1 := fun x hx => hA2 x (hF'A hx)
    have hF'C : F' ≤ C := hF'A.trans hAC
    set Fb : Subgroup (OddQuot a) := modOdd a F' with hFb
    have hF'4 : Nat.card F' = 4 := by
      rw [hF'E.2]
      norm_num
    have hFbJ : Fb ≤ memberJoin Ω a := modOdd_le_memberJoin (hF'A.trans hAY)
    have hfaith : ∀ x ∈ Fb, x ≠ 1 → ¬ ∀ y ∈ Q, x * y = y * x := by
      intro x hx hx1 hcomm
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
      have hkZ : (k : G) ∈ Z := hZmem k (hF'A hk)
        (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm y hy).symm)
      have hk1 : (k : G) ∈ F' ⊓ Z := ⟨hk, hkZ⟩
      rw [hF'Z, Subgroup.mem_bot] at hk1
      exact hx1 (by rw [show k = 1 from Subtype.ext hk1, map_one])
    have hKG := hgen F' hF'A hF'4 hfaith
    refine hKG.trans (iSup₂_le fun x hx => iSup_le fun hx1 => ?_)
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
    have hkF' : (k : G) ∈ F' := hk
    have hk1 : (k : G) ≠ 1 := fun h => hx1 (by rw [show k = 1 from Subtype.ext h, map_one])
    have hka : (k : G) ≠ a := by
      intro h
      refine hfaith _ hx hx1 fun y _ => ?_
      have : k = ⟨a, haC⟩ := Subtype.ext h
      rw [this]
      exact oddQuotMk_central haC y
    have hkA : (k : G) ∈ A := hF'A hkF'
    have hcomm : a * (k : G) = (k : G) * a :=
      congrArg Subtype.val (hA.1.is_comm.comm (⟨a, haA⟩ : A) ⟨k, hkA⟩)
    have hE4 : Nat.card (Subgroup.closure ({a, (k : G)} : Set G)) = 4 :=
      card_closure_pair_eq_four (hA2 a haA) (hA2 _ hkA) ha1 hk1 (Ne.symm hka) hcomm
    have hEA : Subgroup.closure ({a, (k : G)} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      exacts [haA, hkA]
    have hEmem : Subgroup.closure ({a, (k : G)} : Set G) ∈ signalizerFunctorEk 2 2 A :=
      ⟨hEA, by rw [hE4]; norm_num⟩
    rintro q ⟨hqJ, hqk⟩
    have hkq : oddQuotMk a k * q = q * oddQuotMk a k :=
      (Subgroup.mem_centralizer_singleton_iff.mp hqk).symm
    obtain ⟨y, hyC, hyY, hyk, hyq⟩ := exists_lift_centralizer (E := Subgroup.zpowers (k : G))
      (fun e he => by
        rcases mem_zpowers_involution (hF'2 _ hkF') he with rfl | rfl
        exacts [one_mul 1, hF'2 _ hkF'])
      (Subgroup.zpowers_le.mpr (hAY hkA)) hqJ
      (fun e he heC => by
        rcases mem_zpowers_involution (hF'2 _ hkF') he with rfl | rfl
        · change oddQuotMk a 1 * q = q * oddQuotMk a 1
          rw [map_one, one_mul, mul_one]
        · exact hkq)
    have hyE : y ∈ Subgroup.centralizer
        ((Subgroup.closure ({a, (k : G)} : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hsub : ({a, (k : G)} : Set G) ⊆
          ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
        rintro z (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hyk _ (Subgroup.mem_zpowers _))
      exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.closure_le _).mpr hsub hx)
    exact ⟨⟨y, hyC⟩, hJmem _ hEmem y hyE hyY, hyq⟩

end Component

section Main

structure CommutingInputs (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (a : G) : Prop where
  single : ∀ D : LocalLieSystemAt p f Ω a, SingleClassComponents p f D
  perfect : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card),
    ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, R ≤ ⁅R, R⁆
  toral : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card),
    ModelFacts.CommutingFundamentalGeneration p (D.tag j) (D.rank j) (D.exp j)

omit [Finite G] in
theorem CommutingInputs.of_facts {a : G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hno : ∀ D : LocalLieSystemAt p f Ω a, ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    (hF3 : NoComponentOverF3 p f Ω a) (hMFC : ModelFacts.CommutingFundamentalFacts p) :
    CommutingInputs p f Ω a where
  single D := singleClassComponents_of_tags D (hno D)
  perfect D j := by
    have hq4 : 4 ≤ p ^ f := by omega
    refine LieSystemData.fundPerfect D hp2 hq4 (fun i _ => ?_) j
    have := five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq i).imp id And.right) (hF3 D i)
    omega
  toral D j := hMFC (D.tag j) (D.rank j) (D.exp j) (D.isFundTag j) (D.admissible j)

variable {A : Subgroup G} {𝒦 : Set (Subgroup G)} {a : G}

theorem layerGenerationLie_of_commutingFundamental (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    (hM : MemberFamily p f Ω A 𝒦) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hI : CommutingInputs p f Ω a) :
    LayerGenerationLie Ω A a := by
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hM.elem.2 x hx
  refine LayerGenerationLie.of_centralizedGenerated hA2 (𝒜 := Ω)
    (InClass.isInvolutionMember hΩ hq) ?_
  intro L hL _ hjoin F₀ hF
  obtain ⟨D⟩ := hIH {a} hnc
  obtain ⟨D', hD'Q, -⟩ := lieDecomposition_localSystem_comp hp2 h0 fundamentalWholeA1 hq hΩ D
  have : (memberJoin Ω a).Normal := memberJoin_normal hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · obtain ⟨j, hj⟩ := hD'Q i
    exact centralizedGeneratedAt_of_commutingFundamental hΩ hM ha ha1 D j (hI.single D j)
      (fun R hR => commutator_self_eq_of_le (hI.perfect D j R hR)) (hI.toral D j) hj.symm
      (fun K hK => modOdd_le_or_commutes D' i hK) hF
  · exfalso
    exact not_commutes_self_of_isQuasisimple hL'.2.2 fun x hx y hy => hcomm x hx y (hjoin hy)

theorem componentLayersAt_of_commutingFundamental (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    (hM : MemberFamily p f Ω A 𝒦) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hI : CommutingInputs p f Ω a) :
    ComponentLayersAt Ω A a :=
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponent L)
    (fun _ hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponent_le_join hp2 h0 fundamentalWholeA1
      hΩ hIH hnc hL)
    (layerGenerationLie_of_commutingFundamental hp2 hq h0 hΩ hIH hM ha ha1 hnc hI)

theorem centralizerGenerationModOTwo_of_commutingFundamental (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    (hM : MemberFamily p f Ω A 𝒦) (ha : a ∈ A) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hI : CommutingInputs p f Ω a) : CentralizerGenerationModOTwo Ω A a := by
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
  obtain ⟨D⟩ := hIH {a} hnc
  obtain ⟨D', hD'Q, -⟩ := lieDecomposition_localSystem_comp hp2 h0 fundamentalWholeA1 hq hΩ D
  have hΩc : ConjInvariant Ω := hΩ.conjInvariant
  set J : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 A,
    (Subgroup.centralizer (F : Set G) ⊓ centLayer Ω a) with hJ
  have hQ : ∀ i, D'.Q i ≤ modOdd a J := by
    intro i
    refine component_le_modOdd_of_gen hM.elem hM.card ha ha1 hAY (D'.le_join i)
      (D'.normal_subgroupOf i) ?_
    intro F' hF'A hF'4 hfaith
    rcases D'.rankOne_or_lie i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | hlie
    ·
      exfalso
      have hr1 : RankOneAt Ω a (D'.Q i) := by
        refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
        obtain ⟨j, hj⟩ := D'.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
        by_cases hji : j = i
        · subst hji
          exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
        · exact Or.inr fun x hx y hy => D'.commute j i hji x (hj hx) y hy
      obtain ⟨g, hgF, hg1⟩ := exists_ne_one_of_card_eq_two_pow (S := F') (n := 2) (by norm_num)
        (by rw [hF'4]; norm_num)
      have hgA : g ∈ A := hF'A hgF
      have hgC : g ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨g, hgA⟩ : A) ⟨a, ha⟩))
      have hsq : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hgC⟩ = 1 :=
        Subtype.ext (by rw [← pow_two]; exact hM.elem.2 g hgA)
      exact hfaith _ (oddQuotMk_mem_modOdd hgF hgC)
        (fun h => hg1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h)))
        (fun y hy => oddQuotMk_centralizes_of_memberFamily hM ha (Or.inr hr1) hgA hgC y hy)
    ·
      obtain ⟨j, hj⟩ := hD'Q i
      have hFbJ : modOdd a F' ≤ memberJoin Ω a := modOdd_le_memberJoin (hF'A.trans hAY)
      have hFbN : modOdd a F' ≤ Subgroup.normalizer ((D'.Q i : Subgroup (OddQuot a)) :
          Set (OddQuot a)) :=
        hFbJ.trans (le_normalizer_of_normal_subgroupOf (D'.le_join i) (D'.normal_subgroupOf i))
      exact le_iSup_centralizer_of_centralizedGeneratedAt
        (centralizedGeneratedAt_of_commutingFundamental hΩ hM ha ha1 D j (hI.single D j)
          (fun R hR => commutator_self_eq_of_le (hI.perfect D j R hR)) (hI.toral D j) hj.symm
          (fun K hK => modOdd_le_or_commutes D' i hK) ⟨hF'A, hF'4, hFbN, hfaith⟩)
  have hJY : J ≤ centLayer Ω a := iSup₂_le fun _ _ => inf_le_right
  show centLayer Ω a ≤ oddCoreIn (centLayer Ω a) ⊔ J
  intro y hy
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := centLayer_le_centralizer Ω a hy
  have hyJ := oddQuotMk_mem_memberJoin hy hyC
  rw [← D'.iSup_eq] at hyJ
  obtain ⟨k, hkJ, hk⟩ := mem_modOdd_iff.mp ((iSup_le hQ) hyJ)
  have hkY : (k : G) ∈ centLayer Ω a := hJY hkJ
  have hker : (⟨k, hkY⟩ : ↥(centLayer Ω a))⁻¹ * ⟨y, hy⟩ ∈ (layerToOddQuot Ω a).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    change (oddQuotMk a k)⁻¹ * oddQuotMk a ⟨y, hyC⟩ = 1
    rw [hk, inv_mul_cancel]
  rw [ker_layerToOddQuot hΩc] at hker
  have hodd : (k : G)⁻¹ * y ∈ oddCoreIn (centLayer Ω a) := ⟨_, hker, rfl⟩
  have hmem : (k : G) * ((k : G)⁻¹ * y) ∈ J ⊔ oddCoreIn (centLayer Ω a) :=
    Subgroup.mul_mem_sup hkJ hodd
  rwa [mul_inv_cancel_left, sup_comm] at hmem

end Main

section Triple

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

theorem ExactTriple.memberFamily (hp2 : p ≠ 2) (hf : 0 < f)
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω)
    (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃) :
    MemberFamily p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) where
  elem := T.isElemAbelian
  card := T.card_eq_eight hind
  subset := by
    rintro K (rfl | rfl | rfl)
    exacts [hΩ₁, hΩ₂, hΩ₃]
  nonempty := ⟨K₁, Or.inl rfl⟩
  involution := by
    rintro K (rfl | rfl | rfl)
    · exact ⟨z₁, Subgroup.subset_closure (by simp), hz₁, T.le_centralizer₁⟩
    · exact ⟨z₂, Subgroup.subset_closure (by simp), hz₂, T.le_centralizer₂⟩
    · exact ⟨z₃, Subgroup.subset_closure (by simp), hz₃, T.le_centralizer₃⟩
  generate := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Subgroup.subset_closure ⟨K₁, Or.inl rfl, hz₁⟩
      · exact Subgroup.subset_closure ⟨K₂, Or.inr (Or.inl rfl), hz₂⟩
      · exact Subgroup.subset_closure ⟨K₃, Or.inr (Or.inr rfl), hz₃⟩
    · refine (Subgroup.closure_le _).mpr ?_
      rintro w ⟨K, hK, hw⟩
      rcases hK with rfl | rfl | rfl
      · rw [hz₁.eq_of_isCentralInvolution hp2 hf hw.isCentralInvolution]
        exact Subgroup.subset_closure (by simp)
      · rw [hz₂.eq_of_isCentralInvolution hp2 hf hw.isCentralInvolution]
        exact Subgroup.subset_closure (by simp)
      · rw [hz₃.eq_of_isCentralInvolution hp2 hf hw.isCentralInvolution]
        exact Subgroup.subset_closure (by simp)

theorem componentLayersAt_of_commutingFundamental_exactTriple [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃)
    (hI : ∀ a ∈ T.group, a ≠ 1 → CommutingInputs p f Ω a) :
    ∀ a ∈ T.group, a ≠ 1 → ComponentLayersAt Ω T.group a := fun a ha ha1 =>
  componentLayersAt_of_commutingFundamental hp2 hq h0 hΩ hIH
    (T.memberFamily hp2 (pos_of_five_le_pow hq) hind
      hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃) ha ha1 (not_subset_center_of_ne_one hnab ha1) (hI a ha ha1)

theorem centralizerGenerationModOTwo_of_commutingFundamental_exactTriple [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃)
    (hI : ∀ a ∈ T.group, a ≠ 1 → CommutingInputs p f Ω a) :
    ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      CentralizerGenerationModOTwo Ω T.group a := by
  intro a ha hfa
  obtain ⟨K, -, hK⟩ := hfa
  exact centralizerGenerationModOTwo_of_commutingFundamental hp2 hq h0 hΩ hIH
    (T.memberFamily hp2 (pos_of_five_le_pow hq) hind
      hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃) ha (not_subset_center_of_ne_one hnab hK.ne_one)
    (hI a ha hK.ne_one)

theorem stage2_of_exactTriple_of_commutingFundamental [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω)
    (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃)
    (hI : ∀ a ∈ T.group, a ≠ 1 → CommutingInputs p f Ω a) (hconn : OmegaConnected Ω)
    (hlink : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      InvolutionLink p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) a) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.group, deltaCore F = ⊥) ∧
      Stage2 Ω {x | x ∈ T.group ∧ x ≠ 1 ∧ TripleMeetsAt Ω K₁ K₂ K₃ x} :=
  stage2_of_exactTriple_of_layers_wb hnab hp2 hq h9 h0 fundamentalWholeA1 hΩ hsingle hIH T hind
    hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃
    (componentLayersAt_of_commutingFundamental_exactTriple hnab hp2 hq h0 hΩ hIH T hind hΩ₁ hΩ₂
      hΩ₃ hz₁ hz₂ hz₃ hI)
    hconn
    (centralizerGenerationModOTwo_of_commutingFundamental_exactTriple hnab hp2 hq h0 hΩ hIH T
      hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ hI)
    hlink

end Triple

section Chain

theorem exactMembers_and_localOddCentral_of_frameFamily_commuting [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hI : ∀ a ∈ A, a ≠ 1 → CommutingInputs p f Ω a)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  obtain ⟨K₀, hK₀⟩ := hM.nonempty
  obtain ⟨z₀, -, hz₀, -⟩ := hM.involution K₀ hK₀
  have h0 := ModelFacts.modelClauseZero
  exact exactMembers_and_localOddCentral_of_memberFamily_meets hnab hp2 hq h9 hΩ hsingle hIH hM
    (fun a ha ha1 D => (hI a ha ha1).single D)
    (fun a ha ha1 => componentLayersAt_of_commutingFundamental hp2 hq h0 hΩ hIH hM ha ha1
      (not_subset_center_of_ne_one hnab ha1) (hI a ha ha1))
    hconn
    (fun a ha hfa => by
      obtain ⟨K, -, hK⟩ := hfa
      exact centralizerGenerationModOTwo_of_commutingFundamental hp2 hq h0 hΩ hIH hM ha
        (not_subset_center_of_ne_one hnab hK.ne_one) (hI a ha hK.ne_one))
    hK₀ hz₀ hcover

@[expose] def FrameCommutingInputs (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) → ∀ A : Subgroup G,
        MemberFamily p f (CoreAssembly.conjClass K) A
          (frameFamily p f (CoreAssembly.conjClass K) A) →
        ∀ a ∈ A, a ≠ 1 → CommutingInputs p f (CoreAssembly.conjClass K) a

theorem bootTriple_of_commuting (h9 : p ^ f ≠ 9) (hI : FrameCommutingInputs p f)
    (hcover : FrameCoverage p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hM⟩ := exists_memberFamily_of_indepTriple hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily_commuting hnab hp2 hq h9
    hΩ (CoreAssembly.exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow)
    (omegaConnected_of_deltaConnected hconn) hM (hI G hnab K z hz hBelow hconn A hM)
    (hcover G hnab K z hz hBelow hconn A hM)
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

end Chain

end CFSG.ClassicalInvolution.Balance.Bootstrap
