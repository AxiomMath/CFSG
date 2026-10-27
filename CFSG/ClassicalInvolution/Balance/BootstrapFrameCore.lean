module

public import CFSG.ClassicalInvolution.Balance.BootstrapBootTriple
public import CFSG.ClassicalInvolution.Balance.QNineStage
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

section Component

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem component_le_modOdd_of_hgen {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (haA : a ∈ A) (ha1 : a ≠ 1) (hAY : A ≤ centLayer Ω a)
    {Q : Subgroup (OddQuot a)} (hQJ : Q ≤ memberJoin Ω a)
    (hgen : ∀ F' ∈ signalizerFunctorEk 2 2 A,
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
    have hfaith : ∀ x ∈ modOdd a F', x ≠ 1 → ¬ ∀ y ∈ Q, x * y = y * x := by
      intro x hx hx1 hcomm
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
      have hkZ : (k : G) ∈ Z := hZmem k (hF'A hk)
        (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm y hy).symm)
      have hk1 : (k : G) ∈ F' ⊓ Z := ⟨hk, hkZ⟩
      rw [hF'Z, Subgroup.mem_bot] at hk1
      exact hx1 (by rw [show k = 1 from Subtype.ext hk1, map_one])
    have hKG := hgen F' hF'E hfaith
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

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem centralizerGenerationModOTwo_of_components (hΩc : ConjInvariant Ω) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8) (haA : a ∈ A) (ha1 : a ≠ 1)
    (hAY : A ≤ centLayer Ω a) (D : LieDecomposition (memberImages Ω a) (memberJoin Ω a))
    (hgen : ∀ i, ∀ F' ∈ signalizerFunctorEk 2 2 A,
      (∀ x ∈ modOdd a F', x ≠ 1 → ¬ ∀ y ∈ D.Q i, x * y = y * x) →
        D.Q i ≤ ⨆ g ∈ modOdd a F', ⨆ (_ : g ≠ 1),
          memberJoin Ω a ⊓ Subgroup.centralizer ({g} : Set (OddQuot a))) :
    CentralizerGenerationModOTwo Ω A a := by
  classical
  set J : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 A,
    (Subgroup.centralizer (F : Set G) ⊓ centLayer Ω a) with hJ
  have hQ : ∀ i, D.Q i ≤ modOdd a J := fun i =>
    component_le_modOdd_of_hgen hA hcard haA ha1 hAY (D.le_join i) (hgen i)
  have hJY : J ≤ centLayer Ω a := iSup₂_le fun _ _ => inf_le_right
  show centLayer Ω a ≤ oddCoreIn (centLayer Ω a) ⊔ J
  intro y hy
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := centLayer_le_centralizer Ω a hy
  have hyJ := oddQuotMk_mem_memberJoin hy hyC
  rw [← D.iSup_eq] at hyJ
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

section Stage2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem deltaCore_eq_bot_and_localOddCentral_of_frameFamily [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω)
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hMF1 : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
      SingleClassComponents p f D)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a)
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a)
    (hgenModO : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a →
      CentralizerGenerationModOTwo Ω A a) :
    (∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) ∧
      ∃ K₀ ∈ frameFamily p f Ω A, ∃ z₀ ∈ A, IsClassicalMember p f K₀ z₀ ∧
        K₀ ≤ Subgroup.centralizer (A : Set G) ∧ LocalOddCentral Ω {z₀} := by
  have h0 := ModelFacts.modelClauseZero
  have hA1 := fundamentalWholeA1
  have hL : LocalHypotheses p f Ω A :=
    { inClass := hΩ
      odd := hp2
      five := hq
      noncentral := fun a _ ha1 hc =>
        not_subset_center_of_ne_one hnab ha1 (Set.singleton_subset_iff.mpr hc)
      lie := hIH
      single := hMF1 }
  have hlink : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a →
      InvolutionLink p f Ω A (frameFamily p f Ω A) a := by
    intro a ha hfa
    obtain ⟨K, hK𝒦, hK⟩ := hfa
    refine involutionLink_of_inCommonComponent hL ha hK.ne_one hM.subset (fun K hK => ?_) ?_
    · obtain ⟨z, hzA, hz, -⟩ := hM.involution K hK
      exact ⟨z, hzA, hz⟩
    · intro M hMa
      obtain ⟨L, hL𝒦, hcc⟩ := hcover a ha ⟨K, hK𝒦, hK⟩ M hMa
      obtain ⟨-, -, -, hLA⟩ := hM.involution L hL𝒦
      exact ⟨L, hL𝒦, hLA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)), hcc⟩
  have hgen := generation_of_memberFamily_of_closure hΩ hM hconn hgenModO hlink
  have hRB : RankThreeBalance A :=
    ⟨hM.elem, hM.card, weakBalanced_of_memberFamily hnab hp2 hq h0 hA1 hΩ hIH hM,
      twoBalancedWrt_of_memberFamily_of_layers hM hloc⟩
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hRB
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  obtain ⟨K₀, hK₀⟩ := hM.nonempty
  obtain ⟨z₀, hz₀A, hz₀, hK₀A⟩ := hM.involution K₀ hK₀
  refine ⟨hΔ, K₀, hK₀, z₀, hz₀A, hz₀, hK₀A,
    localOddCentral_of_deltaCore_eq_bot hnab hp2 hq h0 hA1 hΩ hIH hM.elem hM.card hΔ hz₀A
      hz₀.ne_one fun K hK => ?_⟩
  obtain ⟨L, hL𝒦, hcc⟩ := hcover z₀ hz₀A ⟨K₀, hK₀, hz₀⟩ K hK
  obtain ⟨hLΩ, hLA, z, hzA, hz⟩ := hL𝒦
  exact ⟨L, hLΩ, z, hzA, hz, hLA, hcc⟩

theorem exactMembers_and_localOddCentral_of_frameFamily_of_layers_nine [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : OmegaConnected Ω) (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hMF1 : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
      SingleClassComponents p f D)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a)
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a)
    (hgenModO : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a →
      CentralizerGenerationModOTwo Ω A a)
    (hnine : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → p ^ f = 9 →
      LocalLeviComponent p f Ω a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have h0 := ModelFacts.modelClauseZero
  have hA1 := fundamentalWholeA1
  obtain ⟨hΔ, K₀, hK₀, z₀, hz₀A, hz₀, hK₀A, hP1⟩ :=
    deltaCore_eq_bot_and_localOddCentral_of_frameFamily hnab hp2 hq hΩ hIH hconn hM hMF1 hcover
      hloc hgenModO
  have hK₀Ω : K₀ ∈ Ω := hM.subset hK₀
  refine ⟨?_, localOddCentral_of_classicalMember hp2 hf hΩ hsingle hK₀Ω hz₀ hP1⟩
  by_cases h9 : p ^ f = 9
  · exact exactMembers_of_localLeviComponent hp2 hq hΩ hsingle hP1
      (hnine z₀ hz₀A ⟨K₀, hK₀, hz₀⟩ h9)
  · obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
      Nat.prime_two A hM.elem (by rw [hM.card]; norm_num)
    exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH hK₀Ω hz₀
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hM.elem hF₀.1)
      (hK₀A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)

end Stage2

end CFSG.ClassicalInvolution.Balance.Bootstrap
