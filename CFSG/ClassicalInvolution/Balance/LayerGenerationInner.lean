module

public import CFSG.ClassicalInvolution.Balance.BootstrapAuditFamily
public import CFSG.ClassicalInvolution.Balance.LayerGenerationLie

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

@[expose] def LayerGenerationInvolutoryModel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), CFSG.IsComponent L →
    IsOddLieComponentBig L → ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
      F ≤ Subgroup.normalizer (L : Set X) → (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
      (∃ T : Subgroup X, T ≤ L ∧ (∀ x ∈ T, x * x = 1) ∧
        ∀ f ∈ F, ∃ x ∈ T, ∀ y ∈ L, f * y * f⁻¹ = x * y * x⁻¹) →
        L ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f

theorem layerGenerationInvolutoryModel_of_model (h : LayerGenerationModel) :
    LayerGenerationInvolutoryModel :=
  fun X _ _ L hL hbig F h4 h2 hN hf _ => h X L hL hbig F h4 h2 hN hf

section Abstract

variable {X : Type} [Group X]

theorem commute_of_mem_closure {S : Set X} (h : ∀ z ∈ S, ∀ w ∈ S, z * w = w * z) {x y : X}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) : Commute x y := by
  have h1 : ∀ z ∈ S, ∀ y ∈ Subgroup.closure S, Commute z y := by
    intro z hz y hy
    induction hy using Subgroup.closure_induction with
    | mem w hw => exact h z hz w hw
    | one => exact Commute.one_right z
    | mul a b _ _ iha ihb => exact iha.mul_right ihb
    | inv a _ iha => exact iha.inv_right
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact h1 z hz y hy
  | one => exact Commute.one_left y
  | mul a b _ _ iha ihb => exact iha.mul_left ihb
  | inv a _ iha => exact iha.inv_left

theorem mul_self_eq_one_of_mem_closure {S : Set X} (h2 : ∀ z ∈ S, z * z = 1)
    (h : ∀ z ∈ S, ∀ w ∈ S, z * w = w * z) {x : X} (hx : x ∈ Subgroup.closure S) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact h2 z hz
  | one => exact mul_one 1
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := commute_of_mem_closure h ha hb
    calc a * b * (a * b) = a * a * (b * b) := by
          rw [mul_assoc, ← mul_assoc b a b, hab.symm.eq, mul_assoc a b b, ← mul_assoc]
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a _ iha => rw [← mul_inv_rev, iha, inv_one]

theorem exists_involution_action {Ψ : Set (Subgroup X)} {Y : Subgroup X}
    (D : LieDecomposition Ψ Y) (i : D.ι) {Z : Set X} (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hZc : ∀ z ∈ Z, ∀ w ∈ Z, z * w = w * z) (hZΨ : ∀ z ∈ Z, ∃ K ∈ Ψ, z ∈ K) :
    ∃ T : Subgroup X, T ≤ D.Q i ∧ (∀ x ∈ T, x * x = 1) ∧
      ∀ g ∈ Subgroup.closure Z, ∃ x ∈ T, ∀ y ∈ D.Q i, g * y * g⁻¹ = x * y * x⁻¹ := by
  classical
  set Zi : Set X := {z | z ∈ Z ∧ z ∈ D.Q i} with hZi
  have hZiZ : Zi ⊆ Z := fun z hz => hz.1
  refine ⟨Subgroup.closure Zi, (Subgroup.closure_le _).2 fun z hz => hz.2, ?_, ?_⟩
  · intro x hx
    exact mul_self_eq_one_of_mem_closure (fun z hz => hZ2 z hz.1)
      (fun z hz w hw => hZc z hz.1 w hw.1) hx
  · intro g hg
    induction hg using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨K, hK, hzK⟩ := hZΨ z hz
      obtain ⟨j, hj⟩ := D.exists_le K hK
      by_cases hji : j = i
      · subst hji
        exact ⟨z, Subgroup.subset_closure ⟨hz, hj hzK⟩, fun y _ => rfl⟩
      · refine ⟨1, Subgroup.one_mem _, fun y hy => ?_⟩
        rw [D.commute j i hji z (hj hzK) y hy, mul_assoc, mul_inv_cancel, mul_one]
        simp
    | one => exact ⟨1, Subgroup.one_mem _, fun y _ => by simp⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨x₁, hx₁, h₁⟩ := iha
      obtain ⟨x₂, hx₂, h₂⟩ := ihb
      refine ⟨x₁ * x₂, Subgroup.mul_mem _ hx₁ hx₂, fun y hy => ?_⟩
      have hx₂L : x₂ ∈ D.Q i := (Subgroup.closure_le _).2 (fun z hz => hz.2) hx₂
      have hy' : x₂ * y * x₂⁻¹ ∈ D.Q i :=
        (D.Q i).mul_mem ((D.Q i).mul_mem hx₂L hy) ((D.Q i).inv_mem hx₂L)
      calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
        _ = a * (x₂ * y * x₂⁻¹) * a⁻¹ := by rw [h₂ y hy]
        _ = x₁ * (x₂ * y * x₂⁻¹) * x₁⁻¹ := h₁ _ hy'
        _ = x₁ * x₂ * y * (x₁ * x₂)⁻¹ := by group
    | inv a _ iha =>
      obtain ⟨x, hx, h⟩ := iha
      refine ⟨x⁻¹, Subgroup.inv_mem _ hx, fun y hy => ?_⟩
      have hxL : x ∈ D.Q i := (Subgroup.closure_le _).2 (fun z hz => hz.2) hx
      have hy' : x⁻¹ * y * x ∈ D.Q i :=
        (D.Q i).mul_mem ((D.Q i).mul_mem ((D.Q i).inv_mem hxL) hy) hxL
      have h3 := h _ hy'
      have h4 : a * (x⁻¹ * y * x) * a⁻¹ = y := by
        rw [h3]
        group
      calc a⁻¹ * y * a⁻¹⁻¹ = a⁻¹ * (a * (x⁻¹ * y * x) * a⁻¹) * a := by
            rw [h4]
            group
        _ = x⁻¹ * y * x⁻¹⁻¹ := by group

end Abstract

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {𝒦 : Set (Subgroup G)}

omit [Finite G] in
theorem memberFamily_exists_involution_action (hM : MemberFamily p f Ω A 𝒦) {a : G} (ha : a ∈ A)
    (D : LieDecomposition (memberImages Ω a) (memberJoin Ω a)) (i : D.ι) :
    ∃ T : Subgroup (OddQuot a), T ≤ D.Q i ∧ (∀ x ∈ T, x * x = 1) ∧
      ∀ g ∈ A, ∀ hgC : g ∈ Subgroup.centralizer ({a} : Set G), ∃ x ∈ T, ∀ y ∈ D.Q i,
        oddQuotMk a ⟨g, hgC⟩ * y * (oddQuotMk a ⟨g, hgC⟩)⁻¹ = x * y * x⁻¹ := by
  classical
  have hcom : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hAC : ∀ {g : G}, g ∈ A → g ∈ Subgroup.centralizer ({a} : Set G) := fun hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcom hg ha)
  have hz2 : ∀ {K : Subgroup G} {z : G}, IsClassicalMember p f K z → z * z = 1 := by
    intro K z hz
    have := pow_orderOf_eq_one z
    rwa [hz.orderOf_eq_two, pow_two] at this
  set Z : Set (OddQuot a) := {x | ∃ K ∈ 𝒦, ∃ z : G, ∃ _ : IsClassicalMember p f K z,
      ∃ hzC : z ∈ Subgroup.centralizer ({a} : Set G), oddQuotMk a ⟨z, hzC⟩ = x} with hZ
  have hZ2 : ∀ x ∈ Z, x * x = 1 := by
    rintro _ ⟨K, hK, z, hz, hzC, rfl⟩
    rw [← map_mul]
    have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z, hzC⟩ = 1 :=
      Subtype.ext (hz2 hz)
    rw [this, map_one]
  have hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := by
    rintro _ ⟨K, hK, z, hz, hzC, rfl⟩ _ ⟨K', hK', z', hz', hzC', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcom (hM.mem_of_isClassicalMember hK hz)
      (hM.mem_of_isClassicalMember hK' hz'))
  have hZΨ : ∀ x ∈ Z, ∃ L ∈ memberImages Ω a, x ∈ L := by
    rintro _ ⟨K, hK, z, hz, hzC, rfl⟩
    obtain ⟨-, -, -, hKA⟩ := hM.involution K hK
    have hKC : K ≤ Subgroup.centralizer ({a} : Set G) :=
      hKA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
    exact ⟨modOdd a K, ⟨K, ⟨hM.subset hK, hKC⟩, rfl⟩, oddQuotMk_mem_modOdd hz.mem hzC⟩
  have hAZ : ∀ g : G, g ∈ A → ∀ hgC : g ∈ Subgroup.centralizer ({a} : Set G),
      oddQuotMk a ⟨g, hgC⟩ ∈ Subgroup.closure Z := by
    intro g hg
    have hg' : g ∈ Subgroup.closure {z | ∃ K ∈ 𝒦, IsClassicalMember p f K z} := by
      rw [← hM.generate]
      exact hg
    induction hg' using Subgroup.closure_induction with
    | mem z hz =>
      intro hzC
      obtain ⟨K, hK, hz⟩ := hz
      exact Subgroup.subset_closure ⟨K, hK, z, hz, hzC, rfl⟩
    | one =>
      intro hgC
      have : (⟨1, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul g₁ g₂ h₁ h₂ ih₁ ih₂ =>
      intro hgC
      have hg₁ : g₁ ∈ A := by
        rw [hM.generate]
        exact h₁
      have hg₂ : g₂ ∈ A := by
        rw [hM.generate]
        exact h₂
      have : (⟨g₁ * g₂, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) =
          ⟨g₁, hAC hg₁⟩ * ⟨g₂, hAC hg₂⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ (ih₁ hg₁ (hAC hg₁)) (ih₂ hg₂ (hAC hg₂))
    | inv g₁ h₁ ih₁ =>
      intro hgC
      have hg₁ : g₁ ∈ A := by
        rw [hM.generate]
        exact h₁
      have : (⟨g₁⁻¹, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = ⟨g₁, hAC hg₁⟩⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ (ih₁ hg₁ (hAC hg₁))
  obtain ⟨T, hTL, hT2, hT⟩ := exists_involution_action D i hZ2 hZc hZΨ
  exact ⟨T, hTL, hT2, fun g hg hgC => hT _ (hAZ g hg hgC)⟩

omit [Finite G] in
theorem memberFamily_exists_involution_action_modOdd (hM : MemberFamily p f Ω A 𝒦) {a : G}
    (ha : a ∈ A) (D : LieDecomposition (memberImages Ω a) (memberJoin Ω a)) (i : D.ι)
    {F₀ : Subgroup G} (hF₀ : F₀ ≤ A) :
    ∃ T : Subgroup (OddQuot a), T ≤ D.Q i ∧ (∀ x ∈ T, x * x = 1) ∧
      ∀ g ∈ modOdd a F₀, ∃ x ∈ T, ∀ y ∈ D.Q i, g * y * g⁻¹ = x * y * x⁻¹ := by
  obtain ⟨T, hTL, hT2, hT⟩ := memberFamily_exists_involution_action hM ha D i
  refine ⟨T, hTL, hT2, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact hT k (hF₀ hk) k.2

end Local

section Providers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem LayerGenerationLieBig.of_involutoryModel (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    (hmodel : LayerGenerationInvolutoryModel) (hM : MemberFamily p f Ω A 𝒦) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) : LayerGenerationLieBig Ω A a := by
  intro L hL hbig hjoin F₀ hF
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH hnc
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hM.elem.2 x hx
  rcases D.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
    obtain ⟨T, hTL, hT2, hT⟩ := memberFamily_exists_involution_action_modOdd hM ha D i hF₀A
    have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_sq_eq_one hA2 (hF₀A hg) ha
    have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => hA2 g (hF₀A hg)
    exact OddCentralizerFree.of_le_layers (hmodel (OddQuot a) (D.Q i) hL hbig (modOdd a F₀)
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) (modOdd_sq_eq_one hA2 hF₀A) hFn hfaith
      ⟨T, hTL, hT2, hT⟩)
  · exfalso
    have hcommL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy => hcomm x hx y (hjoin hy)
    have hq2 := hL'.2.2
    have : Group.IsPerfect ↥L := ⟨hq2.1⟩
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq2.2
    have : Nontrivial ↥L :=
      (QuotientGroup.mk_surjective :
        Function.Surjective (QuotientGroup.mk : ↥L → ↥L ⧸ Subgroup.center ↥L)).nontrivial
    exact Group.IsPerfect.not_isMulCommutative ↥L
      ⟨⟨fun x y => Subtype.ext (hcommL x x.2 y y.2)⟩⟩

theorem componentLayersAt_of_involutoryModel [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (hM : MemberFamily p f Ω A 𝒦)
    (hmodel : LayerGenerationInvolutoryModel) :
    ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a := fun a ha ha1 =>
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponentBig L)
    (fun _ hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig hp2 h0 fundamentalWholeA1 hq hΩ
      hIH (not_subset_center_of_ne_one hnab ha1) (NoComponentOverF3.of_ne_27 a hq h27) hL)
    (LayerGenerationLieBig.of_involutoryModel hp2 h0 fundamentalWholeA1 hΩ hIH hmodel hM ha
      (not_subset_center_of_ne_one hnab ha1))

end Providers

section KG8

variable {X : Type} [Group X] [Finite X]

theorem kg8_generation_involutory (hmodel : LayerGenerationInvolutoryModel) {Y Q F : Subgroup X}
    (hQY : Q ≤ Y) (hQN : (Q.subgroupOf Y).Normal) (hqs : CFSG.Open.IsQuasisimple ↥Q)
    (hbig : IsOddLieComponentBig Q) (hFY : F ≤ Y) (hF4 : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1) (hFN : F ≤ Subgroup.normalizer (Q : Set X))
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ Q, f * x = x * f)
    (hinv : ∃ T : Subgroup X, T ≤ Q ∧ (∀ x ∈ T, x * x = 1) ∧
      ∀ f ∈ F, ∃ x ∈ T, ∀ y ∈ Q, f * y * f⁻¹ = x * y * x⁻¹) :
    Q ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X) := by
  set L : Subgroup ↥Y := Q.subgroupOf Y with hL
  set F' : Subgroup ↥Y := F.subgroupOf Y with hF'
  have : L.Normal := hQN
  have hqsL : CFSG.Open.IsQuasisimple ↥L :=
    Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hQY) hqs
  have hcomp : CFSG.IsComponent L := by
    rw [CFSG.isComponent_iff_open]
    exact ⟨le_top, isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf, hqsL⟩
  have hnt : ∃ x : ↥Q, (Subgroup.subgroupOfEquivOfLe hQY).symm x ≠ 1 := by
    have : Nontrivial (↥Q ⧸ Subgroup.center ↥Q) := hqs.2.toNontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥Q ⧸ Subgroup.center ↥Q)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨x, fun h => hy ?_⟩
    have hx1 : x = 1 := (MulEquiv.map_eq_one_iff _).mp h
    rw [hx1]
    rfl
  have hbigL : IsOddLieComponentBig L := by
    obtain ⟨t, n, p, f, hp, h5, hn, ht, hm⟩ := hbig
    exact isOddLieComponentBig_of_surjective hqs
      (Subgroup.subgroupOfEquivOfLe hQY).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQY).symm.surjective hnt hp h5 hn ht hm
  have hF'4 : Nat.card F' = 4 := by
    rw [← hF4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFY).toEquiv
  have hF'2 : ∀ f ∈ F', f * f = 1 := fun f hf => Subtype.ext (hF2 f.1 hf)
  have hF'N : F' ≤ Subgroup.normalizer (L : Set ↥Y) := fun f hf => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact Subgroup.mem_normalizer_iff.mp (hFN (show f.1 ∈ F from hf)) h.1
  have hfaith' : ∀ f ∈ F', f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f := by
    intro f hf hf1 hcomm
    refine hfaith f.1 (show f.1 ∈ F from hf) (fun h => hf1 (Subtype.ext h)) fun x hx => ?_
    exact congrArg Subtype.val (hcomm ⟨x, hQY hx⟩ hx)
  have hinv' : ∃ T : Subgroup ↥Y, T ≤ L ∧ (∀ x ∈ T, x * x = 1) ∧
      ∀ f ∈ F', ∃ x ∈ T, ∀ y ∈ L, f * y * f⁻¹ = x * y * x⁻¹ := by
    obtain ⟨T, hTQ, hT2, hT⟩ := hinv
    refine ⟨T.subgroupOf Y, fun x hx => hTQ hx, fun x hx => Subtype.ext (hT2 x.1 hx),
      fun f hf => ?_⟩
    obtain ⟨x, hx, hxy⟩ := hT f.1 (show f.1 ∈ F from hf)
    exact ⟨⟨x, hQY (hTQ hx)⟩, hx, fun y hy => Subtype.ext (hxy y.1 hy)⟩
  have hKG := hmodel ↥Y L hcomp hbigL F' hF'4 hF'2 hF'N hfaith' hinv'
  have hle : (⨆ f ∈ F', ⨆ (_ : f ≠ 1), centralizerLayer f) ≤
      (⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X)).comap Y.subtype := by
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({f} : Set ↥Y) := Subgroup.map_subtype_le _ hx
    have hcomm : x * f = f * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hf1' : (f : X) ≠ 1 := fun h => hf1 (Subtype.ext h)
    have hmem : (x : X) ∈ Y ⊓ Subgroup.centralizer ({f.1} : Set X) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)⟩
    have hsub : (Y ⊓ Subgroup.centralizer ({f.1} : Set X)) ≤
        ⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X) :=
      le_iSup₂_of_le f.1 (show f.1 ∈ F from hf) (le_iSup_of_le hf1' le_rfl)
    exact hsub hmem
  intro x hx
  exact hle (hKG (show (⟨x, hQY hx⟩ : ↥Y) ∈ L from hx))

end KG8

end CFSG.ClassicalInvolution.Balance.Bootstrap
