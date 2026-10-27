module

public import CFSG.ClassicalInvolution.Balance.BootstrapTripleBridge
public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaDelta
public import CFSG.ClassicalInvolution.Balance.BootstrapExact
public import CFSG.ClassicalInvolution.Balance.BootstrapP1

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace ExactTriple

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

theorem card_eq_four (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hd : z₁ * z₂ = z₃) :
    Nat.card T.group = 4 := by
  classical
  rw [T.group_eq_closure_pair hd]
  have c : z₂ * z₁ = z₁ * z₂ := T.comm₁₂'.symm
  have s1 := T.sq₁
  have s2 := T.sq₂
  have s1' : ∀ b, z₁ * (z₁ * b) = b := fun b => by rw [← mul_assoc, s1, one_mul]
  have c' : ∀ b, z₂ * (z₁ * b) = z₁ * (z₂ * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right s1
  have i2 : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right s2
  have key : ∀ x (hx : x ∈ Subgroup.closure ({z₁, z₂} : Set G)),
      x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₁ * z₂ := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₁ * z₂) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> subst hy <;> simp
    · simp
    · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
        simp [mul_assoc, s1, s2, s1', c, c']
    · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]
  have hsub : (Subgroup.closure ({z₁, z₂} : Set G) : Set G) ⊆
      ({1, z₁, z₂, z₁ * z₂} : Finset G) := by
    intro x hx
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] using key x hx
  have hle : Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) ≤ 4 := by
    calc Nat.card (Subgroup.closure ({z₁, z₂} : Set G))
        = Nat.card ((Subgroup.closure ({z₁, z₂} : Set G) : Set G)) := rfl
      _ ≤ Nat.card (({1, z₁, z₂, z₁ * z₂} : Finset G) : Set G) :=
        Nat.card_mono (Set.toFinite _) hsub
      _ = Finset.card ({1, z₁, z₂, z₁ * z₂} : Finset G) := Nat.card_eq_finsetCard _
      _ ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        simp
  set A₁ : Subgroup G := Subgroup.closure ({z₁} : Set G) with hA₁
  set A₂ : Subgroup G := Subgroup.closure ({z₁, z₂} : Set G) with hA₂
  have h1 : (⊥ : Subgroup G) < A₁ := by
    refine lt_of_le_of_ne bot_le fun hh => T.ne_one₁ ?_
    have : z₁ ∈ A₁ := Subgroup.subset_closure rfl
    rwa [← hh, Subgroup.mem_bot] at this
  have h2 : A₁ < A₂ := by
    refine lt_of_le_of_ne (Subgroup.closure_mono (by simp)) fun hh => ?_
    have : z₂ ∈ A₂ := Subgroup.subset_closure (by simp)
    rw [← hh] at this
    exact T.not_mem_closure_single this
  have c1 := two_mul_card_le_of_lt' h1
  have c2 := two_mul_card_le_of_lt' h2
  have hbot : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
  omega

theorem independent_or_dependent (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) :
    (z₁ * z₂ ≠ z₃ ∧ Nat.card T.group = 8) ∨
      (z₁ * z₂ = z₃ ∧ T.group = Subgroup.closure ({z₁, z₂} : Set G) ∧ Nat.card T.group = 4) := by
  by_cases h : z₁ * z₂ = z₃
  · exact Or.inr ⟨h, T.group_eq_closure_pair h, T.card_eq_four h⟩
  · exact Or.inl ⟨h, T.card_eq_eight h⟩

end ExactTriple

theorem distinctCentralTriple_independent_or_dependent {z : G} {J : Subgroup G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzJ : z ∈ J) (hJ : J ≤ Subgroup.centralizer {z})
    (h : DistinctCentralTriple z J) :
    ∃ g : Fin 3 → G, ∃ T : ExactTriple (J.map (MulAut.conj (g 0)⁻¹).toMonoidHom)
      (J.map (MulAut.conj (g 1)⁻¹).toMonoidHom) (J.map (MulAut.conj (g 2)⁻¹).toMonoidHom)
      ((g 0)⁻¹ * z * g 0) ((g 1)⁻¹ * z * g 1) ((g 2)⁻¹ * z * g 2),
      ((g 0)⁻¹ * z * g 0 * ((g 1)⁻¹ * z * g 1) ≠ (g 2)⁻¹ * z * g 2 ∧ Nat.card T.group = 8) ∨
      ((g 0)⁻¹ * z * g 0 * ((g 1)⁻¹ * z * g 1) = (g 2)⁻¹ * z * g 2 ∧
        Nat.card T.group = 4) := by
  obtain ⟨g, T⟩ := exists_exactTriple_of_distinctCentralTriple hz2 hz1 hzJ hJ h
  refine ⟨g, T, ?_⟩
  rcases T.independent_or_dependent with ⟨hind, hc⟩ | ⟨hd, -, hc⟩
  · exact Or.inl ⟨hind, hc⟩
  · exact Or.inr ⟨hd, hc⟩

theorem stage2_of_rankThreeBalance [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : RankThreeBalance A)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤)
    {𝒦 : Set (Subgroup G)}
    (h𝒦 : ∀ K ∈ 𝒦, K ∈ Ω ∧ ∃ z ∈ A, IsClassicalMember p f K z ∧
      K ≤ Subgroup.centralizer (A : Set G))
    (hne : 𝒦.Nonempty) :
    (∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) ∧ ExactMembers Ω ∧
      ∀ x ∈ A, x ≠ 1 → (∀ K ∈ centMembers Ω x, ∃ L ∈ 𝒦, InCommonComponent x K L) →
        LocalOddCentral Ω {x} := by
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hA
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨hK₀Ω, z₀, hz₀A, hz₀, hK₀A⟩ := h𝒦 K₀ hK₀
  obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two A hA.elem (by rw [hA.card]; norm_num)
  refine ⟨hΔ, ?_, ?_⟩
  · exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH hK₀Ω hz₀
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA.elem hF₀.1)
      (hK₀A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)
  · intro x hxA hx1 hmeet
    refine localOddCentral_of_deltaCore_eq_bot hnab hp2 hq h0 hA1 hΩ hIH hA.elem hA.card hΔ hxA
      hx1 fun K hK => ?_
    obtain ⟨L, hL, hcc⟩ := hmeet K hK
    obtain ⟨hLΩ, z, hzA, hz, hLA⟩ := h𝒦 L hL
    exact ⟨L, hLΩ, z, hzA, hz, hLA, hcc⟩

theorem exactMembers_of_dependent_triple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hΩ₁ : K₁ ∈ Ω) (hz₁ : IsClassicalMember p f K₁ z₁) (hΔ : deltaCore T.group = ⊥) :
    ExactMembers Ω :=
  exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH hΩ₁ hz₁ T.isElemAbelian
    T.le_centralizer₁ hΔ

theorem exactMembers_of_dependent_triple_of_rankThreeBalance [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hd : z₁ * z₂ = z₃) (hΩ₁ : K₁ ∈ Ω) (hz₁ : IsClassicalMember p f K₁ z₁) {A : Subgroup G}
    (hA : RankThreeBalance A) (hBA : T.group ≤ A)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤) :
    deltaCore T.group = ⊥ ∧ ExactMembers Ω := by
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hA
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen T.group
    ⟨hBA, by rw [T.card_eq_four hd]; norm_num⟩
  exact ⟨hΔ, exactMembers_of_dependent_triple hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH T hΩ₁ hz₁ hΔ⟩

end CFSG.ClassicalInvolution.Balance.Bootstrap
