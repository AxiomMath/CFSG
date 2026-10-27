module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogEdge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphNormal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Orient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] def SpThreeStandard (e : L ≃* StatedSp 3 K) : Prop :=
  ∀ k l : Fin 3, k ≠ l → ¬ (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k l)

@[expose] def SpThreeTwisted (e : L ≃* StatedSp 3 K) : Prop :=
  ∀ k l : Fin 3, k ≠ l → (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k l)

@[expose] def SpThreeLinearNormalized (e : L ≃* StatedSp 3 K) (t : G) (f : ℕ) (k : Fin 3)
    (b : Bool) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : K ≃+* F)
    (ρ : centralizerPerfectCore (modelToG e (rootTorusSp K k)) →* projectiveSL (2 * 2) F)
    (hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K k)) : Set G)),
    Nat.card F = 2 ^ f ∧ Function.Surjective ρ ∧
      ρ.ker ≤ center (centralizerPerfectCore (modelToG e (rootTorusSp K k))) ∧
      Odd (Nat.card ρ.ker) ∧
      (∀ (x : StatedSp 2 K) (y : centralizerPerfectCore (modelToG e (rootTorusSp K k))),
        (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
          ρ y = spModelPSL 2 F (statedSpMap (σ : K →+* F) 2 (cond b (tauSp x) x))) ∧
      ∀ y, ρ ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).normalizerMonoidHom
          ⟨t, hN⟩ y) =
        (conjAut (2 * 2) F (spBlockSwapGL 2 F) * dualAut (2 * 2) F) (ρ y)

theorem spThreeLinearNormalized_false_or_true {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .linearEven) :
    SpThreeLinearNormalized e t f k false ∨ SpThreeLinearNormalized e t f k true := by
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K k)) : Set G) :=
    le_normalizer_neighbourCore e htC k
  obtain ⟨F, _, _, _, σ, ρ, hF, hρ, hker, hodd, hN1, hN3⟩ :=
    exists_normalized_neighbourCore_linearEven_three hset hKc hf e htC ht k rfl rfl hk hN
  rcases hN1 with h1 | h1
  · exact Or.inl ⟨F, inferInstance, inferInstance, inferInstance, σ, ρ, hN, hF, hρ, hker, hodd,
      h1, hN3⟩
  · exact Or.inr ⟨F, inferInstance, inferInstance, inferInstance, σ, ρ, hN, hF, hρ, hker, hodd,
      h1, hN3⟩

omit [Finite K] in
theorem forall_not_sq_dvd_of_normalized_std {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3} (h : SpThreeLinearNormalized e t f k false) :
    ∀ l : Fin 3, l ≠ k → ¬ (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k l) := by
  obtain ⟨F, _, _, _, σ, ρ, -, -, -, -, hodd, hN1, -⟩ := h
  intro l hlk
  exact not_sq_dvd_natCard_edgeCoreSp_of_std hKc hf e hlk σ ρ hodd hN1

omit [Finite K] in
theorem forall_sq_dvd_of_normalized_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3} (h : SpThreeLinearNormalized e t f k true) :
    ∀ l : Fin 3, l ≠ k → (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k l) := by
  obtain ⟨F, _, _, _, σ, ρ, -, -, hρ, hker, -, hN1, -⟩ := h
  intro l hlk
  exact sq_dvd_natCard_edgeCoreSp_of_twisted hKc hf e hlk σ ρ hρ hker hN1

end Orient

section Same

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem spThreeStandard_or_twisted_linearEven {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hroot : ∀ k : Fin 3, RootKindSp e t f k .linearEven) :
    SpThreeStandard e ∨ SpThreeTwisted e := by
  have hor : ∀ k : Fin 3, (∀ l : Fin 3, l ≠ k → ¬ (Nat.card K) ^ 2 ∣
      Nat.card (edgeCoreSp e k l)) ∨
      (∀ l : Fin 3, l ≠ k → (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k l)) := by
    intro k
    rcases spThreeLinearNormalized_false_or_true hset hKc hf e htC ht k (hroot k) with h | h
    · exact Or.inl (forall_not_sq_dvd_of_normalized_std hKc hf h)
    · exact Or.inr (forall_sq_dvd_of_normalized_twisted hKc hf h)
  rcases hor 0 with h0 | h0
  · refine Or.inl fun k l hkl => ?_
    by_cases hk : k = 0
    · subst hk
      exact h0 l (Ne.symm hkl)
    · rcases hor k with hk' | hk'
      · exact hk' l (Ne.symm hkl)
      · exact absurd (edgeCoreSp_comm e k 0 ▸ hk' 0 (Ne.symm hk)) (h0 k hk)
  · refine Or.inr fun k l hkl => ?_
    by_cases hk : k = 0
    · subst hk
      exact h0 l (Ne.symm hkl)
    · rcases hor k with hk' | hk'
      · exact absurd (edgeCoreSp_comm e 0 k ▸ h0 k hk) (hk' 0 (Ne.symm hk))
      · exact hk' l (Ne.symm hkl)

theorem spThreeLinearNormalized_of_standard {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .linearEven) (hstd : SpThreeStandard e) :
    SpThreeLinearNormalized e t f k false := by
  rcases spThreeLinearNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · exact h
  · obtain ⟨l, hlk⟩ : ∃ l : Fin 3, l ≠ k := ⟨k + 1, by fin_cases k <;> decide⟩
    exact absurd (forall_sq_dvd_of_normalized_twisted hKc hf h l hlk) (hstd k l (Ne.symm hlk))

theorem spThreeLinearNormalized_of_twisted {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .linearEven) (htw : SpThreeTwisted e) :
    SpThreeLinearNormalized e t f k true := by
  rcases spThreeLinearNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · obtain ⟨l, hlk⟩ : ∃ l : Fin 3, l ≠ k := ⟨k + 1, by fin_cases k <;> decide⟩
    exact absurd (htw k l (Ne.symm hlk)) (forall_not_sq_dvd_of_normalized_std hKc hf h l hlk)
  · exact h

end Same

@[expose] def SpThreeLinearEvenStandardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .linearEven) → SpThreeStandard e →
        SpGlobalCoverType e f .linearEven

@[expose] def SpThreeLinearEvenTwistedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .linearEven) → SpThreeTwisted e →
        Sp2mKindType (spGlobal e) 3 f .omegaPlus

theorem spThreeLinearEvenRecognitionInput_of_oriented
    (hs : SpThreeLinearEvenStandardInput) (ht : SpThreeLinearEvenTwistedInput) :
    SpThreeLinearEvenRecognitionInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot
  have htC : t ∈ centralizer (L : Set G) := by
    have h1 : t ∈ zpowers t := mem_zpowers t
    rw [← hKt] at h1
    exact h1.1
  rcases spThreeStandard_or_twisted_linearEven hset hKc hf e htC hto hroot with h | h
  · exact Or.inl (hs G L hset f K hKc hf e t hto hKt hroot h)
  · exact Or.inr (ht G L hset f K hKc hf e t hto hKt hroot h)

end CFSG.SeitzReduction.SymplecticPilot
