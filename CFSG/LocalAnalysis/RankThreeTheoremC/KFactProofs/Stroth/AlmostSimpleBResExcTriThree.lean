module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcTri
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcG2Three
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResPglThree
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Lang.E6Descent (inv_conj_mul_inv)
open CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl (pow_two_pow_even)
open CFSG.HardMathSupport.Lang.E27Lie (two_pow_mod_three_even two_pow_mod_three_odd)
open CFSG.LieType.AlgebraicGroups

theorem fixesPair_of_autFix_pair {C : Type*} [Group C] {τ : MulAut C} {p : ℕ}
    (h : HasIndepPair p ↥(Sec4.autFix τ)) : FixesIndepPair p τ :=
  fixesPair_of_injective_fixed (Sec4.autFix τ).subtype (Subgroup.subtype_injective _)
    (fun y => y.2) h

theorem FixesIndepPair.of_inv {p : ℕ} {P : Type*} [Group P] {α : MulAut P}
    (h : FixesIndepPair p α⁻¹) : FixesIndepPair p α := by
  obtain ⟨y₁, y₂, hc, h1, h2, hi, hf1, hf2⟩ := h
  refine ⟨y₁, y₂, hc, h1, h2, hi, ?_, ?_⟩
  · calc α y₁ = α (α⁻¹ y₁) := by rw [hf1]
      _ = y₁ := MulEquiv.apply_symm_apply α y₁
  · calc α y₂ = α (α⁻¹ y₂) := by rw [hf2]
      _ = y₂ := MulEquiv.apply_symm_apply α y₂

section


theorem exists_conj_class_three {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (y = 1 ∨ y = d4TrialityY0Elt K σ) ∧
        (β * α * β⁻¹ = MulAut.conj y * fieldActor σ σ ∨
          β * α⁻¹ * β⁻¹ = MulAut.conj y * fieldActor σ σ) := by
  have key : ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (MulAut.conj g * fieldActor σ σ) ^ 3 = 1 →
      ∃ (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        (y = 1 ∨ y = d4TrialityY0Elt K σ) ∧
          β * (MulAut.conj g * fieldActor σ σ) * β⁻¹ = MulAut.conj y * fieldActor σ σ := by
    intro g hg3
    obtain ⟨h, y, hy, hyy⟩ := exists_conj_eq_of_geom d4TrialityGeomClasses_holds
      d4DiagramCentIrred_holds d4SecondCentIrred_holds hK hσ g hg3
    refine ⟨(MulAut.conj h⁻¹)⁻¹, y, ?_, ?_⟩
    · rcases hy with h1 | h0
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h0)
    · rw [hyy]
      group
  obtain ⟨g, hg | hg⟩ := Item8ModelProof.exists_conj_mul_sigma hn hK hσ hα3 hαin
  · subst hg
    obtain ⟨β, y, hy, h⟩ := key g hα3
    exact ⟨β, y, hy, Or.inl h⟩
  · have hinv : α⁻¹ = MulAut.conj (fieldActor σ σ g⁻¹) * fieldActor σ σ := by
      rw [hg, inv_conj_mul_inv]
    have h3 : (MulAut.conj (fieldActor σ σ g⁻¹) * fieldActor σ σ) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hα3, inv_one]
    obtain ⟨β, y, hy, h⟩ := key _ h3
    exact ⟨β, y, hy, Or.inr (by rw [hinv]; exact h)⟩

theorem fixesPair_sigma0 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    FixesIndepPair 3 (fieldActor (t := TwistTag.D4) σ σ) := by
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨e⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ) hK2
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : CharP (fixSubfield σ) 2 := RingHom.charP (fixSubfield σ).subtype
    (fixSubfield σ).subtype_injective 2
  have hpair := hasIndepPair_adjointG2_three (fixSubfield σ) (card_fixSubfield_of_cube hn hK hσ)
  exact fixesPair_of_injective_fixed
    ((fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _)).subtype
    (Subgroup.subtype_injective _) (fun y => y.2) (HasIndepPair.of_mulEquiv e.symm hpair)

theorem fixesPair_y0_odd {n : ℕ} (hn : Odd n) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    FixesIndepPair 3 (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) := by
  obtain ⟨F, hFf, hFfin, hcard, ⟨e⟩⟩ := kF82D4SecondCentY0_holds n hn K σ hK hσ
  have h3 : 3 ∣ 2 ^ n + 1 := by
    have := two_pow_mod_three_odd hn
    omega
  have hpair := hasIndepPair_projImage_glPi_false (F := F) (q := 2 ^ n) Nat.one_le_two_pow hcard h3
  exact fixesPair_of_autFix_pair (HasIndepPair.of_mulEquiv e.symm hpair)

theorem fixesPair_y0_even {n : ℕ} (hn : 1 ≤ n) (hne : Even n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    FixesIndepPair 3 (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨μ, hμ⟩ := LangTwisted2Proof.exists_cube_root_unit (L := AlgebraicClosure K)
  set Fr := iterateFrobenius (AlgebraicClosure K) 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hFrμ : Fr (μ : AlgebraicClosure K) = (μ : AlgebraicClosure K) := by
    rw [hFr]
    exact pow_two_pow_even hμ hne
  obtain ⟨e₁⟩ := CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl.nonempty_autFix_equiv_secFixE hn hK hσ hμ hFrμ
  have e₂ := CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl.secFixEEquiv hμ hFrμ
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let _ := ZMod.algebra (AlgebraicClosure K) 2
  let ι : GaloisField 2 n →+* AlgebraicClosure K :=
    (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 n)
      (M := AlgebraicClosure K)).toRingHom
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨G₀, hG⟩ := CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl.exists_secD_fix hq hFr μ
  have e₃ := CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl.pglFixEEquiv ι hq hcard hFr μ hG
  have h3 : 3 ∣ Nat.card (GaloisField 2 n) - 1 := by
    rw [hcard]
    have := two_pow_mod_three_even hne
    omega
  exact fixesPair_of_autFix_pair
    (HasIndepPair.of_mulEquiv (e₁.trans (e₂.trans e₃.symm)).symm (hasIndepPair_pgl_three h3))

theorem fixesPair_graphFixed_three {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    FixesIndepPair 3 α := by
  obtain ⟨β, y, hy, h⟩ := exists_conj_class_three hn hK hσ hα3 hαin
  have hτ : FixesIndepPair 3 (MulAut.conj y * fieldActor (t := TwistTag.D4) σ σ) := by
    rcases hy with rfl | rfl
    · rw [map_one, one_mul]
      exact fixesPair_sigma0 hn hK hσ
    · rcases Nat.even_or_odd n with he | ho
      · exact fixesPair_y0_even hn he hK hσ
      · exact fixesPair_y0_odd ho hK hσ
  have hconj : ∀ γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      β * γ * β⁻¹ = MulAut.conj y * fieldActor σ σ → FixesIndepPair 3 γ := by
    intro γ hγ
    rw [← hγ] at hτ
    have h2 := hτ.map β⁻¹
    have : β⁻¹ * (β * γ * β⁻¹) * β⁻¹⁻¹ = γ := by group
    rwa [this] at h2
  rcases h with h | h
  · exact hconj α h
  · exact FixesIndepPair.of_inv (hconj α⁻¹ h)

theorem chevTwoOuterFixesPair_trialityD4_three :
    ChevTwoOuterFixesPairAt (fun p => p = 3) LieIndexTrialityD4 := by
  intro p hp hp2 hp3 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  subst hp3
  obtain ⟨d, hv⟩ := d
  cases d with
  | trialityD4 q =>
    have hq2 : q.p = 2 := hchar
    have hCEM0 := (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46).trialityD4 q hv hq2
    have hCEM : ChevalleyExceptionalModel L .trialityD4 2 q.exponent :=
      CFSG.RankThree.PartOne.chevalleyExceptionalModel_congr e.symm hCEM0
    obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨eK⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two q.exponent_pos hCEM.2
    apply FixesIndepPair.of_mulEquiv eK
    exact fixesPair_graphFixed_three q.exponent_pos hKcard hσ (by rw [← map_pow, hαp, map_one])
      ((congr_mem_inner_iff eK α).not.2 hα)
  | A _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | B _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | C _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | D _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | E6 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | E7 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | E8 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | F4 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | G2 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | suzuki _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | reeG2 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | reeF4 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | tits => exact absurd hF (by simp [LieIndexTrialityD4])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
