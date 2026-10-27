module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree
public import CFSG.GH74.GLS.Stage2.OddAut.HeisField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidModels
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Criterion

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def starSet (S : LangSetup τ L p) (a : Fin τ.rank → Lˣ) : Set (ModGL τ L) :=
  {x | ∃ i : KernelComponent (rootCharHom a),
    ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧
      x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i}

theorem starSet_subset_Γ (S : LangSetup τ L p) (a : Fin τ.rank → Lˣ) : starSet S a ⊆ S.Γ := by
  rintro x ⟨i, -, hx⟩
  exact (inf_le_right : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ S.Γ)
    (commutator_self_le_self _ hx)

@[expose] def NoFrobeniusInnerOn (S : LangSetup τ L p) (X : Set (ModGL τ L)) : Prop :=
  ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
    ∀ z : ModGL τ L, ¬ ∀ x ∈ X,
      z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x

theorem rigidOn_of_model (S : LangSetup τ L p) {K : Type} [Field K] [Finite K] [Algebra K L]
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p₀ ^ f) (hq : Nat.card K = S.D.q)
    [CharP L p₀] (e : adjointGroup τ K ≃* S.Γ)
    (he : ∀ h : adjointGroup τ K, (e h : ModGL τ L) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0)
    (hnf : ∀ α : MulAut (adjointGroup τ K), ∃ (y : ModGL τ K) (σ : K ≃+* K),
      baseChangeGL (algebraMap K L) y ∈ adjointGroup τ L ∧ ∀ h : adjointGroup τ K,
        (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹)
    (X : Set (ModGL τ L)) (hXΓ : X ⊆ S.Γ) (hF : NoFrobeniusInnerOn S X)
    (hI : ∀ z ∈ adjointGroup τ L, (∀ x ∈ X, Commute z x) → z ^ p = 1)
    (δ : MulAut ↥S.Γ) (hδ : Nat.Coprime p (orderOf δ))
    (hfix : ∀ x : ↥S.Γ, (x : ModGL τ L) ∈ X → δ x = x) : δ = 1 := by
  classical
  have : ExpChar L p₀ := ExpChar.prime hp₀
  have hg0C := S.D.g0_mem
  obtain ⟨y, σ, hyY, hy⟩ := hnf ((e.trans δ).trans e.symm)
  obtain ⟨j, hj, hσj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hp₀ hf hK σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : L →+* L, σ' = iterateFrobenius L p₀ j := ⟨_, rfl⟩
  have hσ'ι : ∀ c : K, σ' (algebraMap K L c) = algebraMap K L (σ.toRingHom c) := fun c => by
    rw [hσ', iterateFrobenius_def, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσj, map_pow]
  have hbase : ∀ g : ModGL τ K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom σ') (baseChangeGL (algebraMap K L) g) := fun g => by
    have h1 : σ'.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom := RingHom.ext hσ'ι
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  obtain ⟨z, hz⟩ : ∃ z : ModGL τ L, z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
      Units.map (entrywiseHom σ') S.D.g0 := ⟨_, rfl⟩
  have hδx : ∀ x : S.Γ, (δ x : ModGL τ L) = z * Units.map (entrywiseHom σ') x * z⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have h1 : δ (e h) = e (((e.trans δ).trans e.symm) h) := by simp
    have h2 : baseChangeGL (algebraMap K L) (h : ModGL τ K) =
        S.D.g0 * (e h : ModGL τ L) * S.D.g0⁻¹ := by
      rw [he]
      group
    rw [h1, he, hy, map_mul, map_mul, map_inv, hbase, h2, map_mul, map_mul, map_inv, hz]
    group
  have hfixX : ∀ x ∈ X, z * Units.map (entrywiseHom σ') x * z⁻¹ = x := by
    intro x hx
    have hxΓ : x ∈ S.Γ := hXΓ hx
    have h1 : δ ⟨x, hxΓ⟩ = ⟨x, hxΓ⟩ := hfix ⟨x, hxΓ⟩ hx
    have h2 := hδx ⟨x, hxΓ⟩
    rw [h1] at h2
    exact h2.symm
  have hj0 : j = 0 := by
    by_contra hj0
    exact hF p₀ f j hp₀ (hq.symm.trans hK) (Nat.pos_of_ne_zero hj0) hj z
      (by rw [hσ'] at hfixX; exact hfixX)
  have hF1 : ∀ x : ModGL τ L, Units.map (entrywiseHom σ') x = x := fun x => by
    rw [hσ', hj0, iterateFrobenius_zero]
    exact Units.ext (entrywise_id _)
  have hzC : z ∈ adjointGroup τ L := by
    have : z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 := by rw [hz, hF1]
    rw [this]
    exact mul_mem (mul_mem (inv_mem S.D.g0_mem) hyY) S.D.g0_mem
  have hcomm : ∀ x ∈ X, Commute z x := by
    intro x hx
    have h1 := hfixX x hx
    rw [hF1] at h1
    show z * x = x * z
    calc z * (x : ModGL τ L) = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [h1]
  have hzp : z ^ p = 1 := hI z hzC hcomm
  have hpow : ∀ n : ℕ, ∀ x : ↥S.Γ, ((δ ^ n) x : ModGL τ L) = z ^ n * x * (z ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro x
      simp
    | succ n ih =>
      intro x
      rw [pow_succ' δ n, MulAut.mul_apply, hδx, hF1, ih, pow_succ' z n, mul_inv_rev]
      simp only [mul_assoc]
  have hδp : δ ^ p = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hpow, hzp]
    simp
  have hdvd : orderOf δ ∣ p := orderOf_dvd_of_pow_eq_one hδp
  have h1 : orderOf δ = 1 := (Nat.Coprime.symm hδ).eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.1 h1

end Criterion

section E8

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rigidOn_E8
    (S : LangSetup .E8 L p) (hp3 : 3 < p) (hAlg : S.IsAlgebraic)
    (X : Set (ModGL .E8 L)) (hXΓ : X ⊆ S.Γ) (hF : NoFrobeniusInnerOn S X)
    (hI : ∀ z ∈ adjointGroup .E8 L, (∀ x ∈ X, Commute z x) → z ^ p = 1)
    (δ : MulAut ↥S.Γ) (hδ : Nat.Coprime p (orderOf δ))
    (hfix : ∀ x : ↥S.Γ, (x : ModGL .E8 L) ∈ X → δ x = x) : δ = 1 := by
  have hd : S.Descends :=
    S.descends_of_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hp3
      (S.exists_frobenius_of_steinberg (by decide) (by decide)) hAlg
      (fun K _ _ => commutator_adjointGroup_E8_eq_top K)
  obtain ⟨K, _, _, _, e, hq, he⟩ := hd
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K L
  refine rigidOn_of_model S hp₀ hf hK hq e he (fun α => ?_) X hXΓ hF hI δ hδ hfix
  obtain ⟨g, a, σ, ε, hα⟩ := (ordinary_E_exact_automorphism_normal_form .E8 (Or.inr (Or.inr rfl))
    K).2.2 α
  have hQ : exactQ .E8 K ε = 1 := rfl
  refine ⟨(g : ModGL .E8 K) * rootDiagUnit .E8 a, σ, ?_, fun h => ?_⟩
  · rw [map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
      (torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _))
  · rw [hα h, hQ, mul_one, inv_one, mul_one, mul_inv_rev]
    group

end E8

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
