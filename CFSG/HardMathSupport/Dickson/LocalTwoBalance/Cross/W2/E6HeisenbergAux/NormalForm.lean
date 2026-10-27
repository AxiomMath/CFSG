module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidE6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley


section Model

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem normal_form_of_model_testSet (S : LangSetup τ L p) {K : Type} [Field K] [Finite K]
    [Algebra K L] {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p₀ ^ f)
    (hq : Nat.card K = S.D.q) [CharP L p₀] (e : adjointGroup τ K ≃* S.Γ)
    (he : ∀ h : adjointGroup τ K, (e h : ModGL τ L) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0)
    (Ycl : Set (ModGL τ L))
    (hnf : ∀ α : MulAut (adjointGroup τ K), ∃ (y : ModGL τ K) (σ : K ≃+* K),
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 ∈ Ycl ∧ ∀ h : adjointGroup τ K,
        (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹)
    (X : Set (ModGL τ L)) (hXΓ : X ⊆ S.Γ)
    (hF : ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL τ L, ¬ ∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x)
    (δ : MulAut S.Γ) (hfix : ∀ x : S.Γ, (x : ModGL τ L) ∈ X → δ x = x) :
    ∃ z ∈ Ycl, (∀ x : S.Γ, (δ x : ModGL τ L) = z * x * z⁻¹) := by
  classical
  have : ExpChar L p₀ := ExpChar.prime hp₀
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
  have hfix' : ∀ x ∈ X, z * Units.map (entrywiseHom σ') x * z⁻¹ = x := by
    intro x hx
    have h1 : δ ⟨x, hXΓ hx⟩ = ⟨x, hXΓ hx⟩ := hfix ⟨x, hXΓ hx⟩ hx
    have h2 := hδx ⟨x, hXΓ hx⟩
    rw [h1] at h2
    exact h2.symm
  have hj0 : j = 0 := by
    by_contra hj0
    exact hF p₀ f j hp₀ (hq.symm.trans hK) (Nat.pos_of_ne_zero hj0) hj
      z (by rw [hσ'] at hfix'; exact hfix')
  have hF1 : ∀ x : ModGL τ L, Units.map (entrywiseHom σ') x = x := fun x => by
    rw [hσ', hj0, iterateFrobenius_zero]
    exact Units.ext (entrywise_id _)
  have hzY : z ∈ Ycl := by
    have : z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 := by rw [hz, hF1]
    rw [this]
    exact hyY
  exact ⟨z, hzY, fun x => by rw [hδx, hF1]⟩

end Model

section E6

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem normal_form_E6 (S : LangSetup .E6 L p) (hd : S.Descends) (X : Set (ModGL .E6 L))
    (hXΓ : X ⊆ S.Γ)
    (hF : ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL .E6 L,
        ¬ ∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x)
    (δ : MulAut S.Γ) (hfix : ∀ x : S.Γ, (x : ModGL .E6 L) ∈ X → δ x = x) :
    ∃ z : ModGL .E6 L, (z ∈ adjointGroup .E6 L ∨ ∃ w ∈ adjointGroup .E6 L, z = w * graphP L) ∧
      ∀ x : S.Γ, (δ x : ModGL .E6 L) = z * x * z⁻¹ := by
  obtain ⟨K, _, _, _, e, hq, he⟩ := hd
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K L
  have hnf : ∀ α : MulAut (adjointGroup .E6 K), ∃ (y : ModGL .E6 K) (σ : K ≃+* K),
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 ∈
        {z : ModGL .E6 L | z ∈ adjointGroup .E6 L ∨ ∃ w ∈ adjointGroup .E6 L, z = w * graphP L} ∧
      ∀ h : adjointGroup .E6 K,
        (α h : ModGL .E6 K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E6 K) * y⁻¹ := by
    intro α
    obtain ⟨g, a, σ, ε, hα⟩ :=
      (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 α
    refine ⟨(g : ModGL .E6 K) * rootDiagUnit .E6 a * exactQ .E6 K ε, σ, ?_, fun h => ?_⟩
    · have hga : baseChangeGL (algebraMap K L) ((g : ModGL .E6 K) * rootDiagUnit .E6 a) ∈
          adjointGroup .E6 L := by
        rw [map_mul, baseChangeGL_rootDiagUnit]
        exact mul_mem (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
          (torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _))
      have hg0 := S.D.g0_mem
      have hP : ∀ x ∈ adjointGroup .E6 L,
          graphP L * x * (graphP L)⁻¹ ∈ adjointGroup .E6 L :=
        fun x hx => E6GraphLevi.diagramMap_conj_mem_adjointGroup' hx
      fin_cases ε
      · left
        have hQ : exactQ .E6 K ((0 : Fin 2) : ℕ) = 1 := pow_zero (graphP K)
        simp only [Fin.val_zero] at hQ ⊢
        rw [hQ, mul_one]
        exact mul_mem (mul_mem (inv_mem hg0) hga) hg0
      · right
        refine ⟨S.D.g0⁻¹ * baseChangeGL (algebraMap K L) ((g : ModGL .E6 K) * rootDiagUnit .E6 a) *
          (graphP L * S.D.g0 * (graphP L)⁻¹), ?_, ?_⟩
        · exact mul_mem (mul_mem (inv_mem hg0) hga) (hP _ hg0)
        · have hQ : exactQ .E6 K ((1 : Fin 2) : ℕ) = graphP K := pow_one (graphP K)
          have hbc : baseChangeGL (algebraMap K L) (graphP K) = graphP L :=
            baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6
          simp only [Fin.val_one] at hQ ⊢
          rw [hQ, map_mul, hbc]
          group
    · rw [hα h, mul_inv_rev, mul_inv_rev]
      group
  obtain ⟨z, hz, hδ⟩ := normal_form_of_model_testSet S hp₀ hf hK hq e he _ hnf X hXΓ hF δ hfix
  exact ⟨z, hz, hδ⟩

@[expose] def NormalFormAt (S : LangSetup .E6 L p) : Prop :=
  ∀ (X : Set (ModGL .E6 L)), X ⊆ S.Γ →
    (∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL .E6 L,
        ¬ ∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x) →
    ∀ δ : MulAut S.Γ, (∀ x : S.Γ, (x : ModGL .E6 L) ∈ X → δ x = x) →
      ∃ z : ModGL .E6 L, (z ∈ adjointGroup .E6 L ∨ ∃ w ∈ adjointGroup .E6 L, z = w * graphP L) ∧
        ∀ x : S.Γ, (δ x : ModGL .E6 L) = z * x * z⁻¹

theorem normalFormAt_of_descends (S : LangSetup .E6 L p) (hd : S.Descends) : NormalFormAt S :=
  fun X hXΓ hF δ hfix => normal_form_E6 S hd X hXΓ hF δ hfix

@[expose] def FaithfulAt (S : LangSetup .E6 L p) : Prop :=
  ∀ v ∈ adjointGroup .E6 L, (∀ y : S.Γ, Commute v (y : ModGL .E6 L)) → v = 1

end E6

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
