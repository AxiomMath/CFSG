module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidModels
public import CFSG.GH74.GLS.Stage2.OddAut.HeisField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Criterion

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def rigidTestSet (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) :
    Set (ModGL τ L) :=
  bigComponentSet S D₁ ∪ (D₁ : Set (ModGL τ L))

@[expose] def NoFrobeniusInner (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) : Prop :=
  ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
    ∀ z : ModGL τ L, ¬ ∀ x ∈ rigidTestSet S D₁,
      z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x

@[expose] def CentralizerTrivial (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) : Prop :=
  ∀ z ∈ adjointGroup τ L, (∀ x ∈ rigidTestSet S D₁, Commute z x) → z = 1

theorem bigComponentSet_subset_Γ (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) :
    bigComponentSet S D₁ ⊆ S.Γ := by
  rintro x ⟨a, -, -, i, -, hx⟩
  exact (inf_le_right : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ S.Γ)
    (commutator_self_le_self _ hx)

theorem rigidTestSet_subset_Γ (S : LangSetup τ L p) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) :
    rigidTestSet S D₁ ⊆ S.Γ := by
  rintro x (hx | hx)
  · exact bigComponentSet_subset_Γ S D₁ hx
  · exact (S.E_le (hD₁E hx)).2

theorem setupRigid_of_model_gen (S : LangSetup τ L p) {K : Type} [Field K] [Finite K]
    [Algebra K L] {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p₀ ^ f)
    (hq : Nat.card K = S.D.q) [CharP L p₀] (e : adjointGroup τ K ≃* S.Γ)
    (he : ∀ h : adjointGroup τ K, (e h : ModGL τ L) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0)
    (Ycl : Set (ModGL τ L))
    (hnf : ∀ α : MulAut (adjointGroup τ K), ∃ (y : ModGL τ K) (σ : K ≃+* K),
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 ∈ Ycl ∧ ∀ h : adjointGroup τ K,
        (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹)
    (hF : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      ∀ z ∈ Ycl, (∀ x ∈ rigidTestSet S D₁, Commute z x) → ∀ x : S.Γ, Commute z (x : ModGL τ L)) :
    SetupRigid S := by
  classical
  intro D₁ hD₁E hD₁c δ _ hfixD hfixX
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
  have hfix : ∀ x ∈ rigidTestSet S D₁, z * Units.map (entrywiseHom σ') x * z⁻¹ = x := by
    intro x hx
    have hxΓ : x ∈ S.Γ := rigidTestSet_subset_Γ S hD₁E hx
    have h1 : δ ⟨x, hxΓ⟩ = ⟨x, hxΓ⟩ := by
      rcases hx with hx | hx
      · exact hfixX ⟨x, hxΓ⟩ hx
      · exact hfixD ⟨x, hxΓ⟩ hx
    have h2 := hδx ⟨x, hxΓ⟩
    rw [h1] at h2
    exact h2.symm
  have hj0 : j = 0 := by
    by_contra hj0
    exact hF D₁ hD₁E hD₁c p₀ f j hp₀ (hq.symm.trans hK) (Nat.pos_of_ne_zero hj0) hj
      z (by rw [hσ'] at hfix; exact hfix)
  have hF1 : ∀ x : ModGL τ L, Units.map (entrywiseHom σ') x = x := fun x => by
    rw [hσ', hj0, iterateFrobenius_zero]
    exact Units.ext (entrywise_id _)
  have hzY : z ∈ Ycl := by
    have : z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 := by rw [hz, hF1]
    rw [this]
    exact hyY
  have hcomm : ∀ x ∈ rigidTestSet S D₁, Commute z x := by
    intro x hx
    have h1 := hfix x hx
    rw [hF1] at h1
    show z * x = x * z
    calc z * (x : ModGL τ L) = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [h1]
  have hzΓ := hI D₁ hD₁E hD₁c z hzY hcomm
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hδx, hF1]
  have := (hzΓ x).eq
  rw [MulAut.one_apply]
  calc z * (x : ModGL τ L) * z⁻¹ = x * z * z⁻¹ := by rw [this]
    _ = x := by group

theorem setupRigid_of_model (S : LangSetup τ L p) {K : Type} [Field K] [Finite K] [Algebra K L]
    {p₀ f : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p₀ ^ f) (hq : Nat.card K = S.D.q)
    [CharP L p₀] (e : adjointGroup τ K ≃* S.Γ)
    (he : ∀ h : adjointGroup τ K, (e h : ModGL τ L) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0)
    (hnf : ∀ α : MulAut (adjointGroup τ K), ∃ (y : ModGL τ K) (σ : K ≃+* K),
      baseChangeGL (algebraMap K L) y ∈ adjointGroup τ L ∧ ∀ h : adjointGroup τ K,
        (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹)
    (hF : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁) : SetupRigid S := by
  refine setupRigid_of_model_gen S hp₀ hf hK hq e he (adjointGroup τ L : Set (ModGL τ L))
    (fun α => ?_) hF (fun D₁ hD₁ hc z hz hzc x => ?_)
  · obtain ⟨y, σ, hyC, hy⟩ := hnf α
    refine ⟨y, σ, ?_, hy⟩
    exact mul_mem (mul_mem (inv_mem S.D.g0_mem) hyC) S.D.g0_mem
  · rw [hI D₁ hD₁ hc z hz hzc]
    exact Commute.one_left _

end Criterion

section Tags

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem setupRigid_of_descends_E78 (S : LangSetup τ L p) (hτ : τ = .E7 ∨ τ = .E8)
    (hd : S.Descends)
    (hF : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 → NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁) : SetupRigid S := by
  obtain ⟨K, _, _, _, e, hq, he⟩ := hd
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K L
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by rcases hτ with h | h <;> simp [h]
  refine setupRigid_of_model S hp₀ hf hK hq e he (fun α => ?_) hF hI
  obtain ⟨g, a, σ, ε, hα⟩ := (ordinary_E_exact_automorphism_normal_form τ hτ' K).2.2 α
  have hQ : exactQ τ K ε = 1 := by rcases hτ with rfl | rfl <;> rfl
  refine ⟨(g : ModGL τ K) * rootDiagUnit τ a, σ, ?_, fun h => ?_⟩
  · rw [map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
      (torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _))
  · rw [hα h, hQ, mul_one, inv_one, mul_one, mul_inv_rev]
    group

theorem setupRigid_of_descends_F4 (S : LangSetup τ L p) (hτ : τ = .F4) (hodd : Odd S.D.q)
    (hd : S.Descends)
    (hF : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 → NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁) : SetupRigid S := by
  obtain ⟨K, _, _, _, e, hq, he⟩ := hd
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K L
  have hp2 : p₀ ≠ 2 := by
    rintro rfl
    rw [← hq, hK] at hodd
    exact Nat.not_even_iff_odd.2 hodd ((Nat.even_pow' (by omega)).2 even_two)
  refine setupRigid_of_model S hp₀ hf hK hq e he (fun α => ?_) hF hI
  obtain ⟨⟨g, σ⟩, hα, -⟩ := (odd_F4_and_nonexceptional_G2_automorphism_normal_form hp₀ hp2 hf K hK
    τ (Or.inl hτ)).1 α
  exact ⟨g, σ, LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2, hα⟩

theorem setupRigid_E8
    (S : LangSetup .E8 L p) (hp3 : 3 < p) (hAlg : S.IsAlgebraic)
    (hF : ∀ D₁ : Subgroup (ModGL .E8 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL .E8 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁) : SetupRigid S :=
  setupRigid_of_descends_E78 S (Or.inr rfl)
    (S.descends_of_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hp3
      (S.exists_frobenius_of_steinberg (by decide) (by decide)) hAlg
      (fun K _ _ => commutator_adjointGroup_E8_eq_top K)) hF hI

theorem setupRigid_E7
    (S : LangSetup .E7 L p) (hp3 : 3 < p) (hAlg : S.IsAlgebraic)
    (hF : ∀ D₁ : Subgroup (ModGL .E7 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL .E7 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁) : SetupRigid S :=
  setupRigid_of_descends_E78 S (Or.inl rfl)
    (S.descends_of_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hp3
      (S.exists_frobenius_of_steinberg (by decide) (by decide)) hAlg
      (fun K _ _ => commutator_adjointGroup_E7_eq_top K)) hF hI

theorem setupRigid_F4
    (S : LangSetup .F4 L p) (hodd : Odd S.D.q)
    (hF : ∀ D₁ : Subgroup (ModGL .F4 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL .F4 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁) : SetupRigid S :=
  setupRigid_of_descends_F4 S rfl hodd
    (S.descends_of_exact (Or.inr rfl)
      (S.exists_frobenius_of_steinberg (by decide) (by decide))
      (fun K _ _ => commutator_adjointGroup_F4_eq_top K)) hF hI

end Tags

end CFSG.HardMathSupport.Timmesfeld.LangTorus
