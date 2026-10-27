module

public import CFSG.ClassicalGroups.Orthogonal.SiegelSLPlane
public import CFSG.ClassicalGroups.Orthogonal.SiegelSLTwist
import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelSL

open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 CFSG.CGT.Timmesfeld75
open CFSG.CGT.T75E QuadraticMap Module Matrix
open scoped MatrixGroups

section Assembly

variable {K : Type} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m' : ℕ} {Qf : QuadraticForm K V} {ρ : SL(m' + 2, K) →* (V ≃ₗ[K] V)}

omit [Finite K] [FiniteDimensional K V] in
theorem invT_tvSL {n : ℕ} {c a : Fin n → K} (h : a ⬝ᵥ c = 0) :
    invT (tvSL c a h) = tvSL a c (by rw [dotProduct_comm]; exact h) := by
  apply Subtype.ext
  rw [coe_invT_tvSL, coe_tvSL]

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem movedSpace_one' : movedSpace (1 : V ≃ₗ[K] V) = ⊥ := by
  have h : ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) - 1 = 0 := by
    ext
    simp
  rw [movedSpace, h, LinearMap.range_zero]

omit [CharP K 2] [Finite K] in
private theorem transvection_eq_tvSL {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : K)
    (h : (Pi.single j (1 : K) : Fin n → K) ⬝ᵥ (c • Pi.single i 1) = 0) :
    Matrix.SpecialLinearGroup.transvection hij c = tvSL (c • Pi.single i 1) (Pi.single j 1) h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.transvection_coe, coe_tvSL]
  congr 1
  ext a b
  rw [Matrix.single_apply, vecMulVec_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply]
  by_cases ha : i = a <;> by_cases hb : j = b <;> simp [ha, hb, eq_comm]

theorem SLSetting.sup_eq_top_of_isStar (hs : SLSetting Qf ρ) (hV : commutatorSpace ρ.range = ⊤)
    (hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ))
    (hst' : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map (ρ.comp invT)))
    {F F' : (Fin (m' + 2) → K) →+ V} {W₁ W₂ : Submodule K V} (hF₁ : ∀ x, F x ∈ W₁)
    (hF₂ : ∀ x, F' x ∈ W₂)
    (hP₁ : ∀ c : Fin (m' + 2) → K, c ≠ 0 →
      axisInf ((tvCenterSL c).map ρ) = Submodule.span K {F c})
    (hP₂ : ∀ α : Fin (m' + 2) → K, α ≠ 0 →
      axisInf ((tvCenterSL α).map (ρ.comp invT)) = Submodule.span K {F' α}) :
    W₁ ⊔ W₂ = ⊤ := by
  have hm2 : 2 ≤ m' + 2 := by omega
  have he₀ : (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) ≠ 0 := fun h => by
    simpa using congrFun h 0
  have hstc : ∀ c : Fin (m' + 2) → K, c ≠ 0 → IsStar ((tvCenterSL c).map ρ) := fun c hc =>
    (isStar_map_center_iff ρ hm2 hc he₀).mpr hst
  have hsta : ∀ α : Fin (m' + 2) → K, α ≠ 0 → IsStar ((tvAxisSL α).map ρ) := fun α hα => by
    rw [← map_comp_invT_center]
    exact (isStar_map_center_iff (ρ.comp invT) hm2 hα he₀).mpr hst'
  have hle : commutatorSpace ρ.range ≤ W₁ ⊔ W₂ := by
    refine commutatorSpace_range_le ρ
      (CFSG.ClassicalGroups.SpecialLinear.closure_transvection_eq_top) ?_
    rintro x ⟨i, j, hij, c, rfl⟩
    by_cases hc : c = 0
    · subst hc
      rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one, movedSpace_one']
      exact bot_le
    have h : (Pi.single j (1 : K) : Fin (m' + 2) → K) ⬝ᵥ (c • Pi.single i 1) = 0 := by
      simp [dotProduct_single, hij]
    rw [transvection_eq_tvSL hij c h]
    have hci : c • (Pi.single i (1 : K) : Fin (m' + 2) → K) ≠ 0 := fun h0 => by
      have := congrFun h0 i
      simp [hc] at this
    have hej : (Pi.single j (1 : K) : Fin (m' + 2) → K) ≠ 0 := fun h0 => by
      simpa using congrFun h0 j
    have hmem : tvSL (c • Pi.single i 1) (Pi.single j 1) h ∈
        tvCenterSL (c • (Pi.single i (1 : K) : Fin (m' + 2) → K)) ⊓
          tvAxisSL (Pi.single j (1 : K) : Fin (m' + 2) → K) :=
      ⟨⟨Pi.single j 1, h, rfl⟩, ⟨c • Pi.single i 1, h, rfl⟩⟩
    have hne1 : tvSL (c • Pi.single i 1) (Pi.single j 1) h ≠ 1 := fun h1 => by
      have := hs.siegel _ _ h hci hej
      rw [h1, map_one] at this
      exact not_isLongRootElement_one hs.nondeg this
    rw [hs.movedSpace_eq_sup_of_isStar hci hej h (hstc _ hci) (hsta _ hej) hmem hne1]
    refine sup_le_sup ?_ ?_
    · rw [hP₁ _ hci, Submodule.span_singleton_le_iff_mem]
      exact hF₁ _
    · rw [← map_comp_invT_center, hP₂ _ hej, Submodule.span_singleton_le_iff_mem]
      exact hF₂ _
  rw [hV] at hle
  exact top_le_iff.mp hle

theorem SLSetting.rt1_of_isStar (hs : SLSetting Qf ρ) (hV : commutatorSpace ρ.range = ⊤)
    (hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ))
    (hst' : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map (ρ.comp invT))) :
    ∃ W₁ W₂ : Submodule K V, IsCompl W₁ W₂ ∧
      (∀ w ∈ W₁, Qf w = 0) ∧ (∀ w ∈ W₂, Qf w = 0) ∧
      (∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
      finrank K W₁ = m' + 2 ∧ finrank K V = 2 * (m' + 2) ∧
      (∃ (σ : K ≃+* K) (F : (Fin (m' + 2) → K) →+ V), (∀ (c : K) x, F (c • x) = σ c • F x) ∧
        Function.Injective F ∧ (∀ x, F x ∈ W₁) ∧ (∀ w ∈ W₁, ∃ x, F x = w) ∧
        ∀ (g : SL(m' + 2, K)) x,
          F ((g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ x) = ρ g (F x)) ∧
      ∃ (σ' : K ≃+* K) (F' : (Fin (m' + 2) → K) →+ V), (∀ (c : K) x, F' (c • x) = σ' c • F' x) ∧
        Function.Injective F' ∧ (∀ x, F' x ∈ W₂) ∧ (∀ w ∈ W₂, ∃ x, F' x = w) ∧
        ∀ (g : SL(m' + 2, K)) x,
          F' (((g⁻¹ : SL(m' + 2, K)) : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K)ᵀ *ᵥ x) =
            ρ g (F' x) := by
  obtain ⟨σ, F, W₁, hσ, hinj, hF, hFW, hWF, hW₁, hdim₁, hP₁⟩ := hs.exists_twisted_of_isStar hst
  obtain ⟨σ', F', W₂, hσ', hinj', hF', hFW', hWF', hW₂, hdim₂, hP₂⟩ :=
    hs.comp_invT.exists_twisted_of_isStar hst'
  have hF'g : ∀ (g : SL(m' + 2, K)) x,
      F' (((g⁻¹ : SL(m' + 2, K)) : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K)ᵀ *ᵥ x) =
        ρ g (F' x) := fun g x => by
    have := hF' (invT g) x
    rwa [coe_invT, MonoidHom.comp_apply, invT_invT] at this
  have hinv₁ : ∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁ := fun g w hw => by
    obtain ⟨x, rfl⟩ := hWF w hw
    rw [← hF]
    exact hFW _
  have hinv₂ : ∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂ := fun g w hw => by
    obtain ⟨x, rfl⟩ := hWF' w hw
    rw [← hF'g]
    exact hFW' _
  have htop : W₁ ⊔ W₂ = ⊤ := hs.sup_eq_top_of_isStar hV hst hst' hFW hFW' hP₁ hP₂
  have h2m := hs.two_mul_le_finrank_of_isStar hst
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  rw [htop, finrank_top] at hsum
  have hinf : finrank K ↥(W₁ ⊓ W₂) = 0 := by omega
  have hbot : W₁ ⊓ W₂ = ⊥ := Submodule.finrank_eq_zero.mp hinf
  refine ⟨W₁, W₂, ⟨disjoint_iff.mpr hbot, codisjoint_iff.mpr htop⟩, hW₁, hW₂, hinv₁, hinv₂,
    by omega, by omega, ⟨σ, F, hσ, hinj, hFW, hWF, hF⟩, σ', F', hσ', hinj', hFW', hWF', hF'g⟩

end Assembly

theorem exists_natural_or_dim_six_of_siegel {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hm : 3 ≤ m) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hS₀ : ∃ t₀ : SL(m, K), IsTransvection t₀ ∧
      finrank K (movedSpace (ρ t₀)) = 2 ∧ ∀ w ∈ movedSpace (ρ t₀), Qf w = 0)
    (hV : commutatorSpace ρ.range = ⊤) :
    (∃ W₁ W₂ : Submodule K V, IsCompl W₁ W₂ ∧
      (∀ w ∈ W₁, Qf w = 0) ∧ (∀ w ∈ W₂, Qf w = 0) ∧
      (∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
      finrank K W₁ = m ∧ finrank K V = 2 * m ∧
      (∃ (σ : K ≃+* K) (F : (Fin m → K) →+ V), (∀ (c : K) x, F (c • x) = σ c • F x) ∧
        Function.Injective F ∧ (∀ x, F x ∈ W₁) ∧ (∀ w ∈ W₁, ∃ x, F x = w) ∧
        ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x)) ∧
      ∃ (σ' : K ≃+* K) (F' : (Fin m → K) →+ V), (∀ (c : K) x, F' (c • x) = σ' c • F' x) ∧
        Function.Injective F' ∧ (∀ x, F' x ∈ W₂) ∧ (∀ w ∈ W₂, ∃ x, F' x = w) ∧
        ∀ (g : SL(m, K)) x,
          F' (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) = ρ g (F' x)) ∨
    (m = 4 ∧ finrank K V = 6 ∧
      ∃ t₁ t₂ : SL(m, K), IsTransvection t₁ ∧ IsTransvection t₂ ∧ t₁ * t₂ = t₂ * t₁ ∧
        finrank K ↥(movedSpace (ρ t₁) ⊓ movedSpace (ρ t₂)) = 1 ∧
        ¬ movedSpace (ρ t₁) ≤
          LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace (ρ t₂))) := by
  have hs := slSetting_of_contract hm Qf hnd ρ hρQ hS₀
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hs' := hs.comp_invT
  have hV' : commutatorSpace (ρ.comp invT).range = ⊤ := by rw [range_comp_invT]; exact hV
  by_cases hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)
  · by_cases hst' :
        IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map (ρ.comp invT))
    · exact Or.inl (hs.rt1_of_isStar hV hst hst')
    ·
      right
      have h4 := (hs'.finrank_commutatorSpace_center_eq_three hst').2
      have h1 := hs'.ne_one_of_not_isStar hst'
      obtain rfl : m' = 2 := by omega
      refine ⟨rfl, hs'.finrank_eq_six_of_not_isStar hV' hst', ?_⟩
      obtain ⟨c₁, a₁, c₂, a₂, h₁, h₂, hc₁, ha₁, hc₂, ha₂, hcomm, hmeet, hnorth⟩ :=
        hs'.exists_config_of_not_isStar hst'
      refine ⟨tvSL a₁ c₁ (by rw [dotProduct_comm]; exact h₁),
        tvSL a₂ c₂ (by rw [dotProduct_comm]; exact h₂),
        isTransvection_of_coe ha₁ hc₁ (by rw [dotProduct_comm]; exact h₁) (coe_tvSL _),
        isTransvection_of_coe ha₂ hc₂ (by rw [dotProduct_comm]; exact h₂) (coe_tvSL _), ?_, ?_, ?_⟩
      · rw [← invT_tvSL h₁, ← invT_tvSL h₂, ← map_mul, ← map_mul, hcomm]
      · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, invT_tvSL h₁, invT_tvSL h₂] at hmeet
        exact hmeet
      · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, invT_tvSL h₁, invT_tvSL h₂] at hnorth
        exact hnorth
  ·
    right
    have h4 := (hs.finrank_commutatorSpace_center_eq_three hst).2
    have h1 := hs.ne_one_of_not_isStar hst
    obtain rfl : m' = 2 := by omega
    refine ⟨rfl, hs.finrank_eq_six_of_not_isStar hV hst, ?_⟩
    obtain ⟨c₁, a₁, c₂, a₂, h₁, h₂, hc₁, ha₁, hc₂, ha₂, hcomm, hmeet, hnorth⟩ :=
      hs.exists_config_of_not_isStar hst
    exact ⟨tvSL c₁ a₁ h₁, tvSL c₂ a₂ h₂, isTransvection_of_coe hc₁ ha₁ h₁ (coe_tvSL h₁),
      isTransvection_of_coe hc₂ ha₂ h₂ (coe_tvSL h₂), hcomm, hmeet, hnorth⟩

theorem exists_isTransvection_eq_of_movedSpace_eq {K : Type} [Field K] [Finite K]
    [CharP K 2] {m : ℕ} {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hm : 3 ≤ m) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : SL(m, K) →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hS₀ : ∃ t₀ : SL(m, K), IsTransvection t₀ ∧
      finrank K (movedSpace (ρ t₀)) = 2 ∧ ∀ w ∈ movedSpace (ρ t₀), Qf w = 0)
    {t : SL(m, K)} (ht : IsTransvection t)
    {s : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) (hst : movedSpace s = movedSpace (ρ t)) :
    ∃ g : SL(m, K), IsTransvection g ∧ g * t = t * g ∧ ρ g = s :=
  (slSetting_of_contract hm Qf hnd ρ hρQ hS₀).exists_isTransvection_eq ht hs hst

end CFSG.ClassicalGroups.Orthogonal.SiegelSL
