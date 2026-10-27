module

public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.Phan Matrix

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def tvAt (σ : K ≃+* K) {n : ℕ} (a : Fin n → K) : Set (SUid σ n) :=
  {g | ∃ x : K, x + σ x = 0 ∧ ∀ v, g • v = v + (x * herm σ a v) • a}

theorem tv_mem_tvAt (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) : tv hσ ha hc ∈ tvAt σ a :=
  ⟨c, hc, tv_smul hσ ha hc⟩

theorem exists_eq_tv_of_mem_tvAt (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {a : Fin n → K}
    (ha : herm σ a a = 0) {g : SUid σ n} (hg : g ∈ tvAt σ a) :
    ∃ (c : K) (hc : c + σ c = 0), g = tv hσ ha hc := by
  obtain ⟨x, hx, h⟩ := hg
  exact ⟨x, hx, ext_smul σ fun v => by rw [h, tv_smul]⟩

theorem mem_closure_tvAt_two (hσ : IsUnitaryInvolution σ) {a b : Fin 2 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1)
    (hexp : ∀ v, v = herm σ b v • a + herm σ a v • b) (hP : a 0 * b 1 - b 0 * a 1 ≠ 0)
    (A : SUid σ 2) : A ∈ Subgroup.closure (tvAt σ a ∪ tvAt σ b) := by
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ.invol, hab, map_one]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hab
    exact zero_ne_one hab
  have hsmul : ∀ (g : SUid σ 2) (v : Fin 2 → K),
      g • v = herm σ b v • (g • a) + herm σ a v • (g • b) := by
    intro g v
    conv_lhs => rw [hexp v]
    rw [smul_add, smul_comm, smul_comm g (herm σ a v)]
  have hmemA : ∀ {c : K} (hc : c + σ c = 0),
      tv hσ.invol ha hc ∈ Subgroup.closure (tvAt σ a ∪ tvAt σ b) :=
    fun hc => Subgroup.subset_closure (Or.inl (tv_mem_tvAt hσ.invol ha hc))
  have hmemB : ∀ {c : K} (hc : c + σ c = 0),
      tv hσ.invol hb hc ∈ Subgroup.closure (tvAt σ a ∪ tvAt σ b) :=
    fun hc => Subgroup.subset_closure (Or.inr (tv_mem_tvAt hσ.invol hb hc))
  have key : ∀ A : SUid σ 2, herm σ a (A • a) ≠ 0 →
      A ∈ Subgroup.closure (tvAt σ a ∪ tvAt σ b) := by
    intro A hγ
    set α := herm σ b (A • a) with hα
    set γ := herm σ a (A • a) with hγdef
    set β := herm σ b (A • b) with hβ
    set δ := herm σ a (A • b) with hδ
    have hAa : A • a = α • a + γ • b := hexp _
    have hAb : A • b = β • a + δ • b := hexp _
    have e1 : σ α * γ + σ γ * α = 0 := by
      have := herm_smul_smul σ A a a
      rw [hAa, ha] at this
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
        hba] at this
      linear_combination this
    have e2 : σ β * δ + σ δ * β = 0 := by
      have := herm_smul_smul σ A b b
      rw [hAb, hb] at this
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
        hba] at this
      linear_combination this
    have e3 : σ α * δ + σ γ * β = 1 := by
      have := herm_smul_smul σ A a b
      rw [hAa, hAb, hab] at this
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab,
        hba] at this
      linear_combination this
    have e3' : α * σ δ + γ * σ β = 1 := by
      have := congrArg σ e3
      simp only [map_add, map_mul, hσ.invol, map_one] at this
      linear_combination this
    have e4 : α * δ - β * γ = 1 := by
      have hdet := ((mem_SUid_iff σ).mp A.2).1
      rw [det_eq_of_basis (a := a) (b := b) hAa hAb hP] at hdet
      exact hdet
    have hσγ : σ γ = -γ := by linear_combination (-σ γ) * e4 + δ * e1 - γ * e3
    have hσα : σ α = α := by linear_combination (-σ α) * e4 + α * e3 - β * e1
    have hσδ : σ δ = δ := by linear_combination (-σ δ) * e4 + δ * e3' - γ * e2
    have hσβ : σ β = -β := by linear_combination (-σ β) * e4 + α * e2 - β * e3'
    have hγE : γ + σ γ = 0 := by rw [hσγ]; ring
    have hx : (α - 1) / γ + σ ((α - 1) / γ) = 0 := by
      rw [map_div₀, map_sub, map_one, hσα, hσγ, div_neg]; ring
    have hy : (δ - 1) / γ + σ ((δ - 1) / γ) = 0 := by
      rw [map_div₀, map_sub, map_one, hσδ, hσγ, div_neg]; ring
    set t := tv hσ.invol ha hx * tv hσ.invol hb hγE * tv hσ.invol ha hy with ht
    have hta : t • a = A • a := by
      rw [ht, mul_smul, mul_smul, tv_smul, tv_smul, tv_smul, hAa]
      simp only [herm_add_right, herm_smul_right, ha, hab, hba, mul_zero, zero_smul,
        add_zero, mul_one]
      match_scalars
      all_goals field_simp
      all_goals ring
    have htb : t • b = A • b := by
      rw [ht, mul_smul, mul_smul, tv_smul, tv_smul, tv_smul, hAb]
      simp only [herm_add_right, herm_smul_right, ha, hb, hab, hba, mul_zero,
        add_zero, mul_one, zero_add]
      match_scalars
      all_goals field_simp
      all_goals first | linear_combination e4 | ring
    have hA : A = t := by
      apply ext_smul
      intro v
      rw [hsmul A v, hsmul t v, hta, htb]
    rw [hA, ht]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmemA _) (hmemB _)) (hmemA _)
  by_cases hγ : herm σ a (A • a) = 0
  · obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
    have hα : herm σ b (A • a) ≠ 0 := by
      intro hα
      have h0 : A • a = 0 := by rw [hexp (A • a), hα, hγ, zero_smul, zero_smul, add_zero]
      exact ha0 ((smul_eq_zero_iff_eq A).mp h0)
    have hB : herm σ a ((tv hσ.invol hb hτ * A) • a) ≠ 0 := by
      rw [mul_smul, tv_smul, herm_add_right, herm_smul_right, hγ, hab, zero_add, mul_one]
      exact mul_ne_zero hτ0 hα
    have hA : A = (tv hσ.invol hb hτ)⁻¹ * (tv hσ.invol hb hτ * A) := by group
    rw [hA]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmemB _)) (key _ hB)
  · exact key A hγ


@[expose] def insZero (c : Fin 3) (v : Fin 2 → K) : Fin 3 → K :=
  if c = 0 then ![0, v 0, v 1] else if c = 1 then ![v 0, 0, v 1] else ![v 0, v 1, 0]

theorem herm_insZero (c : Fin 3) (v w : Fin 2 → K) :
    herm σ (insZero c v) (insZero c w) = herm σ v w := by
  fin_cases c <;> simp [insZero, herm, Fin.sum_univ_three, Fin.sum_univ_two]

theorem insZero_self (c : Fin 3) (v : Fin 2 → K) : insZero c v c = 0 := by
  fin_cases c <;> simp [insZero]

theorem smul_insZero (c : Fin 3) (A : SUid σ 2) (v : Fin 2 → K) :
    embSUid σ c A • insZero c v = insZero c (A • v) := by
  rw [smul_def, coe_embSUid, smul_def]
  fin_cases c <;> ext i <;> fin_cases i <;>
    simp [embPair, insZero, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three]

theorem embSUid_tv (hσ : ∀ c, σ (σ c) = c) (c : Fin 3) {a : Fin 2 → K} (ha : herm σ a a = 0)
    {x : K} (hx : x + σ x = 0) :
    embSUid σ c (tv hσ ha hx) =
      tv hσ (show herm σ (insZero c a) (insZero c a) = 0 by rw [herm_insZero, ha]) hx := by
  refine ext_smul σ fun w => ?_
  rw [tv_smul, smul_def, coe_embSUid]
  show embPair c (tvMat σ a x) *ᵥ w = _
  fin_cases c <;> ext i <;> fin_cases i <;>
    simp [embPair, tvMat, insZero, Matrix.mulVec, dotProduct, herm, Matrix.vecMulVec_apply,
      Fin.sum_univ_three] <;> ring

theorem closure_tvAt_insZero (hσ : IsUnitaryInvolution σ) (W : WittData σ) (c : Fin 3) :
    Subgroup.closure (tvAt σ (insZero c (W.hypA 0)) ∪ tvAt σ (insZero c (W.hypB 0))) =
      (embSUid σ c).range := by
  have ha : herm σ (W.hypA 0) (W.hypA 0) = 0 := W.herm_hypA_hypA
  have hb : herm σ (W.hypB 0) (W.hypB 0) = 0 := W.herm_hypB_hypB
  have hab : herm σ (W.hypA 0) (W.hypB 0) = 1 := W.herm_hypA_hypB
  have hP : W.hypA 0 0 * W.hypB 0 1 - W.hypB 0 0 * W.hypA 0 1 ≠ 0 := by
    simp only [WittData.hypA_zero, WittData.hypA_one, WittData.hypB_zero, WittData.hypB_one]
    have h : (1 : K) * ((1 - W.ω)⁻¹ * (W.u * W.ω)) - (1 - W.ω)⁻¹ * W.u = -W.u := by
      field_simp [W.one_sub_ω_ne_zero]
      ring
    rw [h]
    exact neg_ne_zero.mpr W.u_ne_zero
  have ha' : herm σ (insZero c (W.hypA 0)) (insZero c (W.hypA 0)) = 0 := by rw [herm_insZero, ha]
  have hb' : herm σ (insZero c (W.hypB 0)) (insZero c (W.hypB 0)) = 0 := by rw [herm_insZero, hb]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · obtain ⟨x, hx, rfl⟩ := exists_eq_tv_of_mem_tvAt hσ.invol ha' hg
      exact ⟨tv hσ.invol ha hx, embSUid_tv hσ.invol c ha hx⟩
    · obtain ⟨x, hx, rfl⟩ := exists_eq_tv_of_mem_tvAt hσ.invol hb' hg
      exact ⟨tv hσ.invol hb hx, embSUid_tv hσ.invol c hb hx⟩
  · rintro _ ⟨A, rfl⟩
    have hA := mem_closure_tvAt_two hσ ha hb hab (W.eq_hyp_expansion hσ.invol) hP A
    have hle : (Subgroup.closure (tvAt σ (W.hypA 0) ∪ tvAt σ (W.hypB 0))).map (embSUid σ c) ≤
        Subgroup.closure (tvAt σ (insZero c (W.hypA 0)) ∪ tvAt σ (insZero c (W.hypB 0))) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg | hg, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := exists_eq_tv_of_mem_tvAt hσ.invol ha hg
        rw [embSUid_tv]
        exact Subgroup.subset_closure (Or.inl (tv_mem_tvAt hσ.invol ha' hx))
      · obtain ⟨x, hx, rfl⟩ := exists_eq_tv_of_mem_tvAt hσ.invol hb hg
        rw [embSUid_tv]
        exact Subgroup.subset_closure (Or.inr (tv_mem_tvAt hσ.invol hb' hx))
    exact hle ⟨A, hA, rfl⟩

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
