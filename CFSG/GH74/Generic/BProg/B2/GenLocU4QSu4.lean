module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenAux
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

namespace GenLocU4QSu4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem raw_of_sigma (σ : K ≃+* K) (hfun : (fun x : K => x ^ (p ^ f)) = σ) {M : Matrix (Fin 4) (Fin 4) K}
    (h : (M.map σ)ᵀ * M = 1) : (M.map (· ^ (p ^ f)))ᵀ * M = 1 := by
  rw [hfun]; exact h

@[expose] noncomputable def su4Mk (M : Matrix (Fin 4) (Fin 4) K) (hdet : M.det = 1)
    (hB : (M.map (· ^ (p ^ f)))ᵀ * M = 1) : Su K p f 4 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    (mem_SUid (σ := unitaryInvolution K p f)).2 ⟨hdet, by rw [GenLocU4Aux.conjTr_unitaryInvolution]; exact hB⟩⟩

theorem su4Mk_smul (M : Matrix (Fin 4) (Fin 4) K) (hdet : M.det = 1) (hB : (M.map (· ^ (p ^ f)))ᵀ * M = 1)
    (v : Fin 4 → K) : (su4Mk (p := p) (f := f) M hdet hB : Su K p f 4) • v = M *ᵥ v := rfl

theorem coe_su4Mk (M : Matrix (Fin 4) (Fin 4) K) (hdet : M.det = 1) (hB : (M.map (· ^ (p ^ f)))ᵀ * M = 1) :
    (((su4Mk (p := p) (f := f) M hdet hB : Su K p f 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = M := rfl

theorem blockEmb2_zero_eq_tv (hinv : ∀ x : K, unitaryInvolution K p f (unitaryInvolution K p f x) = x)
    (g : Su K p f 2) (a : Fin 2 → K) (c : K) (hc : c + unitaryInvolution K p f c = 0)
    (hg : ∀ y : Fin 2 → K, g • y = y + (c * herm (unitaryInvolution K p f) a y) • a)
    (ha4 : herm (unitaryInvolution K p f) ![a 0, a 1, 0, 0] ![a 0, a 1, 0, 0] = 0) :
    blockEmb2 K p f 3 0 g = tv hinv ha4 hc := by
  apply ext_smul
  intro x
  rw [GenLocU4Aux.blockEmb2_smul_zero, tv_smul]
  have hg0 := congrFun (hg ![x 0, x 1]) 0
  have hg1 := congrFun (hg ![x 0, x 1]) 1
  simp only [smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hg0 hg1
  have hh : herm (unitaryInvolution K p f) ![a 0, a 1, 0, 0] x =
      herm (unitaryInvolution K p f) a ![x 0, x 1] := by
    simp [herm_def, Fin.sum_univ_four, Fin.sum_univ_two]
  rw [hh]
  funext j
  fin_cases j
  · simp [hg0]
  · simp [hg1]
  · simp
  · simp

theorem blockEmb2_two_eq_tv (hinv : ∀ x : K, unitaryInvolution K p f (unitaryInvolution K p f x) = x)
    (g : Su K p f 2) (a : Fin 2 → K) (c : K) (hc : c + unitaryInvolution K p f c = 0)
    (hg : ∀ y : Fin 2 → K, g • y = y + (c * herm (unitaryInvolution K p f) a y) • a)
    (ha4 : herm (unitaryInvolution K p f) ![0, 0, a 0, a 1] ![0, 0, a 0, a 1] = 0) :
    blockEmb2 K p f 3 2 g = tv hinv ha4 hc := by
  apply ext_smul
  intro x
  rw [GenLocU4Aux.blockEmb2_smul_two, tv_smul]
  have hg0 := congrFun (hg ![x 2, x 3]) 0
  have hg1 := congrFun (hg ![x 2, x 3]) 1
  simp only [smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hg0 hg1
  have hh : herm (unitaryInvolution K p f) ![0, 0, a 0, a 1] x =
      herm (unitaryInvolution K p f) a ![x 2, x 3] := by
    simp [herm_def, Fin.sum_univ_four, Fin.sum_univ_two]
  rw [hh]
  funext j
  fin_cases j
  · simp
  · simp
  · simp [hg0]
  · simp [hg1]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem mem_of_two_tv {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) {a b : Fin 2 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1)
    (hexp : ∀ v, v = herm σ b v • a + herm σ a v • b) (hP : a 0 * b 1 - b 0 * a 1 ≠ 0)
    (Γ : Subgroup (SUid σ 2)) (hΓa : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol ha hc ∈ Γ)
    (hΓb : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol hb hc ∈ Γ) (A : SUid σ 2) : A ∈ Γ := by
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
  have key : ∀ A : SUid σ 2, herm σ a (A • a) ≠ 0 → A ∈ Γ := by
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
    exact Γ.mul_mem (Γ.mul_mem (hΓa _ hx) (hΓb _ hγE)) (hΓa _ hy)
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
    exact Γ.mul_mem (Γ.inv_mem (hΓb _ hτ)) (key _ hB)
  · exact key A hγ


omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem herm_va {σ : K ≃+* K} {ι : K} (hι : ι * ι = -1) (hσι : σ ι = ι) :
    herm σ (![1, ι, 0, 0] : Fin 4 → K) ![1, ι, 0, 0] = 0 := by
  rw [herm_def, Fin.sum_univ_four]
  simp [hσι]
  linear_combination hι

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem herm_vb {σ : K ≃+* K} {ι : K} (hι : ι * ι = -1) (hσι : σ ι = ι) :
    herm σ (![0, 0, 1, ι] : Fin 4 → K) ![0, 0, 1, ι] = 0 := by
  rw [herm_def, Fin.sum_univ_four]
  simp [hσι]
  linear_combination hι

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem herm_vc {σ : K ≃+* K} {ι : K} (hι : ι * ι = -1) (hσι : σ ι = ι) :
    herm σ (![1, ι, 1, ι] : Fin 4 → K) ![1, ι, 1, ι] = 0 := by
  rw [herm_def, Fin.sum_univ_four]
  simp [hσι]
  linear_combination 2 * hι

theorem block0_of_tv (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (h2 : (2 : K) ≠ 0) {ι : K}
    (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι) (Γ : Subgroup (Su K p f 4))
    (hP : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0), tv hσ.invol (herm_va hι hσι) hc ∈ Γ)
    (hM : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
      tv hσ.invol (herm_va (ι := -ι) (by linear_combination hι) (by rw [map_neg, hσι])) hc ∈ Γ) :
    ∀ B : Su K p f 2, blockEmb2 K p f 3 0 B ∈ Γ := by
  set σ := unitaryInvolution K p f with hσdef
  have hι0 : ι ≠ 0 := by
    rintro rfl
    simp at hι
  have hσ2 : σ ((2 : K)⁻¹) = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  obtain ⟨a, ha_def⟩ : ∃ a : Fin 2 → K, a = ![(2 : K)⁻¹, ι * (2 : K)⁻¹] := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : Fin 2 → K, b = ![1, -ι] := ⟨_, rfl⟩
  have ha : herm σ a a = 0 := by
    rw [ha_def, herm_def, Fin.sum_univ_two]
    simp [hσ2, hσι]
    field_simp
    linear_combination hι
  have hb : herm σ b b = 0 := by
    rw [hb_def, herm_def, Fin.sum_univ_two]
    simp [hσι]
    linear_combination hι
  have hab : herm σ a b = 1 := by
    rw [ha_def, hb_def, herm_def, Fin.sum_univ_two]
    simp [hσ2, hσι]
    field_simp
    linear_combination -hι
  have hexp : ∀ v, v = herm σ b v • a + herm σ a v • b := by
    intro v
    rw [ha_def, hb_def]
    simp only [herm_def, Fin.sum_univ_two]
    funext j
    fin_cases j <;> simp [hσ2, hσι] <;> field_simp
    · ring
    · linear_combination (2 * v 1) * hι
  have hPab : a 0 * b 1 - b 0 * a 1 ≠ 0 := by
    rw [ha_def, hb_def]
    show (2 : K)⁻¹ * (-ι) - 1 * (ι * (2 : K)⁻¹) ≠ 0
    intro h
    apply hι0
    linear_combination (-1 : K) * h - ι * mul_inv_cancel₀ h2
  have ha4 : herm σ ![a 0, a 1, 0, 0] ![a 0, a 1, 0, 0] = 0 := by
    rw [herm_def, Fin.sum_univ_four]
    have := ha
    rw [herm_def, Fin.sum_univ_two] at this
    simp [this]
  have hΓa : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol ha hc ∈ Γ.comap (blockEmb2 K p f 3 0) := by
    intro c hc
    show blockEmb2 K p f 3 0 (tv hσ.invol ha hc) ∈ Γ
    rw [blockEmb2_zero_eq_tv hσ.invol (tv hσ.invol ha hc) a c hc (fun y => tv_smul hσ.invol ha hc y) ha4]
    refine GenLocU4Aux.tv_mem_of_scalar hσ.invol Γ (u := ![1, ι, 0, 0]) (a := ![a 0, a 1, 0, 0]) 2 h2 ?_
      (fun _ c hc => hP c hc) ha4 c hc
    rw [ha_def]
    funext j
    fin_cases j <;> simp <;> field_simp
  have hΓb : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol hb hc ∈ Γ.comap (blockEmb2 K p f 3 0) := by
    intro c hc
    show blockEmb2 K p f 3 0 (tv hσ.invol hb hc) ∈ Γ
    have hb4 : herm σ ![b 0, b 1, 0, 0] ![b 0, b 1, 0, 0] = 0 := by
      rw [herm_def, Fin.sum_univ_four]
      have := hb
      rw [herm_def, Fin.sum_univ_two] at this
      simp [this]
    rw [blockEmb2_zero_eq_tv hσ.invol (tv hσ.invol hb hc) b c hc (fun y => tv_smul hσ.invol hb hc y) hb4]
    have hbv : (![b 0, b 1, 0, 0] : Fin 4 → K) = ![1, -ι, 0, 0] := by rw [hb_def]; rfl
    have := hM c hc
    simpa [hbv] using this
  intro B
  exact mem_of_two_tv hσ ha hb hab hexp hPab (Γ.comap (blockEmb2 K p f 3 0)) hΓa hΓb B

theorem block2_of_tv (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (h2 : (2 : K) ≠ 0) {ι : K}
    (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι) (Γ : Subgroup (Su K p f 4))
    (hP : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0), tv hσ.invol (herm_vb hι hσι) hc ∈ Γ)
    (hM : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
      tv hσ.invol (herm_vb (ι := -ι) (by linear_combination hι) (by rw [map_neg, hσι])) hc ∈ Γ) :
    ∀ B : Su K p f 2, blockEmb2 K p f 3 2 B ∈ Γ := by
  set σ := unitaryInvolution K p f with hσdef
  have hι0 : ι ≠ 0 := by
    rintro rfl
    simp at hι
  have hσ2 : σ ((2 : K)⁻¹) = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  obtain ⟨a, ha_def⟩ : ∃ a : Fin 2 → K, a = ![(2 : K)⁻¹, ι * (2 : K)⁻¹] := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : Fin 2 → K, b = ![1, -ι] := ⟨_, rfl⟩
  have ha : herm σ a a = 0 := by
    rw [ha_def, herm_def, Fin.sum_univ_two]
    simp [hσ2, hσι]
    field_simp
    linear_combination hι
  have hb : herm σ b b = 0 := by
    rw [hb_def, herm_def, Fin.sum_univ_two]
    simp [hσι]
    linear_combination hι
  have hab : herm σ a b = 1 := by
    rw [ha_def, hb_def, herm_def, Fin.sum_univ_two]
    simp [hσ2, hσι]
    field_simp
    linear_combination -hι
  have hexp : ∀ v, v = herm σ b v • a + herm σ a v • b := by
    intro v
    rw [ha_def, hb_def]
    simp only [herm_def, Fin.sum_univ_two]
    funext j
    fin_cases j <;> simp [hσ2, hσι] <;> field_simp
    · ring
    · linear_combination (2 * v 1) * hι
  have hPab : a 0 * b 1 - b 0 * a 1 ≠ 0 := by
    rw [ha_def, hb_def]
    show (2 : K)⁻¹ * (-ι) - 1 * (ι * (2 : K)⁻¹) ≠ 0
    intro h
    apply hι0
    linear_combination (-1 : K) * h - ι * mul_inv_cancel₀ h2
  have ha4 : herm σ ![0, 0, a 0, a 1] ![0, 0, a 0, a 1] = 0 := by
    rw [herm_def, Fin.sum_univ_four]
    have := ha
    rw [herm_def, Fin.sum_univ_two] at this
    simp [this]
  have hΓa : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol ha hc ∈ Γ.comap (blockEmb2 K p f 3 2) := by
    intro c hc
    show blockEmb2 K p f 3 2 (tv hσ.invol ha hc) ∈ Γ
    rw [blockEmb2_two_eq_tv hσ.invol (tv hσ.invol ha hc) a c hc (fun y => tv_smul hσ.invol ha hc y) ha4]
    refine GenLocU4Aux.tv_mem_of_scalar hσ.invol Γ (u := ![0, 0, 1, ι]) (a := ![0, 0, a 0, a 1]) 2 h2 ?_
      (fun _ c hc => hP c hc) ha4 c hc
    rw [ha_def]
    funext j
    fin_cases j <;> simp <;> field_simp
  have hΓb : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol hb hc ∈ Γ.comap (blockEmb2 K p f 3 2) := by
    intro c hc
    show blockEmb2 K p f 3 2 (tv hσ.invol hb hc) ∈ Γ
    have hb4 : herm σ ![0, 0, b 0, b 1] ![0, 0, b 0, b 1] = 0 := by
      rw [herm_def, Fin.sum_univ_four]
      have := hb
      rw [herm_def, Fin.sum_univ_two] at this
      simp [this]
    rw [blockEmb2_two_eq_tv hσ.invol (tv hσ.invol hb hc) b c hc (fun y => tv_smul hσ.invol hb hc y) hb4]
    have hbv : (![0, 0, b 0, b 1] : Fin 4 → K) = ![0, 0, 1, -ι] := by rw [hb_def]; rfl
    have := hM c hc
    simpa [hbv] using this
  intro B
  exact mem_of_two_tv hσ ha hb hab hexp hPab (Γ.comap (blockEmb2 K p f 3 2)) hΓa hΓb B

end GenLocU4QSu4

end CFSG.GH74.Generic.BProg.B2
