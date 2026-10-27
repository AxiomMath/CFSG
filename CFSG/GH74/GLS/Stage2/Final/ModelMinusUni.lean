module

public import CFSG.GH74.GLS.Stage2.Final.ModelMinusLin
public import CFSG.GH74.GLS.Stage2.Final.ModelLUData

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] [CharP F p] in
theorem exists_pow_pred_eq (hF : Nat.card F = (p ^ f) ^ 2) (hq : 1 ≤ p ^ f) {t : Fˣ}
    (ht : t ^ (p ^ f + 1) = 1) : ∃ u : Fˣ, u ^ (p ^ f - 1) = t := by
  set q := p ^ f with hqdef
  have hcard : Nat.card Fˣ = q ^ 2 - 1 := by rw [Nat.card_units, hF]
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [hk]
    simp only [Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  have hd1 : (q - 1) ∣ Nat.card Fˣ := by rw [hcard, hfac]; exact Dvd.intro _ rfl
  have hd2 : (q + 1) ∣ Nat.card Fˣ := by rw [hcard, hfac]; exact Dvd.intro_left _ rfl
  have hq1 : 0 < q - 1 := by
    rcases Nat.eq_zero_or_pos (q - 1) with h | h
    · exfalso
      have : q = 1 := by omega
      have h1 : Nat.card F = 1 := by rw [hF, this]; norm_num
      have := Finite.one_lt_card (α := F)
      omega
    · exact h
  have hker1 := card_ker_pow_cyclic hd1 hq1
  have hker2 := card_ker_pow_cyclic hd2 (Nat.succ_pos _)
  have hrange := Subgroup.card_ker_mul_card_range (powMonoidHom (q - 1) : Fˣ →* Fˣ)
  rw [hker1, hcard, hfac] at hrange
  have hR : Nat.card (powMonoidHom (q - 1) : Fˣ →* Fˣ).range = q + 1 := by
    have : (q - 1) * Nat.card (powMonoidHom (q - 1) : Fˣ →* Fˣ).range = (q - 1) * (q + 1) := hrange
    exact Nat.eq_of_mul_eq_mul_left hq1 this
  have hle : (powMonoidHom (q - 1) : Fˣ →* Fˣ).range ≤ (powMonoidHom (q + 1) : Fˣ →* Fˣ).ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    show (u ^ (q - 1)) ^ (q + 1) = 1
    rw [← pow_mul, ← hfac]
    have := pow_card_eq_one' (G := Fˣ) (x := u)
    rwa [hcard] at this
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hR, hker2])
  have : t ∈ (powMonoidHom (q + 1) : Fˣ →* Fˣ).ker := by
    rw [MonoidHom.mem_ker]; exact ht
  rw [← heq] at this
  obtain ⟨u, hu⟩ := this
  exact ⟨u, hu⟩

omit [Field F] [Finite F] [CharP F p] in
theorem hq_one (p f : ℕ) [Fact p.Prime] : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem unit_alg (A B i : F) (hA : A ≠ 0) (hB : B ≠ 0) (hii : i * i = -1) (h2 : (2 : F) ≠ 0) :
    ((A + B⁻¹) / 2) * ((B + A⁻¹) / 2) + (i * (A - B⁻¹) / 2) * (i * (B - A⁻¹) / 2) = 1 := by
  field_simp
  linear_combination (A * B - 1) ^ 2 * hii

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem unit_alg2 (A B i : F) (hA : A ≠ 0) (hB : B ≠ 0) (h2 : (2 : F) ≠ 0) :
    ((A + B⁻¹) / 2) * (i * (B - A⁻¹) / 2) = (i * (A - B⁻¹) / 2) * ((B + A⁻¹) / 2) := by
  field_simp

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem unit_alg0 (A B i : F) (hA : A ≠ 0) (_hB : B ≠ 0) (hii : i * i = -1) (h2 : (2 : F) ≠ 0) :
    ((B + A⁻¹) / 2) ^ 2 + (i * (B - A⁻¹) / 2) ^ 2 = B * A⁻¹ := by
  field_simp
  linear_combination (B * A - 1) ^ 2 * hii

variable (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem exists_hilbert90 (δ : F) (hδ : unitaryInvolution F p f δ * δ = 1) :
    ∃ u : F, u ≠ 0 ∧ unitaryInvolution F p f u = δ * u := by
  have hσ : ∀ x, unitaryInvolution F p f x = x ^ (p ^ f) := unitaryInvolution_apply F p f
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ
  have ht : (Units.mk0 δ hδ0) ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [pow_succ, ← hσ]
    exact hδ
  obtain ⟨u, hu⟩ := exists_pow_pred_eq hF (hq_one p f) ht
  refine ⟨(u : F), u.ne_zero, ?_⟩
  rw [hσ]
  have h1 : ((u : F)) ^ (p ^ f - 1) = δ := by
    have := congrArg (fun x : Fˣ => (x : F)) hu
    simpa using this
  have h2 : ((u : F)) ^ (p ^ f) = (u : F) ^ (p ^ f - 1) * u := by
    rw [← pow_succ]
    congr 1
    have := hq_one p f
    omega
  rw [h2, h1, mul_comm]

theorem exists_i_uni (hq4 : p ^ f % 4 = 1) :
    ∃ i : F, i * i = -1 ∧ unitaryInvolution F p f i = i := by
  have hcardF : Nat.card F % 4 ≠ 3 := by
    rw [hF, Nat.pow_mod, hq4]
    norm_num
  obtain ⟨i, hii⟩ := exists_i_of_card (F := F) hcardF
  have hi4 : i ^ 4 = 1 := pow_four_of_sq hii
  refine ⟨(i : F), ?_, ?_⟩
  · have := congrArg (fun x : Fˣ => (x : F)) hii
    simpa using this
  · rw [unitaryInvolution_apply]
    obtain ⟨m, hm⟩ : ∃ m, p ^ f = 4 * m + 1 := ⟨p ^ f / 4, by omega⟩
    have h4 : ((i : F)) ^ 4 = 1 := by
      have := congrArg (fun x : Fˣ => (x : F)) hi4
      simpa using this
    rw [hm, pow_succ, pow_mul, h4, one_pow, one_mul]

theorem exists_unitary_pair (h2 : (2 : F) ≠ 0) (hq4 : p ^ f % 4 = 1) (ε : F)
    (hε : unitaryInvolution F p f ε * ε = 1) :
    ∃ α β : F, α ^ 2 + β ^ 2 = ε ∧
      unitaryInvolution F p f α * α + unitaryInvolution F p f β * β = 1 ∧
      unitaryInvolution F p f α * β = unitaryInvolution F p f β * α := by
  set σ := unitaryInvolution F p f with hσdef
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hF
  obtain ⟨i, hii, hσi⟩ := exists_i_uni hF hq4
  have hσi' : σ i = i := hσi
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε
  obtain ⟨u, hu0, hu⟩ := exists_hilbert90 hF ε⁻¹ (by
    rw [map_inv₀, ← mul_inv, hε, inv_one])
  have hu' : σ u = ε⁻¹ * u := hu
  have hσu0 : σ u ≠ 0 := by rw [hu']; exact mul_ne_zero (inv_ne_zero hε0) hu0
  have hσ2 : σ (2 : F) = 2 := map_ofNat σ 2
  have hσα : σ ((u + (σ u)⁻¹) / 2) = (σ u + u⁻¹) / 2 := by
    rw [map_div₀, map_add, map_inv₀, hσσ, hσ2]
  have hσβ : σ (i * (u - (σ u)⁻¹) / 2) = i * (σ u - u⁻¹) / 2 := by
    rw [map_div₀, map_mul, map_sub, map_inv₀, hσσ, hσ2, hσi']
  refine ⟨(u + (σ u)⁻¹) / 2, i * (u - (σ u)⁻¹) / 2, ?_, ?_, ?_⟩
  · rw [unit_alg0 (σ u) u i hσu0 hu0 hii h2, hu']
    field_simp
  · rw [hσα, hσβ]
    exact unit_alg (σ u) u i hσu0 hu0 hii h2
  · rw [hσα, hσβ]
    exact unit_alg2 (σ u) u i hσu0 hu0 h2

omit [Finite F] [Fact p.Prime] [CharP F p] hF in
theorem conjTr_ccmat_mul (σ : F ≃+* F) (α β : F) (h1 : σ α * α + σ β * β = 1)
    (h2 : σ α * β = σ β * α) : conjTr σ (ccmat α β) * ccmat α β = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, ccmat, Matrix.mul_apply, Fin.sum_univ_four]
  · linear_combination h1
  · linear_combination h2
  · linear_combination -h2
  · linear_combination h1

omit [Finite F] [Fact p.Prime] [CharP F p] hF in
theorem conjTr_jjk_mul (σ : F ≃+* F) (α β : F) (h1 : σ α * α + σ β * β = 1)
    (h2 : σ α * β = σ β * α) : conjTr σ (jjk α β) * jjk α β = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, jjk, Matrix.mul_apply, Fin.sum_univ_four]
  · linear_combination h1
  · linear_combination h2
  · linear_combination -h2
  · linear_combination h1

theorem ccGL_mem_uni (α β : F) (hne : α ^ 2 + β ^ 2 ≠ 0)
    (h1 : unitaryInvolution F p f α * α + unitaryInvolution F p f β * β = 1)
    (h2 : unitaryInvolution F p f α * β = unitaryInvolution F p f β * α) :
    ccGL α β hne ∈ (ModelData.uni hF).U4 := by
  show ccGL α β hne ∈ uniGL (unitaryInvolution F p f) 4
  rw [mem_uniGL]
  exact conjTr_ccmat_mul _ α β h1 h2

theorem nsm_conj_uni (h2 : (2 : F) ≠ 0) (hq4 : p ^ f % 4 = 1) (a : GL (Fin 2) F)
    (ha : a ∈ (ModelData.uni hF).U2) :
    ∃ k ∈ (ModelData.uni hF).K4, k * (swapGL F * yGL F) * k⁻¹ = swapGL F * diagGL a (-a⁻¹) := by
  have hna : -a ∈ (ModelData.uni hF).U2 := by
    have := (ModelData.uni hF).U2.mul_mem (ModelData.uni hF).neg_mem ha
    simpa using this
  have hnorm := norm_det_uni (σ := unitaryInvolution F p f) hna
  have hδ : ((Matrix.GeneralLinearGroup.det (-a) : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hd : ((Matrix.GeneralLinearGroup.det (-a) : Fˣ) : F) = ((-a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det :=
    Matrix.GeneralLinearGroup.val_det_apply (-a)
  have hεn : unitaryInvolution F p f (((Matrix.GeneralLinearGroup.det (-a) : Fˣ) : F)⁻¹) *
      (((Matrix.GeneralLinearGroup.det (-a) : Fˣ) : F)⁻¹) = 1 := by
    rw [map_inv₀, ← mul_inv, hd]
    rw [hnorm, inv_one]
  obtain ⟨α, β, hab, h1, h2'⟩ := exists_unitary_pair hF h2 hq4 _ hεn
  have hne : α ^ 2 + β ^ 2 ≠ 0 := by rw [hab]; exact inv_ne_zero hδ
  refine ⟨diagGL 1 (-a) * ccGL α β hne, ((ModelData.uni hF).mem_K4 _).2 ⟨?_, ?_⟩, ?_⟩
  · refine (ModelData.uni hF).U4.mul_mem (((ModelData.uni hF).diag_mem_iff _ _).2
      ⟨(ModelData.uni hF).U2.one_mem, hna⟩) (ccGL_mem_uni hF α β hne h1 h2')
  · rw [Units.val_mul, Matrix.det_mul, det_diagGL, coe_ccGL, det_ccmat, hab]
    rw [Units.val_one, Matrix.det_one, one_mul, ← hd]
    exact mul_inv_cancel₀ hδ
  · have hc := ccGL_comm_wy α β hne
    calc diagGL 1 (-a) * ccGL α β hne * (swapGL F * yGL F) * (diagGL 1 (-a) * ccGL α β hne)⁻¹
        = diagGL 1 (-a) * (ccGL α β hne * (swapGL F * yGL F) * (ccGL α β hne)⁻¹) *
            (diagGL 1 (-a))⁻¹ := by group
      _ = diagGL 1 (-a) * (swapGL F * yGL F) * (diagGL 1 (-a))⁻¹ := by
          rw [hc, mul_assoc (swapGL F * yGL F), mul_inv_cancel, mul_one]
      _ = swapGL F * diagGL (-(-a)) (-a)⁻¹ := nsm_core (-a)
      _ = swapGL F * diagGL a (-a⁻¹) := by rw [neg_neg, inv_neg]

theorem jj_conj_uni (h2 : (2 : F) ≠ 0) (hq4 : p ^ f % 4 = 1) :
    ∃ k ∈ (ModelData.uni hF).K4, k * diagGL (J0 F) (J0 F) * k⁻¹ = swapGL F * yGL F := by
  have hεn : unitaryInvolution F p f (-1 : F) * (-1 : F) = 1 := by simp
  obtain ⟨α, β, hab, h1, h2'⟩ := exists_unitary_pair hF h2 hq4 (-1) hεn
  have hdet : (jjk α β).det = 1 := by rw [det_jjk, hab]; ring
  let k : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (jjk α β)
    (by rw [hdet]; exact one_ne_zero)
  have hkU : k ∈ (ModelData.uni hF).U4 := by
    show k ∈ uniGL (unitaryInvolution F p f) 4
    rw [mem_uniGL]
    exact conjTr_jjk_mul _ α β h1 h2'
  refine ⟨k, ((ModelData.uni hF).mem_K4 _).2 ⟨hkU, hdet⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact jjk_intertwine α β

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
