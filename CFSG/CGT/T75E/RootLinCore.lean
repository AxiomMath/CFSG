module

public import CFSG.CGT.T75E.RootCommon
public import CFSG.CGT.T75E.RootLinMat
public import CFSG.Timmesfeld.Closure.Bender
public import CFSG.CGT.Timmesfeld75.Sec3Conj

public noncomputable section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.Open Matrix
open scoped MatrixGroups

section Bender

variable {Q : Type} [Group Q] [Finite Q]

theorem commute_of_pow_four (hQ : IsBenderGroup Q) {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (h4 : (a * b) ^ 4 = 1) : a * b = b * a := by
  rcases eq_or_ne a 1 with rfl | ha1
  · simp
  rcases eq_or_ne b 1 with rfl | hb1
  · simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hB, -⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_fusionBenderBorel hQ
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
  have hne := CFSG.Timmesfeld.Connectivity.not_orderOf_mul_eq_four (fun Q' => (hB Q').1) hao hbo
  have hdvd : orderOf (a * b) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have h2 : orderOf (a * b) ∣ 2 := by
    generalize orderOf (a * b) = N at hdvd hne
    have hle : N ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < N := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
    interval_cases N
    · decide
    · decide
    · exact absurd hdvd (by decide)
    · exact absurd rfl hne
  have hsq : (a * b) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h := eq_inv_of_mul_eq_one_left (show a * b * (a * b) = 1 by rw [← pow_two]; exact hsq)
  rw [_root_.mul_inv_rev, hai, hbi] at h
  exact h

end Bender

section Rho

variable {S K Q : Type} [Group S] [Group K] [Group Q] [Finite Q]

theorem rho_eq_one_of_sq (hQ : IsBenderGroup Q) (π : S →* K) {Y : Subgroup K} (ρ : ↥Y →* Q)
    {x y z : S} (hx : π x ∈ Y) (hy : π y ∈ Y) (hxx : x * x = 1) (hyy : y * y = 1)
    (h4 : (x * y) ^ 4 = 1) (hz : z = (x * y) ^ 2) (hzY : π z ∈ Y) : ρ ⟨π z, hzY⟩ = 1 := by
  set X : ↥Y := ⟨π x, hx⟩ with hX
  set Z : ↥Y := ⟨π y, hy⟩ with hZ
  have hXX : X * X = 1 := Subtype.ext (by
    show π x * π x = 1
    rw [← map_mul, hxx, map_one])
  have hZZ : Z * Z = 1 := Subtype.ext (by
    show π y * π y = 1
    rw [← map_mul, hyy, map_one])
  have hXZ4 : (X * Z) ^ 4 = 1 := Subtype.ext (by
    show (π x * π y) ^ 4 = 1
    rw [← map_mul, ← map_pow, h4, map_one])
  have hXZ2 : (⟨π z, hzY⟩ : ↥Y) = (X * Z) ^ 2 := Subtype.ext (by
    show π z = (π x * π y) ^ 2
    rw [hz, map_pow, map_mul])
  have hcomm : ρ X * ρ Z = ρ Z * ρ X :=
    commute_of_pow_four hQ (by rw [← map_mul, hXX, map_one]) (by rw [← map_mul, hZZ, map_one])
      (by rw [← map_mul, ← map_pow, hXZ4, map_one])
  rw [hXZ2, map_pow, pow_two, map_mul]
  calc ρ X * ρ Z * (ρ X * ρ Z) = ρ X * (ρ Z * ρ X) * ρ Z := by group
    _ = ρ X * (ρ X * ρ Z) * ρ Z := by rw [hcomm]
    _ = (ρ X * ρ X) * (ρ Z * ρ Z) := by group
    _ = 1 := by rw [← map_mul, ← map_mul, hXX, hZZ, map_one, mul_one]

end Rho

section Core

variable {K : Type} [Group K] [Finite K] {Tb : Subgroup K} {c₁ c₂ : K} {f n : ℕ}
  {F : Type} [Field F] [CharP F 2]

theorem rootGroup_lin_core (π : SL(n, F) →* K) (hπ : Function.Surjective π) {c : Fin n → F}
    (hc : c ≠ 0) (hTb : Tb = (tvCenterSL c).map π) (hT : IsWC Tb) (hf : 2 ≤ f)
    (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hρ : Function.Surjective ρ) : False := by
  have hQ : IsBenderGroup (PSU3Model f) := .isPSU3 f hf (MulEquiv.refl _)
  obtain ⟨g₁, hg₁⟩ := hπ c₁
  obtain ⟨g₂, hg₂⟩ := hπ c₂
  set p₀ : Fin n → F := c with hp₀
  set p₁ : Fin n → F := (g₁ : Matrix (Fin n) (Fin n) F) *ᵥ c with hp₁
  set p₂ : Fin n → F := (g₂ : Matrix (Fin n) (Fin n) F) *ᵥ c with hp₂
  have hp₁0 : p₁ ≠ 0 := mulVec_ne_zero' g₁ hc
  have hp₂0 : p₂ ≠ 0 := mulVec_ne_zero' g₂ hc
  have hS0 : T3 Tb c₁ c₂ 0 = (tvCenterSL p₀).map π := hTb
  have hS1 : T3 Tb c₁ c₂ 1 = (tvCenterSL p₁).map π := by
    show conjSubgroup c₁ Tb = _
    rw [← hg₁, hTb, ← map_conjSubgroup, conjSubgroup_tvCenterSL]
  have hS2 : T3 Tb c₁ c₂ 2 = (tvCenterSL p₂).map π := by
    show conjSubgroup c₂ Tb = _
    rw [← hg₂, hTb, ← map_conjSubgroup, conjSubgroup_tvCenterSL]
  have hmem : ∀ (i : Fin 3) (p : Fin n → F), T3 Tb c₁ c₂ i = (tvCenterSL p).map π →
      ∀ x ∈ tvCenterSL p, π x ∈ Y3 Tb c₁ c₂ := fun i p h x hx =>
    T3_le_Y3 Tb c₁ c₂ i (by rw [h]; exact Subgroup.mem_map_of_mem π hx)
  have hY : Y3 Tb c₁ c₂ = T3 Tb c₁ c₂ 0 ⊔ T3 Tb c₁ c₂ 1 ⊔ T3 Tb c₁ c₂ 2 := Y3_eq Tb c₁ c₂
  by_cases hI : ∃ μ : F, p₁ = μ • p₀
  ·
    obtain ⟨μ, hμ⟩ := hI
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hp₁0 (by rw [hμ, zero_smul])
    have h10 : T3 Tb c₁ c₂ 1 = T3 Tb c₁ c₂ 0 := by
      rw [hS1, hS0, hμ, tvCenterSL_smul hμ0]
    refine Y3_ne_sup ρ hρ hT hf 0 2 ?_
    rw [hY, h10, sup_idem]
  have hI' : ∀ μ : F, p₁ ≠ μ • p₀ := fun μ h => hI ⟨μ, h⟩
  have hpq01 : ∀ μ : F, p₀ ≠ μ • p₁ := by
    intro μ h
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hc (by rw [h, zero_smul])
    apply hI' μ⁻¹
    rw [h, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  by_cases hII : ∃ α β : F, p₂ = α • p₀ + β • p₁
  ·
    obtain ⟨α, β, hαβ⟩ := hII
    have hle : T3 Tb c₁ c₂ 2 ≤ T3 Tb c₁ c₂ 0 ⊔ T3 Tb c₁ c₂ 1 := by
      rw [hS0, hS1, hS2, ← Subgroup.map_sup]
      exact Subgroup.map_mono (tvCenterSL_le_sup hp₂0 hpq01 hαβ)
    refine Y3_ne_sup ρ hρ hT hf 0 1 ?_
    rw [hY]
    exact le_antisymm (sup_le le_rfl hle) le_sup_left
  have hpq21 : ∀ μ : F, p₂ ≠ μ • p₁ := fun μ h =>
    hII ⟨0, μ, by rw [h, zero_smul, zero_add]⟩
  have hnot : ∀ α β : F, p₂ ≠ α • p₀ + β • p₁ := fun α β h => hII ⟨α, β, h⟩
  have step : ∀ (i : Fin 3) (p : Fin n → F), T3 Tb c₁ c₂ i = (tvCenterSL p).map π →
      (∀ μ : F, p ≠ μ • p₁) → ∀ φ : Fin n → F, ∀ (hφp : φ ⬝ᵥ p = 0) (hφq : φ ⬝ᵥ p₁ = 0),
        ρ ⟨π (tvSL p₁ φ hφq), hmem 1 p₁ hS1 _ ⟨φ, hφq, rfl⟩⟩ = 1 := by
    intro i p hSi hpq φ hφp hφq
    obtain ⟨ψ, hψq, hψp⟩ := exists_dot_of_not_smul (c := p₁) (d := p) hpq
    have hx : π (tvSL p φ hφp) ∈ Y3 Tb c₁ c₂ := hmem i p hSi _ ⟨φ, hφp, rfl⟩
    have hy : π (tvSL p₁ ψ hψq) ∈ Y3 Tb c₁ c₂ := hmem 1 p₁ hS1 _ ⟨ψ, hψq, rfl⟩
    refine rho_eq_one_of_sq hQ π ρ hx hy (tvSL_mul_self hφp) (tvSL_mul_self hψq)
      (tvSL_pair_pow_four hφp hφq hψq) ?_ _
    rw [tvSL_pair_sq hφp hφq hψq]
    apply Subtype.ext
    rw [coe_tvSL, coe_tvSL, hψp, one_smul]
  obtain ⟨θ, hθ0, hθ1, hθ2⟩ := exists_dot_of_not_mem_pair (c := p₀) (e := p₁) (d := p₂) hnot
  have kill : ∀ χ : Fin n → F, ∀ hχ : χ ⬝ᵥ p₁ = 0,
      ρ ⟨π (tvSL p₁ χ hχ), hmem 1 p₁ hS1 _ ⟨χ, hχ, rfl⟩⟩ = 1 := by
    intro χ hχ
    set χ' : Fin n → F := (χ ⬝ᵥ p₂) • θ with hχ'
    have h'1 : χ' ⬝ᵥ p₁ = 0 := by rw [hχ', smul_dotProduct, hθ1, smul_zero]
    have h'0 : χ' ⬝ᵥ p₀ = 0 := by rw [hχ', smul_dotProduct, hθ0, smul_zero]
    have h''1 : (χ - χ') ⬝ᵥ p₁ = 0 := by rw [sub_dotProduct, hχ, h'1, sub_zero]
    have h''2 : (χ - χ') ⬝ᵥ p₂ = 0 := by
      rw [sub_dotProduct, hχ', smul_dotProduct, hθ2, smul_eq_mul, mul_one, sub_self]
    have e : tvSL p₁ χ hχ = tvSL p₁ χ' h'1 * tvSL p₁ (χ - χ') h''1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, coe_tvSL, coe_tvSL, tv_mul_tv_center h'1,
        add_sub_cancel]
    have k1 := step 0 p₀ hS0 hpq01 χ' h'0 h'1
    have k2 := step 2 p₂ hS2 hpq21 (χ - χ') h''2 h''1
    have hy1 : π (tvSL p₁ χ' h'1) ∈ Y3 Tb c₁ c₂ := hmem 1 p₁ hS1 _ ⟨χ', h'1, rfl⟩
    have hy2 : π (tvSL p₁ (χ - χ') h''1) ∈ Y3 Tb c₁ c₂ := hmem 1 p₁ hS1 _ ⟨_, h''1, rfl⟩
    have hsplit : (⟨π (tvSL p₁ χ hχ), hmem 1 p₁ hS1 _ ⟨χ, hχ, rfl⟩⟩ : ↥(Y3 Tb c₁ c₂)) =
        ⟨π (tvSL p₁ χ' h'1), hy1⟩ * ⟨π (tvSL p₁ (χ - χ') h''1), hy2⟩ :=
      Subtype.ext (by
        show π (tvSL p₁ χ hχ) = π (tvSL p₁ χ' h'1) * π (tvSL p₁ (χ - χ') h''1)
        rw [← map_mul, ← e])
    rw [hsplit, map_mul, k1, k2, mul_one]
  have hbot : imgA ρ (T3 Tb c₁ c₂ 1) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨w, hw, rfl⟩
    have hw' : (w : K) ∈ T3 Tb c₁ c₂ 1 := Subgroup.mem_subgroupOf.1 hw
    rw [hS1] at hw'
    obtain ⟨x, ⟨a, ha, hx⟩, hxw⟩ := hw'
    have hx' : x = tvSL p₁ a ha := Subtype.ext hx
    have hwe : w = ⟨π (tvSL p₁ a ha), hmem 1 p₁ hS1 _ ⟨a, ha, rfl⟩⟩ :=
      Subtype.ext (by rw [← hxw, hx'])
    rw [hwe, kill a ha]
    exact Subgroup.one_mem _
  obtain ⟨g, hg⟩ := imgA_conj ρ hT 1
  rw [hbot] at hg
  exact imgA_ne_bot ρ hρ hT hf (conjSubgroup_eq_bot_iff.1 hg.symm)

end Core

end CFSG.CGT.T75E
