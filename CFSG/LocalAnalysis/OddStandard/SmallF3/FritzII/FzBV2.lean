module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBV1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRRk

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {c : Bool} {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ P : Subgroup G} {q s : G} {β : ℕ → G}

theorem fzb_sq_of_M (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β) (hF : FzbFactsGen c)
    {M : Subgroup G} (hMT : M ≤ T₂) (hM : ∀ x < 1024, β x ∈ M ↔ fzbIsM x) {a : G}
    (ha : a⁻¹ * q * a ∈ M) :
    ∃ x₀ y₀ : ℕ, x₀ < 1024 ∧ fzbIsM x₀ ∧ β x₀ = a⁻¹ * q * a ∧ fzbMul c x₀ x₀ = y₀ ∧
      y₀ < 64 ∧ β y₀ = a⁻¹ * t * a ∧ fzbMul c y₀ y₀ = 0 := by
  obtain ⟨x₀, hx₀, hβx₀⟩ := hβ.surj (a⁻¹ * q * a) (hMT ha)
  have hmem : β x₀ ∈ M := by rw [hβx₀]; exact ha
  have hxM : fzbIsM x₀ := (hM x₀ hx₀).mp hmem
  have hq2 : q ^ 2 = t := by
    have h1 : β (fzbMul c 64 64) = β 64 * β 64 :=
      hβ.mul 64 (by norm_num) 64 (by norm_num)
    rw [hF.t_eq, hβ.t_eq, hβ.q_eq] at h1
    rw [pow_two]
    exact h1.symm
  have ht2 : t * t = 1 := by
    have h1 : β (fzbMul c 128 128) = β 128 * β 128 :=
      hβ.mul 128 (by norm_num) 128 (by norm_num)
    rw [hF.sq_t, hβ.one, hβ.t_eq] at h1
    exact h1.symm
  have hy₀64 : fzbMul c x₀ x₀ < 64 := hF.M_sq x₀ hx₀ hxM
  have hy₀1024 : fzbMul c x₀ x₀ < 1024 := hF.mul_lt x₀ hx₀ x₀ hx₀
  have hβy : β (fzbMul c x₀ x₀) = a⁻¹ * t * a := by
    rw [hβ.mul x₀ hx₀ x₀ hx₀, hβx₀]
    calc (a⁻¹ * q * a) * (a⁻¹ * q * a) = a⁻¹ * (q * q) * a := by group
      _ = a⁻¹ * q ^ 2 * a := by rw [pow_two]
      _ = a⁻¹ * t * a := by rw [hq2]
  have hsq0 : fzbMul c (fzbMul c x₀ x₀) (fzbMul c x₀ x₀) = 0 := by
    apply hβ.inj _ (hF.mul_lt _ hy₀1024 _ hy₀1024) 0 (by norm_num)
    rw [hβ.mul _ hy₀1024 _ hy₀1024, hβy, hβ.one]
    calc (a⁻¹ * t * a) * (a⁻¹ * t * a) = a⁻¹ * (t * t) * a := by group
      _ = a⁻¹ * 1 * a := by rw [ht2]
      _ = 1 := by group
  exact ⟨x₀, fzbMul c x₀ x₀, hx₀, hxM, hβx₀, rfl, hy₀64, hβy, hsq0⟩

theorem fzb_H1_false (h : Ctx t L S x₁ x₂ lam rho tau)
    (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s) (hβ : FzbChart true T₂ P x₁ x₂ t q s lam β)
    (hlt : ∀ x < 1024, ∀ y < 1024, fzbMul true x y < 1024) (hH : FzbH1) {y₀ : ℕ}
    (hy4 : 4 ≤ y₀) (hy64 : y₀ < 64) (hy2 : fzbMul true y₀ y₀ = 0) :
    ¬ ∃ g : G, g⁻¹ * t * g = β y₀ := by
  rintro ⟨g, hg⟩
  obtain ⟨Lc, hLcard, hL0, hLmem, hLpair⟩ := hH y₀ hy4 hy64 hy2
  have hA : ∀ x ∈ Lc, x < 1024 := fun x hx => (hLmem x hx).1
  have hmul : ∀ x ∈ Lc, ∀ y ∈ Lc, fzbMul true x y ∈ Lc :=
    fun x hx y hy => (hLpair x hx y hy).2
  obtain ⟨E, hET, hEcard, hEmem⟩ := fzb_subgroup_of_codes hβ hlt hL0 hA hmul
  have hy₀1024 : y₀ < 1024 := by omega
  have hcode : ∀ e ∈ E, ∃ x, x < 1024 ∧ x ∈ Lc ∧ β x = e := by
    intro e he
    obtain ⟨x, hx, hxe⟩ := hβ.surj e (hET he)
    refine ⟨x, hx, ?_, hxe⟩
    have hxE : β x ∈ E := by rw [hxe]; exact he
    exact (hEmem x hx).mp hxE
  have hEcomm : IsMulCommutative E := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, hx, hxL, hxβ⟩ := hcode a a.2
    obtain ⟨y, hy, hyL, hyβ⟩ := hcode b b.2
    have h1 : fzbMul true x y = fzbMul true y x := (hLpair x hxL y hyL).1
    have h2 : β x * β y = β y * β x := (fzb_chart_comm hβ hlt hx hy).mp h1
    simpa [hxβ, hyβ] using h2
  have hEsq : ∀ e ∈ E, e ^ 2 = 1 := by
    intro e he
    obtain ⟨x, hx, hxL, hxβ⟩ := hcode e he
    have hsq : fzbMul true x x = 0 := (hLmem x hxL).2.1
    rw [pow_two, ← hxβ, ← hβ.mul x hx x hx, hsq, hβ.one]
  have hEel : CFSG.Open.IsElemAbelian 2 E := ⟨hEcomm, hEsq⟩
  have hEcent : E ≤ T₂ ⊓ invCent (β y₀) := by
    intro e he
    refine ⟨hET he, ?_⟩
    obtain ⟨x, hx, hxL, hxβ⟩ := hcode e he
    have hcomm : fzbMul true x y₀ = fzbMul true y₀ x := (hLmem x hxL).2.2
    have h2 : β x * β y₀ = β y₀ * β x := (fzb_chart_comm hβ hlt hx hy₀1024).mp hcomm
    rw [invCent]
    refine (Subgroup.mem_centralizer_singleton_iff).mpr ?_
    rw [← hxβ]
    exact h2
  have hE32 : 16 < Nat.card E := by rw [hEcard, hLcard]; norm_num
  exact fzr_not_conj_of_elem_gt h hS.isPGroup hS.S_le hEcent hEel hE32 ⟨g, hg⟩

theorem fzb_branchA (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s) (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β)
    (hF : FzbFacts c) (hH : c = true → FzbH1) (hV : c = false → FzbV1) {M : Subgroup G}
    (hMT : M ≤ T₂) (hM : ∀ x < 1024, β x ∈ M ↔ fzbIsM x) {a : G} (ha : a⁻¹ * q * a ∈ M) :
    False := by
  obtain ⟨-, -, ht1, -, -⟩ := fzb_chart_q hβ hF.toFzbFactsGen
  obtain ⟨x₀, y₀, hx₀, hxM, -, hy₀eq, hy₀64, hβy₀, hy₀sq⟩ :=
    fzb_sq_of_M hβ hF.toFzbFactsGen hMT hM ha
  have hconj : ∃ g : G, g⁻¹ * t * g = β y₀ := ⟨a, hβy₀.symm⟩
  by_cases hy4 : y₀ < 4
  · have hz : β y₀ ∈ fourGrp x₁ x₂ := (hβ.Z_eq _).mpr ⟨y₀, hy4, rfl⟩
    have hz1 : β y₀ ≠ 1 := by
      intro h1
      apply ht1
      have h2 : a⁻¹ * t * a = 1 := hβy₀ ▸ h1
      calc t = a * (a⁻¹ * t * a) * a⁻¹ := by group
        _ = 1 := by rw [h2]; group
    exact fzb_Z_not_conj h hK hS hβ hF.toFzbFactsGen hz hz1 hconj
  · push_neg at hy4
    cases c with
    | false =>
      have hlt := hV rfl x₀ hx₀ hxM (by rw [hy₀eq]; exact hy₀sq)
      rw [hy₀eq] at hlt
      omega
    | true =>
      exact fzb_H1_false h hS hβ hF.mul_lt (hH rfl) hy4 hy₀64 hy₀sq hconj

end CFSG.OddStandard.SmallF3.FritzII
