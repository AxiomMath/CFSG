module

public import CFSG.LargeExtraspecial.GLW4RhoMat
public import CFSG.LargeExtraspecial.GLW4GoodLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem ρ_mul {a b : G} (ha : a ∈ S.M) (hb : b ∈ S.M) :
    S.ρ ⟨a * b, S.M.mul_mem ha hb⟩ = S.ρ ⟨a, ha⟩ * S.ρ ⟨b, hb⟩ := by
  rw [← map_mul]
  exact congrArg S.ρ (Subtype.ext rfl)

theorem ρ_inv {a : G} (ha : a ∈ S.M) : S.ρ ⟨a⁻¹, S.M.inv_mem ha⟩ = (S.ρ ⟨a, ha⟩)⁻¹ := by
  rw [← map_inv]
  exact congrArg S.ρ (Subtype.ext rfl)

omit [Finite G] in
theorem conj_eq_of_isZ {ε g : G} (hε : ε = 1 ∨ ε = S.z) (hg : g ∈ S.M) : g * ε * g⁻¹ = ε := by
  rcases hε with rfl | rfl
  · group
  · rw [S.z_comm hg, mul_inv_cancel_right]

omit [Finite G] in
theorem conj_eq_of_isZ' {ε g : G} (hε : ε = 1 ∨ ε = S.z) (hg : g ∈ S.M) : ε * g * ε⁻¹ = g := by
  rcases hε with rfl | rfl
  · group
  · rw [← S.z_comm hg, mul_inv_cancel_right]

omit [Finite G] in
theorem mem_M_of_isZ {ε : G} (hε : ε = 1 ∨ ε = S.z) : ε ∈ S.M := by
  rcases hε with rfl | rfl
  · exact S.M.one_mem
  · exact S.QG_le_M S.z_mem_QG

omit [Finite G] in
theorem mul_self_of_isZ {ε : G} (hε : ε = 1 ∨ ε = S.z) : ε * ε = 1 := by
  rcases hε with rfl | rfl
  · exact mul_one 1
  · exact S.z_mul_z

omit [Finite G] in
theorem commutator_mul_isZ {a b ε ε' : G} (ha : a ∈ S.M) (hb : b ∈ S.M) (hε : ε = 1 ∨ ε = S.z)
    (hε' : ε' = 1 ∨ ε' = S.z) : ⁅a * ε, b * ε'⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * ε * (b * ε') * (a * ε)⁻¹ * (b * ε')⁻¹
      = a * (ε * (b * ε') * ε⁻¹) * a⁻¹ * ε'⁻¹ * b⁻¹ := by group
    _ = a * b * (ε' * a⁻¹ * ε'⁻¹) * b⁻¹ := by
        rw [conj_eq_of_isZ' hε (S.M.mul_mem hb (mem_M_of_isZ hε'))]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [conj_eq_of_isZ' hε' (S.M.inv_mem ha)]

omit [Finite G] in
theorem commute_of_commutator_eq {a b c ε : G} (hb : b ∈ S.M) (hε : ε = 1 ∨ ε = S.z)
    (hab : ⁅a, b⁆ = ε) (hac : ⁅a, c⁆ = ε) : a * (a * b * c) = (a * b * c) * a := by
  have hεε := mul_self_of_isZ hε
  have hba : b * a = ε * (a * b) := by
    have h1 : a * b = ε * (b * a) := by rw [← hab, commutatorElement_def]; group
    calc b * a = ε * ε * (b * a) := by rw [hεε, one_mul]
      _ = ε * (ε * (b * a)) := by group
      _ = ε * (a * b) := by rw [← h1]
  have hca : c * a = ε * (a * c) := by
    have h1 : a * c = ε * (c * a) := by rw [← hac, commutatorElement_def]; group
    calc c * a = ε * ε * (c * a) := by rw [hεε, one_mul]
      _ = ε * (ε * (c * a)) := by group
      _ = ε * (a * c) := by rw [← h1]
  have hεb : b * ε = ε * b := by
    calc b * ε = b * ε * b⁻¹ * b := by group
      _ = ε * b := by rw [conj_eq_of_isZ hε hb]
  symm
  calc a * b * c * a = a * b * (c * a) := by group
    _ = a * b * (ε * (a * c)) := by rw [hca]
    _ = a * (b * ε) * a * c := by group
    _ = a * (ε * b) * a * c := by rw [hεb]
    _ = a * ε * (b * a) * c := by group
    _ = a * ε * (ε * (a * b)) * c := by rw [hba]
    _ = a * (ε * ε) * a * b * c := by group
    _ = a * (a * b * c) := by rw [hεε]; group

section Lift

variable {A₀ B₀ : Subgroup G} (hA₀ : C.IsZCompl A₀) (hB₀ : IsZComplB C B₀) {σ₀ : G}
  (hσ₀ : σ₀ ∈ S.M) (hσ₀X : σ₀ ∉ C.X)
include hA₀ hB₀ hσ₀ hσ₀X

theorem exists_goodOut_lift {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar) :
    ∃ m : G, ∃ hm : m ∈ S.M, S.ρ ⟨m, hm⟩ = s ∧ GoodOut A₀ B₀ m := by
  obtain ⟨⟨m₀, hm₀⟩, rfl⟩ := hs
  have hm₀X : m₀ ∉ C.X := fun h => hsX (C.ρ_mem_Xbar h hm₀)
  obtain ⟨q, hq, hg⟩ := exists_goodOut hA₀ hB₀ hσ₀ hσ₀X hm₀ hm₀X
  refine ⟨q * m₀, S.M.mul_mem (S.QG_le_M hq) hm₀, ?_, hg⟩
  rw [ρ_mul (S.QG_le_M hq) hm₀, (S.ρ_eq_one_iff ⟨q, S.QG_le_M hq⟩).mpr hq, one_mul]

theorem exists_goodIn_lift {x : S.O} (hx : x ∈ C.Xbar) :
    ∃ m : G, ∃ hm : m ∈ S.M, S.ρ ⟨m, hm⟩ = x ∧ GoodIn A₀ B₀ m := by
  obtain ⟨⟨m₀, hm₀⟩, rfl⟩ := C.Xbar_le hx
  obtain ⟨q, hq, hg⟩ := exists_goodIn hA₀ hB₀ hσ₀ hσ₀X (C.mem_X_iff.mpr ⟨hm₀, hx⟩)
  refine ⟨q * m₀, S.M.mul_mem (S.QG_le_M hq) hm₀, ?_, hg⟩
  rw [ρ_mul (S.QG_le_M hq) hm₀, (S.ρ_eq_one_iff ⟨q, S.QG_le_M hq⟩).mpr hq, one_mul]

omit hσ₀ hσ₀X in
theorem eq_or_eq_mul_z {m m' : G} (hm : m ∈ S.M) (hm' : m' ∈ S.M)
    (hρ : S.ρ ⟨m', hm'⟩ = S.ρ ⟨m, hm⟩) (hg : GoodIn A₀ B₀ (m' * m⁻¹)) :
    m' = m ∨ m' = m * S.z := by
  have hq : m' * m⁻¹ ∈ S.QG := (S.ρ_eq_one_iff ⟨_, S.M.mul_mem hm' (S.M.inv_mem hm)⟩).mp (by
    rw [ρ_mul hm' (S.M.inv_mem hm), ρ_inv hm, hρ, mul_inv_cancel])
  rcases eq_one_or_z_of_goodIn hA₀ hB₀ hq hg with h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · refine Or.inr ?_
    rw [S.z_comm hm]
    calc m' = m' * m⁻¹ * m := by group
      _ = S.z * m := by rw [h]

omit hσ₀ hσ₀X in
theorem commutator_isZ {m m' : G} (hm : m ∈ S.M) (hm' : m' ∈ S.M)
    (hc : S.ρ ⟨m, hm⟩ * S.ρ ⟨m', hm'⟩ = S.ρ ⟨m', hm'⟩ * S.ρ ⟨m, hm⟩)
    (hg : GoodOut A₀ B₀ m) (hg' : GoodOut A₀ B₀ m') : ⁅m, m'⁆ = 1 ∨ ⁅m, m'⁆ = S.z := by
  have hM : ⁅m, m'⁆ ∈ S.M := by
    rw [commutatorElement_def]
    exact S.M.mul_mem (S.M.mul_mem (S.M.mul_mem hm hm') (S.M.inv_mem hm)) (S.M.inv_mem hm')
  have hq : ⁅m, m'⁆ ∈ S.QG := (S.ρ_eq_one_iff ⟨_, hM⟩).mp (by
    have h1 : (⟨⁅m, m'⁆, hM⟩ : S.M) = ⁅(⟨m, hm⟩ : S.M), ⟨m', hm'⟩⁆ := rfl
    rw [h1, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc)
  refine eq_one_or_z_of_goodIn hA₀ hB₀ hq ?_
  rw [commutatorElement_def]
  exact ((hg.mul hg').mul_out hg.inv).mul hg'.inv

end Lift

theorem exists_tau_sigma (e : Basis (Fin 4) (ZMod 2) C.At) {τ₀ : G} (hτ₀M : τ₀ ∈ S.M)
    (hτ₀X : τ₀ ∉ C.X) (hτ₀ : τ₀ * τ₀ = 1) (hN : gram C e (S.ρ ⟨τ₀, hτ₀M⟩) = N) :
    ∃ τ σ : G, ∃ (hτM : τ ∈ S.M) (hσM : σ ∈ S.M), τ ∉ C.X ∧ τ * τ = 1 ∧
      gram C e (S.ρ ⟨τ, hτM⟩) = N ∧ σ ∉ C.X ∧ σ * τ = τ * σ ∧
      (σ * σ = 1 ∨ σ * σ = S.z) ∧ ∀ a, C.formOf (S.ρ ⟨σ, hσM⟩) a a = 0 := by
  obtain ⟨A₀, hA₀⟩ := C.exists_isZCompl
  have hB₀ := isZComplB_conj_outer hA₀ hτ₀M hτ₀X
  have hRX := Config.ρ_not_mem_Xbar hτ₀M hτ₀X
  obtain ⟨s₁, s₂, s₃, x, hs₁, hs₁X, hs₂, hs₂X, hs₃, hs₃X, hx, i₁, c₂, c₃, hRs, hx₁, hx₂, halt⟩ :=
    exists_rho_data e (Config.ρ_mem_Mbar _) hRX hN
  obtain ⟨m₁, hm₁, hρ₁, g₁⟩ := exists_goodOut_lift hA₀ hB₀ hτ₀M hτ₀X hs₁ hs₁X
  obtain ⟨m₂, hm₂, hρ₂, g₂⟩ := exists_goodOut_lift hA₀ hB₀ hτ₀M hτ₀X hs₂ hs₂X
  obtain ⟨m₃, hm₃, hρ₃, g₃⟩ := exists_goodOut_lift hA₀ hB₀ hτ₀M hτ₀X hs₃ hs₃X
  obtain ⟨y, hy, hρy, gy⟩ := exists_goodIn_lift hA₀ hB₀ hτ₀M hτ₀X hx
  have hτM : m₁ * m₂ * m₃ ∈ S.M := S.M.mul_mem (S.M.mul_mem hm₁ hm₂) hm₃
  have hρτ : S.ρ ⟨m₁ * m₂ * m₃, hτM⟩ = S.ρ ⟨τ₀, hτ₀M⟩ := by
    rw [ρ_mul (S.M.mul_mem hm₁ hm₂) hm₃, ρ_mul hm₁ hm₂, hρ₁, hρ₂, hρ₃, hRs]
  have hτX : m₁ * m₂ * m₃ ∉ C.X := fun h => hRX (hρτ ▸ C.ρ_mem_Xbar h hτM)
  have gτ := (g₁.mul g₂).mul_out g₃
  have hRR : S.ρ ⟨τ₀, hτ₀M⟩ * S.ρ ⟨τ₀, hτ₀M⟩ = 1 := by
    rw [← ρ_mul hτ₀M hτ₀M]
    exact (S.ρ_eq_one_iff ⟨τ₀ * τ₀, S.M.mul_mem hτ₀M hτ₀M⟩).mpr
      (show τ₀ * τ₀ ∈ S.QG by rw [hτ₀]; exact S.QG.one_mem)
  have hττ : m₁ * m₂ * m₃ * (m₁ * m₂ * m₃) = 1 := by
    have hQ : m₁ * m₂ * m₃ * (m₁ * m₂ * m₃) ∈ S.QG :=
      (S.ρ_eq_one_iff ⟨_, S.M.mul_mem hτM hτM⟩).mp (by rw [ρ_mul hτM hτM, hρτ, hRR])
    rcases eq_one_or_z_of_goodIn hA₀ hB₀ hQ (gτ.mul gτ) with h | h
    · exact h
    · exfalso
      have hpM : m₁ * m₂ * m₃ * τ₀⁻¹ ∈ S.M := S.M.mul_mem hτM (S.M.inv_mem hτ₀M)
      have hp : m₁ * m₂ * m₃ * τ₀⁻¹ ∈ S.QG := (S.ρ_eq_one_iff ⟨_, hpM⟩).mp (by
        rw [ρ_mul hτM (S.M.inv_mem hτ₀M), ρ_inv hτ₀M, hρτ, mul_inv_cancel])
      apply Config.mul_conj_ne_z hτ₀M hτ₀X (Or.inl hτ₀) hp
      calc m₁ * m₂ * m₃ * τ₀⁻¹ * (τ₀ * (m₁ * m₂ * m₃ * τ₀⁻¹) * τ₀⁻¹)
          = m₁ * m₂ * m₃ * (m₁ * m₂ * m₃) * (τ₀ * τ₀)⁻¹ := by group
        _ = S.z := by rw [h, hτ₀, inv_one, mul_one]
  have hσX : m₁ ∉ C.X := fun h => hs₁X (hρ₁ ▸ C.ρ_mem_Xbar h hm₁)
  have hσσ : m₁ * m₁ = 1 ∨ m₁ * m₁ = S.z := by
    refine eq_one_or_z_of_goodIn hA₀ hB₀ ((S.ρ_eq_one_iff ⟨_, S.M.mul_mem hm₁ hm₁⟩).mp ?_)
      (g₁.mul g₁)
    rw [ρ_mul hm₁ hm₁, hρ₁, i₁]
  have c₁₂ := commutator_isZ hA₀ hB₀ hm₁ hm₂ (by rw [hρ₁, hρ₂]; exact c₂) g₁ g₂
  have hyM : ∀ {m : G}, m ∈ S.M → y * m * y⁻¹ ∈ S.M := fun hm =>
    S.M.mul_mem (S.M.mul_mem hy hm) (S.M.inv_mem hy)
  have hρc : ∀ {m : G} (hm : m ∈ S.M), S.ρ ⟨y * m * y⁻¹, hyM hm⟩ = x * S.ρ ⟨m, hm⟩ * x⁻¹ :=
    fun hm => by rw [ρ_mul (S.M.mul_mem hy hm) (S.M.inv_mem hy), ρ_mul hy hm, ρ_inv hy, hρy]
  obtain ⟨ε₁, hε₁, e₁⟩ : ∃ ε, (ε = 1 ∨ ε = S.z) ∧ y * m₁ * y⁻¹ = m₁ * ε := by
    rcases eq_or_eq_mul_z hA₀ hB₀ hm₁ (hyM hm₁) (by rw [hρc hm₁, hρ₁, hx₁])
      (((gy.mul_out g₁).mul_in gy.inv).mul g₁.inv) with h | h
    exacts [⟨1, Or.inl rfl, by rw [h, mul_one]⟩, ⟨S.z, Or.inr rfl, h⟩]
  obtain ⟨ε₂, hε₂, e₂⟩ : ∃ ε, (ε = 1 ∨ ε = S.z) ∧ y * m₂ * y⁻¹ = m₃ * ε := by
    rcases eq_or_eq_mul_z hA₀ hB₀ hm₃ (hyM hm₂) (by rw [hρc hm₂, hρ₂, hx₂, hρ₃])
      (((gy.mul_out g₂).mul_in gy.inv).mul g₃.inv) with h | h
    exacts [⟨1, Or.inl rfl, by rw [h, mul_one]⟩, ⟨S.z, Or.inr rfl, h⟩]
  have heq : ⁅m₁, m₂⁆ = ⁅m₁, m₃⁆ := by
    have h1 : y * ⁅m₁, m₂⁆ * y⁻¹ = ⁅m₁, m₂⁆ := conj_eq_of_isZ c₁₂ hy
    have h2 : y * ⁅m₁, m₂⁆ * y⁻¹ = ⁅y * m₁ * y⁻¹, y * m₂ * y⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [← h1, h2, e₁, e₂, commutator_mul_isZ hm₁ hm₃ hε₁ hε₂]
  refine ⟨m₁ * m₂ * m₃, m₁, hτM, hm₁, hτX, hττ, by rw [hρτ]; exact hN, hσX,
    commute_of_commutator_eq hm₂ c₁₂ rfl heq.symm, hσσ, fun a => ?_⟩
  rw [hρ₁]
  exact halt a

end CFSG.LargeExtraspecial.GLW4
