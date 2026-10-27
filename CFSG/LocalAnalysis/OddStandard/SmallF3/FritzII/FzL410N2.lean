module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Nrm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H2a

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

private theorem sigma4_decomp :
    ∀ a b : Equiv.Perm (Fin 4), a ^ 3 = 1 → a ≠ 1 → b ^ 2 = 1 → b * a * b⁻¹ = a⁻¹ →
      ∀ π : Equiv.Perm (Fin 4), ∃ i : Fin 3, ∃ j : Fin 2,
        π * (a ^ (i : ℕ) * b ^ (j : ℕ))⁻¹ ∈ fzlV4 := by
  decide +kernel

private theorem z2_cube : ∀ x : Multiplicative (ZMod 2), x ^ 3 = 1 → x = 1 := by
  decide +kernel

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem rho_mem_N2 : rho ∈ fzN2 t x₁ x₂ := (fzl_rho_Z D.ctx).1

theorem lam_mem_N2 : lam ∈ fzN2 t x₁ x₂ := (fzl_lam_Z D.ctx).1

theorem N2_decomp (n : G) (hn : n ∈ fzN2 t x₁ x₂) :
    ∃ r ∈ R, ∃ i j : ℕ, i < 3 ∧ j < 2 ∧ n = r * rho ^ i * lam ^ j := by
  obtain ⟨f, hF⟩ := D.exF
  have hρ := D.rho_mem_N2
  have hl := D.lam_mem_N2
  obtain ⟨hf3, hf1⟩ := fzl_f_rho D.ctx D.card_two hF hρ
  obtain ⟨hl2, hlr⟩ := fzl_f_lam D.ctx D.card_two hF hρ hl
  have ha3 : (f ⟨rho, hρ⟩).2 ^ 3 = 1 := by simpa using congrArg Prod.snd hf3
  have ha1 : (f ⟨rho, hρ⟩).2 ≠ 1 := by
    intro h
    apply hf1
    have h1 : (f ⟨rho, hρ⟩).1 ^ 3 = 1 := by simpa using congrArg Prod.fst hf3
    exact Prod.ext (z2_cube _ h1) h
  have hb2 : (f ⟨lam, hl⟩).2 ^ 2 = 1 := by simpa using congrArg Prod.snd hl2
  have hba : (f ⟨lam, hl⟩).2 * (f ⟨rho, hρ⟩).2 * (f ⟨lam, hl⟩).2⁻¹ = ((f ⟨rho, hρ⟩).2)⁻¹ := by
    simpa using congrArg Prod.snd hlr
  obtain ⟨i, j, hij⟩ := sigma4_decomp _ _ ha3 ha1 hb2 hba (f ⟨n, hn⟩).2
  have hmN : rho ^ (i : ℕ) * lam ^ (j : ℕ) ∈ fzN2 t x₁ x₂ :=
    (fzN2 t x₁ x₂).mul_mem (Subgroup.pow_mem _ hρ _) (Subgroup.pow_mem _ hl _)
  have hgN : n * (rho ^ (i : ℕ) * lam ^ (j : ℕ))⁻¹ ∈ fzN2 t x₁ x₂ :=
    (fzN2 t x₁ x₂).mul_mem hn ((fzN2 t x₁ x₂).inv_mem hmN)
  refine ⟨n * (rho ^ (i : ℕ) * lam ^ (j : ℕ))⁻¹, ?_, i, j, i.2, j.2, by group⟩
  rw [D.hR]
  refine (fzl_R_mem_iff D.ctx D.card_two hF _).mpr ⟨hgN, ?_⟩
  have hsub : (⟨n * (rho ^ (i : ℕ) * lam ^ (j : ℕ))⁻¹, hgN⟩ : ↥(fzN2 t x₁ x₂)) =
      ⟨n, hn⟩ * ((⟨rho, hρ⟩ : ↥(fzN2 t x₁ x₂)) ^ (i : ℕ) *
        (⟨lam, hl⟩ : ↥(fzN2 t x₁ x₂)) ^ (j : ℕ))⁻¹ := by
    apply Subtype.ext
    simp
  rw [hsub, map_mul, map_inv, map_mul, map_pow, map_pow]
  refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ?_⟩
  simpa using hij

theorem N2_le_M : fzN2 t x₁ x₂ ≤ fz410M R E := by
  have hρ := D.rho_mem_N2
  have hl := D.lam_mem_N2
  have hRn : ∀ n ∈ fzN2 t x₁ x₂, n ∈ normalizer (R : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [D.hR]
    constructor
    · exact fzl_R_normal t x₁ x₂ n hn h
    · intro hh
      have := fzl_R_normal t x₁ x₂ n⁻¹ ((fzN2 t x₁ x₂).inv_mem hn) _ hh
      simpa [mul_assoc] using this
  have hρE : rho ∈ normalizer (E : Set G) := by
    have hr3 : rho * rho * rho = 1 := by
      have := D.str.rho_ord
      simp only [pow_succ, pow_zero, one_mul] at this
      exact this
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact D.str.rho_nrm_E h
    · intro hh
      have h1 := D.str.rho_nrm_E _ hh
      have h2 := D.str.rho_nrm_E _ h1
      have h3 : rho * (rho * (rho * h * rho⁻¹) * rho⁻¹) * rho⁻¹ =
          (rho * rho * rho) * h * (rho * rho * rho)⁻¹ := by group
      rw [h3, hr3] at h2
      simpa using h2
  have hlE : lam ∈ normalizer (E : Set G) := by
    have hl2 : lam * lam = 1 := by rw [← pow_two]; exact D.str.lam_sq
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact D.str.lam_E.1 h
    · intro hh
      have h1 := D.str.lam_E.1 _ hh
      have h3 : lam * (lam * h * lam⁻¹) * lam⁻¹ = (lam * lam) * h * (lam * lam)⁻¹ := by group
      rw [h3, hl2] at h1
      simpa using h1
  intro n hn
  refine Subgroup.mem_inf.mpr ⟨hRn n hn, ?_⟩
  obtain ⟨r, hr, i, j, -, -, rfl⟩ := D.N2_decomp n hn
  have hrE : r ∈ normalizer (E : Set G) := (Subgroup.mem_inf.mp (D.R_le_M hr)).2
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrE (Subgroup.pow_mem _ hρE i))
    (Subgroup.pow_mem _ hlE j)

theorem rho_mem_M : rho ∈ fz410M R E := D.N2_le_M D.rho_mem_N2

theorem lam_mem_M : lam ∈ fz410M R E := D.N2_le_M D.lam_mem_N2

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
