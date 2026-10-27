module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthAutFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthInduced

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

variable {G : Type} [Group G]

theorem OrthCoord.inner_of_even {K M : Subgroup G} {ρ : ↥K →* Perm (Fin 5)} {θ : G → Fv5}
    (hC : OrthCoord K M ρ θ) (hMp : M = CFSG.Open.pCoreOf 2 K) {φ : G → G}
    (hφ : IsIsoOn K K φ) {σ : Perm (Fin 5)} (hσ : sign σ = 1)
    (hind : ∀ l : ↥K, ρ ⟨φ l, hφ.mem l l.2⟩ = σ * ρ l * σ⁻¹) :
    ∃ g ∈ K, ∀ y ∈ K, φ y = g * y * g⁻¹ := by
  classical
  obtain ⟨l₀, hl₀⟩ := hC.surj σ hσ
  let φ' : G → G := fun y => (l₀ : G)⁻¹ * φ y * l₀
  have hφ' : IsIsoOn K K φ' := by
    have hcomp : IsIsoOn K K ((fun x => (l₀ : G)⁻¹ * x * ((l₀ : G)⁻¹)⁻¹) ∘ φ) :=
      hφ.comp (isIsoOn_conj (K.inv_mem l₀.2))
    refine hcomp.congr fun x hx => ?_
    show (l₀ : G)⁻¹ * φ x * ((l₀ : G)⁻¹)⁻¹ = (l₀ : G)⁻¹ * φ x * l₀
    rw [inv_inv]
  have hb : ∀ l : ↥K, ρ ⟨φ' l, hφ'.mem l l.2⟩ = ρ l := by
    intro l
    have hsub : (⟨φ' l, hφ'.mem l l.2⟩ : ↥K) = l₀⁻¹ * ⟨φ l, hφ.mem l l.2⟩ * l₀ := by
      apply Subtype.ext
      simp [φ']
    calc ρ ⟨φ' l, hφ'.mem l l.2⟩
        = ρ (l₀⁻¹ * ⟨φ l, hφ.mem l l.2⟩ * l₀) := by rw [hsub]
      _ = (ρ l₀)⁻¹ * ρ ⟨φ l, hφ.mem l l.2⟩ * ρ l₀ := by rw [map_mul, map_mul, map_inv]
      _ = (ρ l₀)⁻¹ * (σ * ρ l * σ⁻¹) * ρ l₀ := by rw [hind l]
      _ = ρ l := by rw [hl₀]; group
  have hmem : ∀ y ∈ K, φ' y * y⁻¹ ∈ M := by
    intro y hy
    have hρ : ρ (⟨φ' y * y⁻¹, K.mul_mem (hφ'.mem y hy) (K.inv_mem hy)⟩ : ↥K) = 1 := by
      have hsub : (⟨φ' y * y⁻¹, K.mul_mem (hφ'.mem y hy) (K.inv_mem hy)⟩ : ↥K)
          = ⟨φ' y, hφ'.mem y hy⟩ * ⟨y, hy⟩⁻¹ := by
        apply Subtype.ext
        simp
      rw [hsub, map_mul, hb ⟨y, hy⟩, map_inv, mul_inv_cancel]
    simpa using
      (hC.ker (⟨φ' y * y⁻¹, K.mul_mem (hφ'.mem y hy) (K.inv_mem hy)⟩ : ↥K)).mp hρ
  have hfixM : ∀ m ∈ M, φ' m = m := by
    intro m hm
    have hmK : m ∈ K := hC.le hm
    have hφmM : φ m ∈ M := by
      have hmP : m ∈ CFSG.Open.pCoreOf 2 K := by simpa [hMp] using hm
      simpa [hMp] using IsIsoOn.map_mem_pCoreOf hφ hmP
    have hcmM : φ' m ∈ M := by
      have h := hC.conj_mem (l₀⁻¹) hφmM
      simpa [φ'] using h
    by_cases hm1 : m = 1
    · rw [hm1, IsIsoOn.map_one hφ']
    · have hfix : ∀ l ∈ K, l * m * l⁻¹ = m → l * φ' m * l⁻¹ = φ' m := by
        intro l hl hlm
        have hml : φ' l * l⁻¹ ∈ M := hmem l hl
        have hlcM : l * φ' m * l⁻¹ ∈ M := hC.conj_mem' hl hcmM
        have hφ'l : φ' l = (φ' l * l⁻¹) * l := by group
        have hconj : φ' (l * m * l⁻¹) = φ' l * φ' m * (φ' l)⁻¹ :=
          IsIsoOn.map_conj hφ' hl hmK
        have heq1 : φ' (l * m * l⁻¹) = φ' m := by rw [hlm]
        have hcomm : (φ' l * l⁻¹) * (l * φ' m * l⁻¹)
            = (l * φ' m * l⁻¹) * (φ' l * l⁻¹) := hC.comm hml hlcM
        have hcalc : φ' l * φ' m * (φ' l)⁻¹ = l * φ' m * l⁻¹ := by
          rw [hφ'l]
          calc (φ' l * l⁻¹) * l * φ' m * ((φ' l * l⁻¹) * l)⁻¹
              = (φ' l * l⁻¹) * (l * φ' m * l⁻¹) * (φ' l * l⁻¹)⁻¹ := by group
            _ = (l * φ' m * l⁻¹) * (φ' l * l⁻¹) * (φ' l * l⁻¹)⁻¹ := by rw [hcomm]
            _ = l * φ' m * l⁻¹ := by group
        calc l * φ' m * l⁻¹ = φ' l * φ' m * (φ' l)⁻¹ := hcalc.symm
          _ = φ' (l * m * l⁻¹) := hconj.symm
          _ = φ' m := heq1
      rcases hC.eq_one_or_eq_of_fix hm hm1 hcmM hfix with h | h
      · exact absurd (hφ'.injOn m hmK 1 K.one_mem
          (h.trans (IsIsoOn.map_one hφ').symm)) hm1
      · exact h
  obtain ⟨c₀, hc₀M, hc₀⟩ := hC.exists_inner_of_fix hφ' hfixM
  refine ⟨(l₀ : G) * c₀, K.mul_mem l₀.2 (hC.le hc₀M), fun y hy => ?_⟩
  calc φ y = (l₀ : G) * φ' y * (l₀ : G)⁻¹ := by simp only [φ']; group
    _ = (l₀ : G) * (c₀ * y * c₀⁻¹) * (l₀ : G)⁻¹ := by rw [hc₀ y hy]
    _ = ((l₀ : G) * c₀) * y * ((l₀ : G) * c₀)⁻¹ := by group

theorem OrthCoord.out_aut {K M : Subgroup G} {ρ : ↥K →* Perm (Fin 5)} {θ : G → Fv5}
    (hC : OrthCoord K M ρ θ) (hMp : M = CFSG.Open.pCoreOf 2 K) {φ₁ φ₂ : G → G}
    (h₁ : IsIsoOn K K φ₁) (h₂ : IsIsoOn K K φ₂)
    (n₁ : ¬ ∃ g ∈ K, ∀ y ∈ K, φ₁ y = g * y * g⁻¹)
    (n₂ : ¬ ∃ g ∈ K, ∀ y ∈ K, φ₂ y = g * y * g⁻¹) :
    ∃ g ∈ K, ∀ y ∈ K, φ₁ (φ₂ y) = g * y * g⁻¹ := by
  classical
  obtain ⟨σ₁, hσ₁⟩ := hC.exists_induced hMp h₁
  obtain ⟨σ₂, hσ₂⟩ := hC.exists_induced hMp h₂
  have hs1 : sign σ₁ = -1 := by
    rcases Int.units_eq_one_or (sign σ₁) with h | h
    · exact absurd (hC.inner_of_even hMp h₁ h hσ₁) n₁
    · exact h
  have hs2 : sign σ₂ = -1 := by
    rcases Int.units_eq_one_or (sign σ₂) with h | h
    · exact absurd (hC.inner_of_even hMp h₂ h hσ₂) n₂
    · exact h
  have hψ : IsIsoOn K K (φ₁ ∘ φ₂) := h₂.comp h₁
  have hind : ∀ l : ↥K, ρ ⟨(φ₁ ∘ φ₂) l, hψ.mem l l.2⟩
      = (σ₁ * σ₂) * ρ l * (σ₁ * σ₂)⁻¹ := by
    intro l
    have hsub : (⟨(φ₁ ∘ φ₂) l, hψ.mem l l.2⟩ : ↥K)
        = ⟨φ₁ (φ₂ l), h₁.mem (φ₂ l) (h₂.mem l l.2)⟩ := by
      apply Subtype.ext
      simp only [Function.comp_apply]
    rw [hsub, hσ₁ ⟨φ₂ l, h₂.mem l l.2⟩, hσ₂ l]
    group
  have hs : sign (σ₁ * σ₂) = 1 := by
    rw [Equiv.Perm.sign_mul, hs1, hs2]
    exact Int.units_mul_self (-1)
  have hres := hC.inner_of_even hMp hψ hs hind
  simpa only [Function.comp_apply] using hres

end CFSG.EvenSporadicStandard.HNRecog.Section4
