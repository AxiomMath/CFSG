module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthAutFix

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

private def NoCommOrderThree (σ τ : Perm (Fin 5)) : Prop :=
  sign σ = 1 → sign τ = 1 → σ * σ = 1 → τ ^ 3 = 1 → τ ≠ 1 → σ * τ = τ * σ → σ = 1

private instance (σ τ : Perm (Fin 5)) : Decidable (NoCommOrderThree σ τ) := by
  unfold NoCommOrderThree; infer_instance

theorem eq_one_of_comm_order_three : ∀ σ τ : Perm (Fin 5), sign σ = 1 → sign τ = 1 →
    σ * σ = 1 → τ ^ 3 = 1 → τ ≠ 1 → σ * τ = τ * σ → σ = 1 := by
  have h : ∀ σ τ : Perm (Fin 5), NoCommOrderThree σ τ := by decide +kernel
  exact fun σ τ => h σ τ

variable {G : Type} [Group G] {K M : Subgroup G} {ρ : ↥K →* Perm (Fin 5)} {θ : G → Fv5}

theorem OrthCoord.mem_of_comm_order_three (hC : OrthCoord K M ρ θ) {y ε : G} (hy : y ∈ K)
    (hε : ε ∈ K) (hy2 : y * y = 1) (hε3 : ε ^ 3 = 1) (hε1 : ε ≠ 1) (hcomm : y * ε = ε * y) :
    y ∈ M := by
  have hεM : ρ ⟨ε, hε⟩ ≠ 1 := fun h1 => by
    have hM : ε ∈ M := (hC.ker ⟨ε, hε⟩).mp h1
    have h2 : ε * ε = 1 := hC.mul_self_eq_one hM
    have h3 : ε ^ 3 = ε := by
      calc ε ^ 3 = (ε * ε) * ε := by rw [pow_succ, pow_two]
        _ = ε := by rw [h2, one_mul]
    exact hε1 (h3.symm.trans hε3)
  have hσ2 : ρ ⟨y, hy⟩ * ρ ⟨y, hy⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hy⟩ : ↥K) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
    rw [this, map_one]
  have hτ3 : ρ ⟨ε, hε⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨ε, hε⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hε3)
    rw [this, map_one]
  have hcomm' : ρ ⟨y, hy⟩ * ρ ⟨ε, hε⟩ = ρ ⟨ε, hε⟩ * ρ ⟨y, hy⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext hcomm)
  have h1 := eq_one_of_comm_order_three _ _ (hC.sign_eq ⟨y, hy⟩) (hC.sign_eq ⟨ε, hε⟩) hσ2 hτ3 hεM
    hcomm'
  exact (hC.ker ⟨y, hy⟩).mp h1

theorem OrthCoord.aut_cent (hC : OrthCoord K M ρ θ) {y : G} (hy : y ∈ M) (hy1 : y ≠ 1)
    {φ : G → G} (hφ : IsIsoOn K K φ) (hfix : ∀ l ∈ K, y * l = l * y → φ l = l) :
    (∀ l ∈ K, φ l = l) ∨ ∀ l ∈ K, φ l = y * l * y⁻¹ := by
  obtain ⟨c, hcM, hc⟩ := hC.exists_inner_of_fix hφ
    (fun x hx => hfix x (hC.le hx) (hC.comm hy hx))
  have hkey : c = 1 ∨ c = y := by
    refine hC.eq_one_or_eq_of_fix hy hy1 hcM fun l hl hly => ?_
    have hyl : y * l = l * y := by
      calc y * l = (l * y * l⁻¹) * l := by rw [hly]
        _ = l * y := by group
    have hcl : c * l * c⁻¹ = l := (hc l hl).symm.trans (hfix l hl hyl)
    have hcl' : c * l = l * c := by
      calc c * l = (c * l * c⁻¹) * c := by group
        _ = l * c := by rw [hcl]
    calc l * c * l⁻¹ = (c * l) * l⁻¹ := by rw [hcl']
      _ = c := by group
  rcases hkey with rfl | rfl
  · left
    intro l hl
    rw [hc l hl]
    group
  · right
    exact hc

end CFSG.EvenSporadicStandard.HNRecog.Section4
