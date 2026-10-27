module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Norm
public import CFSG.LocalAnalysis.EvenBN.Common.SwapUnique
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4R2Two

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.GroupTheory
open scoped commutatorElement

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem isSylowOf_R (h : d.Hyp) :
    CFSG.ABGLocalTools.IsSylowOf 2 d.R (d.L ⊔ zpowers d.t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLt : d.L ≤ centralizer ({d.t} : Set G) := h.L_le_H
  have hSt : d.S ≤ centralizer ({d.t} : Set G) := (d.pull_le_L _).trans hLt
  have hR : Nat.card d.R = 2 * Nat.card d.S :=
    Common.SwapUnique.card_sup_zpowers_of_le_centralizer h.t_mul_t hSt
      (fun ht => h.t_not_mem_L (d.pull_le_L _ ht))
  have hK : Nat.card (d.L ⊔ zpowers d.t : Subgroup G) = 2 * Nat.card d.L :=
    Common.SwapUnique.card_sup_zpowers_of_le_centralizer h.t_mul_t hLt h.t_not_mem_L
  have hL : Nat.card d.L = 13685760 := by
    rw [Nat.card_congr d.η.toEquiv]
    exact card_SU52.1
  have hle : d.R ≤ d.L ⊔ zpowers d.t := sup_le_sup_right (d.pull_le_L _) _
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hle, IsPGroup.of_card (n := 11) ?_, ?_⟩
  · rw [hR, d.card_S]
    norm_num
  · have h1 := Subgroup.relIndex_mul_card d.R (d.L ⊔ zpowers d.t)
    rw [inf_eq_left.2 hle, hK, hR, hL, d.card_S] at h1
    have h2 : d.R.relIndex (d.L ⊔ zpowers d.t) = 13365 := by omega
    rw [h2]
    decide

section B4


theorem Y_le_K (h : d.Hyp) (hK₃ : d.K₃ ≤ d.K) (hLev : d.Lev ≤ zpowers d.e₂ ⊔ d.K₃) :
    d.Y ≤ d.K := by
  rw [h.Y_eq_E₂]
  show ⁅d.Lev, d.U⁆ ≤ d.K
  have hUN : ∀ b ∈ d.U, b ∈ normalizer (d.K : Set G) := fun b hb =>
    d.mem_normalizer_K (Subgroup.le_normalizer (Subgroup.mem_inf.1 hb).2)
  let S₀ : Subgroup G :=
    { carrier := {a | a ∈ normalizer (d.K : Set G) ∧ ∀ b ∈ d.U, ⁅a, b⁆ ∈ d.K}
      mul_mem' := by
        rintro a a' ⟨hNa, hca⟩ ⟨hNa', hca'⟩
        refine ⟨(normalizer (d.K : Set G)).mul_mem hNa hNa', fun b hbU => ?_⟩
        have e : ⁅a * a', b⁆ = a * ⁅a', b⁆ * a⁻¹ * ⁅a, b⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact d.K.mul_mem ((mem_normalizer_iff.1 hNa _).1 (hca' b hbU)) (hca b hbU)
      one_mem' := ⟨one_mem _, fun b _ => by simp⟩
      inv_mem' := by
        rintro a ⟨hNa, hca⟩
        refine ⟨(normalizer (d.K : Set G)).inv_mem hNa, fun b hbU => ?_⟩
        have e : ⁅a⁻¹, b⁆ = a⁻¹ * ⁅a, b⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (mem_normalizer_iff.1 ((normalizer (d.K : Set G)).inv_mem hNa) _).1
          (d.K.inv_mem (hca b hbU))
        simpa using this }
  have he₂ : d.e₂ ∈ S₀ := by
    refine ⟨d.mem_normalizer_K (Subgroup.le_normalizer (mem_centralizer_singleton_iff.2 rfl)),
      fun b hbU => ?_⟩
    have hbc : b * d.e₂ = d.e₂ * b := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hbU).2
    exact (commutatorElement_eq_one_iff_mul_comm.2 hbc.symm) ▸ d.K.one_mem
  have hK₃S : d.K₃ ≤ S₀ := fun k hk => by
    have hkK : k ∈ d.K := hK₃ hk
    refine ⟨Subgroup.le_normalizer hkK, fun b hbU => ?_⟩
    have e : ⁅k, b⁆ = k * (b * k⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def, mul_assoc]
    rw [e]
    exact d.K.mul_mem hkK ((mem_normalizer_iff.1 (hUN b hbU) k⁻¹).1 (d.K.inv_mem hkK))
  have hS₀ : zpowers d.e₂ ⊔ d.K₃ ≤ S₀ := sup_le (zpowers_le.2 he₂) hK₃S
  rw [commutator_le]
  intro a ha b hb
  exact (hS₀ (hLev ha)).2 b hb

theorem normalizer_R_le_normalizer_Dsub (h : d.Hyp) (hWK : d.W ≤ d.K) :
    normalizer (d.R : Set G) ≤ normalizer (d.Dsub : Set G) := by
  intro g hg
  have hgZ := h.normalizer_R_le_normalizer_ZR hg
  obtain ⟨c, hcH, hcz, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_normalizer_ZR hgZ
  exact mul_mem (h.H_le_normalizer_Dsub hcH)
    (Subgroup.le_normalizer (d.K_le_Dsub (hWK hw)))

end B4

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
