module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParY
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {t : OGroup Q}

theorem fx_aut6_piOrth_mul_t_eq (htt : t * t = 1) :
    (piOrth Q * t : OGroup Q) = blockHom htt (piOrth (Q.restrict (fixSp t)), 1) := by
  have h1 := blockHom_piOrth_piOrth htt
  have h2 := blockHom_one_piOrth htt
  calc piOrth Q * t
      = blockHom htt (piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) *
          blockHom htt (1, piOrth (Q.restrict (commSp t))) := by rw [h1, h2]
    _ = blockHom htt ((piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) *
          (1, piOrth (Q.restrict (commSp t)))) := (map_mul _ _ _).symm
    _ = blockHom htt (piOrth (Q.restrict (fixSp t)), 1) := by
          rw [Prod.mk_mul_mk, mul_one, piOrth_mul_self]

theorem fx_aut6_involution_cases (D : Om6Par Q t) {b : OGroup (Q.restrict (fixSp t))}
    (hbb : b * b = 1) :
    b = 1 ∨ b = piOrth (Q.restrict (fixSp t)) ∨ ∃ α : ℤˣ, invType b = (1, α) := by
  have hle : invDim b ≤ 2 := by
    have h := invDim_le b
    rwa [D.dimP] at h
  rcases (by omega : invDim b = 0 ∨ invDim b = 1 ∨ invDim b = 2) with h | h | h
  · exact Or.inl ((invDim_eq_zero_iff hbb).mp h)
  · exact Or.inr (Or.inr ⟨invSign b, Prod.ext h rfl⟩)
  · exact Or.inr (Or.inl ((invDim_eq_finrank_iff hbb).mp (by rw [D.dimP]; exact h)))

theorem fx_aut6_one_cases (D : Om6Par Q t) {g : OGroup Q} (hgg : g * g = 1)
    (hW : ∀ w ∈ commSp t, (g : V ≃ₗ[ZMod 3] V) w = w)
    (hP : ∀ p ∈ fixSp t, (g : V ≃ₗ[ZMod 3] V) p ∈ fixSp t) :
    g = 1 ∨ g = piOrth Q * t ∨ ∃ α : ℤˣ, invType g = (1, α) := by
  obtain ⟨b, hb⟩ := (FGSplit.comm D.nd D.htt).ext_surj g (fun w => hW w w.2) (fun p => hP p p.2)
  have hbg : blockHom D.htt (b, 1) = g := hb
  have hbb : b * b = 1 := by
    have h : blockHom D.htt (b * b, 1) = blockHom D.htt 1 := by
      rw [map_one, ← hgg, ← hbg, ← map_mul]
      rfl
    exact congrArg Prod.fst (blockHom_injective D.htt h)
  rcases fx_aut6_involution_cases D hbb with h | h | ⟨α, hα⟩
  · left
    rw [← hbg, h]
    exact map_one _
  · right
    left
    rw [← hbg, h, fx_aut6_piOrth_mul_t_eq D.htt]
  · right
    right
    exact ⟨α, by rw [← hbg, ff_invType_blockHom_inl D.nd D.htt hbb, hα]⟩

private theorem fx_aut6_piOrth_comm (g : OGroup Q) : piOrth Q * g = g * piOrth Q :=
  (Subgroup.mem_center_iff.mp piOrth_mem_center g).symm

theorem fx_aut6_cent_cases (D : Om6Par Q t) {y : simGroup Q}
    (hy : ∀ u ∈ D.L ⊔ D.R, simAct Q y u = u) (hy2 : y * y ∈ piSim Q) :
    y ∈ piSim Q ∨ y * orthToSim Q t ∈ piSim Q ∨
      ∃ g : OGroup Q, g * g = 1 ∧ (∃ α : ℤˣ, invType g = (1, α)) ∧
        ∃ k ∈ piSim Q, y = orthToSim Q g * k := by
  obtain ⟨hP, ⟨c, hc1, hcw⟩, hiso⟩ := D.cent_data hy
  let y₀ : OGroup Q := ⟨(y : V ≃ₗ[ZMod 3] V), hiso⟩
  have hy0 : y = orthToSim Q y₀ := rfl
  have hc2 : c * c = 1 := by rcases hc1 with rfl | rfl <;> decide
  have hsq : y₀ * y₀ = 1 := by
    rcases mem_piSim_iff.mp hy2 with h | h
    · exact orthToSim_injective (by rw [map_mul, ← hy0, h, map_one])
    · exfalso
      obtain ⟨w, hw, hw0⟩ := D.exists_W
      have h1 : (y : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) w) = w := by
        rw [hcw w hw, map_smul, hcw w hw, smul_smul, hc2, one_smul]
      have h2 : (y : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) w) = -w := by
        have := congrArg (fun s : simGroup Q => (s : V ≃ₗ[ZMod 3] V) w) h
        simpa [coe_piOrth_apply] using this
      have h3 : (2 : ZMod 3) • w = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h1]
        rw [h2]
        exact neg_add_cancel w
      exact hw0 (by
        have h4 := congrArg (fun v => (2 : ZMod 3)⁻¹ • v) h3
        simpa [smul_smul] using h4)
  rcases hc1 with rfl | rfl
  · rcases fx_aut6_one_cases D hsq
      (fun w hw => by simpa using hcw w hw) hP with h | h | ⟨α, hα⟩
    · left
      exact mem_piSim_iff.mpr (Or.inl (by rw [hy0, h, map_one]))
    · right
      left
      refine mem_piSim_iff.mpr (Or.inr ?_)
      rw [hy0, h, ← map_mul, mul_assoc, D.htt, mul_one]
    · exact Or.inr (Or.inr ⟨y₀, hsq, ⟨α, hα⟩, 1, one_mem _, by rw [mul_one, hy0]⟩)
  · set g : OGroup Q := piOrth Q * y₀ with hg
    have hπ2 : piOrth Q * piOrth Q = 1 := piOrth_mul_self
    have hgg : g * g = 1 := by
      rw [hg, mul_assoc, ← mul_assoc y₀, ← fx_aut6_piOrth_comm y₀, mul_assoc, hsq, mul_one, hπ2]
    have hgW : ∀ w ∈ commSp t, (g : V ≃ₗ[ZMod 3] V) w = w := by
      intro w hw
      change (piOrth Q : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) w) = w
      rw [hcw w hw, coe_piOrth_apply]
      simp
    have hgP : ∀ p ∈ fixSp t, (g : V ≃ₗ[ZMod 3] V) p ∈ fixSp t := by
      intro p hp
      change (piOrth Q : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) p) ∈ fixSp t
      rw [coe_piOrth_apply]
      exact (fixSp t).neg_mem (hP p hp)
    have hy0g : y₀ = piOrth Q * g := by rw [hg, ← mul_assoc, hπ2, one_mul]
    rcases fx_aut6_one_cases D hgg hgW hgP with h | h | ⟨α, hα⟩
    · left
      refine mem_piSim_iff.mpr (Or.inr ?_)
      rw [hy0, hy0g, h, mul_one]
    · right
      left
      refine mem_piSim_iff.mpr (Or.inl ?_)
      have : y₀ = t := by rw [hy0g, h, ← mul_assoc, hπ2, one_mul]
      rw [hy0, this, ← map_mul, D.htt, map_one]
    · refine Or.inr (Or.inr ⟨g, hgg, ⟨α, hα⟩, orthToSim Q (piOrth Q),
        mem_piSim_iff.mpr (Or.inr rfl), ?_⟩)
      rw [hy0, hy0g, fx_aut6_piOrth_comm g, map_mul]

end CFSG.OddStandard.SmallF3.Omega
