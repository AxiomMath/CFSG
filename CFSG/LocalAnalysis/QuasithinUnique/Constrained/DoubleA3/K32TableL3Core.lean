module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableL3Mat
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Core

variable {F : Type} [Field F]

theorem k32_l3_unitri_eq {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ unitriangular 3 F) :
    (u : Matrix (Fin 3) (Fin 3) F) =
      k32U3 ((u : Matrix (Fin 3) (Fin 3) F) 0 1) ((u : Matrix (Fin 3) (Fin 3) F) 0 2)
        ((u : Matrix (Fin 3) (Fin 3) F) 1 2) := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hu
  exact k32U3_eq_of_entries (hlow 1 0 (by decide)) (hlow 2 0 (by decide)) (hlow 2 1 (by decide))
    (hdiag 0) (hdiag 1) (hdiag 2)

theorem k32_l3_unitri_mul {u v : SpecialLinearGroup (Fin 3) F} (hu : u ∈ unitriangular 3 F)
    (hv : v ∈ unitriangular 3 F) :
    ((u * v : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 =
        (u : Matrix (Fin 3) (Fin 3) F) 0 1 + (v : Matrix (Fin 3) (Fin 3) F) 0 1 ∧
      ((u * v : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 =
        (u : Matrix (Fin 3) (Fin 3) F) 1 2 + (v : Matrix (Fin 3) (Fin 3) F) 1 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, k32_l3_unitri_eq hu, k32_l3_unitri_eq hv, k32U3_mul]
  exact ⟨by simp [k32U3], by simp [k32U3]⟩

theorem k32_l3_ext_of_a {u v : SpecialLinearGroup (Fin 3) F} (hu : u ∈ unitriangular 3 F)
    (hv : v ∈ unitriangular 3 F) (hau : (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (hav : (v : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (hb : (u : Matrix (Fin 3) (Fin 3) F) 0 2 = (v : Matrix (Fin 3) (Fin 3) F) 0 2)
    (hc : (u : Matrix (Fin 3) (Fin 3) F) 1 2 = (v : Matrix (Fin 3) (Fin 3) F) 1 2) : u = v := by
  apply Subtype.ext
  rw [k32_l3_unitri_eq hu, k32_l3_unitri_eq hv, hau, hav, hb, hc]

theorem k32_l3_ext_of_c {u v : SpecialLinearGroup (Fin 3) F} (hu : u ∈ unitriangular 3 F)
    (hv : v ∈ unitriangular 3 F) (hcu : (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (hcv : (v : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (ha : (u : Matrix (Fin 3) (Fin 3) F) 0 1 = (v : Matrix (Fin 3) (Fin 3) F) 0 1)
    (hb : (u : Matrix (Fin 3) (Fin 3) F) 0 2 = (v : Matrix (Fin 3) (Fin 3) F) 0 2) : u = v := by
  apply Subtype.ext
  rw [k32_l3_unitri_eq hu, k32_l3_unitri_eq hv, hcu, hcv, ha, hb]

variable [CharP F 2]

theorem k32_l3_dichotomy {T : Matrix (Fin 3) (Fin 3) F} {c' : F} (hc' : c' ≠ 0)
    (hT3 : T ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) F))
    (hns : ¬ ∃ x : F, T = x • (1 : Matrix (Fin 3) (Fin 3) F))
    {V : Subgroup (SpecialLinearGroup (Fin 3) F)} (hV : V ≤ unitriangular 3 F)
    (hC : ∀ u ∈ V, T * (u : Matrix (Fin 3) (Fin 3) F) = (u : Matrix (Fin 3) (Fin 3) F) * T) :
    (∀ u ∈ V, (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) ∨
      (∀ u ∈ V, (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) := by
  have hone : ∀ u ∈ V, (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∨
      (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    intro u hu
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hc⟩ := hcon
    have hcomm := hC u hu
    rw [k32_l3_unitri_eq (hV hu)] at hcomm
    exact hns (k32U3_commute_scalar ha hc hcomm hc' hT3)
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨u₁, hu₁, ha₁⟩, ⟨u₂, hu₂, hc₂⟩⟩ := hcon
  have hc₁ : (u₁ : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := (hone u₁ hu₁).resolve_left ha₁
  have ha₂ : (u₂ : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := (hone u₂ hu₂).resolve_right hc₂
  have hm := hone (u₁ * u₂) (V.mul_mem hu₁ hu₂)
  obtain ⟨hadd, hcadd⟩ := k32_l3_unitri_mul (hV hu₁) (hV hu₂)
  rcases hm with h | h
  · rw [hadd, ha₂, add_zero] at h
    exact ha₁ h
  · rw [hcadd, hc₁, zero_add] at h
    exact hc₂ h

variable [Finite F]

theorem k32_l3_core {T : Matrix (Fin 3) (Fin 3) F} {c' : F} (hc' : c' ≠ 0)
    (hT3 : T ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) F))
    (hns : ¬ ∃ x : F, T = x • (1 : Matrix (Fin 3) (Fin 3) F))
    {V : Subgroup (SpecialLinearGroup (Fin 3) F)} (hV : V ≤ unitriangular 3 F)
    (hC : ∀ u ∈ V, T * (u : Matrix (Fin 3) (Fin 3) F) = (u : Matrix (Fin 3) (Fin 3) F) * T) :
    Nat.card V ≤ Nat.card F := by
  rcases k32_l3_dichotomy hc' hT3 hns hV hC with h | h
  ·
    let σ : V → F × F := fun u =>
      ((u : SpecialLinearGroup (Fin 3) F) 0 2, (u : SpecialLinearGroup (Fin 3) F) 1 2)
    refine k32_card_le_of_dep2 σ (fun s t hst => ?_) (fun s t => ?_)
    · apply Subtype.ext
      exact k32_l3_ext_of_a (hV s.2) (hV t.2) (h _ s.2) (h _ t.2) (congrArg Prod.fst hst)
        (congrArg Prod.snd hst)
    · refine k32l3_sigma_dep hc' hT3 hns ?_ ?_
      · have := hC _ s.2
        rwa [k32_l3_unitri_eq (hV s.2), h _ s.2] at this
      · have := hC _ t.2
        rwa [k32_l3_unitri_eq (hV t.2), h _ t.2] at this
  ·
    let σ : V → F × F := fun u =>
      ((u : SpecialLinearGroup (Fin 3) F) 0 2, (u : SpecialLinearGroup (Fin 3) F) 0 1)
    refine k32_card_le_of_dep2 σ (fun s t hst => ?_) (fun s t => ?_)
    · apply Subtype.ext
      exact k32_l3_ext_of_c (hV s.2) (hV t.2) (h _ s.2) (h _ t.2) (congrArg Prod.snd hst)
        (congrArg Prod.fst hst)
    · refine k32l3_sigma_dep2 hc' hT3 hns ?_ ?_
      · have := hC _ s.2
        rwa [k32_l3_unitri_eq (hV s.2), h _ s.2] at this
      · have := hC _ t.2
        rwa [k32_l3_unitri_eq (hV t.2), h _ t.2] at this

omit [Finite F] in
theorem k32_l3_core_four (hK : ∀ x : F, x ^ 4 = x) {T : Matrix (Fin 3) (Fin 3) F}
    (hdet : T.det = 1) {c' : F} (hc' : c' ≠ 0)
    (hT3 : T ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) F))
    (hns : ¬ ∃ x : F, T = x • (1 : Matrix (Fin 3) (Fin 3) F))
    {V : Subgroup (SpecialLinearGroup (Fin 3) F)} (hV : V ≤ unitriangular 3 F)
    (hC : ∀ u ∈ V, T * (u : Matrix (Fin 3) (Fin 3) F) = (u : Matrix (Fin 3) (Fin 3) F) * T) :
    V = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hcomm := hC u hu
  rcases k32_l3_dichotomy hc' hT3 hns hV hC with h | h
  · have h0 := h u hu
    rw [k32_l3_unitri_eq (hV hu), h0] at hcomm
    obtain ⟨hb, hc⟩ := k32l3_sigma_zero hK hdet hc' hT3 hns hcomm
    apply Subtype.ext
    rw [k32_l3_unitri_eq (hV hu), h0, hb, hc, k32U3_zero, Matrix.SpecialLinearGroup.coe_one]
  · have h0 := h u hu
    rw [k32_l3_unitri_eq (hV hu), h0] at hcomm
    obtain ⟨ha, hb⟩ := k32l3_sigma_zero2 hK hdet hc' hT3 hns hcomm
    apply Subtype.ext
    rw [k32_l3_unitri_eq (hV hu), h0, ha, hb, k32U3_zero, Matrix.SpecialLinearGroup.coe_one]

end Core

end CFSG.QuasithinUnique.DoubleA3
