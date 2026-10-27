module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableSp4Mat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBoundGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique

section Matrices

variable {F : Type} [Field F]

theorem k32J_eq_minorJ : k32J F = minorJ F := by
  ext i j
  simp [k32J, minorJ_apply]

theorem k32_hsp (M : antiSp F) :
    (glMat (M : GL (Fin 4) F))ᵀ * k32J F * glMat (M : GL (Fin 4) F) = k32J F := by
  rw [k32J_eq_minorJ]
  exact mem_antiSp.mp M.2

theorem k32_glMat_pow_three {M : antiSp F} (hM3 : M ^ 3 = 1) :
    glMat (M : GL (Fin 4) F) ^ 3 = 1 := by
  have h := congrArg (fun x : antiSp F => glMat (x : GL (Fin 4) F)) hM3
  simpa using h

theorem k32_glMat_ne_one {M : antiSp F} (hM1 : M ≠ 1) : glMat (M : GL (Fin 4) F) ≠ 1 := by
  intro h
  exact hM1 (antiSp_ext (by simpa using h))

theorem k32_glMat_comm {M w : antiSp F} (h : w * M = M * w) :
    glMat (M : GL (Fin 4) F) * glMat (w : GL (Fin 4) F) =
      glMat (w : GL (Fin 4) F) * glMat (M : GL (Fin 4) F) := by
  have := congrArg (fun x : antiSp F => glMat (x : GL (Fin 4) F)) h
  simpa using this.symm

end Matrices

section RadA1

variable {F : Type} [Field F] [CharP F 2]

theorem k32_glMat_of_mem_radA1 {w : antiSp F} (hw : w ∈ radA1 F) :
    glMat (w : GL (Fin 4) F) =
      k32UMat 0 (glMat (w : GL (Fin 4) F) 0 2) (glMat (w : GL (Fin 4) F) 0 3)
        (glMat (w : GL (Fin 4) F) 1 2) := by
  obtain ⟨b, c, d, rfl⟩ := hw
  rfl

theorem k32_sp4_radA1_bound {M : antiSp F} (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1)
    {W : Subgroup (antiSp F)} [Finite F] (hW : W ≤ radA1 F) (hC : ∀ w ∈ W, w * M = M * w) :
    Nat.card W ≤ Nat.card F := by
  let σ : W → F × F × F := fun w =>
    (glMat ((w : antiSp F) : GL (Fin 4) F) 0 2, glMat ((w : antiSp F) : GL (Fin 4) F) 0 3,
      glMat ((w : antiSp F) : GL (Fin 4) F) 1 2)
  have hrep : ∀ w : W, glMat ((w : antiSp F) : GL (Fin 4) F) =
      k32UMat 0 (σ w).1 (σ w).2.1 (σ w).2.2 := fun w => k32_glMat_of_mem_radA1 (hW w.2)
  refine k32_card_le_of_dep3 σ (fun s t hst => ?_) (fun s t => ?_)
  · apply Subtype.ext
    apply antiSp_ext
    rw [hrep s, hrep t, hst]
  · refine k32_sigma_dep (k32_hsp M) (k32_glMat_pow_three hM3) (k32_glMat_ne_one hM1) ?_ ?_
    · have := k32_glMat_comm (hC (s : antiSp F) s.2)
      rw [hrep s] at this
      exact this
    · have := k32_glMat_comm (hC (t : antiSp F) t.2)
      rw [hrep t] at this
      exact this

end RadA1

section Core

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem k32_minorAut_mem_radA1 {w : antiSp F} (hw : w ∈ radA2 F) : minorAut F w ∈ radA1 F := by
  obtain ⟨a, b, c, rfl⟩ := hw
  refine ⟨c + a * b + a ^ 2 * 0, b ^ 2 + a * b * 0 + c * 0, a ^ 2, antiSp_ext ?_⟩
  simp only [glMat_minorAut, glMat_uElt, minorMap_uMat]

theorem k32_sp4_core {M : antiSp F} (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1)
    {W : Subgroup (antiSp F)} (hWU : W ≤ antiUnipotent F) (hC : ∀ w ∈ W, w * M = M * w) :
    Nat.card W ≤ Nat.card F := by
  have hmem : ∀ w ∈ W, w ∈ radA1 F ∨ w ∈ radA2 F := by
    intro w hw
    obtain ⟨a, b, c, d, hwe⟩ := hWU hw
    by_cases ha : a = 0
    · exact Or.inl ⟨b, c, d, by rw [hwe, ha]⟩
    · by_cases hd : d = 0
      · exact Or.inr ⟨a, b, c, by rw [hwe, hd]⟩
      · exfalso
        have hcomm := k32_glMat_comm (hC w hw)
        rw [hwe, glMat_uElt] at hcomm
        exact k32_glMat_ne_one hM1
          (k32_reg_eq_one ha hd (k32_hsp M) (k32_glMat_pow_three hM3) hcomm)
  rcases subgroup_le_of_subset_union hmem with h | h
  · exact k32_sp4_radA1_bound hM3 hM1 h hC
  · set ρ := minorAut F with hρ
    set W₂ : Subgroup (antiSp F) := W.map (ρ : antiSp F →* antiSp F) with hW₂
    have hW₂le : W₂ ≤ radA1 F := by
      rintro _ ⟨w, hw, rfl⟩
      exact k32_minorAut_mem_radA1 (h hw)
    have hM₂3 : (ρ M) ^ 3 = 1 := by rw [← map_pow, hM3, map_one]
    have hM₂1 : ρ M ≠ 1 := fun h1 => hM1 (ρ.injective (by rw [h1, map_one]))
    have hC₂ : ∀ x ∈ W₂, x * ρ M = ρ M * x := by
      rintro _ ⟨w, hw, rfl⟩
      change ρ w * ρ M = ρ M * ρ w
      rw [← map_mul, ← map_mul, hC w hw]
    have hcard : Nat.card W₂ = Nat.card W := Subgroup.card_map_of_injective ρ.injective
    rw [← hcard]
    exact k32_sp4_radA1_bound hM₂3 hM₂1 hW₂le hC₂

theorem k32_sp4_inner_bound {M : antiSp F} (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1)
    {W : Subgroup (antiSp F)} (hW : IsPGroup 2 ↥W) (hC : ∀ w ∈ W, w * M = M * w) :
    Nat.card W ≤ Nat.card F := by
  obtain ⟨g, hg⟩ := k32_exists_conj_le (card_and_isSylowTwoOf_antiUnipotent (K := F)).2 hW
  set c : antiSp F →* antiSp F := (MulAut.conj g).toMonoidHom with hc
  set W' := W.map c with hW'
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hW'U : W' ≤ antiUnipotent F := by
    rintro _ ⟨w, hw, rfl⟩
    exact hg w hw
  have hM'3 : (c M) ^ 3 = 1 := by rw [← map_pow, hM3, map_one]
  have hM'1 : c M ≠ 1 := fun h1 => hM1 (hcinj (by rw [h1, map_one]))
  have hC' : ∀ x ∈ W', x * c M = c M * x := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hC w hw]
  have hcard : Nat.card W' = Nat.card W := Subgroup.card_map_of_injective hcinj
  rw [← hcard]
  exact k32_sp4_core hM'3 hM'1 hW'U hC'

end Core


end CFSG.QuasithinUnique.DoubleA3
