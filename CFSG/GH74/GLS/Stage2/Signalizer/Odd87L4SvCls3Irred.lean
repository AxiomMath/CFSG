module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls3Hom

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section Irred

variable {F : Type} [Field F]

theorem cls3_eFirst_mulVec (H : Matrix (Fin 3) (Fin 3) F) (w : Fin 4 → F) :
    eFirst H *ᵥ w = ![w 0, (H *ᵥ ![w 1, w 2, w 3]) 0, (H *ᵥ ![w 1, w 2, w 3]) 1,
      (H *ᵥ ![w 1, w 2, w 3]) 2] := by
  funext i
  fin_cases i <;> simp [eFirst, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four]

theorem cls3_eLast_mulVec (H : Matrix (Fin 3) (Fin 3) F) (w : Fin 4 → F) :
    eLast H *ᵥ w = ![(H *ᵥ ![w 0, w 1, w 2]) 0, (H *ᵥ ![w 0, w 1, w 2]) 1,
      (H *ᵥ ![w 0, w 1, w 2]) 2, w 3] := by
  funext i
  fin_cases i <;> simp [eLast, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four]

@[expose] def cls3LowA : (Fin 3 → F) →ₗ[F] (Fin 4 → F) where
  toFun u := ![0, u 0, u 1, u 2]
  map_add' u v := by funext i; fin_cases i <;> simp
  map_smul' c u := by funext i; fin_cases i <;> simp

@[expose] def cls3LowB : (Fin 3 → F) →ₗ[F] (Fin 4 → F) where
  toFun u := ![u 0, u 1, u 2, 0]
  map_add' u v := by funext i; fin_cases i <;> simp
  map_smul' c u := by funext i; fin_cases i <;> simp

theorem cls3LowA_apply (u : Fin 3 → F) : cls3LowA u = ![0, u 0, u 1, u 2] := rfl

theorem cls3LowB_apply (u : Fin 3 → F) : cls3LowB u = ![u 0, u 1, u 2, 0] := rfl

theorem cls3_eFirst_mulVec_lowA (H : Matrix (Fin 3) (Fin 3) F) (u : Fin 3 → F) :
    eFirst H *ᵥ cls3LowA u = cls3LowA (H *ᵥ u) := by
  funext i
  fin_cases i <;> simp [eFirst, cls3LowA_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Fin.sum_univ_four]

theorem cls3_eLast_mulVec_lowB (H : Matrix (Fin 3) (Fin 3) F) (u : Fin 3 → F) :
    eLast H *ᵥ cls3LowB u = cls3LowB (H *ᵥ u) := by
  funext i
  fin_cases i <;> simp [eLast, cls3LowB_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Fin.sum_univ_four]

theorem cls3_dichotomyA {e : Fin 3 → F} {ρ : SL(2, F) →* SL(3, F)} (hρ : DiagAd e ρ) (h2 : (2 : F) ≠ 0)
    (W : Submodule F (Fin 4 → F))
    (hW : ∀ S : SL(2, F), ∀ w ∈ W, eFirst (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) :
    (∀ w ∈ W, w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) ∨ (∀ u : Fin 3 → F, cls3LowA u ∈ W) := by
  have hinv : ∀ S : SL(2, F), ∀ u ∈ W.comap cls3LowA,
      (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ W.comap cls3LowA := by
    intro S u hu
    rw [Submodule.mem_comap] at hu ⊢
    have h1 := hW S _ hu
    rwa [cls3_eFirst_mulVec_lowA] at h1
  rcases hρ.irr (W.comap cls3LowA) hinv with h | h
  · left
    intro w hw
    have hfix : ∀ S : SL(2, F), (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ ![w 1, w 2, w 3] =
        ![w 1, w 2, w 3] := by
      intro S
      have h1 := W.sub_mem (hW S w hw) hw
      have h3 : eFirst (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w =
          cls3LowA ((ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ ![w 1, w 2, w 3] - ![w 1, w 2, w 3]) := by
        rw [cls3_eFirst_mulVec, cls3LowA_apply]
        funext i
        fin_cases i <;> simp
      rw [h3] at h1
      have h4 : (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ ![w 1, w 2, w 3] - ![w 1, w 2, w 3] ∈
          W.comap cls3LowA := h1
      rw [h, Submodule.mem_bot, sub_eq_zero] at h4
      exact h4
    have h5 := hρ.fixed_vec h2 hfix
    exact ⟨congrFun h5 0, congrFun h5 1, congrFun h5 2⟩
  · right
    intro u
    have : u ∈ W.comap cls3LowA := by rw [h]; trivial
    exact this

theorem cls3_dichotomyB {e : Fin 3 → F} {ρ : SL(2, F) →* SL(3, F)} (hρ : DiagAd e ρ) (h2 : (2 : F) ≠ 0)
    (W : Submodule F (Fin 4 → F))
    (hW : ∀ S : SL(2, F), ∀ w ∈ W, eLast (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) :
    (∀ w ∈ W, w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0) ∨ (∀ u : Fin 3 → F, cls3LowB u ∈ W) := by
  have hinv : ∀ S : SL(2, F), ∀ u ∈ W.comap cls3LowB,
      (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ W.comap cls3LowB := by
    intro S u hu
    rw [Submodule.mem_comap] at hu ⊢
    have h1 := hW S _ hu
    rwa [cls3_eLast_mulVec_lowB] at h1
  rcases hρ.irr (W.comap cls3LowB) hinv with h | h
  · left
    intro w hw
    have hfix : ∀ S : SL(2, F), (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ ![w 0, w 1, w 2] =
        ![w 0, w 1, w 2] := by
      intro S
      have h1 := W.sub_mem (hW S w hw) hw
      have h3 : eLast (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w =
          cls3LowB ((ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ ![w 0, w 1, w 2] - ![w 0, w 1, w 2]) := by
        rw [cls3_eLast_mulVec, cls3LowB_apply]
        funext i
        fin_cases i <;> simp
      rw [h3] at h1
      have h4 : (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ ![w 0, w 1, w 2] - ![w 0, w 1, w 2] ∈
          W.comap cls3LowB := h1
      rw [h, Submodule.mem_bot, sub_eq_zero] at h4
      exact h4
    have h5 := hρ.fixed_vec h2 hfix
    exact ⟨congrFun h5 0, congrFun h5 1, congrFun h5 2⟩
  · right
    intro u
    have : u ∈ W.comap cls3LowB := by rw [h]; trivial
    exact this

theorem cls3_irred_of_dichotomy {W : Submodule F (Fin 4 → F)}
    (hA : (∀ w ∈ W, w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) ∨ (∀ u : Fin 3 → F, cls3LowA u ∈ W))
    (hB : (∀ w ∈ W, w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0) ∨ (∀ u : Fin 3 → F, cls3LowB u ∈ W)) :
    W = ⊥ ∨ W = ⊤ := by
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · left
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    obtain ⟨a1, a2, a3⟩ := hA w hw
    obtain ⟨b0, b1, b2⟩ := hB w hw
    funext i
    fin_cases i <;> simp [a1, a2, a3, b0]
  · exfalso
    have := (hA _ (hB (Pi.single 1 1))).1
    simp [cls3LowB_apply] at this
  · exfalso
    have := (hB _ (hA (Pi.single 0 1))).2.1
    simp [cls3LowA_apply] at this
  · right
    rw [eq_top_iff]
    intro w _
    have h1 := hB ![w 0, w 1, w 2]
    have h2 := hA ![0, 0, w 3]
    have hw : w = cls3LowB ![w 0, w 1, w 2] + cls3LowA ![0, 0, w 3] := by
      funext i
      fin_cases i <;> simp [cls3LowA_apply, cls3LowB_apply]
    rw [hw]
    exact W.add_mem h1 h2

end Irred

section Final

variable {F : Type} [Field F] [Finite F]

theorem l4_cls3_irred_std (hodd : Odd (Nat.card F)) {D : GL (Fin 4) F} {d : Fin 4 → F}
    (hd : ∀ i, d i ≠ 0) (hD : ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d)
    (W : Submodule F (Fin 4 → F))
    (hW : ∀ A : SL(4, F), proj 4 F A ∈ fixSub (conjAut 4 F D * dualAut 4 F) → ∀ w ∈ W,
      (A : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨ρA, hA⟩ := exists_diagAd hodd ![d 1, d 2, d 3] (fun i => by fin_cases i <;> simp [hd])
  obtain ⟨ρB, hB⟩ := exists_diagAd hodd ![d 0, d 1, d 2] (fun i => by fin_cases i <;> simp [hd])
  exact cls3_irred_of_dichotomy
    (cls3_dichotomyA hA h2 W fun S w hw => hW (cls3IotaA ρA S) (proj_cls3IotaA_mem hD hA S) w hw)
    (cls3_dichotomyB hB h2 W fun S w hw => hW (cls3IotaB ρB S) (proj_cls3IotaB_mem hD hB S) w hw)

end Final

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
