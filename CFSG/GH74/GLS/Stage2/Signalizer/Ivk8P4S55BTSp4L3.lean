module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4L2
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4L

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open scoped commutatorElement

variable {F : Type} [Field F]

theorem comm_of_conj_central {I : Subgroup (StatedSp 2 F)} {A : GL (Fin 2 ⊕ Fin 2) F}
    (hA : ∀ x ∈ I, ∃ s ∈ center (GL (Fin 2 ⊕ Fin 2) F),
      A * ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * A⁻¹ = s * x)
    {x : StatedSp 2 F} (hx : x ∈ ⁅I, I⁆) : A * (x : GL (Fin 2 ⊕ Fin 2) F) = x * A := by
  have hle : ⁅I, I⁆ ≤ (Subgroup.centralizer ({A} : Set (GL (Fin 2 ⊕ Fin 2) F))).comap
      (StatedSp 2 F).subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨s, hs, hsa⟩ := hA a ha
    obtain ⟨t, ht, htb⟩ := hA b hb
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, map_commutatorElement]
    have h := conj_commutator_of_central hs ht hsa htb
    calc ⁅(StatedSp 2 F).subtype a, (StatedSp 2 F).subtype b⁆ * A
        = A * ⁅(a : GL (Fin 2 ⊕ Fin 2) F), (b : GL (Fin 2 ⊕ Fin 2) F)⁆ * A⁻¹ * A := by
          rw [h]; rfl
      _ = A * ⁅(StatedSp 2 F).subtype a, (StatedSp 2 F).subtype b⁆ := by
          rw [inv_mul_cancel_right]; rfl
  have := hle hx
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

abbrev ulB (x : StatedSp 2 F) : Matrix (Fin 2) (Fin 2) F :=
  (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁

theorem exists_ulB_ne {I : Subgroup (StatedSp 2 F)}
    (hIll : ∀ x ∈ I, (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
    (hperf : ⁅I.map (proj 2 F), I.map (proj 2 F)⁆ = I.map (proj 2 F))
    (hne : I.map (proj 2 F) ≠ ⊥) :
    ∃ x ∈ ⁅I, I⁆, ∃ y ∈ ⁅I, I⁆, ulB x * ulB y ≠ ulB y * ulB x := by
  by_contra hall
  push Not at hall
  have hD : ∀ x ∈ ⁅I, I⁆, (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 :=
    fun x hx => hIll x (Subgroup.commutator_le_self I hx)
  have hD2 : ⁅⁅I, I⁆, ⁅I, I⁆⁆ ≤ kerP := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxi := hD _ (inv_mem hx)
    have hyi := hD _ (inv_mem hy)
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul]
      exact ll_mul (ll_mul (ll_mul (hD x hx) (hD y hy)) hxi) hyi
    · simp only [Subgroup.coe_mul, Units.val_mul]
      rw [ul_mul hyi, ul_mul hxi, ul_mul (hD y hy)]
      have h1 := ul_inv hxi
      have h2 := ul_inv hyi
      change ulB x * ulB y * ulB x⁻¹ * ulB y⁻¹ = 1
      rw [hall x hx y hy, Matrix.mul_assoc (ulB y), h1, Matrix.mul_one, h2]
  have hD3 : ⁅⁅⁅I, I⁆, ⁅I, I⁆⁆, ⁅⁅I, I⁆, ⁅I, I⁆⁆⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hD2 hD2).trans commutator_kerP_eq_bot.le)
  apply hne
  have e := congrArg (fun H => H.map (proj 2 F)) hD3
  simp only [Subgroup.map_commutator, hperf, Subgroup.map_bot] at e
  exact e

theorem false_of_lagrangian (h2 : (2 : F) ≠ 0) {I : Subgroup (StatedSp 2 F)}
    (hIll : ∀ x ∈ I, (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
    (hperf : ⁅I.map (proj 2 F), I.map (proj 2 F)⁆ = I.map (proj 2 F))
    (hne : I.map (proj 2 F) ≠ ⊥) {A₁ A₂ : GL (Fin 2 ⊕ Fin 2) F} {μ₁ μ₂ : F}
    (hJ₁ : (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jJ *
      (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = μ₁ • jJ)
    (hJ₂ : (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jJ *
      (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = μ₂ • jJ)
    (hll₁ : (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
    (hll₂ : (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0)
    (hsq₁ : ∃ l : F, (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * A₁ = l • 1)
    (hsq₂ : ∃ l : F, (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * A₂ = l • 1)
    (hsq₁₂ : ∃ l : F,
      ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = l • 1)
    (hns₁ : ∀ l : F, (A₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1)
    (hns₂ : ∀ l : F, (A₂ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1)
    (hns₁₂ : ∀ l : F,
      ((A₁ * A₂ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1)
    (hc₁ : ∀ x ∈ I, ∃ s ∈ center (GL (Fin 2 ⊕ Fin 2) F),
      A₁ * ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * A₁⁻¹ = s * x)
    (hc₂ : ∀ x ∈ I, ∃ s ∈ center (GL (Fin 2 ⊕ Fin 2) F),
      A₂ * ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * A₂⁻¹ = s * x) : False := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_ulB_ne hIll hperf hne
  have hscal : ∀ A : GL (Fin 2 ⊕ Fin 2) F,
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 →
      (∀ x ∈ I, ∃ s ∈ center (GL (Fin 2 ⊕ Fin 2) F),
        A * ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * A⁻¹ = s * x) →
      ∃ c : F, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = c • 1 := by
    intro A hll hc
    have hcomm : ∀ z ∈ ⁅I, I⁆, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ *
        ulB z = ulB z * (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ := by
      intro z hz
      have h := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F =>
        ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁)) (comm_of_conj_central hc hz)
      simp only [Units.val_mul] at h
      rwa [ul_mul (hIll z (Subgroup.commutator_le_self I hz)), ul_mul hll] at h
    by_contra hns
    push Not at hns
    exact hxy (comm_of_comm_nonscalar hns (hcomm x hx).symm (hcomm y hy).symm)
  obtain ⟨c₁, hP₁⟩ := hscal A₁ hll₁ hc₁
  obtain ⟨c₂, hP₂⟩ := hscal A₂ hll₂ hc₂
  exact false_of_three h2 hJ₁ hJ₂ hll₁ hll₂ hP₁ hP₂ hsq₁ hsq₂ hsq₁₂ hns₁ hns₂ hns₁₂

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
