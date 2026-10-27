module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFStepCEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section D1outer




variable {n : ℕ}


section D1

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.s_ne (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) :
    a 0 * a 1 * a 2 * a 3 ≠ 1 ∧ a 0 * a 1 * a 2 * a 3 ≠ t :=
  frame_prod_ne (h.q8 (hfr.mem 0)) (hfr.haM 0) (hfr.haM 1) (hfr.haM 2) (hfr.haM 3) (hfr.sq h 0)
    (fun m hm m' hm' => hfr.cross h (i := 0) (j := 1) (by decide) hm hm')
    (fun m hm m' hm' => hfr.cross h (i := 0) (j := 2) (by decide) hm hm')
    (fun m hm m' hm' => hfr.cross h (i := 0) (j := 3) (by decide) hm hm')

theorem WFFrame.s_sq (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) :
    (a 0 * a 1 * a 2 * a 3) * (a 0 * a 1 * a 2 * a 3) = 1 := by
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have hcW : ∀ p q : Fin 4, Commute (a p) (a q) := fun p q => hfr.comm_a h p q
  rw [prod4_sq_comm (hcW 0 1) (hcW 0 2) (hcW 0 3) (hcW 1 2) (hcW 1 3) (hcW 2 3), hfr.sq h, hfr.sq h,
    hfr.sq h, hfr.sq h, ht, one_mul, ht]

theorem WFFrame.s_comm_t (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) :
    t * (a 0 * a 1 * a 2 * a 3) = (a 0 * a 1 * a 2 * a 3) * t := by
  have hti : ∀ p, Commute t (a p) := fun p => hfr.t_comm h p (hfr.haM p)
  exact ((((hti 0).mul_right (hti 1)).mul_right (hti 2)).mul_right (hti 3)).eq

theorem WFFrame.d1_ee (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (x : Y) :
    (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) = 1 := by
  calc (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) =
      x * ((a 0 * a 1 * a 2 * a 3) * (a 0 * a 1 * a 2 * a 3)) * x⁻¹ := by group
    _ = 1 := by rw [hfr.s_sq h]; group

theorem WFFrame.d1_et (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y} (hxt : x * t = t * x) :
    (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * t = t * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) := by
  have hxt' : x⁻¹ * t = t * x⁻¹ := by
    calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hxt]
      _ = t * x⁻¹ := by group
  calc (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * t = x * (a 0 * a 1 * a 2 * a 3) * (x⁻¹ * t) := by group
    _ = x * (a 0 * a 1 * a 2 * a 3) * (t * x⁻¹) := by rw [hxt']
    _ = x * ((a 0 * a 1 * a 2 * a 3) * t) * x⁻¹ := by group
    _ = x * (t * (a 0 * a 1 * a 2 * a 3)) * x⁻¹ := by rw [hfr.s_comm_t h]
    _ = (x * t) * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := by group
    _ = (t * x) * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := by rw [hxt]
    _ = t * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) := by group

theorem WFFrame.d1_es (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) :
    (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * (a 0 * a 1 * a 2 * a 3) =
      (a 0 * a 1 * a 2 * a 3) * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) := by
  obtain ⟨c, hc⟩ := exists_comm_coeff x M t
  have hct : ∀ i, c i = t := fun i => by
    rcases hc i with ⟨hcen, -⟩ | ⟨-, e⟩
    · exact absurd hcen (hmv i)
    · exact e
  have h1 := hfr.e_s h hxo hxt hxM hc
  rw [hct 0, hct 1, hct 2, hct 3] at h1
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have e4 : t * t * t * t = 1 := by rw [ht, one_mul, ht]
  have hEprod : x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ =
      (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) := by group
  rw [hEprod]
  rw [e4, one_mul] at h1
  exact h1

theorem WFFrame.d1_ne (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) :
    x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ ≠ 1 ∧ x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ ≠ t ∧
      x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ ≠ a 0 * a 1 * a 2 * a 3 ∧
      x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ ≠ (a 0 * a 1 * a 2 * a 3) * t := by
  have hall := hfr.c6_core h hxo hxt hxM (k := a) (fun i => ⟨hfr.haM i, hfr.sq h i⟩)
  have ⟨hs1, hst⟩ := hfr.s_ne h
  have hxt' : x⁻¹ * t * x = t := by
    calc x⁻¹ * t * x = x⁻¹ * (t * x) := mul_assoc _ _ _
      _ = x⁻¹ * (x * t) := by rw [hxt]
      _ = t := by group
  refine ⟨fun e => hs1 ?_, fun e => hst ?_, fun e => hmv 0 (hall (Or.inl ?_) 0),
    fun e => hmv 0 (hall (Or.inr ?_) 0)⟩
  · have : a 0 * a 1 * a 2 * a 3 = x⁻¹ * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * x := by group
    rw [this, e]; group
  · have : a 0 * a 1 * a 2 * a 3 = x⁻¹ * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * x := by group
    rw [this, e, hxt']
  · rw [e]; group
  · rw [e]
    calc (a 0 * a 1 * a 2 * a 3) * t * (a 0 * a 1 * a 2 * a 3)⁻¹ =
        t * (a 0 * a 1 * a 2 * a 3) * (a 0 * a 1 * a 2 * a 3)⁻¹ := by rw [hfr.s_comm_t h]
      _ = t := by group

theorem prod4_central {Z : Type*} [Group Z] {t : Z} (ht : t * t = 1) {g : Fin 4 → Z}
    (hg : ∀ i, g i = 1 ∨ g i = t) : g 0 * g 1 * g 2 * g 3 = 1 ∨ g 0 * g 1 * g 2 * g 3 = t := by
  have key : ∀ p q : Z, (p = 1 ∨ p = t) → (q = 1 ∨ q = t) → (p * q = 1 ∨ p * q = t) := by
    rintro p q (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact ht
  exact key _ _ (key _ _ (key _ _ (hg 0) (hg 1)) (hg 2)) (hg 3)

theorem WFFrame.prod4_three (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {A B C : Fin 4 → Y}
    (hA : ∀ i, A i ∈ M i) (hB : ∀ i, B i ∈ M i) (hC : ∀ i, C i ∈ M i) :
    (A 0 * A 1 * A 2 * A 3) * (B 0 * B 1 * B 2 * B 3) * (C 0 * C 1 * C 2 * C 3) =
      (A 0 * B 0 * C 0) * (A 1 * B 1 * C 1) * (A 2 * B 2 * C 2) * (A 3 * B 3 * C 3) := by
  have cr : ∀ (i j : Fin 4), i ≠ j → ∀ {m m' : Y}, m ∈ M i → m' ∈ M j → m * m' = m' * m :=
    fun i j hij m m' hm hm' => hfr.cross h hij hm hm'
  rw [prod4_mul2 (cr 1 0 (by decide) (hA 1) (hB 0)) (cr 2 0 (by decide) (hA 2) (hB 0))
    (cr 2 1 (by decide) (hA 2) (hB 1)) (cr 3 0 (by decide) (hA 3) (hB 0))
    (cr 3 1 (by decide) (hA 3) (hB 1)) (cr 3 2 (by decide) (hA 3) (hB 2))]
  exact prod4_mul2 (cr 1 0 (by decide) ((M 1).mul_mem (hA 1) (hB 1)) (hC 0))
    (cr 2 0 (by decide) ((M 2).mul_mem (hA 2) (hB 2)) (hC 0))
    (cr 2 1 (by decide) ((M 2).mul_mem (hA 2) (hB 2)) (hC 1))
    (cr 3 0 (by decide) ((M 3).mul_mem (hA 3) (hB 3)) (hC 0))
    (cr 3 1 (by decide) ((M 3).mul_mem (hA 3) (hB 3)) (hC 1))
    (cr 3 2 (by decide) ((M 3).mul_mem (hA 3) (hB 3)) (hC 2))

theorem WFFrame.d1_cycle (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) :
    (a 0 * a 1 * a 2 * a 3) * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) *
        (x * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * x⁻¹) = 1 ∨
      (a 0 * a 1 * a 2 * a 3) * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) *
        (x * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * x⁻¹) = t := by
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have hU : ∀ i, x * a i * x⁻¹ ∈ M i := fun i => hfr.act_mem hxM i (hfr.haM i)
  have hU' : ∀ i, (x * x) * a i * (x * x)⁻¹ ∈ M i := fun i => by
    have e : (x * x) * a i * (x * x)⁻¹ = x * (x * a i * x⁻¹) * x⁻¹ := by group
    rw [e]; exact hfr.act_mem hxM i (hU i)
  have e1 : x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ =
      (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) := by group
  have e2 : x * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * x⁻¹ =
      ((x * x) * a 0 * (x * x)⁻¹) * ((x * x) * a 1 * (x * x)⁻¹) * ((x * x) * a 2 * (x * x)⁻¹) *
        ((x * x) * a 3 * (x * x)⁻¹) := by group
  rw [e2, e1]
  rw [hfr.prod4_three h (A := a) (B := fun i => x * a i * x⁻¹)
    (C := fun i => (x * x) * a i * (x * x)⁻¹) hfr.haM hU hU']
  exact prod4_central ht (g := fun i => a i * (x * a i * x⁻¹) * ((x * x) * a i * (x * x)⁻¹))
    (fun i => (h.q8 (hfr.mem i)).cycle3 hxo hxt (fun m hm => hfr.act_mem hxM i hm) (hmv i)
      (hfr.haM i) (hfr.sq h i))

end D1

end D1outer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
