module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFQ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf27Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf53Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf55Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf68Frame

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

section Frame




variable {n : ℕ}

@[expose] def FrameInv {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (K W' : Subgroup Y) : Set Y :=
  {s | ∃ (J : Fin 4 → Subgroup Y) (b : Fin 4 → Y), Function.Injective J ∧ (∀ i, J i ∈ twinSet Ω K) ∧
    (∀ i, b i ∈ J i ⊓ W' ∧ orderOf (b i) = 4) ∧ s = b 0 * b 1 * b 2 * b 3}

structure WFIn (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) : Prop where
  exit : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄
  hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))
  hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W
  hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W
  hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W
  hu₁ : u₁ ∈ W
  hu₂ : u₂ ∈ W
  uniq : ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
    ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
    ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, L ≠ L' →
    ∀ a ∈ L ⊓ W', ∀ a' ∈ L' ⊓ W', orderOf a = 4 → orderOf a' = 4 →
      ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (a * a')),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) = {V}
  oddC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥

structure WFFrame {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (K : Subgroup Y) (t : Y) (W : Subgroup Y)
    (M : Fin 4 → Subgroup Y) (a : Fin 4 → Y) (y : Y) : Prop where
  inj : Function.Injective M
  mem : ∀ i, M i ∈ twinSet Ω K
  surj : ∀ J ∈ twinSet Ω K, ∃ i, M i = J
  haM : ∀ i, a i ∈ M i
  haW : ∀ i, a i ∈ W
  ha4 : ∀ i, orderOf (a i) = 4
  fuse : y * t * y⁻¹ = a 0 * a 1 * a 2 * a 3
  fuse_ne : y * t * y⁻¹ ≠ t
  ycent : y ∈ Subgroup.centralizer ({a 0 * a 1} : Set Y)

section WFInFacts

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem WFIn.hStd (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : V3Std n Y R S t K K' K₃ u₁ u₂ u₃ :=
  h.exit.1

theorem WFIn.hyp (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    HypOmegaGen (CoreAssembly.conjClass (tightCore R)) :=
  (CoreData.of_S h.hStd.perp.core).hyp

theorem WFIn.partI (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) :=
  (CoreData.of_S h.hStd.perp.core).partIHypG

theorem WFIn.uniqInv (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) : IsUniqueInvolution J t :=
  isUniqueInvolution_of_mem_twinSet h.hStd.datum.hz hJ

theorem WFIn.q8 (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) : Q8Facts J t := by
  obtain ⟨e⟩ := members_q8_of_isPGroup h.hStd.perp h.exit.2.2.2.1 J hJ.1
  exact q8Facts_of_iso (h.uniqInv hJ) e

theorem WFIn.comm (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J J' : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K)
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (hne : J ≠ J') : Commutes J J' := by
  have h2g := h.exit.2.2.2.1
  intro x hx y hy
  have h1 := A7T22.le_trivialOnQuot_of_twin h.hyp hJ.1 hJ'.1 hne (h.uniqInv hJ) (h.uniqInv hJ') hx
  exact commute_of_trivialOnQuot (h2g J' hJ'.1) h1 hy

theorem WFIn.t_mem (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : t ∈ W := by
  rw [← h.hStd.datum.sq₁]
  exact W.mul_mem h.hu₁ h.hu₁

theorem WFIn.abelian (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
  Q3.Q3T6.abelian_of_mem_WSet3 h.hyp h.hW

theorem WFIn.exists_frame (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    ∃ (M : Fin 4 → Subgroup Y) (a : Fin 4 → Y) (y : Y),
      WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y := by
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := h.exit
  have hd := hStd.datum
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hV := twinSet_four hStd hF
  obtain ⟨hK₄, h41, h42, h43, -⟩ := hF
  obtain ⟨a₁, a₂, a₃, a₄, y, ha₁, ho₁, ha₂, ho₂, ha₃, ho₃, ha₄, ho₄, -, -, -, -, -, -, hy, hyne,
    hW₁, hW₂, hW₃, hW₄, hyC, -⟩ :=
    exists_fuse_cent2W h.partI hd hperp hK₄ h41 h42 h43 hStd.wyl h.hW h.t_mem
  have hKK' : K ≠ K' := hd.hne.symm
  have hKK₃ : K ≠ K₃ := hd.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hd.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have hKt : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := mem_twinSet_self hd.mem hd.hz
  refine ⟨![K, K', K₃, K₄], ![a₁, a₂, a₃, a₄], y, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hyne, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hKK', hKK'.symm, hKK₃, hKK₃.symm, hKK₄, hKK₄.symm,
      hK'K₃, hK'K₃.symm, hK'K₄, hK'K₄.symm, hK₃K₄, hK₃K₄.symm] at hij ⊢
  · intro i; fin_cases i
    · exact hKt
    · exact hd.hK'
    · exact hd.hK₃
    · exact hK₄
  · intro J hJ
    rcases hV J hJ with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · intro i; fin_cases i
    · exact ha₁
    · exact ha₂
    · exact ha₃
    · exact ha₄
  · intro i; fin_cases i
    · exact hW₁
    · exact hW₂
    · exact hW₃
    · exact hW₄
  · intro i; fin_cases i
    · exact ho₁
    · exact ho₂
    · exact ho₃
    · exact ho₄
  · simpa using hy
  · simpa using hyC

end WFInFacts

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
