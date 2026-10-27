module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eCross

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem exists_not_mem_D (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n) (h5 : V3Fourth n)
    (h7 : V3Alpha13 n) (hOpen : V3SecOpenW n) :
    ∃ c : Y, c * t * c⁻¹ = t ∧ c * (y * t * y⁻¹) * c⁻¹ ∉ C.D := by
  by_contra hcon
  push Not at hcon
  have hd := C.H.ex.1.datum
  obtain ⟨a, ha, -, -, -, -, hta, -⟩ := C.sides
  obtain ⟨β, hτβ, hβ, hcross⟩ := C.tau_cross ha hta
  have hconj := C.P.step2 C.t_mem_D C.tau_mem_D ha hβ hcross hta hτβ ⟨y, rfl⟩ C.hno2 hcon
  have htop' := A6Gen.ae6I_sup_centralizer_eq_top hEW hcit hP h4 h5 h7 hOpen C.H
  have htop : C.I ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤ := by
    rw [eq_top_iff, ← htop']
    exact sup_le_sup_right le_sup_left _
  have hall : ∀ g : Y, g * t * g⁻¹ ∈ C.D := fun g => hconj g (by rw [htop]; exact Subgroup.mem_top g)
  have hcore := C.H.ex.1.perp.core
  haveI := hcore.simple
  have hNle : Subgroup.normalClosure ({t} : Set Y) ≤ C.D := by
    unfold Subgroup.normalClosure
    rw [Subgroup.closure_le]
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a', ha', hxa⟩ := hx
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    obtain ⟨g, hg⟩ := isConj_iff.mp hxa
    rw [← hg]
    exact hall g
  have hF := genFittingFStar_le_of_normal hcore.nonab (N := Subgroup.normalClosure ({t} : Set Y))
    inferInstance (x := t) (Subgroup.subset_normalClosure rfl) hd.hz.ne_one
  obtain ⟨p, q, hpq⟩ := hcore.nonab
  apply hpq
  apply Subtype.ext
  have hexp : ∀ x : ↥(genFittingFStar Y), (x : Y) * x = 1 := fun x => C.hDsq x (hNle (hF x.2))
  have hx := hexp p
  have hy := hexp q
  have hxy := hexp (p * q)
  simp only [Subgroup.coe_mul] at hxy ⊢
  calc (p : Y) * q = ((p : Y) * q)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = (q : Y)⁻¹ * (p : Y)⁻¹ := mul_inv_rev _ _
    _ = (q : Y) * p := by rw [inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]

end A6eCtx

theorem v3AE6H_of {n : ℕ} (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n) (h5 : V3Fourth n) (h7 : V3Alpha13 n)
    (hOpen : V3SecOpenW n) (hD : V3AE6D n) (hDN : V3AE6DNorm n) (hI : V3AE6I n) : V3AE6H n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨C⟩ := nonempty_ctx hD hDN hI H fr
  have hd := H.ex.1.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨c, hc, hxD⟩ := C.exists_not_mem_D hEW hcit hP h4 h5 h7 hOpen
  obtain ⟨a, ha, hta, hxI, hfix, hpres⟩ := C.step4 hc hxD
  obtain ⟨β, hτβ, hβ, hcross⟩ := C.tau_cross ha hta
  have htt : t * t = 1 := hd.hz.sq
  have hxx : c * (y * t * y⁻¹) * c⁻¹ * (c * (y * t * y⁻¹) * c⁻¹) = 1 := by
    calc c * (y * t * y⁻¹) * c⁻¹ * (c * (y * t * y⁻¹) * c⁻¹) = (c * y) * (t * t) * (c * y)⁻¹ := by group
      _ = 1 := by rw [htt]; group
  obtain ⟨i, hi, hit, hcomm⟩ := C.P.exists_conj_comm hxI hxx ha hβ hcross hfix hpres C.t_mem_D hta
    C.tau_mem_D hτβ
  have hic : (i * c) * t * (i * c)⁻¹ = t := by
    calc (i * c) * t * (i * c)⁻¹ = i * (c * t * c⁻¹) * i⁻¹ := by group
      _ = t := by rw [hc, hit]
  have hconj : (i * c) * (y * t * y⁻¹) * (i * c)⁻¹ = i * (c * (y * t * y⁻¹) * c⁻¹) * i⁻¹ := by
    group
  refine ⟨i * c, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := hic
    calc (i * c) * t = ((i * c) * t * (i * c)⁻¹) * (i * c) := by group
      _ = t * (i * c) := by rw [this]
  · rw [hconj]
    intro hmem
    apply hxD
    have := C.P.conj_mem_D (C.I.inv_mem hi) hmem
    simpa [mul_assoc] using this
  · obtain ⟨-, hτP⟩ := A6Hx.t_tau_mem_ae6P H fr
    exact A6Hx.conj_mem_ae6P hinv hic hτP
  · rw [hconj]
    exact hcomm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
