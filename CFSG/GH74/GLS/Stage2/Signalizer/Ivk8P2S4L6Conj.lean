module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Act
import CFSG.GH74.AS16.Standard

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

theorem quasisimple_cj (g : G) {J : Subgroup G} (hq : IsQuasisimple ↥J) :
    IsQuasisimple ↥(cj g J) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hq

theorem isL34_cj (g : G) {J : Subgroup G} (h : IsL34Quotient ↥J) : IsL34Quotient ↥(cj g J) :=
  TwoThin.isL34Quotient_of_mulEquiv
    (J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) h

theorem isCompIn_cj {X J : Subgroup G} (h : IsCompIn X J) (g : G) : IsCompIn (cj g X) (cj g J) := by
  have := AS16.isCompIn_conj h g⁻¹
  simpa [conjugate, cj] using this

theorem isPGroup_cj {p : ℕ} (g : G) {A : Subgroup G} (hA : IsPGroup p ↥A) :
    IsPGroup p ↥(cj g A) :=
  hA.map _

theorem mem_normalizer_cj {b y : G} {A : Subgroup G}
    (h : b⁻¹ * y * b ∈ normalizer (A : Set G)) :
    y ∈ normalizer ((cj b A : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro x
  rw [mem_cj, mem_cj]
  have h1 := h (b⁻¹ * x * b)
  have e : b⁻¹ * (y * x * y⁻¹) * b = (b⁻¹ * y * b) * (b⁻¹ * x * b) * (b⁻¹ * y * b)⁻¹ := by
    group
  rw [e]
  exact h1

theorem alphaZ_mem_innSub {I : Subgroup G} {w : G} (hwI : w ∈ I) :
    alphaZ I (Subgroup.le_normalizer hwI) ∈ innSub (↥I ⧸ center ↥I) := by
  refine ⟨QuotientGroup.mk (⟨w, hwI⟩ : ↥I), ?_⟩
  exact (YCfg.yAct_of_mem I ⟨w, hwI⟩).symm

end Conj

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
