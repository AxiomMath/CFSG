module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7T
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Lam
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFusionHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerI1I2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def PA5.s7_JT (a : PA5 L t E z) : Subgroup ↥a.s7_N₁ :=
  (derivedIn a.Abar).subgroupOf a.s7_N₁

theorem PA5.s7_JT_map_eq (hb : PAB G L t E W z) (a : PA5 L t E z) :
    a.s7_JT.map a.s7_N₁.subtype = derivedIn a.Abar :=
  Subgroup.map_subgroupOf_eq_of_le (a.s7_J_le_N₁ hb)

theorem s7te_derivedIn_perfect {H : Type} [Group H] (A : Subgroup H)
    (e : ↥A ≃* MulAut (alternatingGroup (Fin 6))) : ⁅derivedIn A, derivedIn A⁆ = derivedIn A := by
  have h1 : (_root_.commutator ↥A).map e.toMonoidHom = innA6 := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, ← _root_.commutator_def,
      s7_commutator_mulAut_alt6]
  have h2 : ⁅_root_.commutator ↥A, _root_.commutator ↥A⁆ = _root_.commutator ↥A := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_commutator, h1, innA6_perfect]
  unfold derivedIn
  rw [← Subgroup.map_commutator, h2]

theorem PA5.s7_JT_perfect (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ⁅a.s7_JT, a.s7_JT⁆ = a.s7_JT := by
  apply Subgroup.map_injective (f := a.s7_N₁.subtype) a.s7_N₁.subtype_injective
  rw [Subgroup.map_commutator, a.s7_JT_map_eq hb, s7te_derivedIn_perfect a.Abar a.eAbar]

theorem PA5.s7_yT_mem_JT (hb : PAB G L t E W z) (a : PA5 L t E z) : a.s7_yT hb ∈ a.s7_JT :=
  a.y_J

theorem PA5.s7_JT_map_le (hb : PAB G L t E W z) (a : PA5 L t E z) :
    a.s7_JT.map a.s7_κ ≤ centralizerDerived (a.s7_κ (a.s7_tT hb)) := by
  let ψ : ↥a.Abar →* ↥a.s7_N₁ := Subgroup.inclusion (a.s7_Abar_le_N₁ hb)
  have hJ : a.s7_JT = (_root_.commutator ↥a.Abar).map ψ := by
    apply Subgroup.map_injective (f := a.s7_N₁.subtype) a.s7_N₁.subtype_injective
    rw [a.s7_JT_map_eq hb, Subgroup.map_map]
    rfl
  have hcomm : ∀ x : ↥a.Abar, a.s7_κ (ψ x) ∈ centralizer ({a.s7_κ (a.s7_tT hb)} : Set _) := by
    intro x s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have h := (S5.Abar_comm hb a.toPA0 x.2).1
    have : ψ x * a.s7_tT hb = a.s7_tT hb * ψ x := Subtype.ext h
    rw [← map_mul, ← map_mul, this]
  let g : ↥a.Abar →* ↥(centralizer ({a.s7_κ (a.s7_tT hb)} : Set _)) :=
    (a.s7_κ.comp ψ).codRestrict _ hcomm
  have hg : (centralizer ({a.s7_κ (a.s7_tT hb)} : Set _)).subtype.comp g = a.s7_κ.comp ψ := rfl
  rw [hJ, Subgroup.map_map, ← hg, ← Subgroup.map_map]
  unfold centralizerDerived
  apply Subgroup.map_mono
  rw [_root_.commutator_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

end Basic

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
