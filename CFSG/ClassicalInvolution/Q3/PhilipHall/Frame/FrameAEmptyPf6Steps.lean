module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3C4
public import CFSG.ClassicalInvolution.Q3.Q3T6DSFuse

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

section Vocab

variable {G : Type} [Group G]

@[expose] def frameH20 (Ω : Set (Subgroup G)) (a : G) (R R' : Subgroup G) : Subgroup G :=
  (⨆ U ∈ {U : Subgroup G | U ∈ USet Ω ∧ U ≤ Subgroup.centralizer ({a} : Set G)}, U) ⊔ R ⊔ R'

end Vocab

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

structure Frame205Data (_d : Std20Frame K K' J S R R' W V z t) (a : G) : Prop where
  conf : AConf3 S K K' J z a
  cL : a ∈ centralizerModOdd (S : Subgroup G)
    (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K'))
  centX : ∀ x ∈ sec20X (CoreAssembly.conjClass K) z K K',
    a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K')

namespace Std20Frame

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem cmo_L_le_cmo_M :
    centralizerModOdd (S : Subgroup G)
        (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) ≤
      centralizerModOdd (S : Subgroup G) (K ⊔ K') := by
  intro u hu
  obtain ⟨huS, -, -, hucomm⟩ := hu
  have hMN : (S : Subgroup G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
    (d.hSz).trans (le_normalizer_sup_pair d.hyp.conjInvariant d.viol.hzK d.twins d.ne)
  have huM : u ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := hMN huS
  refine ⟨huS, huM, mem_normalizer_oddCore_of_mem_normalizer huM, fun m hm => ?_⟩
  set L : Subgroup G := K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K') with hL
  have hML : K ⊔ K' ≤ L := le_sup_left
  have h1 : ⁅u, m⁆ ∈ oddCoreOf L := hucomm m (hML hm)
  have h2 : ⁅u, m⁆ ∈ K ⊔ K' := by
    have e : ⁅u, m⁆ = (u * m * u⁻¹) * m⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (K ⊔ K').mul_mem ((Subgroup.mem_normalizer_iff.mp huM m).mp hm) ((K ⊔ K').inv_mem hm)
  have hQ : oddCoreOf L ⊓ (K ⊔ K') ≤ oddCoreOf (K ⊔ K') := by
    refine Balance.le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
    · intro g hg
      have hgL : g ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
        mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hML hg))
      have hgM : g ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
        Subgroup.le_normalizer hg
      rw [mem_normalizer_iff_conjSub_eq] at hgL hgM ⊢
      rw [late_conjSub_inf, hgL, hgM]
    · exact (oddCoreOf_odd_natCard L).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact hQ ⟨h1, h2⟩

theorem z_mem_cmo_L :
    z ∈ centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) := by
  have hCz := d.sup_le_centralizer_z
  have hXz : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sec20X_le_centralizer (le_sup_left.trans hCz) (le_sup_right.trans hCz)
  have hLz : K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K') ≤
      Subgroup.centralizer ({z} : Set G) :=
    sup_le hCz ((Subgroup.closure_le _).mpr fun x hx => hXz hx.1)
  have hzL : z ∈ K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K') :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left d.viol.hzK.mem)
  refine ⟨d.z_mem_S, Subgroup.le_normalizer hzL,
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hzL), fun l hl => ?_⟩
  have := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (hLz hl)).symm
  rw [this]
  exact (oddCoreOf _).one_mem

theorem oddCoreOf_sec20X_le :
    oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ≤
      oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
  have hCz := d.sup_le_centralizer_z
  have hXz : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sec20X_le_centralizer (le_sup_left.trans hCz) (le_sup_right.trans hCz)
  exact AscFusion.le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self _).trans hXz)
    (fun c hc => mem_normalizer_oddCore_of_mem_normalizer
      (le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins hc))
    (oddCoreOf_odd_natCard _)

end Std20Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
