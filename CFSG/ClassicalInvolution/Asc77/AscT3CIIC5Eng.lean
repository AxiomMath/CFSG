module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K K' : Subgroup G} {S : Sylow 2 G} {z : G}

omit [Finite G] in
theorem sec20X_le_centralizer {Ω : Set (Subgroup G)} (hz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hz' : K' ≤ Subgroup.centralizer ({z} : Set G)) :
    sec20X Ω z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
  sup_le (sup_le (iSup₂_le fun _ hU => hU.2) hz) hz'

theorem concl20_5_of_7_of (hCz : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G))
    (hMN : (S : Subgroup G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G))
    (hzK : IsUniqueInvolution K z) (hzS : z ∈ (S : Subgroup G)) (c7 : Concl20_7 S K K' z) :
    Concl20_5 S K K' z := by
  have hXz : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sec20X_le_centralizer (le_sup_left.trans hCz) (le_sup_right.trans hCz)
  have hLz : K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K') ≤
      Subgroup.centralizer ({z} : Set G) :=
    sup_le hCz ((Subgroup.closure_le _).mpr fun x hx => hXz hx.1)
  show centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) = Subgroup.zpowers z
  apply le_antisymm
  · intro u hu
    obtain ⟨huS, -, -, hucomm⟩ := hu
    have huM : u ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := hMN huS
    have hu7 : u ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') := by
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
    rw [c7] at hu7
    exact hu7
  · have hzL : z ∈ K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K') :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left hzK.mem)
    refine Subgroup.zpowers_le.mpr ⟨hzS, Subgroup.le_normalizer hzL,
      mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hzL), fun l hl => ?_⟩
    · have := commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hLz hl)).symm
      rw [this]
      exact (oddCoreOf _).one_mem

end CFSG.ClassicalInvolution.Asc77.T3CII
