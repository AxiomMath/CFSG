module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesPlane
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.SeitzReduction.OmegaPilot (diagOmega)
open CFSG.Quasithin (perfectCore)

section PlaneTorus

variable {K : Type} [Field K] [Finite K] {m : ℕ}

theorem perfectCore_statedOmega_inf_centralizer_planeTorusParam (hK : 4 ≤ Nat.card K)
    (I : Finset (Fin m)) :
    perfectCore (StatedOmega (StatedQuadPlus m K) ⊓
      centralizer (diagOmega K m '' (SymplecticPilot.planeTorusParam K I : Set (Fin m → Kˣ)))) =
      perfectCore (OmegaPilot.omegaBlock K I) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hK
  exact OmegaPilot.perfectCore_statedOmega_inf_centralizer_eq_perfectCore_omegaBlock _
    (fun s hs a ha b hb => by
      rw [SymplecticPilot.diagSpEntry_eq_one_of_mem_planeTorusParam hs ha,
        SymplecticPilot.diagSpEntry_eq_one_of_mem_planeTorusParam hs hb])
    (fun a b hab hI => SymplecticPilot.exists_mem_planeTorusParam_diagSpEntry_ne hκ hab hI)

end PlaneTorus

theorem card_perfectCore_omegaPlus8_A (k : Type) [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) :
    Nat.card (perfectCore (StatedOmega (StatedQuadPlus 4 k) ⊓
      Subgroup.centralizer (diagOmega k 4 '' {t | t 1 = 1 ∧ t 2 = 1 ∧ t 3 = 1}))) =
      ordSL 4 (Nat.card k) := by
  have hset : {t : Fin 4 → kˣ | t 1 = 1 ∧ t 2 = 1 ∧ t 3 = 1} =
      (SymplecticPilot.planeTorusParam k ({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4 → kˣ)) := by
    ext t
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, SymplecticPilot.mem_planeTorusParam,
      Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  have hc : ({1, 2, 3} : Finset (Fin 4)).card = 3 := by decide
  rw [hset, perfectCore_statedOmega_inf_centralizer_planeTorusParam hk,
    OmegaPilot.perfectCore_omegaBlock (N := ({1, 2, 3} : Finset (Fin 4))) (by rw [hc]),
    Subgroup.card_map_of_injective (OmegaPilot.spEmbedGL_injective _), hc]
  exact natCard_statedOmega_quadPlus_three hk

theorem card_perfectCore_omegaPlus8_M2 (k : Type) [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) :
    Nat.card (perfectCore (StatedOmega (StatedQuadPlus 4 k) ⊓
      Subgroup.centralizer (diagOmega k 4 '' {t | t 2 = 1 ∧ t 3 = 1}))) =
      ordSL 2 (Nat.card k) ^ 2 := by
  have hset : {t : Fin 4 → kˣ | t 2 = 1 ∧ t 3 = 1} =
      (SymplecticPilot.planeTorusParam k ({2, 3} : Finset (Fin 4)) : Set (Fin 4 → kˣ)) := by
    ext t
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, SymplecticPilot.mem_planeTorusParam,
      Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  rw [hset, perfectCore_statedOmega_inf_centralizer_planeTorusParam hk]
  exact natCard_perfectCore_omegaBlock_of_card_two hk (by decide)

theorem card_perfectCore_omegaPlus8_M3 (k : Type) [Field k] [Finite k] [CharP k 2]
    (hk : 4 ≤ Nat.card k) :
    Nat.card (perfectCore (StatedOmega (StatedQuadPlus 4 k) ⊓
      Subgroup.centralizer (diagOmega k 4 '' {t | t 2 = t 1 ∧ t 3 = 1}))) =
      ordSL 2 (Nat.card k) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hk
  have hκ1 : κ ≠ 1 := SymplecticPilot.units_ne_one_of_mul_self_ne_one hκ
  have hsub : {t : Fin 4 → kˣ | t 2 = t 1 ∧ t 3 = 1} ⊆
      (OmegaPilot.levelParam (K := k) ({1, 2} : Finset (Fin 4)) : Set (Fin 4 → kˣ)) := by
    intro t ht
    obtain ⟨h21, -⟩ := ht
    rw [SetLike.mem_coe, OmegaPilot.mem_levelParam]
    intro i hi i' hi'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi'
    rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl
    · rfl
    · exact h21.symm
    · exact h21
    · rfl
  have hsep : ∀ a : Fin 4 ⊕ Fin 4, SymplecticPilot.planeOf a ≠ 3 →
      ∃ s ∈ {t : Fin 4 → kˣ | t 2 = t 1 ∧ t 3 = 1}, SymplecticPilot.diagSpEntry s a ≠ 1 := by
    intro a ha
    refine ⟨fun i => if i = 3 then 1 else κ, ⟨by simp, by simp⟩, ?_⟩
    rcases a with i | i <;>
      simp only [SymplecticPilot.planeOf_inl, SymplecticPilot.planeOf_inr] at ha <;>
      simp [SymplecticPilot.diagSpEntry_inl, SymplecticPilot.diagSpEntry_inr, ha, hκ1]
  have hfac : ∀ t ∈ (OmegaPilot.levelParam (K := k) ({1, 2} : Finset (Fin 4)) : Set (Fin 4 → kˣ)),
      ∃ s ∈ {t : Fin 4 → kˣ | t 2 = t 1 ∧ t 3 = 1}, ∃ c : kˣ, t = s * Pi.mulSingle 3 c := by
    intro t ht
    have h21 : t 2 = t 1 := OmegaPilot.mem_levelParam.1 ht 2 (by decide) 1 (by decide)
    refine ⟨t * Pi.mulSingle 3 (t 3)⁻¹, ⟨?_, ?_⟩, t 3, ?_⟩
    · simp [h21]
    · simp
    · rw [mul_assoc, ← Pi.mulSingle_mul, inv_mul_cancel, Pi.mulSingle_one, mul_one]
  have hJc : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  rw [perfectCore_statedOmega_inf_centralizer_eq_of_plane (3 : Fin 4) hsub (fun s hs => hs.2)
      hsep hfac,
    OmegaPilot.perfectCore_statedOmega_inf_centralizer_eq_level hk
      (J := ({1, 2} : Finset (Fin 4))) (by rw [hJc]) _
      (fun s hs => OmegaPilot.mem_levelParam.1 hs)
      (fun a b hab hJ => OmegaPilot.exists_mem_levelParam_diagSpEntry_ne hκ hab hJ),
    Subgroup.card_map_of_injective (OmegaPilot.spEmbedGL_injective _),
    natCard_omegaLeviSL (by rw [hJc]; norm_num), hJc]

end CFSG.SeitzReduction.F4Pilot
