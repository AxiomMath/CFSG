module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY4P03

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
open scoped commutatorElement MatrixGroups

section Final


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layerComm_of_act (hs : Std8 Ω K J S R T W z t) {P M : Subgroup G} (hPD : P ∈ DSet Ω W)
    (hMΩ : M ∈ Ω) (hPM : P ≤ M) {u : G} (hu : IsUniqueInvolution M u)
    (hact : ∃ ε : ℕ, ε ≤ 1 ∧
      ∀ x ∈ nbrLayer Ω K z, ⁅u * t ^ ε, x⁆ ∈ oddCoreOf (nbrLayer Ω K z)) :
    ∀ x ∈ T, x * u = u * x := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hW := hs.hW.1
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have hPsyl : IsSylow2In P M :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hMΩ hPD.1 hPM
  obtain ⟨ε, hε, hact⟩ := hact
  have huW : u ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hMΩ hPD hPsyl hu).2
  have htW : t ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hJΩ hTD hTsyl hs.ht).2
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  have htε : t ^ ε ∈ (S : Subgroup G) := (S : Subgroup G).pow_mem (hWS htW) ε
  intro x hx
  have hxY : x ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hs.hJ (layerT_le_exactCore hs hx)
  have hc := hact x hxY
  have hvS : u * t ^ ε ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem (hWS huW) htε
  have hcS : ⁅u * t ^ ε, x⁆ ∈ (S : Subgroup G) := by
    rw [commutatorElement_def]
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem hvS (hTS hx)) ((S : Subgroup G).inv_mem hvS))
      ((S : Subgroup G).inv_mem (hTS hx))
  have hc2 : IsPGroup 2 (Subgroup.zpowers ⁅u * t ^ ε, x⁆) :=
    (S.isPGroup').to_le ((Subgroup.zpowers_le).mpr hcS)
  have hc1 : ⁅u * t ^ ε, x⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc hc2
  have hcomm : (u * t ^ ε) * x = x * (u * t ^ ε) := by
    rw [commutatorElement_def] at hc1
    calc (u * t ^ ε) * x = (u * t ^ ε * x * (u * t ^ ε)⁻¹ * x⁻¹) * (x * (u * t ^ ε)) := by
          group
      _ = x * (u * t ^ ε) := by rw [hc1, one_mul]
  have htx : t ^ ε * x = x * t ^ ε := by
    interval_cases ε
    · simp
    · rw [pow_one]
      exact hs.ht.commute_of_mem (hTJ hx)
  have h2 : (u * x) * t ^ ε = (x * u) * t ^ ε := by
    calc (u * x) * t ^ ε = u * (x * t ^ ε) := by rw [mul_assoc]
      _ = u * (t ^ ε * x) := by rw [htx]
      _ = (u * t ^ ε) * x := by rw [mul_assoc]
      _ = x * (u * t ^ ε) := hcomm
      _ = (x * u) * t ^ ε := by rw [mul_assoc]
  exact (mul_right_cancel h2).symm

theorem false_of_layerCommutes (hs : Std8 Ω K J S R T W z t) (hS4 : MuIsoS4 Ω W)
    (hcent : ∀ P ∈ DSet Ω W, ∀ M ∈ Ω, P ≤ M → M ≠ K → M ≠ J → ∀ u : G,
      IsUniqueInvolution M u → ∀ x ∈ T, x * u = u * x) : False := by
  obtain ⟨φ⟩ := hS4
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hP : PartIHyp Ω := ⟨hΩ, hs.stand.cls, hs.stand.aEmpty⟩
  have hW := hs.hW.1
  have c : Q3CL.Thompson.Ctx Ω W := ⟨hΩ, hW, Q3CL.thompsonKey hP W hW, hs.stand.aEmpty⟩
  obtain ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ, hnot⟩ := s26_exists_third hs φ
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hMΩ
  have hcent' := hcent P hPD M hMΩ hPM.1 hMK hMJ u hu
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  obtain ⟨t', ht', htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hTD
  obtain ⟨rP, hrP, hrPW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hPD
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  let ρP : Rep Ω W := ⟨M, P, rP, hMΩ, hPD, hPM, hrP, hrPW⟩
  have hrel : σ.r * u * σ.r⁻¹ = t * u :=
    c.conj_involution σ ρP (fun h => hMJ h.symm) hnot hs.ht hu
  have hcomm : σ.r * u = u * σ.r := hcent' t' ht'
  have hcu : σ.r * u * σ.r⁻¹ = u := by
    rw [hcomm]
    group
  rw [hcu] at hrel
  apply hs.ht.ne_one
  have : t * u = 1 * u := by rw [← hrel, one_mul]
  exact mul_right_cancel this

theorem not_muIsoS4_of_layerL3M11 (hs : Std8 Ω K J S R T W z t)
    (hshape : LayerL3 Ω K z ∨ LayerM11 Ω K z) : ¬ MuIsoS4 Ω W := fun hS4 =>
  false_of_layerCommutes hs hS4 fun _ hPD _ hMΩ hPM hMK hMJ _ hu =>
    layerComm_of_act hs hPD hMΩ hPM hu
      (exists_act_of_layerL3M11 hs hshape hPD hMΩ hPM hMK hMJ hu)

theorem c26_2_of_layerL3M11 [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    (_hint : Uniform.IsIntrinsicU (.sl2 3 1) K z) (hshape : LayerL3 Ω K z ∨ LayerM11 Ω K z) :
    ¬ MuIsoS4 Ω W :=
  not_muIsoS4_of_layerL3M11 h.std hshape

end Final

end CFSG.ClassicalInvolution.Q3.Q3AM
