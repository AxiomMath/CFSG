module

public import Certificates.Certificate3374
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelAut
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelLink
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar

namespace Model

theorem leviCheck_true : leviCheck = true := Certificates.certificate3374

theorem wordElt_cons {X : Type*} [Group X] (p : Fin 6 → X) {s : ℕ} (hs : s < 6) (w : List ℕ) :
    wordElt p (s :: w) = p ⟨s, hs⟩ * wordElt p w := by
  simp [wordElt, pAt, hs]

theorem pM_word_act {ε : Eps} (w : List ℕ) (hw : ∀ s ∈ w, s < 6) (v : V6) :
    wordElt (pM ε) w * psiM ε v * (wordElt (pM ε) w)⁻¹ =
      psiM ε (toMat 6 6 (wordRows ε w) *ᵥ v) := by
  induction w generalizing v with
  | nil =>
    rw [show wordRows ε [] = id6 from rfl, toMat_id6, one_mulVec]
    simp [wordElt]
  | cons s w ih =>
    have hs : s < 6 := hw s List.mem_cons_self
    rw [wordElt_cons _ hs]
    calc pM ε ⟨s, hs⟩ * wordElt (pM ε) w * psiM ε v * (pM ε ⟨s, hs⟩ * wordElt (pM ε) w)⁻¹
        = pM ε ⟨s, hs⟩ * (wordElt (pM ε) w * psiM ε v * (wordElt (pM ε) w)⁻¹) *
            (pM ε ⟨s, hs⟩)⁻¹ := by group
      _ = pM ε ⟨s, hs⟩ * psiM ε (toMat 6 6 (wordRows ε w) *ᵥ v) * (pM ε ⟨s, hs⟩)⁻¹ := by
          rw [ih (fun t ht => hw t (List.mem_cons_of_mem _ ht))]
      _ = psiM ε (toMat 6 6 (wordRows ε (s :: w)) *ᵥ v) := by
          rw [pM_act, show wordRows ε (s :: w) = bmul 6 6 (genRows ε s) (wordRows ε w) from rfl,
            toMat_bmul, mulVec_mulVec]
          rfl

theorem rep_leviArr {ε : Eps} (w : List ℕ) (hw : ∀ s ∈ w, s < 6) :
    Rep (deg ε) (leviArr ε w) (wordElt (pM ε) w) := by
  induction w with
  | nil => exact rep_idA
  | cons s w ih =>
    have hs : s < 6 := hw s List.mem_cons_self
    rw [wordElt_cons _ hs]
    exact rep_compA (rep_pM ⟨s, hs⟩).1 (ih fun t ht => hw t (List.mem_cons_of_mem _ ht))

@[expose] noncomputable def kM : Equiv.Perm (Fin (deg .minus)) := wordElt (pM .minus) leviWord

theorem kM_pow : kM ^ 4 = 1 := by
  have h := leviCheck_true
  simp only [leviCheck, Bool.and_eq_true, beq_iff_eq] at h
  have hr := rep_leviArr (ε := .minus) leviWord (by decide)
  have e := eq_of_eqA (rep_compA (rep_compA hr hr) (rep_compA hr hr)) rep_idA h.2
  have h4 : kM ^ 4 = kM * kM * (kM * kM) := by simp [pow_succ, mul_assoc]
  rw [h4]
  exact e

theorem kM_act (v : V6) :
    kM * psiM .minus v * kM⁻¹ = psiM .minus (toMat 6 6 leviRows *ᵥ v) := by
  have h := leviCheck_true
  simp only [leviCheck, Bool.and_eq_true, beq_iff_eq] at h
  rw [kM, pM_word_act leviWord (by decide), h.1]

theorem kM_mem_P : kM ∈ PM .minus := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  have hs6 : s < 6 := by
    simp only [leviWord, List.mem_cons, List.not_mem_nil, or_false] at hs
    omega
  rw [pAt, dite_eq_left hs6]
  exact PQm_le_PM (pM_mem_P _)

end Model

variable {G : Type} [Group G]

theorem exists_levi_minus {L : Subgroup G} (θ : L ≃* Model.Lm .minus) :
    ∃ k ∈ pull θ (Model.PM .minus),
      (∀ v, lin (fun v => pullE θ (Model.psiM .minus v)
          ((Model.modelLinkFacts .minus).ψ_mem_L v)) k v =
        toMat 6 6 #[57, 30, 52, 24, 16, 32] *ᵥ v) ∧ k ^ 4 = 1 := by
  have hF := (Model.modelLinkFacts .minus).transport θ
  have hkL : Model.kM ∈ Model.Lm .minus := (Model.modelLinkFacts .minus).P_le_L Model.kM_mem_P
  refine ⟨pullE θ Model.kM hkL, (pullE_mem_pull _).2 Model.kM_mem_P, fun v => ?_, ?_⟩
  · rw [lin, ← pullE_conj, pullE_congr (Model.kM_act v) _
      ((Model.modelLinkFacts .minus).ψ_mem_L _)]
    exact Function.leftInverse_invFun hF.ψ_inj _
  · have h4 : (⟨Model.kM, hkL⟩ : Model.Lm .minus) ^ 4 = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact Model.kM_pow)
    have h : (θ.symm ⟨Model.kM, hkL⟩) ^ 4 = 1 := by rw [← map_pow, h4, map_one]
    have := congrArg (fun x : L => (x : G)) h
    simpa [pullE] using this

theorem exists_link_minus' {L : Subgroup G} (hL : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) :
    ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G),
      RadicalData .minus L U Q P a ψ p ∧ UGens .minus U Q ψ u ∧
        LinkFacts .minus L U Q P a ψ p u ∧ AutCent L Q ∧
        ∃ k ∈ P, (∀ v, lin ψ k v = toMat 6 6 #[57, 30, 52, 24, 16, 32] *ᵥ v) ∧ k ^ 4 = 1 := by
  obtain ⟨e⟩ := OmegaEightMinus.nonempty_mulEquiv_omegaT hL
  have hF := (Model.modelLinkFacts .minus).transport (e : L ≃* Model.Lm .minus)
  have hA := (Model.autCent .minus).transport (Model.modelLinkFacts .minus).Q_le_L
    (e : L ≃* Model.Lm .minus)
  exact ⟨_, _, _, _, _, _, _,
    hF.radicalData (OmegaEightMinus.involutionsInOddPart_of_lieModel_minus hL),
    ⟨hF.u_mem, hF.u_act, hF.U_le⟩, hF, hA, exists_levi_minus (e : L ≃* Model.Lm .minus)⟩

end CFSG.EvenSmallLie.OmegaEight.Stage1
