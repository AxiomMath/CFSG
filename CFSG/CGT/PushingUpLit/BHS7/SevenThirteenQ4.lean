module

public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenQ3
public import CFSG.CGT.PushingUpLit.BHS7.SevenEight
public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenA
public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenB

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def Seven12Q (G T : Subgroup Γ) : Prop :=
  ⁅vSub G T, zSub T⁆ = ⊥ → ∃ E ∈ bStarT G T, ∀ x ∈ qSub (vSub G T) T, ∀ e ∈ E,
    ⁅x, e⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ)

section Finite

variable [Finite Γ] {G T : Subgroup Γ}

theorem branch_q_false (h : MinCex G T) (h5 : Seven5 G T)
    (h7 : Seven7 G T) (h12 : Seven12Q G T) (hZ : ⁅vSub G T, zSub T⁆ = ⊥)
    (hoff : ∃ A : Subgroup Γ, A ≤ T ∧ IsOffG (vSub G T) A ∧
      Nat.card (vSub G T) < wtG (vSub G T) A) : False := by
  have hT : IsSylowTwoOf T G := h.sylow
  have h5' : ¬ IsMinParabolic2 T G := h5
  set V : Subgroup Γ := vSub G T with hVdef
  have hV : IsElemAbelian 2 V := isElemAbelian_vSub h.charTwo hT
  have hVn : G ≤ Subgroup.normalizer (V : Set Γ) := le_normalizer_vSub G T
  have hVQ : V ≤ pCoreOf 2 G := vSub_le_pCoreOf h.charTwo hT
  obtain ⟨E, hE, hcomm⟩ := h12 hZ
  obtain ⟨H, hH, hEH, hsub, huniq⟩ := h7 E hE
  have hcomm' : ∀ x ∈ tZero G T, ∀ e ∈ E, ⁅x, e⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
    rw [tZero_of_eq hZ]
    exact hcomm
  have hne : ¬ tZero G T ≤ Subgroup.centralizer (V : Set Γ) := by
    rw [tZero_of_eq hZ]
    obtain ⟨A, hAT, hAoff, hAwt⟩ := hoff
    obtain ⟨A', hA'min, -⟩ := exists_offStarMin_le (V := V) (T := T) (A := A) ⟨hAT, hAoff, hAwt⟩
    intro hle
    exact hA'min.1.2.1.2.1 ((le_qSub hA'min).trans hle)
  obtain ⟨-, hTH, hNH, hCH⟩ := seven_thirteen_one h hE hcomm' hne huniq
  obtain ⟨P, hTP, hPG, hPH, hmin⟩ := exists_minimal_overgroup h h5' hH hTH hNH
  have hEG : E ≤ G := hE.1.2.le
  have hPE : P ⊔ E = G := sup_eq_top_of_not_le huniq hPG.le hEG hTP hPH
  have hMP : MinPar P T (P ⊓ H) := minPar_of_minimal h hTH hNH hTP hPG hPH hmin
  have hPV : P ≤ Subgroup.normalizer (V : Set Γ) := hPG.le.trans hVn
  have hK : ⁅V, opResidual 2 P⁆ ≠ ⊥ := by
    intro h0
    apply hPH
    have hKC : opResidual 2 P ≤ Subgroup.centralizer (V : Set Γ) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : ⁅v, k⁆ ∈ (⁅V, opResidual 2 P⁆ : Subgroup Γ) :=
        Subgroup.commutator_mem_commutator hv hk
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hKH : opResidual 2 P ≤ H := fun k hk => hCH ⟨hPG.le (opResidual_le 2 P hk), hKC hk⟩
    exact (le_sup_opResidual hMP.syl).trans (sup_le hTH hKH)
  obtain ⟨W, hW⟩ := exists_isModuleW hMP.syl hMP.lt_P hMP.max hV.2 hPV hK
  exact false_of_offQ h.charTwo h.sylow hV hVQ hVn (pCoreOf_autOn_vSub_eq_bot hT) hE.1.2
    (commutator_vSub_ne_bot hEG hE.2) (le_sup_left.trans hEH) hsub hTH hH.1.le hMP hPG.le hPE.ge
    hW hoff

end Finite

end CFSG.CGT.PushingUpLit.BHS7
