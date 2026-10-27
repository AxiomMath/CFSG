module

public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenE
public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenB
public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenD
public import CFSG.CGT.PushingUpLit.BHS7.VFacts

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem zSub_le : zSub T ≤ T :=
  (C1GN.omegaOneCenterOf_le_self (baum T)).trans (C1GN.baum_le T)

omit [Finite Γ] in
theorem le_normalizer_zSub : T ≤ Subgroup.normalizer (zSub T : Set Γ) := by
  intro t ht
  refine BHS.mem_normalizer_of_conjSub_eq ?_
  have h1 : zSub (A1b.conjSub t T) = A1b.conjSub t (zSub T) := by
    unfold zSub
    rw [baum_conjSub, omegaOneCenterOf_conjSub]
  rw [← h1, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer ht)]

omit [Finite Γ] in
theorem zSub_le_centralizer_thompsonJ : zSub T ≤ Subgroup.centralizer (thompsonJ T : Set Γ) := by
  intro z hz
  have h1 : z ∈ Subgroup.centralizer (baum T : Set Γ) :=
    (C1GN.omegaOneCenterOf_le_centerOf (baum T) hz).2
  rw [Subgroup.mem_centralizer_iff] at h1 ⊢
  intro j hj
  exact h1 j (B6.thompsonJ_le_baum T hj)

theorem branch_z_false (h : MinCex G T) {H P : Subgroup Γ}
    (hTH : T ≤ H) (hNH : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ H)
    (hCH : G ⊓ Subgroup.centralizer (vSub G T : Set Γ) ≤ H) (hTP : T ≤ P) (hPG : P < G)
    (hPH : ¬ P ≤ H) (hmin : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ H)
    (hZ : ⁅vSub G T, zSub T⁆ ≠ ⊥)
    (hA : zSub T ⊓ pCoreOf 2 P ≤ Subgroup.centralizer (vSub G T : Set Γ)) : False := by
  have hT : IsSylowTwoOf T G := h.sylow
  set V : Subgroup Γ := vSub G T with hVdef
  have hV : IsElemAbelian 2 V := isElemAbelian_vSub h.charTwo hT
  have hVn : G ≤ Subgroup.normalizer (V : Set Γ) := le_normalizer_vSub G T
  have hPV : P ≤ Subgroup.normalizer (V : Set Γ) := hPG.le.trans hVn
  have hMP : MinPar P T (P ⊓ H) := minPar_of_minimal h hTH hNH hTP hPG hPH hmin
  have hPT : IsSylowOf 2 T P := hMP.syl
  have hMlt : P ⊓ H < P := hMP.lt_P
  have hMu : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ P ⊓ H := hMP.max
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
    exact (le_sup_opResidual hPT).trans (sup_le hTH hKH)
  obtain ⟨W, hW⟩ := exists_isModuleW hPT hMlt hMu hV.2 hPV hK
  have hZT : zSub T ≤ T := zSub_le
  have hZP : ¬ zSub T ≤ pCoreOf 2 P := by
    intro hle
    apply hZ
    have hZC : zSub T ≤ Subgroup.centralizer (V : Set Γ) := fun z hz => hA ⟨hz, hle hz⟩
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv z hz
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hZC hz) v hv
  have hQ : ⁅W, pCoreOf 2 P⁆ = ⊥ :=
    commutator_pCoreOf_eq_bot hPT hMlt hMu hW hPV hZT le_normalizer_zSub hA hZP
  have hPW := hW.normalized
  have hO2 : pCoreOf 2 P ≤ Subgroup.centralizer (W : Set Γ) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : ⁅w, q⁆ ∈ (⁅W, pCoreOf 2 P⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hw hq
    rw [hQ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hWe : IsElemAbelian 2 W := isElemAbelian_mono' hV hW.le_V
  have hWT : W ≤ T := hW.le_V.trans ((vSub_le_pCoreOf h.charTwo hT).trans hT.pCoreOf_le)
  have hker : P ⊓ Subgroup.centralizer (W : Set Γ) ≤ P ⊓ H := by
    set N' : Subgroup Γ := P ⊓ Subgroup.centralizer (W : Set Γ) with hN'
    have hN'n : P ≤ Subgroup.normalizer (N' : Set Γ) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        B6.le_normalizer_centralizer hPW hg⟩
    by_contra hnot
    have hKN := three_three_b hPT hMu inf_le_left hN'n hnot
    apply hW.ne_bot
    have h0 : ⁅W, opResidual 2 P⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw k hk
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp (hKN hk).2 w hw
    rw [← hW.comm_eq, h0]
  have hJ : W ≤ thompsonJ T := le_thompsonJ_of_minPar hMP hWe hPW hker hO2 hWT
  apply hZP
  intro z hz
  have hzJ := zSub_le_centralizer_thompsonJ hz
  have hzW : z ∈ Subgroup.centralizer (W : Set Γ) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => Subgroup.mem_centralizer_iff.mp hzJ w (hJ hw)
  exact centralizer_inf_le_pCoreOf hW ⟨hzW, hZT hz⟩

end CFSG.CGT.PushingUpLit.BHS7
