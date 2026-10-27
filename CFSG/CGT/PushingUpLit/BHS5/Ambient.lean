module

public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
public import CFSG.CGT.PushingUpLit.BHS.HomTransfer
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS

variable {Γ : Type} [Group Γ] [Finite Γ]

structure AmbHyp (G T M : Subgroup Γ) : Prop where
  charTwo : CharTwo G
  minpar : MinPar G T M
  ne : cStarStarIn G T ≠ G

section General

variable {G : Subgroup Γ}

omit [Finite Γ] in
theorem omegaOneCenterOf_pCoreOf_le : omegaOneCenterOf (pCoreOf 2 G) ≤ pCoreOf 2 G := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hx, -⟩
  exact hx.1

omit [Finite Γ] in
theorem isElemAbelian_omegaOneCenterOf_pCoreOf :
    IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 G)) := by
  refine B2F.isElemAbelian_closure ?_ ?_
  · rintro a ⟨ha, -⟩ b ⟨hb, -⟩
    exact Subgroup.mem_centralizer_iff.1 hb.2 a ha.1
  · rintro a ⟨-, ha2⟩
    exact ha2

omit [Finite Γ] in
theorem le_normalizer_omegaOneCenterOf_pCoreOf :
    G ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 G) : Set Γ) :=
  (le_normalizer_pCoreOf 2 G).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

omit [Finite Γ] in
theorem pCoreOf_le_centralizer_omegaOneCenterOf :
    pCoreOf 2 G ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 G) : Set Γ) := by
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
  have hv' : v ∈ centerOf (pCoreOf 2 G) := (Subgroup.closure_le _).2 (fun z hz => hz.1) hv
  exact (Subgroup.mem_centralizer_iff.1 hv'.2 x hx).symm

end General

section Basic

variable {G T M : Subgroup Γ} (h : AmbHyp G T M)

include h

theorem AmbHyp.pCoreOf_le_T : pCoreOf 2 G ≤ T := by
  have := pCoreOf_map_le (MonoidHom.id Γ) h.minpar.syl
  simpa using this

theorem AmbHyp.V_le_T : omegaOneCenterOf (pCoreOf 2 G) ≤ T :=
  omegaOneCenterOf_pCoreOf_le.trans h.pCoreOf_le_T

theorem AmbHyp.omegaOneCenterOf_T_le_V :
    omegaOneCenterOf T ≤ omegaOneCenterOf (pCoreOf 2 G) := by
  refine Subgroup.closure_mono ?_
  rintro x ⟨hx, hx2⟩
  refine ⟨⟨?_, ?_⟩, hx2⟩
  · refine h.charTwo ⟨h.minpar.T_le hx.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact Subgroup.mem_centralizer_iff.1 hx.2 y (h.pCoreOf_le_T hy)
  · refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact Subgroup.mem_centralizer_iff.1 hx.2 y (h.pCoreOf_le_T hy)

omit [Finite Γ] in
theorem AmbHyp.T_le_cStarStar : T ≤ cStarStarIn G T := by
  refine le_sup_of_le_left (le_inf h.minpar.T_le ?_)
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  have hz' : z ∈ centerOf T := (Subgroup.closure_le _).2 (fun w hw => hw.1) hz
  exact (Subgroup.mem_centralizer_iff.1 hz'.2 x hx).symm

omit [Finite Γ] in
theorem AmbHyp.cStarStar_le_M : cStarStarIn G T ≤ M :=
  h.minpar.max _ h.T_le_cStarStar
    (lt_of_le_of_ne (sup_le inf_le_left inf_le_left) h.ne)

theorem AmbHyp.cenV_le_M :
    G ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 G) : Set Γ) ≤ M := by
  intro g hg
  refine h.cStarStar_le_M (le_sup_left (a := G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ))
    ⟨hg.1, ?_⟩)
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  exact Subgroup.mem_centralizer_iff.1 hg.2 z (h.omegaOneCenterOf_T_le_V hz)

theorem AmbHyp.not_thompsonJ_le_centralizer_V :
    ¬ thompsonJ T ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 G) : Set Γ) := by
  intro hJ
  set V : Subgroup Γ := omegaOneCenterOf (pCoreOf 2 G) with hV
  set N : Subgroup Γ := G ⊓ Subgroup.centralizer (V : Set Γ) with hN
  have hNG : N ≤ G := inf_le_left
  have hGN : G ≤ Subgroup.normalizer (N : Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg,
        B6.le_normalizer_centralizer le_normalizer_omegaOneCenterOf_pCoreOf hg⟩
  have hsyl : IsSylowTwoOf (T ⊓ N) N := B6.isSylowTwoOf_inf_normal h.minpar.syl hNG hGN
  have hJle : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJTN : thompsonJ T ≤ T ⊓ N := le_inf hJle (le_inf (hJle.trans h.minpar.T_le) hJ)
  have hJeq : thompsonJ T = thompsonJ (T ⊓ N) := thompsonJ_eq_of_le hJTN inf_le_left
  have hfr := B6.frattini_two hNG hGN hsyl
  apply h.ne
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun g hg => ?_
  have hKN : G ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer (N : Set Γ) := inf_le_left.trans hGN
  have hg' : g ∈ ((G ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup Γ) : Set Γ) ⊔ N : Subgroup Γ) :
      Set Γ) := by
    rw [sup_comm]
    exact hfr hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ N hKN] at hg'
  obtain ⟨m, hm, n, hn, rfl⟩ := hg'
  refine mul_mem ?_ ?_
  · refine le_sup_right (a := G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ)) ⟨hm.1, ?_⟩
    have := normalizer_le_normalizer_thompsonJ (T ⊓ N) hm.2
    rwa [← hJeq] at this
  · refine le_sup_left (a := G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ)) ⟨hn.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    exact Subgroup.mem_centralizer_iff.1 hn.2 z (h.omegaOneCenterOf_T_le_V hz)

end Basic

end CFSG.CGT.PushingUpLit.BHS5
