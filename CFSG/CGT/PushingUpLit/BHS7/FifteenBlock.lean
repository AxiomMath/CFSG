module

public import CFSG.CGT.PushingUpLit.BHS7.SevenSix

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem exists_isBTBlock_le_of_lSet (h : MinCex G T) {X : Subgroup Γ} (hX : X ∈ lSet G T) :
    ∃ F : Subgroup Γ, IsBTBlock G T F ∧ F ≤ X ∧ ¬ F ≤ cStarIn G T := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  obtain ⟨hXG, hBX, hXC⟩ := hX
  obtain ⟨S, hS, hBS⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBX
  obtain ⟨-, -, 𝒢, hblock, -, -, hc, -⟩ := seven_three h hT ⟨hXG, hBX, hXC⟩ hS
  have hSX : baum S = baum T :=
    baum_eq_of_isPGroup_of_baum_le hT hS.2.1 (hS.1.trans hXG.le) hBS
  by_contra hall
  push Not at hall
  apply hXC
  rw [← hc]
  refine sup_le (two_three_d hT hb0 hXG.le hS hBS) (iSup₂_le fun F hF => ?_)
  by_contra hFC
  exact hFC (hall F (isBTBlock_of_sub (hblock F hF) hXG.le hSX hFC) (hblock F hF).le)

theorem exists_isBTBlock_le (h : MinCex G T) (h5 : ¬ IsMinParabolic2 T G) {L : Subgroup Γ}
    (hTL : T ≤ L) (hLG : L ≤ G) (hLC : ¬ L ≤ cStarIn G T) :
    ∃ F : Subgroup Γ, IsBTBlock G T F ∧ F ≤ L ∧ ¬ F ≤ cStarIn G T := by
  rcases hLG.lt_or_eq with hlt | heq
  · exact exists_isBTBlock_le_of_lSet h ⟨hlt, (inf_le_left : baum T ≤ T).trans hTL, hLC⟩
  · obtain ⟨F, hF, hFC⟩ := exists_isBTBlock_not_le h h5
    exact ⟨F, hF, hF.le.trans heq.ge, hFC⟩

omit [Finite Γ] in
theorem le_centralizer_of_isPGroup_autOn {V F : Subgroup Γ} (hF : IsBTBlock G T F)
    (hFN : F ≤ Subgroup.normalizer (V : Set Γ)) (h2 : IsPGroup 2 ↥(autOn F V)) :
    F ≤ Subgroup.centralizer (V : Set Γ) := by
  have hY := SubTwo.noTwoQuotient_of_oResidualTwo hF.residual
  have key := hY (F ⊓ Subgroup.centralizer (V : Set Γ)) inf_le_left ?_ ?_
  · exact key ▸ inf_le_right
  · intro f hf
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hf,
      B6.le_normalizer_centralizer (fun x hx => hFN hx) hf⟩
  · intro y hy
    obtain ⟨k, hk⟩ := h2 ⟨conjAct V ⟨y, hFN hy⟩, mem_autOn_iff.2 ⟨⟨y, hFN hy⟩, hy, rfl⟩⟩
    refine ⟨k, F.pow_mem hy _, ?_⟩
    have hmem : y ^ 2 ^ k ∈ Subgroup.normalizer (V : Set Γ) :=
      (Subgroup.normalizer (V : Set Γ)).pow_mem (hFN hy) _
    have h3 : conjAct V ⟨y ^ 2 ^ k, hmem⟩ = 1 := by
      have e : (⟨y ^ 2 ^ k, hmem⟩ : ↥(Subgroup.normalizer (V : Set Γ))) =
          (⟨y, hFN hy⟩ : ↥(Subgroup.normalizer (V : Set Γ))) ^ 2 ^ k := Subtype.ext (by simp)
      have h4 := congrArg Subtype.val hk
      rw [e, map_pow]
      simpa using h4
    exact (conjAct_eq_one_iff V ⟨y ^ 2 ^ k, hmem⟩).1 h3

end CFSG.CGT.PushingUpLit.BHS7
