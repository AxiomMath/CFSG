module

public import CFSG.Quasithin.H13.A5S1327zd
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327p

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem pCoreOf_le_UH_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {hU : IsElemAbelian 2 (S.UH H)}
    {K₁ K₂ : Subgroup (MulAut (IntMod (S.UH H) hU))} (D : S2A S H hU K₁ K₂)
    (hQV : pCoreOf 2 (L ⊔ T) ≤ V) : pCoreOf 2 H ≤ S.UH H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have B := D.blocks
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hUO, -, hUred⟩ : S.UH H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (S.UH H) ∧ IsTwoReducedIn H (S.UH H) :=
    conjClosure_isTwoReducedIn_of_charTwo hsyl (S.charTwo_of_inH hH.1) le_rfl
  have hCU : H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H :=
    S.centralizer_UH_le_pCoreOf_all_F4 h331 h1222 h5172 hH hHZ hsolv
  have hHN : H ≤ Subgroup.normalizer (S.UH H : Set G) := B.le_norm
  have hTN : T ≤ Subgroup.normalizer (S.UH H : Set G) := hTH.trans hHN

  have hO : pCoreOf 2 (L ⊔ T) = V := le_antisymm hQV S.V_le_pCoreOf_LT
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer_F4 h5172 hH hHZ)
  have hodd : ∃ (t : G) (ht : t ∈ T), (S.frame.ρ ⟨t, S.frame.T_le ht⟩).sign ≠ 1 :=
    ⟨j, thompsonJ_le_self T hjJ, by
      rw [show (⟨j, S.frame.T_le (thompsonJ_le_self T hjJ)⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = ⟨j, hjN⟩ from rfl, hj]
      decide⟩
  have hcardT : Nat.card ↥T = 128 := by
    rw [S.card_T_eq hodd, hO, S.card_V]

  have hTC : T ⊓ Subgroup.centralizer (S.UH H : Set G) = pCoreOf 2 H := by
    apply le_antisymm
    · exact (inf_le_inf_right _ hTH).trans hCU
    · refine le_inf (pCoreOf_two_le_of_isSylowTwoOf hsyl) ?_
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp (hUO hu).2 q hq).symm

  have hJH := (E2_3_two_sylow_of_isSolvable hU (S.hyp501.minParabolic_of_isHStar_F4 h331 hH).1
    hsolv (fun p hp hp2 => by
      obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
      have : Fact p.Prime := ⟨hp⟩
      have h1 := hq p hp hp2
      rwa [← pRank_top_subtype]) hUred
    (S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ)).2
  rw [B.eqJ] at hJH
  have hcardK : Nat.card ↥(K₁ ⊔ K₂) = 36 := by
    have := B2F.card_sup_mul_card_inf_of_commute B.comm
    rw [B.inf, Subgroup.card_bot, mul_one, (S1417.card_of_actsAsNaturalL2 B.nat₁).1,
      (S1417.card_of_actsAsNaturalL2 B.nat₂).1] at this
    omega
  have hcardJ : Nat.card ↥(autI hU (thompsonJ T)) = 4 :=
    S1417.card_eq_four_of_isSylowTwoOf hJH hcardK
  obtain ⟨t, htT, ht⟩ := B.swap
  have htJ : t ∉ autI hU (thompsonJ T) := by
    intro h
    have := B.conjAut_K1 (hJH.1 h)
    rw [ht] at this
    exact B.ne this.symm
  have hJT : autI hU (thompsonJ T) ≤ autI hU T := autI_mono hU (thompsonJ_le_self T)
  have htJT : ¬ autI hU T ≤ autI hU (thompsonJ T) := fun h => htJ (h htT)
  have hcardTs : 8 ≤ Nat.card ↥(autI hU T) := by
    have h1 := Subgroup.relIndex_mul_card (autI hU (thompsonJ T)) (autI hU T)
    rw [inf_of_le_left hJT, hcardJ] at h1
    have h2 : (autI hU (thompsonJ T)).relIndex (autI hU T) ≠ 1 := fun h =>
      htJT (Subgroup.relIndex_eq_one.mp h)
    have h3 : 0 < Nat.card ↥(autI hU T) := Nat.card_pos
    omega

  have hmul := card_autI_mul_card_inf hU hTN
  rw [hTC, hcardT] at hmul
  have hO2 : Nat.card ↥(pCoreOf 2 H) ≤ 16 := by
    by_contra hlt
    push Not at hlt
    have : 8 * 17 ≤ Nat.card ↥(autI hU T) * Nat.card ↥(pCoreOf 2 H) :=
      Nat.mul_le_mul hcardTs hlt
    omega

  have hcardU : Nat.card ↥(S.UH H) = 16 := by
    have hc : ∀ a ∈ commV K₁, ∀ b ∈ commV K₂, a * b = b * a := fun a _ b _ => mul_comm a b
    have h1 := B2F.card_sup_mul_card_inf_of_commute hc
    rw [D.top, B.commV_inf, Subgroup.card_bot, mul_one,
      (S1417.card_of_actsAsNaturalL2 B.nat₁).2, (S1417.card_of_actsAsNaturalL2 B.nat₂).2,
      Subgroup.card_top] at h1
    exact h1
  exact (Subgroup.eq_of_le_of_card_ge (hUO.trans inf_le_left) (by rw [hcardU]; exact hO2)).ge

end Setting

end CFSG.Quasithin.H13.A5
