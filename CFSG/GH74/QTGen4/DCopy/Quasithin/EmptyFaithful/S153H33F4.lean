module

public import CFSG.Quasithin.EmptyFaithful.S153R33
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D44

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153H

theorem input33CharTwoSup_free (h113 : StageLemma14113) :
    ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
      CtxComp T Mc M V₁ V₂ Yp I t → IsComponentIn L I →
        ∀ L₁ : Subgroup G, L₁ ≤ conjClosure L (Sgp153 T V₁) →
          Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L₁ : Set G) → CharTwo L₁ → ¬ L₁ ≤ M ⊓ I →
            CharTwo (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL L₁ hL₁ hN hcL hnot
  have hDI : Yp ⊔ Sgp153 T V₁ ≤ I := c.inH.1.1
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans hDI
  have hL₁I : L₁ ≤ I := hL₁.trans (conjClosure_le fun s hs l hl =>
    I.mul_mem (I.mul_mem (hSI hs) (hL.1 hl)) (I.inv_mem (hSI hs)))
  have hXn : L₁ ⊔ (Yp ⊔ Sgp153 T V₁) ≤ Subgroup.normalizer (L₁ : Set G) :=
    sup_le Subgroup.le_normalizer hN
  have hL₁ne : L₁ ≠ ⊥ := fun hb => hnot (hb ▸ bot_le)
  have hO₂ : pCoreOf 2 L₁ ≠ ⊥ := by
    intro hb
    apply hL₁ne
    have h1 : L₁ ⊓ Subgroup.centralizer (pCoreOf 2 L₁ : Set G) ≤ pCoreOf 2 L₁ := hcL
    rw [hb] at h1
    rw [eq_bot_iff]
    intro x hx
    refine Subgroup.mem_bot.mpr (Subgroup.mem_bot.mp (h1 ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩))
    rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]
  have hO₂X : pCoreOf 2 L₁ ≤ pCoreOf 2 (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L₁).trans le_sup_left)
      (hXn.trans (normalizer_le_normalizer_pCoreOf 2 L₁)) (pCoreOf_isPGroup 2 L₁)
  have hX : IsHPlus Yp (Sgp153 T V₁) M (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) :=
    ⟨⟨le_sup_right, fun hb => hO₂ (le_bot_iff.mp (hO₂X.trans hb.le))⟩,
      fun hXM => hnot (le_inf (le_sup_left.trans hXM) hL₁I)⟩
  have hodd : oddCoreIn (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) = ⊥ :=
    S153D.input15311Eight_of_stages h113 G T Mc M V₁ V₂ Yp t c.hyp _ hX
  have hsolv : Group.IsSolvable ↥(Yp ⊔ Sgp153 T V₁) := S153D.isSolvable_Yp_sup' h113 c.hyp
  refine DoubleA3.charTwo_of_no_component (fun K hK => ?_) hodd
  have hperf : Group.IsPerfect ↥K := (BenderBranch.isQuasisimple_of_isComponentIn hK).1
  have hKL₁ : K ≤ L₁ := S153R.le_of_isPerfect_of_le_sup_solvable hN hK.1
  exact DoubleA3.not_isComponentIn_of_charTwo hcL K
    (BenderBranch.isComponentIn_of_le hK hKL₁ le_sup_left)

theorem input15333_of_charTwoSup_F4 (h11 : StageLemma14111) (h113 : StageLemma14113) :
    Stage15325_F4 → ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G]
      (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
      CtxComp T Mc M V₁ V₂ Yp I t → ∃ L : Subgroup G, Concl15333 T M V₁ Yp I L := by
  intro hS25 G _ _ T Mc M V₁ V₂ Yp I t c
  obtain ⟨L, hL⟩ := exists_component c
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  obtain ⟨z, hz, hz1, hZ⟩ := exists_generator_Z c.hyp.hyp
  have h115 := lemma115Hyp_of_ctx h11 h113 c hz hz1 hZ
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  refine ⟨L, ?_⟩
  refine
    { mem := Id2519.mem_cComp_of_isComponentIn hL
      quasisimple := hq
      center_eq := centerOf_eq_pCoreOf_of_isComponentIn c.oddCore hL
      not_le := not_le_M_of_isComponentIn c hL
      inv_le := ?_
      comp_prop := ?_ }
  ·
    intro L₁ hL₁ hN hchar
    by_contra hnle
    have hL₁I : L₁ ≤ I := hL₁.trans (conjClosure_le fun s hs l hl =>
      I.mul_mem (I.mul_mem (hSI hs) (hL.1 hl)) (I.inv_mem (hSI hs)))
    have hCX := input33CharTwoSup_free h113 G T Mc M V₁ V₂ Yp I L t c hL L₁ hL₁ hN hchar hnle
    have hV₁ne : ∃ v ∈ V₁, v ≠ 1 := by
      have hV₁b : V₁ ≠ ⊥ := by
        intro hb
        have := c.hyp.decomp.card₁
        rw [hb, Subgroup.card_bot] at this
        omega
      obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₁b
      exact ⟨v, hv, fun h1 => hv1 (Subtype.ext h1)⟩
    have hV₁S : V₁ ≤ Sgp153 T V₁ :=
      le_inf (c.hyp.decomp.le₁.trans c.hyp.hyp.VZ_le_T) Subgroup.le_normalizer
    have hX : IsHPlus Yp (Sgp153 T V₁) M (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) := by
      refine ⟨⟨le_sup_right, ?_⟩, fun hXM => hnle (le_inf (le_sup_left.trans hXM) hL₁I)⟩
      intro hb
      obtain ⟨v, hv, hv1⟩ := hV₁ne
      have hvX : v ∈ L₁ ⊔ (Yp ⊔ Sgp153 T V₁) := Subgroup.mem_sup_right (Subgroup.mem_sup_right (hV₁S hv))
      have h1 : (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) ⊓
          Subgroup.centralizer (pCoreOf 2 (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) : Set G) ≤
          pCoreOf 2 (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) := hCX
      rw [hb] at h1
      refine hv1 (Subgroup.mem_bot.mp (h1 ⟨hvX, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩))
      rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]
    exact hS25 G T Mc M V₁ V₂ Yp t c.hyp _ hX hCX
  ·
    intro K hKc
    obtain ⟨-, hcomm, -, hchar⟩ := h115.component_action hKc
    have hcent : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
        Subgroup.centralizer {z} := by
      rw [hZ]
      exact centralizer_zpowers_eq z
    refine ⟨not_le_M_of_isComponentIn c hKc, ?_, ?_, ?_⟩
    · rw [hZ]
      exact hcomm
    · exact le_bot_iff.mp ((oddCoreIn_le_of_isComponentIn hKc).trans c.oddCore.le)
    · rw [hcent]
      exact hchar

end S153H

end CFSG.Quasithin
