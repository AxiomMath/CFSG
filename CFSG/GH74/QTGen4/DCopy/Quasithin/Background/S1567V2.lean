module

public import CFSG.Quasithin.Background.S1567V2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.S1567W4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

@[expose] def Input15368PsiL3Loc_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368NoTwo T Mc M E s →
    Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(StatedSL 3 (ZMod 2))) →
    Nat.card ↥(⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆) ≤ 2 ^ 6

theorem false_of_L32_of_loc_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}
    (h11 : StageLemma14111) (h113 : StageLemma14113) (hloc : Input15368PsiL3Loc_F4)
    (c : Ctx153 G T Mc M V₁ V₂ t) (r45 : Res15345 T Mc M V₁ V₂) (r46 : Res15346 T M V₁ V₂)
    (r49 : Res15349 T Mc M V₁) (r50 : Res15350 T M) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s)
    (hL3 : Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(StatedSL 3 (ZMod 2)))) : False := by
  have k : Ctx67 G T Mc M V₁ V₂ E t :=
    ⟨c, r45, r46, r49, r50, L, r66, ⟨r67.sylow_GE, r67.baum_le, r67.CGS_le⟩⟩
  have hQ := hloc G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl r68 hL3
  have hVEV0 : VE67 T M E ≤ V0_153 T Mc M E s := S1567.VE67_le_V0 k r67
  have hV0Q := S1567.V0_le_Q k gl r68
  have h64 := S1567.sixtyFour_le_card_VE67 k r67
  have hV0c : Nat.card ↥(V0_153 T Mc M E s) ≤ 2 ^ 6 :=
    (Subgroup.card_le_of_le hV0Q).trans hQ
  have hV0E : V0_153 T Mc M E s = VE67 T M E :=
    (Subgroup.eq_of_le_of_card_ge hVEV0 (hV0c.trans h64)).symm
  have hQV0 : ⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆ =
      V0_153 T Mc M E s :=
    (Subgroup.eq_of_le_of_card_ge hV0Q
      (hQ.trans (h64.trans (Subgroup.card_le_of_le hVEV0)))).symm
  have hQX : ⁅pCoreOf 2 (G0_153 T Mc M E s), XE153 E⁆ ≤ V0_153 T Mc M E s :=
    hQV0 ▸ Subgroup.commutator_mono le_rfl S1567.XE_le_oTwoUpper_G0
  refine S1567.false_of_VE_normalized h11 h113 k r67 gl ?_ ?_
  · intro y hy
    have h1 : y ∈ G0_153 T Mc M E s := Subgroup.mem_sup_left (Subgroup.mem_sup_left hy)
    have h2 := V0_normal h1
    rwa [hV0E] at h2
  · intro x hx a ha
    have haQ : a ∈ pCoreOf 2 (G0_153 T Mc M E s) :=
      S1567.conjSubgroup_VE67_le_pCore_G0 k r67 gl hV0E ha
    have h1 : ⁅x, a⁆ ∈ ⁅XE153 E, pCoreOf 2 (G0_153 T Mc M E s)⁆ :=
      Subgroup.commutator_mem_commutator hx haQ
    rw [Subgroup.commutator_comm] at h1
    have hcomm : ⁅x, a⁆ ∈ VE67 T M E := hV0E ▸ hQX h1
    rw [commutatorElement_def] at hcomm
    have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right ha)

theorem input15368PsiL3_of_loc_F4 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hloc : Input15368PsiL3Loc_F4) : Input15368PsiL3_F4 := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl r68 hL3
  exact (false_of_L32_of_loc_F4 h11 h113 hloc c r45 r46 r49 r50 L r66 r67 gl r68 hL3).elim

end CFSG.Quasithin
