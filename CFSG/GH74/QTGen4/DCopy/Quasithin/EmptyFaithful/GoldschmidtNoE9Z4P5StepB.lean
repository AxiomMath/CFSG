module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S1469One
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P5Defs
public import CFSG.Quasithin.EmptyFaithful.S146GoldA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stepB_E9_F4 (hcab : GoldschmidtCentralAbelianBound) (h9 : Stage1469W)
    (h105 : Stage14610FiveW_F4) (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three)
    (h4 : Stage1463Four) {T M : Subgroup G} (S : Setting146 G T M)
    (hD : FinalData146E9 T M) : False := by
  obtain ⟨H, u, H₂, hH, hu, hCu, h211, hm, hT0, hH₂C, hS3, hH₂M, hrk⟩ := hD
  obtain ⟨I, hI, hIc⟩ := exists_isIStar_choice hCu
  have hTH : T ≤ H := hH.1.1
  have hlIL : lI T M I ≤ yOfL22 T M := (oTwoUpper_le _).trans inf_le_left
  have hlII : lI T M I ≤ I := (oTwoUpper_le _).trans inf_le_right
  have ha := h1 G T M S H hH u hu
  have hb := h2 G T M S H hH u hu
  have hc := h3 G T M S H hH u hu
  have hd := h4 G T M S H hH u hu

  have hLT := h9 G T M H u S hH hu I hI h211 hm

  have hL_eq : yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) := by
    refine le_antisymm ?_ (sup_le hlIL (LieType.BorelTits.pCoreOf_le 2 _))
    refine le_sup_pCoreOf_of_S3 (X := yOfL22 T M ⊔ T) le_sup_left ?_ S.hyp1281.residual
      (oTwoUpper_oTwoUpper _) hlIL S.facts.sThree (S.hyp.sylow.1.to_le inf_le_left)
      (inf_le_left.trans le_sup_right) hLT
    exact sup_le Subgroup.le_normalizer (S.hyp.m_max.1.2.trans S.hyp1281.normal)

  obtain ⟨hI₀, hGT⟩ := six_main_central hcab S hH hu ha hb hc hd hI h211 hL_eq hT0 hH₂C hS3 hH₂M
  have hTI_le : T ⊓ I ≤ (lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)) :=
    le_sup_right.trans le_sup_left
  obtain ⟨-, hTI₀⟩ := hI.of_le_inf hI₀.1 hTI_le

  have hTIH₂ : T ⊓ I ≤ H₂ := by
    refine le_trans ?_ hT0
    rcases (isIStar_sylow_cases S hu ha.2.1 hb hd.1 hI).2 with h | h
    · rw [h]; exact tU_le_tZero T u
    · exact h.le
  have hOc : oTwoUpper H₂ ≤ Subgroup.centralizer ({u} : Set G) :=
    S.oTwoUpper_le_centralizer hH hH₂C
  have hH₂H : H₂ ≤ H := hH₂C.trans (centralizerMod_le_left _ _ _)
  have hI₂H : oTwoUpper H₂ ⊔ (T ⊓ I) ≤ H :=
    sup_le ((oTwoUpper_le H₂).trans hH₂H) (inf_le_left.trans hTH)
  have hI₀eq := eq_sup_lI_sup (T := T) (M := M) (A := lI T M I) (B := T ⊓ I)
    (C := oTwoUpper H₂) (oTwoUpper_oTwoUpper _) hlIL rfl hTI₀
  have hcent : T ⊓ ((lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I))) = tU T u →
      (lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro h
    have hIT : T ⊓ I = tU T u := by rw [← hTI₀]; exact h
    have hIc' := hIc hIT
    exact sup_le (sup_le (hlII.trans hIc') (inf_le_right.trans hIc'))
      (sup_le hOc (inf_le_right.trans hIc'))

  have hrank := h105 G T M H u S hH hu _ hI₀ h211 hm (oTwoUpper H₂ ⊔ (T ⊓ I))
    (by rw [hTI₀]; exact le_sup_right) hI₂H hGT.2.2.1 hI₀eq hcent
  have hconj : conjClosure (VZ T M) (oTwoUpper H₂ ⊔ (T ⊓ I)) =
      conjClosure (VZ T M) (oTwoUpper H₂) :=
    conjClosure_sup_eq_of_normalizes (hTIH₂.trans (le_normalizer_oTwoUpper H₂))
      (inf_le_left.trans S.T_le_normalizer_V)
  rw [hconj, hrk] at hrank
  norm_num at hrank

end CFSG.Quasithin
