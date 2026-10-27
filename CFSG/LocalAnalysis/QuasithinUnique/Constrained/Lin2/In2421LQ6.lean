module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ1
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Generic3

variable {G : Type*} [Group G]

theorem conjR_iSup {ι : Sort*} (f : ι → Subgroup G) (g : G) :
    conjR (⨆ i, f i) g = ⨆ i, conjR (f i) g := by
  simp only [conjR_def]
  exact Subgroup.map_iSup _ _

end Generic3

namespace Lin2Hyp0

section LQ6

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem conjR_Z_le_conjR_U {k m : G}
    (hne : conjR (lin2Z L (thompsonJ S)) k ⊓ conjR (blockU L) m ≠ ⊥) :
    conjR (lin2Z L (thompsonJ S)) k ≤ conjR (blockU L) m := by
  have h1 : conjR (lin2Z L (thompsonJ S)) (k * m⁻¹) ⊓ blockU L ≠ ⊥ := by
    intro h
    apply hne
    have : conjR (conjR (lin2Z L (thompsonJ S)) k ⊓ conjR (blockU L) m) m⁻¹ = ⊥ := by
      rw [conjR_inf, conjR_conjR_inv, conjR_conjR]
      exact h
    exact conjR_eq_bot_iff.1 this
  have h2 := E.conj_Z_le_U hcfg h1
  have h3 := conjR_mono h2 m
  rwa [conjR_conjR, inv_mul_cancel_right] at h3

theorem conjR_R_eq_of_normalizes {h : G}
    (hN : thompsonJ S ≤ Subgroup.normalizer (conjR (thompsonJ S) h : Set G)) :
    conjR (thompsonJ S) h = thompsonJ S := by
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hp2R : IsPGroup 2 (thompsonJ S) := hcfg.sylowT.isPGroup.to_le hRT
  have hp2 : IsPGroup 2 (conjR (thompsonJ S) h) := (isPGroup_conjR_iff 2).2 hp2R
  have hsup := isPGroup_sup_of_le_normalizer hN hp2R hp2
  obtain ⟨d, -, hd⟩ := exists_le_conjR_of_isSylowTwoOf hcfg.sylowT (le_top : _ ≤ ⊤) hsup
  have h1 : conjR (thompsonJ S) d⁻¹ ≤ T := by
    rw [conjR_le_iff, inv_inv]; exact le_sup_left.trans hd
  have h2 : conjR (conjR (thompsonJ S) h) d⁻¹ ≤ T := by
    rw [conjR_le_iff, inv_inv]; exact le_sup_right.trans hd
  have e1 := E.conjR_R_eq_of_le_T hcfg h1
  rw [conjR_conjR] at h2
  have e2 := E.conjR_R_eq_of_le_T hcfg h2
  have hRd : conjR (thompsonJ S) d = thompsonJ S := by
    have := congrArg (fun X => conjR X d) e1
    simp only [conjR_inv_conjR] at this
    exact this.symm
  calc conjR (thompsonJ S) h = conjR (conjR (thompsonJ S) (h * d⁻¹)) d := by
        rw [conjR_conjR]; congr 1; group
    _ = conjR (thompsonJ S) d := by rw [e2]
    _ = thompsonJ S := hRd

theorem thompsonJ_eq_of_lt {x h : G} (hx : x ∈ T) (hxS : x ∉ S) {X V : Subgroup G}
    (hXP : X ≤ conjR (thompsonJ S) h) (hne : X ≠ conjR (thompsonJ S) h) (hVX : V ≤ X)
    (hVel : IsElemAbelian 2 V) (hVc : Nat.card V = Nat.card (blockU L)) :
    thompsonJ X = V := by
  obtain ⟨hRU, -⟩ := E.RUU hcfg hx hxS
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hXT : X ≤ conjR T h := hXP.trans (conjR_mono hRT h)
  have hVmax : IsMaxElemAbelian X V :=
    ⟨hVX, hVel, fun B _ hB => (E.card_le_card_U_of_isElemAbelian hcfg hx hxS hB).trans hVc.ge⟩
  have hVcases := E.eq_or_eq_of_card_eq_of_le_conjR_T hcfg hx hxS hVel hVc (hVX.trans hXT)
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    have hAV : Nat.card V ≤ Nat.card A := hA.2.2 V hVX hVel
    have hAU : Nat.card A ≤ Nat.card (blockU L) :=
      E.card_le_card_U_of_isElemAbelian hcfg hx hxS hA.2.1
    have hAc : Nat.card A = Nat.card (blockU L) := by omega
    have hAcases := E.eq_or_eq_of_card_eq_of_le_conjR_T hcfg hx hxS hA.2.1 hAc (hA.1.trans hXT)
    by_contra hAVne'
    have hsup : conjR (blockU L) h ⊔ conjR (conjR (blockU L) x) h ≤ X := by
      rcases hAcases with hA1 | hA1 <;> rcases hVcases with hV1 | hV1
      · exact absurd (le_of_eq (hA1.trans hV1.symm)) hAVne'
      · exact sup_le (hA1 ▸ hA.1) (hV1 ▸ hVX)
      · exact sup_le (hV1 ▸ hVX) (hA1 ▸ hA.1)
      · exact absurd (le_of_eq (hA1.trans hV1.symm)) hAVne'
    apply hne
    apply le_antisymm hXP
    rw [← conjR_sup, ← hRU] at hsup
    exact hsup
  · exact CFSG.QuasithinUnique.GammaExtra.le_thompsonJ hVmax

end LQ6

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
