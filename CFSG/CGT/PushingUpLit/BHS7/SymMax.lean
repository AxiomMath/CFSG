module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaMaxSwapCore
public import CFSG.CGT.PushingUpLit.BHS7.OmegaSL

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem card_autOn_baum_of_isBTBlock (h : MinCex G T) {E : Subgroup Γ} (hE : IsBTBlock G T E)
    (hn : ¬ E ≤ cStarIn G T) {m : ℕ} (hm2 : 2 ≤ m) (hnat : IsNaturalAltModule ↥E m) :
    Nat.card ↥(autOn (baum T) (pCoreOf 2 E)) = 2 ^ m := by
  classical
  have hG : CharTwo G := h.charTwo
  have hT : IsSylowOf 2 T G := h.sylow
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.2.1.to_le hBT
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hE
  have hEG : E ≤ G := hE.le
  have hHG : E ⊔ baum T ≤ G := sup_le hEG (hBT.trans hT2.1)
  have hHE : E ⊔ baum T ≤ Subgroup.normalizer (E : Set Γ) :=
    sup_le Subgroup.le_normalizer hBE
  obtain ⟨S₀, hS₀, hBS₀⟩ := B6.exists_isSylowTwoOf_ge hB2 (le_sup_right : baum T ≤ E ⊔ baum T)
  obtain ⟨T₁, hT₁, hST₁⟩ := B6.exists_isSylowTwoOf_ge hS₀.2.1 (hS₀.1.trans hHG)
  have hb : baum T₁ = baum T := baum_eq_of_le_sylow hT2 hT₁ (hBS₀.trans hST₁)
  have hCs : cStarIn G T₁ = cStarIn G T := cStarIn_eq_of_baum_eq hT2 hT₁ hb hb0
  have hE₁ : IsBTBlock G T₁ E := isBTBlock_of_sub hE le_rfl hb.symm (by rw [hCs]; exact hn)
  have hSE : IsSylowTwoOf (S₀ ⊓ E) E := B6.isSylowTwoOf_inf_normal hS₀ le_sup_left hHE
  have hS₁ : IsSylowTwoOf (T₁ ⊓ E) E := by
    have hle : S₀ ⊓ E ≤ T₁ ⊓ E := inf_le_inf_right E hST₁
    have hR2 : IsPGroup 2 ↥(T₁ ⊓ E) := hT₁.2.1.to_le inf_le_left
    have heq : S₀ ⊓ E = T₁ ⊓ E := OMS.eq_of_isSylowTwoOf_le hSE inf_le_right hR2 hle
    rwa [← heq]
  have hmain := card_autOn_baum_of_isSylowTwoOf hG (isSylowOf_of_isSylowTwoOf hT₁) hE₁ hm2 hnat hS₁
    (fun c hc hcW => by
      rw [hb] at hc
      exact exists_pow_two_eq_one_of_centralizes hchar hE.elemAbelian.1 hB2 hBE hc hcW)
  rwa [hb] at hmain

end CFSG.CGT.PushingUpLit.BHS7
