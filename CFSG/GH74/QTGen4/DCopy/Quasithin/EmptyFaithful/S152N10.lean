module

public import CFSG.Quasithin.EmptyFaithful.S152N10
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

open S152N

section Final

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stageLemma15210_of_F4 (h1518 : StageLemma1518) (h15201 : StageLemma15201_F4) :
    StageLemma15210_F4 := by
  intro G _ _ T Mc M hs D hD
  have hc := h15201 G T Mc M hs
  have hTM : T ≤ M := hs.mf.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hV : IsElemAbelian 2 (V154 T Mc M) := by
    by_contra hV
    have : D ∈ (∅ : Set (Subgroup (MulAut (V154 T Mc M)))) := by
      unfold QsetOn at hD
      rwa [dite_eq_right hV] at hD
    exact this
  have hD0 : D ∈ @Qset ↥(V154 T Mc M) (commGroupOfElemAbelian hV) (autOn T (V154 T Mc M)) := by
    unfold QsetOn at hD
    rwa [dite_eq_left hV] at hD
  obtain ⟨⟨hA2, hr⟩, hcq⟩ := hD0
  have hrk : rk (IntMod (V154 T Mc M) hV) = 4 := by
    have h1 := card_eq_two_pow_of_isPGroup
      (isPGroup_two_of_sq_eq_one (fun v : IntMod (V154 T Mc M) hV => IntMod.sq_eq_one v))
    have h2 : Nat.card (IntMod (V154 T Mc M) hV) = 16 := hc.card
    rw [h2] at h1
    have : (2 : ℕ) ^ rk (IntMod (V154 T Mc M) hV) = 2 ^ 4 := by omega
    exact Nat.pow_right_injective (le_refl 2) this

  have hq : (2 : WithTop ℚ) ≤ qOf (autI hV M) := by
    have h18 := h1518 G T Mc M hs.qtfe hs.mf hs.ce
    have hqOn : qOn M (V154 T Mc M) = 2 := by
      rcases h18 with ⟨-, h⟩ | ⟨-, -, h⟩ <;> exact h
    have : qInt M (V154 T Mc M) hV = 2 := by rw [← qOn_eq hV]; exact hqOn
    exact this.ge
  have hTbM : autI hV T ≤ autI hV M := autI_mono hV hTM
  have hD' : D ∈ Qset (autI hV M) := ⟨⟨⟨hA2.1.trans hTbM, hA2.2⟩, hr⟩, hcq⟩
  obtain ⟨hrkD, hrkC⟩ := rk_of_mem_Qset (V := IntMod (V154 T Mc M) hV)
    (fun v => IntMod.sq_eq_one v) hrk hq hD'
  obtain ⟨hcomm, hP2⟩ := tbar_props hs hc hV
  have hA2I : IsA2 (autI hV T) D := hA2
  have hDp : IsPGroup 2 D := hA2I.isElemAbelian2.isPGroup
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · exact hP2 x (hA2.1 hx) (hA2I.isElemAbelian2.2 x hx) hx1
  ·
    have h1 : Nat.card D = 2 ^ rk D := card_eq_two_pow_of_isPGroup hDp
    have h2 : rk D = 1 := hrkD
    rw [h1, h2, pow_one]
  ·
    have hY : preOn T (V154 T Mc M) D ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
      (preOn_le _ _ _).trans (hTM.trans hMN)
    have h1 := S1417.commutator_eq_map_commV hV hY
    have h2 : autI hV (preOn T (V154 T Mc M) D) = D := autOn_preOn hA2.1
    rw [h1, h2, Subgroup.card_map_of_injective (S1417.inclMod_injective hV),
      card_eq_two_pow (fun v : IntMod (V154 T Mc M) hV => IntMod.sq_eq_one v) (commV D), hrkC]
    norm_num
  ·
    intro x hx
    have hxV := hMN (hTM hx)
    have hxP : x ∈ Subgroup.normalizer (preOn T (V154 T Mc M) D : Set G) :=
      le_normalizer_preOn (hTM.trans hMN) (fun g hg y hy => by
        have hgy : g * y * g⁻¹ = y := by
          rw [hcomm g hg y (hA2.1 hy)]; group
        rw [hgy]; exact hy) hx
    exact A4.mem_normalizer_commutator hxV hxP

end Final

end CFSG.Quasithin
