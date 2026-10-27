module

public import CFSG.CGT.PushingUpLit.BHS.ThreeSixC
public import CFSG.CGT.PushingUpLit.BHS5.JSplit
public import CFSG.CGT.PushingUpLit.BHS7.Pending
public import CFSG.CGT.PushingUpLit.BHS7.VFacts

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5 CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem wt_le_card_vSub (hG : CharTwo G) (hT : IsSylowTwoOf T G) (h13 : Seven13 G T)
    {X : Subgroup (MulAut ↥(vSub G T))}
    (hX : @IsElemAbelian2 ↥(vSub G T) (commGroupOfElemAbelian (isElemAbelian_vSub hG hT)) X)
    (hXG : X ≤ autOn G (vSub G T)) :
    Nat.card X * Nat.card (@fixV ↥(vSub G T) (commGroupOfElemAbelian (isElemAbelian_vSub hG hT)) X)
      ≤ Nat.card (vSub G T) := by
  classical
  have hV : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub hG hT
  let _ : CommGroup ↥(vSub G T) := commGroupOfElemAbelian hV
  have hGN : G ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := le_normalizer_vSub G T
  have hTN : T ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := hT.1.trans hGN
  have hsyl : IsSylowTwoOf (autOn T (vSub G T)) (autOn G (vSub G T)) :=
    CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hT hGN
  have hX2 : IsPGroup 2 ↥X := isPGroup_of_isElemAbelian2 hX
  obtain ⟨S, hS, hXS⟩ := B6.exists_isSylowTwoOf_ge hX2 hXG
  obtain ⟨g, hg, hgS⟩ := B6.isSylowTwoOf_exists_conj hsyl hS
  set X' : Subgroup (MulAut ↥(vSub G T)) := A1b.conjSub g⁻¹ X with hX'
  have hX'T : X' ≤ autOn T (vSub G T) := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ X := by
      have := (A1b.mem_conjSub_iff).1 hx
      simpa using this
    have h2 : g * x * g⁻¹ ∈ S := hXS h1
    rw [hgS] at h2
    have h3 : g⁻¹ * (g * x * g⁻¹) * g ∈ autOn T (vSub G T) :=
      (B6.mem_conjSub.1 h2)
    simpa [mul_assoc] using h3
  have hwtX : wt X' = wt X := by
    unfold wt
    rw [hX', show A1b.conjSub g⁻¹ X = X.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      Glauberman.card_map_conj, Glauberman.fixV_map_conj, Subgroup.card_map_of_injective
        (g⁻¹).injective]
  have hX'el : IsElemAbelian2 X' := isElemAbelian2_conjSub hX g⁻¹
  obtain ⟨Y, hY, hYmax⟩ := Set.exists_max_image {Z : Subgroup (MulAut ↥(vSub G T)) | Z ≤ X'}
    (fun Z => wt Z) (Set.toFinite _)
    ⟨⊥, show (⊥ : Subgroup (MulAut ↥(vSub G T))) ≤ X' from bot_le⟩
  have hYX' : Y ≤ X' := hY
  have hvY : wt Y ≤ Nat.card (vSub G T) := by
    by_cases hY0 : Y = ⊥
    · rw [hY0]
      exact (B1.card_bot_mul_card_fixV).le
    · have hYoff : IsOff Y := ⟨le_top, hY0, isElemAbelian2_mono' hX'el hYX',
        fun B hB => hYmax B (hB.trans hYX')⟩
      obtain ⟨A, hAT, hAY⟩ := exists_autOn_eq (hYX'.trans hX'T)
      have hAN : A ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := hAT.trans hTN
      have hoff : IsOffG (vSub G T) A :=
        (isOffG_iff_isOff_autOn hV hAN).mpr (hAY ▸ hYoff)
      have h := h13.2 A hAT
      have hle : wtG (vSub G T) A ≤ Nat.card (vSub G T) := by
        by_contra hlt
        exact h ⟨hoff, not_le.1 hlt⟩
      rw [← wt_autOn hV hAN, hAY] at hle
      exact hle
  calc Nat.card X * Nat.card (fixV X) = wt X := rfl
    _ = wt X' := hwtX.symm
    _ ≤ wt Y := hYmax X' (show X' ≤ X' from le_rfl)
    _ ≤ Nat.card (vSub G T) := hvY

end CFSG.CGT.PushingUpLit.BHS7
