module

public import CFSG.LargeExtraspecial.S12DWCount
public import CFSG.Fischer.Classification.Recognition.R3Order
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12Seven
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Fischer.Classification

namespace S12Insp4

theorem not_three_pow_six_dvd_card_O {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 4) : ¬ 3 ^ 6 ∣ Nat.card S.O := by
  intro h
  have hprod := S12DW.card_orthogonalGroup_mul_ncard_eq S.q_nondegenerate (m := 4)
    (by rw [S.finrank_Qt_eq_two_mul_width, hw])
  have hdvd : Nat.card S.O ∣ 2 ^ (4 ^ 2) * ∏ j ∈ Finset.Icc 1 4, (2 ^ (2 * j) - 1) :=
    ⟨_, hprod.symm⟩
  have hnot : ¬ 3 ^ 6 ∣ 2 ^ (4 ^ 2) * ∏ j ∈ Finset.Icc 1 4, (2 ^ (2 * j) - 1) := by decide
  exact hnot (h.trans hdvd)

theorem card_center_reflGroup_le_two {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) (hm : 4 ≤ m) :
    Nat.card (Subgroup.center (F3.reflGroup f)) ≤ 2 := by
  let ι : Subgroup.center (F3.reflGroup f) → ({1, -1} : Set (GL (Fin m) (ZMod 3))) :=
    fun z => ⟨((z : F3.reflGroup f) : GL (Fin m) (ZMod 3)), by
      rcases F3.coe_eq_of_mem_center hf hm z.2 with h | h
      · exact Or.inl h
      · exact Or.inr h⟩
  have hι : Function.Injective ι := fun z₁ z₂ h =>
    Subtype.ext (Subtype.ext
      (congrArg (fun w : ({1, -1} : Set (GL (Fin m) (ZMod 3))) => (w : GL (Fin m) (ZMod 3))) h))
  refine (Nat.card_le_card_of_injective ι hι).trans ?_
  rw [Nat.card_coe_set_eq]
  exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

end S12Insp4

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_reflGroup_ge_eight (hw : S.width = 4) {g : G} {m : ℕ} (hm : 8 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) : False := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, -⟩ := (fischerCentralQuotientModel_iff _).1 hmod
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (F3.reflGroup f))
  have hZ := S12Insp4.card_center_reflGroup_le_two hf (by omega)
  have hZ0 : 0 < Nat.card (Subgroup.center (F3.reflGroup f)) := Nat.card_pos
  have h3 := Recognition.R3.pow_threeExp_dvd m f hf
  have hexp : 6 ≤ Recognition.R3.threeExp m := by
    unfold Recognition.R3.threeExp
    split_ifs <;> omega
  have h36 : 3 ^ 6 ∣ Nat.card (S.Xbar12 g) * Nat.card (Subgroup.center (F3.reflGroup f)) := by
    rw [Nat.card_congr ψ.toEquiv, ← h1]
    exact (pow_dvd_pow 3 hexp).trans h3
  have hcop : Nat.Coprime (3 ^ 6) (Nat.card (Subgroup.center (F3.reflGroup f))) := by
    refine Nat.Coprime.pow_left _ ?_
    interval_cases Nat.card (Subgroup.center (F3.reflGroup f)) <;> decide
  exact S12Insp4.not_three_pow_six_dvd_card_O S hw
    ((hcop.dvd_of_dvd_mul_right h36).trans (Subgroup.card_subgroup_dvd_card _))

end Setting

end CFSG.LargeExtraspecial
