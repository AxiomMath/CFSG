module

public import CFSG.GH74.SectionalRank
public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat
public import CFSG.Quasithin.H13.L32NStatements
public import CFSG.Quasithin.H13.L32NNotation
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.QTGen4

open CFSG.GH74 CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open

theorem finrank_hatModel_le_four {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    {U : Subgroup G} (D : HatModelU U) : Module.finrank (ZMod 2) D.V ≤ 4 := by
  classical
  have hπ1 : D.π 1 = 0 := by
    have h := D.π_mul 1 U.one_mem 1 U.one_mem
    rw [mul_one] at h
    have h' : D.π 1 + D.π 1 = D.π 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  let φ : ↥U →* Multiplicative D.V :=
    { toFun := fun u => Multiplicative.ofAdd (D.π (u : G))
      map_one' := by
        show Multiplicative.ofAdd (D.π ((1 : ↥U) : G)) = 1
        rw [Subgroup.coe_one, hπ1]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (D.π ((a * b : ↥U) : G)) = _
        rw [Subgroup.coe_mul, D.π_mul _ a.2 _ b.2, ofAdd_add] }
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨u, hu, hπ⟩ := D.π_surj (Multiplicative.toAdd y)
    exact ⟨⟨u, hu⟩, by simp [φ, hπ]⟩
  have hU : SectionalTwoRankLE ↥U 4 := SectionalTwoRankLE.subgroup U hG
  have hY : SectionalTwoRankLE (Multiplicative D.V) 4 :=
    SectionalTwoRankLE.of_surjective φ hsurj hU
  have hE : IsElemAbelian 2 (⊤ : Subgroup (Multiplicative D.V)) := by
    refine ⟨inferInstance, fun x _ => ?_⟩
    have hv : ∀ v : D.V, v + v = 0 := fun v => by
      rw [← two_smul (ZMod 2) v]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_smul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact hv _
  have hc := hY.card_le_of_elementary ⊤ hE
  have hFin : Fintype D.V := Fintype.ofFinite _
  rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hc

theorem lemma14324Big_gen4 :
    ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (T L V : Subgroup G), Hyp14310One G T L V →
      fsuV1 T V < centerOf (fsuU T V) →
      ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
      ∀ D : HatModelU (fsuU T V), 6 ≤ Module.finrank (ZMod 2) D.V →
        G112Concl6 (D.img (l32nH T V)) := by
  intro G _ _ hG T L V _ _ V₂ g _ _ _ D h6
  have := finrank_hatModel_le_four hG D
  omega

end CFSG.GH74.QTGen4
