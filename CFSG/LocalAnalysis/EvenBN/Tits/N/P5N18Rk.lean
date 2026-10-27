module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18Rank
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Elem
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N CFSG.LocalAnalysis.EvenBN.Tits.N.P4

section Rk

variable {G : Type*} [Group G] [Finite G]

theorem card_commImg_le_eight {V N U11 : Subgroup G} {f : G} (hV : IsElemAbelian 2 V)
    (hVcard : Nat.card V = 2 ^ 10) (hVN : Nat.card ↥(V ⊓ N) = 2 ^ 9) (hU11 : Nat.card U11 = 4)
    (hf : f ∈ normalizer (V : Set G)) (hκ : ∀ x ∈ V ⊓ N, x * f * x⁻¹ * f⁻¹ ∈ U11) :
    Nat.card (commImg (actFun V f)) ≤ 8 := by
  classical
  have hc : ∀ a b : ↥V, a * b = b * a := fun a b => Subtype.ext (hV.comm a.2 b.2)
  have h2 : ∀ w : ↥V, w * w = 1 := fun w => Subtype.ext (hV.mul_self_eq_one w.2)
  rw [commImg_eq_range_twistHom hc h2 (actFun V f)]
  set φ := twistHom hc (actFun V f) with hφ
  set A : Subgroup ↥V := N.subgroupOf V with hA
  have hAcard : Nat.card A = 2 ^ 9 := by
    rw [← card_inf_eq_card_subgroupOf N V, inf_comm]
    exact hVN
  have hAindex : A.index = 2 := by
    have := Subgroup.card_mul_index A
    rw [hAcard, hVcard] at this
    omega
  have hφA : ∀ a ∈ A, ((φ a : ↥V) : G) ∈ U11 := by
    intro a ha
    have haN : (a : G) ∈ V ⊓ N := Subgroup.mem_inf.2 ⟨a.2, ha⟩
    have h1 := hκ _ haN
    have haa : (a : G) * a = 1 := hV.mul_self_eq_one a.2
    have hainv : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rw [hainv] at h1
    have e : ((φ a : ↥V) : G) = (a : G) * f * (a : G) * f⁻¹ := by
      rw [hφ, twistHom_apply]
      show (a : G) * ((actFun V f a : ↥V) : G) = _
      rw [actFun_apply_coe V hf]
      group
    rw [e]
    exact h1
  have hM : A.map φ ≤ U11.subgroupOf V := by
    rintro _ ⟨a, ha, rfl⟩
    exact hφA a ha
  have hUcard : Nat.card (U11.subgroupOf V) ≤ 4 := by
    rw [← hU11]
    exact Nat.card_le_card_of_injective (fun x => ⟨(x.1 : G), Subgroup.mem_subgroupOf.1 x.2⟩)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  have hMcard : Nat.card (A.map φ) ≤ 4 :=
    (Subgroup.card_le_of_le hM).trans hUcard
  have hrel : (A.map φ).relIndex φ.range ∣ 2 := by
    have h := Subgroup.relIndex_map_map φ A ⊤
    rw [← MonoidHom.range_eq_map, top_sup_eq, Subgroup.relIndex_top_right] at h
    rw [h, ← hAindex]
    exact Subgroup.index_dvd_of_le le_sup_left
  have hMR : A.map φ ≤ φ.range := Subgroup.map_le_range φ A
  have hmul := Subgroup.relIndex_mul_card (A.map φ) φ.range
  rw [inf_eq_left.2 hMR] at hmul
  have hrel2 : (A.map φ).relIndex φ.range ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
  rw [← hmul]
  calc (A.map φ).relIndex φ.range * Nat.card (A.map φ) ≤ 2 * 4 := Nat.mul_le_mul hrel2 hMcard
    _ = 8 := by norm_num

theorem card_fixSub_le_four {V Z : Subgroup G} {x : G} (hx : x ∈ normalizer (V : Set G))
    (hZ : Nat.card Z ≤ 4) (hfix : ∀ w ∈ V, x * w = w * x → w ∈ Z) :
    Nat.card (fixSub (actFun V x)) ≤ 4 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun w : fixSub (actFun V x) => (⟨(w.1 : G), hfix w.1.1 w.1.2 ?_⟩ : Z)) ?_) hZ
  · have h1 : ((actFun V x w.1 : ↥V) : G) = (w.1 : G) := congrArg Subtype.val w.2
    rw [actFun_apply_coe V hx] at h1
    calc x * (w.1 : G) = (x * (w.1 : G) * x⁻¹) * x := by group
      _ = (w.1 : G) * x := by rw [h1]
  · intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

end Rk

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
