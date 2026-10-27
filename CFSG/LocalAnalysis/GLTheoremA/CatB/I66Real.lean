module

public import CFSG.RankThree.Native.ONThreeFusion
public import CFSG.Sporadic.Recognition.McLASCert
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabJ3Shape

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Subgroup

theorem i66_real_M22 :
    ∀ t : TauCeti.SporadicName.M22.Group, orderOf t = 3 → IsConj t t⁻¹ := by
  intro t ht
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  exact CFSG.RankThree.PartTwo.KFacts.KP4.m22_isConj_of_orderOf ⟨e.symm⟩ ht
    (by rw [orderOf_inv, ht])

theorem i66_card_centralizer_inv {G : Type} [Group G] (y : G) :
    Nat.card (centralizer ({y⁻¹} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  have hset : centralizer ({y⁻¹} : Set G) = centralizer ({y} : Set G) := by
    ext g
    simp only [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  rw [hset]

theorem i66_isConj_inv_of_two_classes {G : Type} [Group G] {u x₁ x₂ : G}
    (h : IsConj u x₁ ∨ IsConj u x₂) (hinv : IsConj u⁻¹ x₁ ∨ IsConj u⁻¹ x₂)
    (hne : Nat.card (centralizer ({x₁} : Set G)) ≠ Nat.card (centralizer ({x₂} : Set G))) :
    IsConj u u⁻¹ := by
  have hcent := i66_card_centralizer_inv u
  rcases h with h1 | h1 <;> rcases hinv with h2 | h2
  · exact h1.trans h2.symm
  · exact absurd (((Subgroup.card_centralizer_of_isConj h2).symm.trans hcent).trans
      (Subgroup.card_centralizer_of_isConj h1)).symm hne
  · exact absurd (((Subgroup.card_centralizer_of_isConj h2).symm.trans hcent).trans
      (Subgroup.card_centralizer_of_isConj h1)) hne
  · exact h1.trans h2.symm

theorem i66_real_ON :
    ∀ t : TauCeti.SporadicName.ONan.Group, orderOf t = 3 → IsConj t t⁻¹ := by
  intro t ht
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have ht' : orderOf (e.symm t) = 3 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨k, hk⟩ := CFSG.RankThree.Native.onThree_fusion (x := e.symm t)
    (y := (e.symm t)⁻¹) ht' (by rw [orderOf_inv, ht'])
  refine isConj_iff.mpr ⟨e k, ?_⟩
  have h2 := congrArg e hk
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h2

theorem i66_real_McL :
    ∀ t : TauCeti.SporadicName.McL.Group, orderOf t = 3 → IsConj t t⁻¹ := by
  intro t ht
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  obtain ⟨x₁, x₂, -, -, c₁, c₂, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mcl_two_classes_order_three_of_certificate
  have ht' : orderOf (e.symm t) = 3 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hinv' : orderOf (e.symm t)⁻¹ = 3 := by rw [orderOf_inv, ht']
  have hne : Nat.card (centralizer ({x₁} : Set _)) ≠ Nat.card (centralizer ({x₂} : Set _)) := by
    rw [c₁, c₂]
    norm_num
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (i66_isConj_inv_of_two_classes (hall _ ht') (hall _ hinv') hne)
  refine isConj_iff.mpr ⟨e c, ?_⟩
  have h2 := congrArg e hc
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h2

theorem i66_j3_real_XA :
    ∃ g ∈ CFSG.Sporadic.Schreier.j3P,
      g * CFSG.RankThree.PartTwo.KFacts.K426.j3tXA * g⁻¹ =
        (CFSG.RankThree.PartTwo.KFacts.K426.j3tXA)⁻¹ := by
  refine ⟨CFSG.RankThree.PartTwo.KFacts.K426.j3tGPerm,
    CFSG.RankThree.PartTwo.KFacts.K426.j3tGPerm_mem, ?_⟩
  have h3 : CFSG.RankThree.PartTwo.KFacts.K426.j3tXA ^ 3 = 1 :=
    (CFSG.RankThree.PartTwo.KFacts.K426.j3tReps_spec (c := 0) (by norm_num)).2
  rw [CFSG.HardMathSupport.Dickson.I271.tabJ3_g_conj]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)

theorem i66_j3_real_R
    (hB : ∃ g ∈ CFSG.Sporadic.Schreier.j3P,
      g * CFSG.RankThree.PartTwo.KFacts.K426.j3tXB * g⁻¹ =
        (CFSG.RankThree.PartTwo.KFacts.K426.j3tXB)⁻¹)
    (x : Equiv.Perm (Fin 6156)) (hx : x ∈ CFSG.Sporadic.Schreier.j3P) (hxo : orderOf x = 3) :
    ∃ h ∈ CFSG.Sporadic.Schreier.j3P, h * x * h⁻¹ = x⁻¹ := by
  obtain ⟨k, hk, c, hc, e, -, rfl⟩ :=
    CFSG.RankThree.PartTwo.KFacts.K426.j3t_fusion hx hxo
  have hg : ∃ g ∈ CFSG.Sporadic.Schreier.j3P, g * c * g⁻¹ = c⁻¹ := by
    rcases hc with rfl | rfl
    · exact i66_j3_real_XA
    · exact hB
  obtain ⟨g, hgR, hgc⟩ := hg
  refine ⟨k * g * k⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hgR) (Subgroup.inv_mem _ hk), ?_⟩
  have hpow : g * c ^ e * g⁻¹ = (c ^ e)⁻¹ := by rw [← conj_pow, hgc, inv_pow]
  calc k * g * k⁻¹ * (k * c ^ e * k⁻¹) * (k * g * k⁻¹)⁻¹
      = k * (g * c ^ e * g⁻¹) * k⁻¹ := by group
    _ = k * (c ^ e)⁻¹ * k⁻¹ := by rw [hpow]
    _ = (k * c ^ e * k⁻¹)⁻¹ := by group

theorem i66_j3_isConj_subgroup
    (hB : ∃ g ∈ CFSG.Sporadic.Schreier.j3P,
      g * CFSG.RankThree.PartTwo.KFacts.K426.j3tXB * g⁻¹ =
        (CFSG.RankThree.PartTwo.KFacts.K426.j3tXB)⁻¹)
    (x : ↥CFSG.Sporadic.Schreier.j3P) (hx : orderOf x = 3) : IsConj x x⁻¹ := by
  have hxo : orderOf (x : Equiv.Perm (Fin 6156)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  obtain ⟨h, hh, hconj⟩ := i66_j3_real_R hB (x : Equiv.Perm (Fin 6156)) x.2 hxo
  refine isConj_iff.mpr ⟨⟨h, hh⟩, Subtype.ext ?_⟩
  simpa using hconj

theorem i66_real_J3
    (hB : ∃ g ∈ CFSG.Sporadic.Schreier.j3P,
      g * CFSG.RankThree.PartTwo.KFacts.K426.j3tXB * g⁻¹ =
        (CFSG.RankThree.PartTwo.KFacts.K426.j3tXB)⁻¹) :
    ∀ t : TauCeti.SporadicName.J3.Group, orderOf t = 3 → IsConj t t⁻¹ := by
  intro t ht
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  let φ : TauCeti.SporadicName.J3.Group ≃* ↥CFSG.Sporadic.Schreier.j3P :=
    ψ.symm.trans CFSG.Sporadic.Schreier.j3PermEquiv
  have hφ : orderOf (φ t) = 3 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨c, hc⟩ := isConj_iff.mp (i66_j3_isConj_subgroup hB (φ t) hφ)
  refine isConj_iff.mpr ⟨φ.symm c, ?_⟩
  have h2 := congrArg φ.symm hc
  simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using h2

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
