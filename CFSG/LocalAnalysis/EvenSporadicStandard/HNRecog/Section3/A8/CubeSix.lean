module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Fig8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_two_four_of_cube (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hA8 : Vert A8Shapes a z) {E : Subgroup G} (hE : IsElemTwo 3 E)
    (h6 : Nat.card {x : G // x ∈ E ∧ IsConj a x} = 6) {x y : G} (hxE : x ∈ E) (hyE : y ∈ E)
    (hx : IsConj a x) (hy : IsConj a y) (hxy : IsConj a (x * y)) :
    ∃ t ∈ derivedOf (Gxy x y), t ^ 2 = 1 ∧ t ≠ 1 ∧ E = Subgroup.closure ({x, y, t} : Set G) ∧
      ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy x y)), ∀ s : alternatingGroup (Fin 8),
        (φ s : G) = t → (s : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  classical
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have ha_ne : a ≠ 1 := by
    intro h1
    have ho := h.orderOf_a
    rw [h1, orderOf_one] at ho
    norm_num at ho
  have hx2 : x ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    rw [← hc, conj_pow, ha2, mul_one, mul_inv_cancel]
  have hy_sq : y ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    rw [← hc, conj_pow, ha2, mul_one, mul_inv_cancel]
  have hxy_ne : x ≠ y := by
    intro h1
    have hone : x * y = 1 := by rw [h1, ← pow_two, hy_sq]
    exact ha_ne (isConj_one_left.mp (hone ▸ hxy))
  haveI hEcomm : IsMulCommutative ↥E := hE.1.1
  have hxy_comm : x * y = y * x := by
    have := mul_comm' (⟨x, hxE⟩ : ↥E) (⟨y, hyE⟩ : ↥E)
    exact congrArg Subtype.val this
  have hxz : IsF5Type x z := isF5Type_of_isConj h hx (IsConj.refl z)
  have hy_orb : y ∈ orb2A x x := ⟨hx.symm.trans hy, hx.symm.trans hxy⟩
  obtain ⟨t, ht_mem, ht2, ht1, hEeq⟩ :=
    exists_t_of_cube (hF3 x z hx (IsConj.refl z)) hE hxE hyE hxy_ne hy_orb
  have htE : t ∈ E := by
    rw [hEeq]
    exact Subgroup.subset_closure (by simp)
  have hxt_comm : x * t = t * x := by
    have := mul_comm' (⟨x, hxE⟩ : ↥E) (⟨t, htE⟩ : ↥E)
    exact congrArg Subtype.val this
  have hyt_comm : y * t = t * y := by
    have := mul_comm' (⟨y, hyE⟩ : ↥E) (⟨t, htE⟩ : ↥E)
    exact congrArg Subtype.val this
  refine ⟨t, ht_mem, ht2, ht1, hEeq, ?_⟩
  intro φ s hs
  have hs2 : s ^ 2 = 1 := by
    apply φ.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hs, ht2]
  have hs1 : s ≠ 1 := by
    intro h1
    exact ht1 (by rw [← hs, h1, map_one, Subgroup.coe_one])
  rcases cycleType_eq_of_sq_eq_one hs2 hs1 with h22 | h24
  ·
    exfalso
    have hfig := fig8a_of_fusion2 hI hxz (hF1.of_isConj hx (IsConj.refl z))
      (hF2.of_isConj hx (IsConj.refl z)) (hA8 x z hx (IsConj.refl z)) y hy_orb φ s h22
    obtain ⟨_, hxtZ, hytZ, hxytZ⟩ := hfig
    rw [hs] at hxtZ hytZ hxytZ
    have hnot_xt : ¬ IsConj a (x * t) := fun hc => not_isConj_of_isF5Type hI h (hc.trans hxtZ.symm)
    have hnot_yt : ¬ IsConj a (y * t) := fun hc => not_isConj_of_isF5Type hI h (hc.trans hytZ.symm)
    have hnot_xyt : ¬ IsConj a (x * y * t) :=
      fun hc => not_isConj_of_isF5Type hI h (hc.trans hxytZ.symm)
    have hsub : {e : G | e ∈ E ∧ IsConj a e} ⊆ ({x, y, x*y, t} : Set G) := by
      intro e he
      obtain ⟨heE, heA⟩ := he
      have heE' : e ∈ Subgroup.closure ({x, y, t} : Set G) := by
        rwa [hEeq] at heE
      rcases eq_of_mem_closure_three hx2 hy_sq ht2 hxy_comm hxt_comm hyt_comm heE' with
        h1 | hxe | hye | hxye | hte | hxte | hyte | hxyte
      · exact absurd (isConj_one_left.mp (h1 ▸ heA)) ha_ne
      · rw [hxe]; simp
      · rw [hye]; simp
      · rw [hxye]; simp
      · rw [hte]; simp
      · exact absurd (hxte ▸ heA) hnot_xt
      · exact absurd (hyte ▸ heA) hnot_yt
      · exact absurd (hxyte ▸ heA) hnot_xyt
    have hfin : ({x, y, x*y, t} : Set G).Finite := by
      apply Set.Finite.insert x
      apply Set.Finite.insert y
      apply Set.Finite.insert (x*y)
      exact Set.finite_singleton t
    have hle : ({e : G | e ∈ E ∧ IsConj a e} : Set G).ncard ≤ 4 := by
      have hle1 := Set.ncard_le_ncard hsub hfin
      have h4 : ({x, y, x*y, t} : Set G).ncard ≤ 4 := by
        have hb1 : ({x, y, x*y, t} : Set G).ncard ≤ ({y, x*y, t} : Set G).ncard + 1 :=
          Set.ncard_insert_le x ({y, x*y, t} : Set G)
        have hb2 : ({y, x*y, t} : Set G).ncard ≤ ({x*y, t} : Set G).ncard + 1 :=
          Set.ncard_insert_le y ({x*y, t} : Set G)
        have hb3 : ({x*y, t} : Set G).ncard ≤ ({t} : Set G).ncard + 1 :=
          Set.ncard_insert_le (x*y) ({t} : Set G)
        rw [Set.ncard_singleton] at hb3
        omega
      exact hle1.trans h4
    have h6' : ({e : G | e ∈ E ∧ IsConj a e} : Set G).ncard = 6 := by
      rw [← Nat.card_coe_set_eq]
      exact h6
    omega
  · exact h24

end CFSG.EvenSporadicStandard.HNRecog.Section3
