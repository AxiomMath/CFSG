module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpTheta
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpLineAux

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

@[expose] def IsClique3 (c u v w : G) : Prop :=
  (u ≠ v ∧ IsConj c (u * v)) ∧ (u ≠ w ∧ IsConj c (u * w)) ∧ (v ≠ w ∧ IsConj c (v * w))

theorem IsLine.isClique3 {c u v w : G} (hc : c ≠ 1) (hl : IsLine c {u, v, w}) :
    IsClique3 c u v w := by
  classical
  haveI : IsKleinFour (Elem2 2) := cp_isKleinFour_elem2
  obtain ⟨hconj, hcard, ⟨φ⟩⟩ := hl
  let f : Fin 3 → G := ![u, v, w]
  have hf_range : Set.range f = ({u, v, w} : Set G) := by
    ext x
    rw [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [f]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp [f]⟩
      · exact ⟨1, by simp [f]⟩
      · exact ⟨2, by simp [f]⟩
  have hinj : Function.Injective f := by
    have hcard_range : (Set.range f).ncard = 3 := by rw [hf_range, hcard]
    refine Set.injOn_univ.mp ?_
    refine (Set.ncard_image_iff (f := f) (s := Set.univ)).mp ?_
    simp only [Set.image_univ, hcard_range, Set.ncard_univ, Nat.card_fin]
  have huv : u ≠ v := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (hinj (by simp [f, h]))
  have huw : u ≠ w := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (hinj (by simp [f, h]))
  have hvw : v ≠ w := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (hinj (by simp [f, h]))
  have humem : u ∈ ({u, v, w} : Set G) := by simp
  have hvmem : v ∈ ({u, v, w} : Set G) := by simp
  have hwmem : w ∈ ({u, v, w} : Set G) := by simp
  have hu1 : u ≠ 1 := fun h => hc (isConj_one_left.mp (h ▸ hconj u humem))
  have hv1 : v ≠ 1 := fun h => hc (isConj_one_left.mp (h ▸ hconj v hvmem))
  have hw1 : w ≠ 1 := fun h => hc (isConj_one_left.mp (h ▸ hconj w hwmem))
  let U : ↥(Subgroup.closure ({u, v, w} : Set G)) := ⟨u, Subgroup.subset_closure humem⟩
  let V : ↥(Subgroup.closure ({u, v, w} : Set G)) := ⟨v, Subgroup.subset_closure hvmem⟩
  let W : ↥(Subgroup.closure ({u, v, w} : Set G)) := ⟨w, Subgroup.subset_closure hwmem⟩
  have hUV : U ≠ V := fun h => huv (by simpa [U, V] using congrArg Subtype.val h)
  have hUW : U ≠ W := fun h => huw (by simpa [U, W] using congrArg Subtype.val h)
  have hVW : V ≠ W := fun h => hvw (by simpa [V, W] using congrArg Subtype.val h)
  have hU1 : U ≠ 1 := fun h => hu1 (by simpa [U] using congrArg Subtype.val h)
  have hV1 : V ≠ 1 := fun h => hv1 (by simpa [V] using congrArg Subtype.val h)
  have hW1 : W ≠ 1 := fun h => hw1 (by simpa [W] using congrArg Subtype.val h)
  have hφU1 : φ U ≠ 1 := fun h => hU1 (φ.injective (h.trans (map_one φ).symm))
  have hφV1 : φ V ≠ 1 := fun h => hV1 (φ.injective (h.trans (map_one φ).symm))
  have hφW1 : φ W ≠ 1 := fun h => hW1 (φ.injective (h.trans (map_one φ).symm))
  have hφUV : φ U ≠ φ V := fun h => hUV (φ.injective h)
  have hφUW : φ U ≠ φ W := fun h => hUW (φ.injective h)
  have hφVW : φ V ≠ φ W := fun h => hVW (φ.injective h)
  have hφVU : φ V ≠ φ U := fun h => hUV (φ.injective h).symm
  have hφWU : φ W ≠ φ U := fun h => hUW (φ.injective h).symm
  have hφWV : φ W ≠ φ V := fun h => hVW (φ.injective h).symm
  have hW_eq : W = U * V := by
    have h := IsKleinFour.eq_mul_of_ne_all (x := φ U) (y := φ V) (z := φ W)
      hφU1 hφV1 hφUV hφW1 hφWU hφWV
    exact φ.injective (by rw [map_mul]; exact h)
  have hV_eq : V = U * W := by
    have h := IsKleinFour.eq_mul_of_ne_all (x := φ U) (y := φ W) (z := φ V)
      hφU1 hφW1 hφUW hφV1 hφVU hφVW
    exact φ.injective (by rw [map_mul]; exact h)
  have hU_eq : U = V * W := by
    have h := IsKleinFour.eq_mul_of_ne_all (x := φ V) (y := φ W) (z := φ U)
      hφV1 hφW1 hφVW hφU1 hφUV hφUW
    exact φ.injective (by rw [map_mul]; exact h)
  have hw_uv : w = u * v := by
    have := congrArg Subtype.val hW_eq
    simpa [U, V, W, Subgroup.coe_mul] using this
  have hv_uw : v = u * w := by
    have := congrArg Subtype.val hV_eq
    simpa [U, V, W, Subgroup.coe_mul] using this
  have hu_vw : u = v * w := by
    have := congrArg Subtype.val hU_eq
    simpa [U, V, W, Subgroup.coe_mul] using this
  exact ⟨⟨huv, by rw [← hw_uv]; exact hconj w hwmem⟩,
    ⟨huw, by rw [← hv_uw]; exact hconj v hvmem⟩,
    ⟨hvw, by rw [← hu_vw]; exact hconj u humem⟩⟩

theorem theta_line (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {x y t : G} (hx : IsConj a x) (hy : y ∈ orb2A a x)
    (ht : t ∈ InvIn (Gxyz a x y)) : IsLine a' {θ x, θ y, θ (x * y)} := by
  have hy' : IsConj a y := hy.1
  have hxy' : IsConj a (x * y) := hy.2
  have hx2 : orderOf x = 2 := h.orderOf_eq_two (Or.inl hx)
  have hy2 : orderOf y = 2 := h.orderOf_eq_two (Or.inl hy')
  have hxy2 : orderOf (x * y) = 2 := h.orderOf_eq_two (Or.inl hxy')
  have htG : t ∈ Gxyz a x y := ht.1
  have htinv : orderOf t = 2 := ht.2
  have htGa : t ∈ Gx a := (mem_Gxyz.mp htG).1
  have htGx : t ∈ Gx x := (mem_Gxyz.mp htG).2.1
  have htGy : t ∈ Gx y := (mem_Gxyz.mp htG).2.2
  have htInv : t ∈ InvIn (Gx a) := ⟨htGa, htinv⟩
  have hxt_mem : x ∈ Gx t := mem_Gx.2 (mem_Gx.1 htGx).symm
  have hyt_mem : y ∈ Gx t := mem_Gx.2 (mem_Gx.1 htGy).symm
  have hxyt_mem : x * y ∈ Gx t := (Gx t).mul_mem hxt_mem hyt_mem
  have htxy : t ∈ Gx (x * y) := mem_Gx.2 (mem_Gx.1 hxyt_mem).symm
  have hxt : t ∈ InvIn (Gxy a x) := ⟨mem_Gxy.mpr ⟨htGa, htGx⟩, htinv⟩
  have hyt : t ∈ InvIn (Gxy a y) := ⟨mem_Gxy.mpr ⟨htGa, htGy⟩, htinv⟩
  have hxyt : t ∈ InvIn (Gxy a (x * y)) := ⟨mem_Gxy.mpr ⟨htGa, htxy⟩, htinv⟩
  have hψ := F.iso t htInv
  have hθxy : θ (x * y) = θ x * θ y := by
    rw [hθ.eq_app (x * y) hxy' t hxyt, hθ.eq_app x hx t hxt, hθ.eq_app y hy' t hyt]
    exact hψ.map_mul x hxt_mem y hyt_mem
  have hxθord : orderOf (θ x) = 2 := by
    rw [hθ.eq_app x hx t hxt, hψ.orderOf_eq hxt_mem, hx2]
  have hyθord : orderOf (θ y) = 2 := by
    rw [hθ.eq_app y hy' t hyt, hψ.orderOf_eq hyt_mem, hy2]
  have hcomm : θ x * θ y = θ y * θ x :=
    h'.mul_comm (Or.inl (hθ.typed h h' hα hx)) (Or.inl (hθ.typed h h' hα hy'))
      (Or.inl (hθxy ▸ hθ.typed h h' hα hxy'))
  have hne : x ≠ y := by
    intro hxy_eq
    have h1 : x * y = 1 := by rw [hxy_eq]; exact cp_mul_self_eq_one_of_orderOf_eq_two hy2
    exact cp_ne_one_of_orderOf_eq_two h.typ.orderOf_a (isConj_one_left.mp (h1 ▸ hxy'))
  have hθx_ne_θy : θ x ≠ θ y := fun heq =>
    hne (hψ.injOn x hxt_mem y hyt_mem (by
      rw [← hθ.eq_app x hx t hxt, ← hθ.eq_app y hy' t hyt]
      exact heq))
  have hres := cp_isLine_of_comm (c := a') (u := θ x) (v := θ y)
    (cp_ne_one_of_orderOf_eq_two h'.typ.orderOf_a)
    (hθ.typed h h' hα hx) (hθ.typed h h' hα hy')
    (hθxy ▸ hθ.typed h h' hα hxy')
    (cp_mul_self_eq_one_of_orderOf_eq_two hxθord)
    (cp_mul_self_eq_one_of_orderOf_eq_two hyθord) hcomm hθx_ne_θy
  simpa [hθxy] using hres

theorem theta_line_one (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {x y : G}
    (hx : x ∈ orb2A a a ∪ orb2B a z a ∪ orb4A a z a ∪ orb4B a a ∪ orb5A a a)
    (hy : y ∈ orb2A a x) : IsLine a' {θ x, θ y, θ (x * y)} := by
  have hxA : IsConj a x := by
    have hx' := hx
    simp only [Set.mem_union] at hx'
    rcases hx' with ((((h2A | h2B) | h4A) | h4B) | h5A)
    · exact h2A.1
    · exact h2B.1
    · exact h4A.1
    · exact h4B.1
    · exact h5A.1.1
  have hxΓ : x ∈ gammaSet a z a :=
    h.loc.gamma.self.eq_gamma a x (IsConj.refl a) hxA
  obtain ⟨s, hs2, hs⟩ :=
    h.loc.gamma.self.inv_one a x y (IsConj.refl a) hxA hxΓ hy hx
  exact theta_line h h' hα hθ hxA hy ⟨hs, hs2⟩

theorem theta_line_two (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {x y b : G} (hx : x ∈ orb3A a a ∪ orb6A a a)
    (hb : b ∈ orb2A a a ∩ orb2A a x) (hy : y ∈ orb2A a x)
    (hyb : y ∈ orb2A a b ∪ orb2B a z b ∪ orb3A a b ∪ orb4B a b ∪ orb6A a b) :
    IsLine a' {θ x, θ y, θ (x * y)} := by
  have hxA : IsConj a x := by
    have hx' := hx
    simp only [Set.mem_union] at hx'
    rcases hx' with h3A | h6A
    · exact h3A.1
    · exact h6A.1
  have hxΓ : x ∈ gammaSet a z a :=
    h.loc.gamma.self.eq_gamma a x (IsConj.refl a) hxA
  obtain ⟨s, hs2, hs⟩ :=
    h.loc.gamma.self.inv_two_i a x y b (IsConj.refl a) hxA hxΓ hy hx hb hyb
  exact theta_line h h' hα hθ hxA hy ⟨hs, hs2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
