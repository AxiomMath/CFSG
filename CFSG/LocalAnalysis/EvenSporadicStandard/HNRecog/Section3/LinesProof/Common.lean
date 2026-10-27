module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Coset
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.A8Pair
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

theorem lines_common (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hF3 : Vert Fusion3Facts a z)
    (hPic : Vert A8Pictures a z) {x y t : G} (hx : IsConj a x) (hy : IsConj a y)
    (hxy : IsConj a (x * y)) (htxy : t ≠ x * y) (ht : t ∈ orb2A a x ∩ orb2A a y) :
    (orb2A a x ∩ orb2A a y ∩ orb2A a t).Nonempty := by
  have hx2 : x ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hy]; exact pow_orderOf_eq_one y
  have hxy2 : (x * y) ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hxy]; exact pow_orderOf_eq_one (x * y)
  have hcomm : x * y = y * x := comm_of_sq_mul hx2 hy2 hxy2
  have hyx : y ∈ orb2A x x := ⟨hx.symm.trans hy, hx.symm.trans hxy⟩
  have hF3x : Fusion3Facts x z := hF3 x z hx (IsConj.refl z)
  have hPicx : A8Pictures x z := hPic x z hx (IsConj.refl z)
  have hX : IsShapeTwoTwoTimesA8 ↥(Gxy x y) := hF3x.shape_2A y hyx
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hX
  obtain ⟨htA, hxtA⟩ := ht.1
  obtain ⟨-, hytA⟩ := ht.2
  have ht2 : t ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h htA]; exact pow_orderOf_eq_one t
  have hxt2 : (x * t) ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hxtA]; exact pow_orderOf_eq_one (x * t)
  have hyt2 : (y * t) ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hytA]; exact pow_orderOf_eq_one (y * t)
  have hxt_comm : x * t = t * x := comm_of_sq_mul hx2 ht2 hxt2
  have hyt_comm : y * t = t * y := comm_of_sq_mul hy2 ht2 hyt2
  have htG : t ∈ Gxy x y := mem_Gxy.mpr ⟨mem_Gx.mpr hxt_comm, mem_Gx.mpr hyt_comm⟩
  obtain ⟨s, hs, hs2, ht_eq, hsB⟩ :=
    lines_AAA h hnc hx hyx hX hPicx htG htA hxtA hytA htxy
  have hsG : s ∈ Gxy x y := derivedOf_le _ hs
  have hsx : x * s = s * x := mem_Gx.mp (mem_Gxy.mp hsG).1
  have hsy : y * s = s * y := mem_Gx.mp (mem_Gxy.mp hsG).2
  have hsd : (x * y) * s = s * (x * y) := by
    rw [mul_assoc, hsy, ← mul_assoc, hsx, mul_assoc]
  have hσ : (φ.symm ⟨s, hs⟩ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} :=
    lines_cycleType_of_isConj_z h hnc hx hyx hPicx φ hs hs2 hsB
  obtain ⟨σ', hσ', hσσ'⟩ := linesA8_exists_partner hσ
  let u : G := (φ σ' : G)
  have hu_mem : u ∈ derivedOf (Gxy x y) := (φ σ').2
  have huG : u ∈ Gxy x y := derivedOf_le _ hu_mem
  have hux : x * u = u * x := mem_Gx.mp (mem_Gxy.mp huG).1
  have huy : y * u = u * y := mem_Gx.mp (mem_Gxy.mp huG).2
  let t₁ : G := x * y * u
  have hfig8b := hPicx.fig8b y hyx φ σ' hσ'
  have hxu : IsConj x (x * u) := hfig8b.2.1
  have hyu : IsConj x (y * u) := hfig8b.2.2.1
  have hxyu : IsConj x (x * y * u) := hfig8b.2.2.2
  have ht₁A : IsConj a t₁ := hx.trans hxyu
  have hx_t₁ : x * t₁ = y * u := by
    change x * (x * y * u) = y * u
    rw [mul_assoc x y u, ← mul_assoc x x (y * u), ← pow_two, hx2, one_mul]
  have hy_t₁ : y * t₁ = x * u := by
    change y * (x * y * u) = x * u
    calc y * (x * y * u) = (y * x) * (y * u) := by group
      _ = (x * y) * (y * u) := by rw [← hcomm]
      _ = x * (y * (y * u)) := by group
      _ = x * u := by rw [← mul_assoc y y u, ← pow_two, hy2, one_mul]
  have hxt₁A : IsConj a (x * t₁) := by rw [hx_t₁]; exact hx.trans hyu
  have hyt₁A : IsConj a (y * t₁) := by rw [hy_t₁]; exact hx.trans hxu
  have hφσ : (φ (φ.symm ⟨s, hs⟩) : G) = s := by rw [MulEquiv.apply_symm_apply]
  have hφσσ' : (φ (φ.symm ⟨s, hs⟩ * σ') : G) = s * u := by
    rw [map_mul]
    change (φ (φ.symm ⟨s, hs⟩) : G) * (φ σ' : G) = s * u
    rw [hφσ]
  have hfig8a := hPicx.fig8a y hyx φ (φ.symm ⟨s, hs⟩ * σ') hσσ'
  have hsu : IsConj x (s * u) := by rw [← hφσσ']; exact hfig8a.1
  have htt₁ : t * t₁ = s * u := by
    rw [ht_eq]
    change (x * y * s) * (x * y * u) = s * u
    calc (x * y * s) * (x * y * u) = s * (x * y) * (x * y) * u := by rw [hsd]; group
      _ = s * ((x * y) * (x * y)) * u := by group
      _ = s * u := by rw [← pow_two, hxy2, mul_one]
  have htt₁A : IsConj a (t * t₁) := by rw [htt₁]; exact hx.trans hsu
  exact ⟨t₁, ⟨⟨⟨ht₁A, hxt₁A⟩, ⟨ht₁A, hyt₁A⟩⟩, ⟨ht₁A, htt₁A⟩⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
