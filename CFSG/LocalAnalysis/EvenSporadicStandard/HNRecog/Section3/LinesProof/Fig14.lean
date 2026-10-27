module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Coset
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

private theorem lines14_comm_sq {u v w : G} (hu : v * u = u * v) (hw : v * w = w * v) :
    v * (u * w) ^ 2 = (u * w) ^ 2 * v := by
  have hcomm : Commute v (u * w) := by
    show v * (u * w) = (u * w) * v
    calc v * (u * w) = (v * u) * w := by group
      _ = (u * v) * w := by rw [hu]
      _ = u * (v * w) := by group
      _ = u * (w * v) := by rw [hw]
      _ = (u * w) * v := by group
  exact (hcomm.pow_right 2).eq

private theorem lines14_comm_inv_left {u v : G} (h : u * v = v * u) : u⁻¹ * v = v * u⁻¹ := by
  have h' : v * u⁻¹ = u⁻¹ * v := by
    calc v * u⁻¹ = u⁻¹ * (u * v) * u⁻¹ := by group
      _ = u⁻¹ * (v * u) * u⁻¹ := by rw [h]
      _ = u⁻¹ * v := by group
  exact h'.symm

theorem lines_fig14_dihedral (h : IsF5Type a z) {x : G} (hx : x ∈ orb4A a z a) :
    IsConj z ((a * x) ^ 2) ∧ a * (a * x) ^ 2 = (a * x) ^ 2 * a ∧
      x * (a * x) ^ 2 = (a * x) ^ 2 * x ∧ (a * x) ^ 2 * x = a * x * a⁻¹ ∧
      a * (a * x) ^ 2 = x * a * x⁻¹ := by
  obtain ⟨hxA, hzzB⟩ := hx
  have hord : orderOf (a * x) = 4 := tableV_orderOf_orb4A h ⟨hxA, hzzB⟩
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hx2 : x ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hxA]; exact pow_orderOf_eq_one x
  have hasq : a * a = 1 := by simpa [pow_two] using ha2
  have hxsq : x * x = 1 := by simpa [pow_two] using hx2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right hasq
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxsq
  obtain ⟨haz, hxz, -, -⟩ := tableV_dihedral ha2 hx2 hxA (m := 2) (by rw [hord])
  have hzx : (a * x) ^ 2 * x = a * x * a := by
    rw [pow_two]
    calc (a * x) * (a * x) * x = (a * x) * a * (x * x) := by group
      _ = (a * x) * a := by rw [hxsq, mul_one]
  have haz' : a * (a * x) ^ 2 = x * a * x := by
    rw [pow_two]
    calc a * ((a * x) * (a * x)) = (a * a) * (x * a * x) := by group
      _ = x * a * x := by rw [hasq, one_mul]
  exact ⟨hzzB, haz, hxz, by rw [hai]; exact hzx, by rw [hxi]; exact haz'⟩

theorem lines_fig14_a (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hF3 : Vert Fusion3Facts a z)
    (hPic : Vert A8Pictures a z) {x : G} (hx : x ∈ orb4A a z a) {c : G}
    (hc : c ∈ orb2A a a ∩ orb2A a x) :
    IsConj a ((a * x) ^ 2 * c) ∧ IsConj a ((a * x) ^ 2 * x) ∧ IsConj a ((a * x) ^ 2 * x * c) ∧
      IsConj a (a * (a * x) ^ 2) ∧ IsConj a (a * c * (a * x) ^ 2) := by
  obtain ⟨hca, hcac⟩ := hc.1
  obtain ⟨-, hcxc⟩ := hc.2
  obtain ⟨hzzB, haz, hxz, hzzx, hazz⟩ := lines_fig14_dihedral h hx
  have hxA : IsConj a x := hx.1
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hx2 : x ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hxA]; exact pow_orderOf_eq_one x
  have hc2 : c ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hca]; exact pow_orderOf_eq_one c
  have hca2 : (a * c) ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hcac]; exact pow_orderOf_eq_one _
  have hxc2 : (x * c) ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hcxc]; exact pow_orderOf_eq_one _
  have hac : a * c = c * a := comm_of_sq_mul ha2 hc2 hca2
  have hxc : x * c = c * x := comm_of_sq_mul hx2 hc2 hxc2
  have hczz : c * (a * x) ^ 2 = (a * x) ^ 2 * c := lines14_comm_sq hac.symm hxc.symm
  have hwzz : (a * x) ^ 2 ∈ Gxy a c :=
    mem_Gxy.mpr ⟨mem_Gx.mpr haz, mem_Gx.mpr hczz⟩
  have hXac : IsShapeTwoTwoTimesA8 ↥(Gxy a c) := hF3.self.shape_2A c hc.1
  have hzxc_eq : (a * x) ^ 2 * x * c = a * (x * c) * a⁻¹ := by
    rw [hzzx]
    calc (a * x * a⁻¹) * c = a * x * (a⁻¹ * c) := by group
      _ = a * x * (c * a⁻¹) := by rw [lines14_comm_inv_left hac]
      _ = a * (x * c) * a⁻¹ := by group
  have hpbw_eq' : x * (a * c) * x⁻¹ = a * c * (a * x) ^ 2 := by
    have hcxinv : c * x⁻¹ = x⁻¹ * c := (lines14_comm_inv_left hxc).symm
    calc x * (a * c) * x⁻¹ = x * a * (c * x⁻¹) := by group
      _ = x * a * (x⁻¹ * c) := by rw [hcxinv]
      _ = (x * a * x⁻¹) * c := by group
      _ = (a * (a * x) ^ 2) * c := by rw [← hazz]
      _ = a * ((a * x) ^ 2 * c) := by rw [mul_assoc]
      _ = a * (c * (a * x) ^ 2) := by rw [← hczz]
      _ = a * c * (a * x) ^ 2 := by rw [mul_assoc]
  have hpbw_eq : a * c * (a * x) ^ 2 = x * (a * c) * x⁻¹ := hpbw_eq'.symm
  have hzzxA : IsConj a ((a * x) ^ 2 * x) := by
    rw [hzzx]
    exact hxA.trans (isConj_iff.mpr ⟨a, rfl⟩)
  have hazzA : IsConj a (a * (a * x) ^ 2) := by
    rw [hazz]
    exact isConj_iff.mpr ⟨x, rfl⟩
  have hpbwA : IsConj a (a * c * (a * x) ^ 2) := by
    rw [hpbw_eq]
    exact hcac.trans (isConj_iff.mpr ⟨x, rfl⟩)
  have hczzA : IsConj a (c * (a * x) ^ 2) :=
    lines_coset h hnc (IsConj.refl a) hc.1 hXac hPic.self hwzz hzzB hazzA hpbwA
  refine ⟨?_, hzzxA, ?_, hazzA, hpbwA⟩
  · rw [← hczz]; exact hczzA
  · rw [hzxc_eq]; exact hcxc.trans (isConj_iff.mpr ⟨a, rfl⟩)

theorem lines_fig14_b (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hF3 : Vert Fusion3Facts a z)
    (hPic : Vert A8Pictures a z) {x : G} (hx : x ∈ orb4A a z a) {t : G}
    (ht : t ∈ orb2B a z a ∩ orb2A a x) :
    IsConj a ((a * x) ^ 2 * t) ∧ IsConj a ((a * x) ^ 2 * x) ∧ IsConj a (t * (a * x) ^ 2 * x) ∧
      IsConj a (a * (a * x) ^ 2) ∧ IsConj z (t * a * (a * x) ^ 2) := by
  obtain ⟨hta, htza⟩ := ht.1
  obtain ⟨-, htxa⟩ := ht.2
  obtain ⟨hzzB, haz, hxz, hzzx, hazz⟩ := lines_fig14_dihedral h hx
  have hxA : IsConj a x := hx.1
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hx2 : x ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hxA]; exact pow_orderOf_eq_one x
  have ht2 : t ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hta]; exact pow_orderOf_eq_one t
  have hat2 : (a * t) ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_z h htza]; exact pow_orderOf_eq_one _
  have hxt2 : (x * t) ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h htxa]; exact pow_orderOf_eq_one _
  have hat : a * t = t * a := comm_of_sq_mul ha2 ht2 hat2
  have hxt : x * t = t * x := comm_of_sq_mul hx2 ht2 hxt2
  have htzz : t * (a * x) ^ 2 = (a * x) ^ 2 * t := lines14_comm_sq hat.symm hxt.symm
  have hwzz : (a * x) ^ 2 ∈ Gxy x t :=
    mem_Gxy.mpr ⟨mem_Gx.mpr hxz, mem_Gx.mpr htzz⟩
  have hb : t ∈ orb2A x x := ⟨hxA.symm.trans hta, hxA.symm.trans htxa⟩
  have hXxt : IsShapeTwoTwoTimesA8 ↥(Gxy x t) := (hF3 x z hxA (IsConj.refl z)).shape_2A t hb
  have hPicxt : A8Pictures x z := hPic x z hxA (IsConj.refl z)
  have htxA : IsConj a (t * x) := by rw [← hxt]; exact htxa
  have hxzz : x * (a * x) ^ 2 = (a * x) ^ 2 * x := hxz
  have hpw : IsConj a (x * (a * x) ^ 2) := by
    rw [hxzz, hzzx]
    exact hxA.trans (isConj_iff.mpr ⟨a, rfl⟩)
  have hxtzz_eq : x * t * (a * x) ^ 2 = a * (x * t) * a⁻¹ := by
    calc x * t * (a * x) ^ 2 = x * (t * (a * x) ^ 2) := by rw [mul_assoc]
      _ = x * ((a * x) ^ 2 * t) := by rw [htzz]
      _ = (x * (a * x) ^ 2) * t := by rw [← mul_assoc]
      _ = ((a * x) ^ 2 * x) * t := by rw [hxzz]
      _ = (a * x * a⁻¹) * t := by rw [hzzx]
      _ = a * x * (a⁻¹ * t) := by group
      _ = a * x * (t * a⁻¹) := by rw [lines14_comm_inv_left hat]
      _ = a * (x * t) * a⁻¹ := by group
  have hpbw : IsConj a (x * t * (a * x) ^ 2) := by
    rw [hxtzz_eq]
    exact htxa.trans (isConj_iff.mpr ⟨a, rfl⟩)
  have htzA : IsConj a (t * (a * x) ^ 2) :=
    lines_coset h hnc hxA hb hXxt hPicxt hwzz hzzB hpw hpbw
  have hzzxA : IsConj a ((a * x) ^ 2 * x) := by
    rw [hzzx]
    exact hxA.trans (isConj_iff.mpr ⟨a, rfl⟩)
  have hazzA : IsConj a (a * (a * x) ^ 2) := by
    rw [hazz]
    exact isConj_iff.mpr ⟨x, rfl⟩
  have htxx_eq : t * (a * x) ^ 2 * x = a * (t * x) * a⁻¹ := by
    have hasq : a * a = 1 := by simpa [pow_two] using ha2
    have hxsq : x * x = 1 := by simpa [pow_two] using hx2
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right hasq
    rw [hai]
    calc t * (a * x) ^ 2 * x = t * a * x * a * (x * x) := by rw [pow_two]; group
      _ = t * a * x * a := by rw [hxsq, mul_one]
      _ = a * t * x * a := by rw [← hat]
      _ = a * (t * x) * a := by group
  have htxxA : IsConj a (t * (a * x) ^ 2 * x) := by
    rw [htxx_eq]
    exact htxA.trans (isConj_iff.mpr ⟨a, rfl⟩)
  have htaZ : IsConj z (t * a) := by rw [← hat]; exact htza
  have htazz_eq : t * a * (a * x) ^ 2 = x * (t * a) * x⁻¹ := by
    have htxinv : x⁻¹ * t = t * x⁻¹ := lines14_comm_inv_left hxt
    calc t * a * (a * x) ^ 2 = (a * t) * (a * x) ^ 2 := by rw [← hat]
      _ = a * (t * (a * x) ^ 2) := by group
      _ = a * ((a * x) ^ 2 * t) := by rw [htzz]
      _ = (a * (a * x) ^ 2) * t := by group
      _ = (x * a * x⁻¹) * t := by rw [← hazz]
      _ = x * a * (x⁻¹ * t) := by group
      _ = x * a * (t * x⁻¹) := by rw [htxinv]
      _ = x * (a * t) * x⁻¹ := by group
      _ = x * (t * a) * x⁻¹ := by rw [hat]
  have htazzA : IsConj z (t * a * (a * x) ^ 2) := by
    rw [htazz_eq]
    exact htaZ.trans (isConj_iff.mpr ⟨x, rfl⟩)
  refine ⟨?_, hzzxA, htxxA, hazzA, htazzA⟩
  · rw [← htzz]; exact htzA

end CFSG.EvenSporadicStandard.HNRecog.Section3
