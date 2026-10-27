module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.FiveLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.ShapeCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem oddInvFive_comm_of_sq_mul {G : Type} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have h1 : x * y * (x * y) = 1 := by simpa [pow_two] using hxy
  have hxx : x * x = 1 := by simpa [pow_two] using hx
  have hyy : y * y = 1 := by simpa [pow_two] using hy
  calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h1
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [inv_eq_of_mul_eq_one_right hyy, inv_eq_of_mul_eq_one_right hxx]

private theorem oddInvFive_conj_sq_centralizes {G : Type} [Group G] {c y : G}
    (h : c * y * c⁻¹ = y⁻¹) : c ^ 2 * y = y * c ^ 2 := by
  rw [pow_two]
  have h1 : c * c * y * (c * c)⁻¹ = y := by
    calc c * c * y * (c * c)⁻¹ = c * (c * y * c⁻¹) * c⁻¹ := by group
      _ = c * y⁻¹ * c⁻¹ := by rw [h]
      _ = (c * y * c⁻¹)⁻¹ := by rw [conj_inv]
      _ = (y⁻¹)⁻¹ := by rw [h]
      _ = y := inv_inv y
  calc c * c * y = c * c * y * (c * c)⁻¹ * (c * c) := by group
    _ = y * (c * c) := by rw [h1]

private theorem oddInvFive_mul_inv_conj {G : Type} [Group G] {a t y : G} (ha : a * a = 1)
    (ht : t * t = 1) (htc : t * y = y * t) (hay : a * y * a = y⁻¹) :
    (a * t) * y * (a * t)⁻¹ = y⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, inv_eq_of_mul_eq_one_right ha]
  calc (a * t) * y * (t * a) = a * (t * y) * (t * a) := by group
    _ = a * (y * t) * (t * a) := by rw [htc]
    _ = a * (y * (t * t)) * a := by group
    _ = a * y * a := by rw [ht]; group
    _ = y⁻¹ := hay

theorem oddInv_five {G : Type} [Group G] [Finite G] {a z x : G} (h : IsF5Type a z)
    (hOrb : GzOrbitFacts a z) (hNo : GzNoFacts a z) (hSGz : StructGzFacts a z)
    (hx : IsConj a x) (haz : a ∈ Gx z) (hxz : x ∈ Gx z) (haQ : a ∉ Qz z) (hxQ : x ∉ Qz z)
    (hnc : ¬ IsConj a (a * z)) (h5 : orderOf (a * x) = 5)
    (hcard : Nat.card ↥(CbarCent z ⟨a * x, Subgroup.mul_mem _ haz hxz⟩) = 50) :
    ∃ t : G, IsConj a t ∧ t ∈ Gxyz a z x := by
  have ha2 : a ^ 2 = 1 := oddInv_sq_eq_one h (IsConj.refl a)
  have hx2 : x ^ 2 = 1 := oddInv_sq_eq_one h hx
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hxx : x * x = 1 := by simpa [pow_two] using hx2
  let σ : ↥(Gx z) := ⟨a * x, Subgroup.mul_mem _ haz hxz⟩
  have hσord : orderOf σ = 5 := by
    rw [Subgroup.orderOf_mk]
    exact h5
  have hcard' : Nat.card ↥(CbarCent z σ) = 50 := by simpa [σ] using hcard
  have hCQ : Qz z ⊓ Gx (a * x) = Subgroup.zpowers z := by
    rcases hSGz.five.1 σ hσord with ⟨-, h1⟩ | ⟨hZZ, -⟩ | ⟨-, h3⟩
    · exact h1
    · exfalso
      have h25 : Nat.card ↥(CbarCent z σ) = 25 := card_of_isShapeZpTimesZp_five hZZ
      rw [hcard'] at h25
      exact absurd h25 (by norm_num)
    · exact h3
  have h5pow : (a * x) ^ 5 = 1 := by
    rw [← h5]
    exact pow_orderOf_eq_one (a * x)
  obtain ⟨t, ht, htA, htout, htc⟩ :=
    oddInv_five_lift h hOrb hNo hx haz hxz haQ hxQ h5pow
  have ht2 : t ^ 2 = 1 := oddInv_sq_eq_one h htA
  have htt : t * t = 1 := by simpa [pow_two] using ht2
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
  have hua : barOf z ⟨a, haz⟩ ∉ _root_.commutator (Gbar z) :=
    oddInv_barOf_not_mem_commutator h hOrb hNo haz haQ (IsConj.refl a)
  have hux : barOf z ⟨x, hxz⟩ ∉ _root_.commutator (Gbar z) :=
    oddInv_barOf_not_mem_commutator h hOrb hNo hxz hxQ hx
  have hua2 : (barOf z ⟨a, haz⟩) ^ 2 = 1 := oddInv_barOf_sq_eq_one haz ha2
  have hux2 : (barOf z ⟨x, hxz⟩) ^ 2 = 1 := oddInv_barOf_sq_eq_one hxz hx2
  have hut2 : (barOf z ⟨t, ht⟩) ^ 2 = 1 := oddInv_barOf_sq_eq_one ht ht2
  have hσbar : barOf z σ = barOf z ⟨a, haz⟩ * barOf z ⟨x, hxz⟩ := rfl
  have h5bar : orderOf (barOf z ⟨a, haz⟩ * barOf z ⟨x, hxz⟩) = 5 := by
    rw [← hσbar]
    exact orderOf_barOf_five hσord
  have htcbar : barOf z ⟨t, ht⟩ * (barOf z ⟨a, haz⟩ * barOf z ⟨x, hxz⟩) =
      (barOf z ⟨a, haz⟩ * barOf z ⟨x, hxz⟩) * barOf z ⟨t, ht⟩ := by
    have h' : (⟨t, ht⟩ : ↥(Gx z)) * ((⟨a, haz⟩ : ↥(Gx z)) * ⟨x, hxz⟩) =
        ((⟨a, haz⟩ : ↥(Gx z)) * ⟨x, hxz⟩) * ⟨t, ht⟩ := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using htc
    have h'' := congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))) h'
    simp only [map_mul] at h''
    simpa [barOf] using h''
  have hSQ : (barOf z ⟨a, haz⟩ * barOf z ⟨t, ht⟩) ^ 2 = 1 :=
    oddInv_gbar_sq_mul e hua hux htout hua2 hux2 hut2 h5bar htcbar
  let atElem : ↥(Gx z) := ⟨a * t, Subgroup.mul_mem _ haz ht⟩
  have hbar_sq : barOf z (atElem ^ 2) = 1 := by
    have h1 : barOf z (atElem ^ 2) = (barOf z ⟨a, haz⟩ * barOf z ⟨t, ht⟩) ^ 2 := by
      have hat : atElem = (⟨a, haz⟩ : ↥(Gx z)) * ⟨t, ht⟩ := rfl
      rw [hat]
      rfl
    rw [h1, hSQ]
  have hQ : (a * t) ^ 2 ∈ Qz z := by
    have hmem := (barOf_eq_one_iff (atElem ^ 2)).mp hbar_sq
    simpa [atElem] using hmem
  have hay : a * (a * x) * a = (a * x)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right haa]
    calc a * (a * x) * a = (a * a) * x * a := by group
      _ = x * a := by rw [haa]; group
  have hcy_inv : (a * t) * (a * x) * (a * t)⁻¹ = (a * x)⁻¹ :=
    oddInvFive_mul_inv_conj haa htt htc hay
  have hGx : (a * t) ^ 2 ∈ Gx (a * x) := by
    rw [mem_Gx]
    exact (oddInvFive_conj_sq_centralizes hcy_inv).symm
  have hzpow : (a * t) ^ 2 ∈ Subgroup.zpowers z := by
    have hmem : (a * t) ^ 2 ∈ Qz z ⊓ Gx (a * x) := Subgroup.mem_inf.mpr ⟨hQ, hGx⟩
    rwa [hCQ] at hmem
  rcases (gzNo_mem_zpowers_iff h.orderOf_z).mp hzpow with hsq | hsq
  ·
    have hat : a * t = t * a := oddInvFive_comm_of_sq_mul ha2 ht2 hsq
    refine ⟨t, htA, mem_Gxyz.mpr ⟨?_, ht, ?_⟩⟩
    · rw [mem_Gx]; exact hat
    · rw [mem_Gx]
      have hxat : x = a * (a * x) := by rw [← mul_assoc, haa, one_mul]
      calc x * t = (a * (a * x)) * t := by conv_lhs => rw [hxat]
        _ = a * ((a * x) * t) := by group
        _ = a * (t * (a * x)) := by rw [← htc]
        _ = (a * t) * (a * x) := by group
        _ = (t * a) * (a * x) := by rw [hat]
        _ = t * (a * (a * x)) := by group
        _ = t * x := by conv_rhs => rw [hxat]
  ·
    exfalso
    have hconj : (a * t) * a * (a * t)⁻¹ = a * z := by
      have h1 : (a * t) * a * (a * t)⁻¹ = (a * t) ^ 2 * a := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right htt, inv_eq_of_mul_eq_one_right haa]
        rw [pow_two]
        group
      rw [h1, hsq, mem_Gx.mp haz]
    exact hnc (isConj_iff.mpr ⟨a * t, hconj⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section3
