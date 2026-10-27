module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTwoOne

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {X Q : Type*} [Group X] [Group Q] {H : Subgroup X} {z : X}

theorem isInvolution_of_orderOf {x : X} (h : orderOf x = 2) : IsInvolution x :=
  ⟨(orderOf_eq_prime_iff.mp h).2, (orderOf_eq_prime_iff.mp h).1⟩

theorem orderOf_of_isInvolution {x : X} (h : IsInvolution x) : orderOf x = 2 :=
  orderOf_eq_prime h.sq_eq_one h.ne_one

theorem mem_map_iff_of_ker_le (f : X →* Q) (hker : f.ker ≤ H) (x : X) :
    f x ∈ H.map f ↔ x ∈ H := by
  constructor
  · rintro ⟨h, hh, hfx⟩
    have hk : h⁻¹ * x ∈ f.ker := by
      change f (h⁻¹ * x) = 1
      rw [map_mul, map_inv, hfx, inv_mul_cancel]
    have hmem := H.mul_mem hh (hker hk)
    rwa [mul_inv_cancel_left] at hmem
  · exact fun hx => ⟨x, hx, rfl⟩

theorem unique_map (f : X →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ H)
    (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H) :
    ∀ q : Q, f z ∈ rightConjugate (H.map f) q ↔ q ∈ H.map f := by
  intro q
  obtain ⟨g, rfl⟩ := hf q
  rw [mem_rightConjugate_iff, ← map_inv, ← map_mul, ← map_mul, mem_map_iff_of_ker_le f hker,
    mem_map_iff_of_ker_le f hker, ← huniq g, mem_rightConjugate_iff]

theorem map_ne_top (f : X →* Q) (hker : f.ker ≤ H)
    (hH : H ≠ ⊤) : H.map f ≠ ⊤ := by
  intro htop
  apply hH
  refine eq_top_iff.mpr fun g _ => (mem_map_iff_of_ker_le f hker g).mp ?_
  rw [htop]
  exact Subgroup.mem_top _

variable [Finite X]

theorem orderOf_map_of_odd (f : X →* Q) (hodd : Odd (Nat.card f.ker)) (hz : orderOf z = 2) :
    orderOf (f z) = 2 :=
  orderOf_of_isInvolution (CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel f hodd
    (isInvolution_of_orderOf hz))

omit [Finite X] in
theorem class_map (f : X →* Q) (hf : Function.Surjective f) :
    involutionPointClass (f z) = f '' involutionPointClass z := by
  ext s
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := hf q
    exact ⟨rightConjugateElem z g, ⟨g, rfl⟩, by simp only [rightConjugateElem, map_mul, map_inv]⟩
  · rintro ⟨t, ⟨g, rfl⟩, rfl⟩
    exact ⟨f g, by simp only [rightConjugateElem, map_mul, map_inv]⟩

omit [Finite X] in
theorem hull_map_eq_top (f : X →* Q) (hf : Function.Surjective f)
    (hhull : involutionPointHull z = ⊤) : involutionPointHull (f z) = ⊤ := by
  have h := MonoidHom.map_closure f (involutionPointClass z)
  rw [← class_map f hf] at h
  show Subgroup.closure (involutionPointClass (f z)) = ⊤
  rw [← h]
  change (involutionPointHull z).map f = ⊤
  rw [hhull, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf]

theorem centralProduct_map (f : X →* Q) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) (hz : orderOf z = 2)
    (h2 : CentralProductCentralizer H z) : CentralProductCentralizer (H.map f) (f z) := by
  obtain ⟨⟨S, hzS, hzc⟩, hcent⟩ := h2
  refine ⟨?_, ?_⟩
  · obtain ⟨T, -, hzT, hcomm⟩ := CFSG.ProperTwoGeneratedCore.central_sylow_two_image f hf S hzS
      (commute_of_mem_center hzS hzc)
    exact ⟨T, hzT, Subgroup.mem_center_iff.mpr fun t => Subtype.ext (hcomm t t.property).eq.symm⟩
  · intro t ht hzt hne
    have hzI := isInvolution_of_orderOf hz
    have htI : IsInvolution t :=
      isInvolution_of_orderOf (class_orderOf (orderOf_map_of_odd f hodd hz) ht)
    obtain ⟨u, huI, hfu, hu⟩ :=
      CFSG.ProperTwoGeneratedCore.commuting_involution_lift_of_odd_kernel f hf hodd hzI htI
        hzt.symm
    have hucls : u ∈ involutionPointClass z :=
      (CFSG.ProperTwoGeneratedCore.involution_point_class_image_iff f hf hodd hzI huI).mp
        (hfu ▸ ht)
    have hune : u ≠ z := fun h => hne (by rw [← hfu, h])
    have hzu : Commute z u := hu.symm
    have hC := hcent u hucls hzu hune
    have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
    have huu := class_mul_self hz hucls
    have hzuI : IsInvolution (z * u) :=
      isInvolution_of_orderOf (orderOf_mul_of_commute hzz huu hzu hune)
    rw [← hfu, ← map_mul, ← CFSG.ProperTwoGeneratedCore.involution_centralizer_image f hf hodd hzuI]
    exact Subgroup.map_mono hC

end CFSG.ComponentClassification.AschbacherStrongEmbedding
