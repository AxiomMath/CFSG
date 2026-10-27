module

public import CFSG.ClassicalInvolution.Q3.Q3OTD4Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)


section Classical

variable {H : Type} [Group H] [Finite H]

theorem quotient_data_plus4 (ψ : spinGroup Q₄ →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) :
    Group.IsPerfect ↥ψ.range ∧
      Function.Surjective ((QuotientGroup.mk' (Subgroup.center ↥ψ.range)).comp ψ.rangeRestrict) ∧
      ((QuotientGroup.mk' (Subgroup.center ↥ψ.range)).comp ψ.rangeRestrict).ker ≤
        Subgroup.center (spinGroup Q₄) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have hθs : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hLp : Group.IsPerfect ↥ψ.range := isPerfect_of_surjective ψ.rangeRestrict hθs
  refine ⟨hLp, (QuotientGroup.mk'_surjective _).comp hθs, ?_⟩
  intro k hk
  have hθk : ψ.rangeRestrict.ker ≤ Subgroup.center (spinGroup Q₄) := ker_rangeRestrict_le ψ hψ
  have hcen := center_le_map_center_of_perfect ψ.rangeRestrict hθs hθk
  have h1 : ψ.rangeRestrict k ∈ Subgroup.center ↥ψ.range := (QuotientGroup.eq_one_iff _).mp hk
  obtain ⟨c, hc, hck⟩ := hcen h1
  have h2 : c⁻¹ * k ∈ ψ.rangeRestrict.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hck, inv_mul_cancel]
  have h3 : k = c * (c⁻¹ * k) := by group
  rw [h3]
  exact mul_mem hc (hθk h2)

theorem involutionOddCore_innerHom_plus4 (ψ : spinGroup Q₄ →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) {R : Subgroup (spinGroup Q₄)}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    {x : spinGroup Q₄} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxc : ∀ r ∈ R, x * r = r * x) :
    CFSG.Assembly.Dichotomy.involutionOddCore
      (FrameVertex.innerHom ψ x : ↥(inducedAutOn ψ.range)) = ⊥ := by
  classical
  obtain ⟨hLp, hfs, hfk⟩ := quotient_data_plus4 ψ hψ
  set L : Subgroup H := ψ.range with hL
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  set f : spinGroup Q₄ →* ↥L ⧸ Subgroup.center ↥L := π.comp ψ.rangeRestrict with hf
  have hZS : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot ↥L
  have hfx1 : f x ≠ 1 := by
    intro h1
    exact hx1 (fundNoncentral_plus4 R hR x hx (hfk ((MonoidHom.mem_ker).mpr h1)))
  have hfx2 : f x * f x = 1 := by rw [← map_mul, hx2, map_one]
  have hz2 : orderOf (f x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hfx2) hfx1
  have hO : oddCoreIn (Subgroup.centralizer ({f x} : Set (↥L ⧸ Subgroup.center ↥L))) = ⊥ :=
    oddCoreFree_plus4 _ f hfs hfk (f x) hz2
  obtain ⟨g, hg⟩ := fundSingleClass_plus4 R hR
  have hinnOn : AutOddFreeInnerOn (↥L ⧸ Subgroup.center ↥L) (fun s => s = f x) := by
    refine autOddFreeInnerOn_of_centralizing_inner _ hZS (fun s hs _ => hs ▸ hO)
      (fun s hs hs2 α hα hcent => ?_)
    subst hs
    obtain ⟨y, hy⟩ := Q3T.exists_eq_conj_of_centralizes_d4 hZS f hfs hfk
      (z := f x) (K := R.map f)
      (by
        rintro _ ⟨r, hr, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxc r hr])
      ⟨x, hx, rfl⟩ (g := g) (by rw [hg]) α hα hcent
    exact ⟨y, hy.symm⟩
  have hinnL : AutOddFreeInnerOn ↥L (fun s => (QuotientGroup.mk s : ↥L ⧸ Subgroup.center ↥L) =
      f x) := autOddFreeInnerOn_of_centralQuotient _ hinnOn
  set a : ↥(inducedAutOn L) := FrameVertex.innerHom ψ x with ha
  have haconj : (a : MulAut ↥L) = MulAut.conj (ψ.rangeRestrict x) := by
    ext y
    rfl
  have ha1 : a ≠ 1 := by
    intro h1
    apply hfx1
    have h2 : MulAut.conj (ψ.rangeRestrict x) = 1 := by
      rw [← haconj, h1]
      rfl
    exact (QuotientGroup.eq_one_iff _).mpr ((conj_eq_one_iff_mem_center _).mp h2)
  have ha2 : a * a = 1 := by rw [ha, ← map_mul, hx2, map_one]
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  exact hinnL (inducedAutOn L) (innSubgroup_le_inducedAutOn L) a (ψ.rangeRestrict x) haconj.symm
    rfl hao

end Classical

theorem central_involution_plus4 {R : Subgroup (spinGroup Q₄)}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    {x : spinGroup Q₄} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∀ r ∈ R, x * r = r * x := by
  have hodd := ModelFacts.TG3.odd_natCard_galoisField_three
  have cq := Q3TY.centralQuot3_plus (m := 4) le_rfl
  obtain ⟨x₀, hx₀R, hx₀1, hx₀c, i, hi, hθx₀⟩ := Q3TD.exists_central_involution3 hR
  have hsq1 : spinAction Q₄ x * spinAction Q₄ x = 1 := by rw [← map_mul, hx2, map_one]
  have hne1 : spinAction Q₄ x ≠ 1 := fun h => hx1 (cq.inj R hR x hx h)
  have hord1 : orderOf (spinAction Q₄ x) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq1) hne1
  have hθx : spinAction Q₄ x = i :=
    hi.eq_of_orderOf_eq_two hodd (Subgroup.mem_map_of_mem _ hx) hord1
  have hxx₀ : x = x₀ := by
    have h1 : x * x₀⁻¹ = 1 := cq.inj R hR _ (R.mul_mem hx (R.inv_mem hx₀R))
      (by rw [map_mul, map_inv, hθx, hθx₀, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  rw [hxx₀]
  exact hx₀c

section Neq

variable {H : Type} [Group H] [Finite H]

theorem innerHom_ne_one_plus4 (ψ : spinGroup Q₄ →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) {R : Subgroup (spinGroup Q₄)}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    {x : spinGroup Q₄} (hx : x ∈ R) (hx1 : x ≠ 1) : FrameVertex.innerHom ψ x ≠ 1 := by
  intro h1
  have hbc : ((FrameVertex.innerHom ψ x : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) =
      MulAut.conj (ψ.rangeRestrict x) := by
    ext y
    rfl
  have h2 : MulAut.conj (ψ.rangeRestrict x) = 1 := by
    rw [← hbc, h1]
    rfl
  have h3 := (conj_eq_one_iff_mem_center _).mp h2
  obtain ⟨hLp, hfs, hfk⟩ := quotient_data_plus4 ψ hψ
  have : x ∈ Subgroup.center (spinGroup Q₄) := hfk ((MonoidHom.mem_ker).mpr
    ((QuotientGroup.eq_one_iff _).mpr h3))
  exact hx1 (fundNoncentral_plus4 R hR x hx this)

end Neq

end CFSG.ClassicalInvolution.Q3.Q3OT
