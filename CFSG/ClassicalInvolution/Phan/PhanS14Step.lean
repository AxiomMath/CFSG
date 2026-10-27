module

public import CFSG.ClassicalInvolution.Phan.PhanS12Close
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.ClassicalInvolution.Phan.PhanS11Iso
public import CFSG.ClassicalInvolution.Phan.PhanS12Plane
public import CFSG.ClassicalInvolution.Phan.PhanS6Dict
public import CFSG.ClassicalInvolution.Phan.PhanS9O5Span

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open scoped MatrixGroups

section Gen

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem actK_inv_smul_of_eq {g : spinGroup (quadOdd 3 F)} {x w : W7 K} {c : K} (hc : c ≠ 0)
    (h : actK g x = c • w) : actK g⁻¹ w = c⁻¹ • x := by
  have h' := actK_inv_actK (K := K) g x
  rw [h, map_smul] at h'
  calc actK g⁻¹ w = c⁻¹ • (c • actK g⁻¹ w) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • x := by rw [h']

end Gen

section Step

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))} (S : Setup M E D)

include S

theorem Setup.exists_R0 (A : SL(2, GaloisField p f)) :
    ∃ u ∈ (E.ι 0).range, spinAction (quadOdd 3 (GaloisField p f)) u = La0 h2 A := by
  have : La0 h2 A ∈ (fr0 h2).La.range := ⟨A, rfl⟩
  rw [← M.map_eq] at this
  obtain ⟨u, hu, hu'⟩ := this
  exact ⟨u, S.R0_mem hu, hu'⟩

theorem Setup.exists_U1 (A : SL(2, GaloisField p f)) :
    ∃ u ∈ (E.ι 1).range, spinAction (quadOdd 3 (GaloisField p f)) u = La1 h2 A := by
  obtain ⟨hmap, -⟩ := U1_spec M.D S.h4
  have : La1 h2 A ∈ (fr1 h2).La.range := ⟨A, rfl⟩
  rw [← hmap] at this
  obtain ⟨u, hu, hu'⟩ := this
  refine ⟨u, ?_, hu'⟩
  rw [S.range 1]
  exact hu

theorem Setup.exists_La0 {u : spinGroup (quadOdd 3 (GaloisField p f))}
    (hu : u ∈ (E.ι 0).range) :
    ∃ A : SL(2, GaloisField p f), spinAction (quadOdd 3 (GaloisField p f)) u = La0 h2 A := by
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) u ∈ (fr0 h2).La.range := by
    rw [← M.map_eq]
    exact ⟨_, S.mem_R0 hu, rfl⟩
  exact ⟨A, hA.symm⟩

theorem Setup.exists_La1 {u : spinGroup (quadOdd 3 (GaloisField p f))}
    (hu : u ∈ (E.ι 1).range) :
    ∃ A : SL(2, GaloisField p f), spinAction (quadOdd 3 (GaloisField p f)) u = La1 h2 A := by
  obtain ⟨hmap, -⟩ := U1_spec M.D S.h4
  have hu' : u ∈ (longBlock (GaloisField p f) 2 1).range.map M.D.θ := by
    rw [S.range 1] at hu
    exact hu
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) u ∈ (fr1 h2).La.range := by
    rw [← hmap]
    exact ⟨_, hu', rfl⟩
  exact ⟨A, hA.symm⟩

theorem Setup.inPi0_actK_R0 {u : spinGroup (quadOdd 3 (GaloisField p f))}
    (hu : u ∈ (E.ι 0).range) {x : W7 (GaloisField p (2 * f))} (hx : InPi0 D x) :
    InPi0 D (actK u x) := by
  obtain ⟨A, hA⟩ := S.exists_La0 hu
  obtain ⟨α, β, γ, rfl⟩ := hx
  obtain ⟨a, b, c, d, h1, h2'⟩ := S.n0.mem_l0 A
  have e3 := S.n0.fix_vE3 A
  refine ⟨α * a + β * c, α * b + β * d, γ, ?_⟩
  simp only [map_add, map_smul, actK_eq_of_spinAction_eq hA, h1, h2', e3]
  module

theorem Setup.inPi0_actK_U1 {u : spinGroup (quadOdd 3 (GaloisField p f))}
    (hu : u ∈ (E.ι 1).range) {x : W7 (GaloisField p (2 * f))} (hx : InPi0 D x) :
    InPi0 D (actK u x) := by
  obtain ⟨A, hA⟩ := S.exists_La1 hu
  obtain ⟨α, β, γ, rfl⟩ := hx
  obtain ⟨a, b, c, d, h1, h2'⟩ := S.n1.mem_l23 A
  have e1 := S.n1.fix_vXi A
  refine ⟨α, β * a + γ * c, β * b + γ * d, ?_⟩
  simp only [map_add, map_smul, actK_eq_of_spinAction_eq hA, h1, h2', e1]
  module

theorem Setup.inPi0_actK_step_inv {u v : spinGroup (quadOdd 3 (GaloisField p f))}
    (hu : u ∈ (E.ι 1).range) (hv : v ∈ (E.ι 0).range) {x : W7 (GaloisField p (2 * f))}
    (hx : InPi0 D x) : InPi0 D (actK (u⁻¹ * v)⁻¹ x) := by
  rw [mul_inv_rev, actK_mul]
  exact S.inPi0_actK_R0 (inv_mem hv) (by
    rw [inv_inv]
    exact S.inPi0_actK_U1 hu hx)

theorem Setup.step_plane {y : W7 (GaloisField p (2 * f))} (hy : InPi0 D y) (hff : IsFF7 D y)
    (hcol : Col7 D (vXi D) y) :
    ∃ u ∈ (E.ι 1).range, ∃ v ∈ (E.ι 0).range, ∃ c : GaloisField p (2 * f), c ≠ 0 ∧
      actK (u⁻¹ * v) (vXi D) = c • y := by
  obtain ⟨α, β, γ, rfl⟩ := hy
  obtain ⟨y', hy'⟩ : ∃ y' : W7 (GaloisField p (2 * f)), y' = β • vE2 D + γ • vE3 D := ⟨_, rfl⟩
  have hsplit : α • vXi D + β • vE2 D + γ • vE3 D = α • vXi D + y' := by
    rw [hy', add_assoc]
  have hxy' : hrm D (vXi D) y' = 0 := by
    rw [hy', hrm_add_right, hrm_smul_right, hrm_smul_right, hrm_vXi_vE2, hrm_vXi_vE3]
    simp
  have hy'x : hrm D y' (vXi D) = 0 := by
    rw [hy', hrm_add_left, hrm_smul_left, hrm_smul_left, hrm_vE2_vXi, hrm_vE3_vXi]
    simp
  have hgram : gram7 D (vXi D) (α • vXi D + y') = 4 * hrm D y' y' := by
    simp only [gram7, hrm_add_left, hrm_add_right, hrm_smul_left, hrm_smul_right, hrm_vXi_vXi,
      hxy', hy'x]
    ring
  have hh' : hrm D y' y' ≠ 0 := by
    intro h0
    apply hcol.2
    rw [hsplit, hgram, h0, mul_zero]
  have hQ : quadOdd 3 (GaloisField p (2 * f)) y' = 0 := by
    have hQ2 := (isFF7_vE2 D S.h2K).1
    have hQ3 := (isFF7_vE3 D S.h2K).1
    rw [hy', QuadraticMap.map_add (quadOdd 3 (GaloisField p (2 * f))) (β • vE2 D) (γ • vE3 D),
      QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, polar_vE2_vE3, hQ2, hQ3]
    simp
  have hffy' : IsFF7 D (β • vE2 D + γ • vE3 D) := by
    rw [← hy']
    exact ⟨hQ, hh'⟩
  obtain ⟨A, c', hc', hA⟩ := S.n1.move β γ hffy'
  obtain ⟨u', hu', hAu'⟩ := S.exists_U1 A
  have hu'2 : actK u' (vE2 D) = c' • y' := by
    rw [actK_eq_of_spinAction_eq hAu', hA, hy']
  have hu'1 : actK u' (vXi D) = vXi D := by
    rw [actK_eq_of_spinAction_eq hAu']
    exact S.n1.fix_vXi A
  have hinv1 : actK u'⁻¹ (vXi D) = vXi D := by
    have := actK_inv_actK u' (vXi D)
    rwa [hu'1] at this
  have hinv2 : actK u'⁻¹ y' = c'⁻¹ • vE2 D := actK_inv_smul_of_eq hc' hu'2
  have hz : actK u'⁻¹ (α • vXi D + y') = α • vXi D + c'⁻¹ • vE2 D := by
    rw [map_add, map_smul, hinv1, hinv2]
  have hzff : IsFF7 D (α • vXi D + c'⁻¹ • vE2 D) := by
    rw [← hz]
    refine isFF7_actK D S.h2K _ ?_
    rw [← hsplit]
    exact hff
  obtain ⟨A', c'', hc'', hA'⟩ := S.n0.move α c'⁻¹ hzff
  obtain ⟨v, hv, hAv⟩ := S.exists_R0 A'
  have hvξ : actK v (vXi D) = c'' • (α • vXi D + c'⁻¹ • vE2 D) := by
    rw [actK_eq_of_spinAction_eq hAv]
    exact hA'
  refine ⟨u'⁻¹, inv_mem hu', v, hv, c'', hc'', ?_⟩
  rw [inv_inv, actK_mul, hvξ, map_smul, ← hz, actK_actK_inv, ← hsplit]

theorem planeBase_of_close (hc : PlaneClose E D) : PlaneBase E D := by
  intro y z hyIn hzIn hffy hffz h1 h2' h3
  obtain ⟨u₁, hu₁, v₁, hv₁, c₁, hc₁, hk₁⟩ := S.step_plane hyIn hffy h1
  have hy1 : actK (u₁⁻¹ * v₁)⁻¹ y = c₁⁻¹ • vXi D := actK_inv_smul_of_eq hc₁ hk₁
  have hz'In : InPi0 D (actK (u₁⁻¹ * v₁)⁻¹ z) := S.inPi0_actK_step_inv hu₁ hv₁ hzIn
  have hz'ff : IsFF7 D (actK (u₁⁻¹ * v₁)⁻¹ z) := isFF7_actK D S.h2K _ hffz
  have hz'col : Col7 D (vXi D) (actK (u₁⁻¹ * v₁)⁻¹ z) := by
    have := (col7_actK D (u₁⁻¹ * v₁)⁻¹ y z).2 h2'
    rw [hy1] at this
    exact (col7_smul D (c := c₁⁻¹) (d := 1) (inv_ne_zero hc₁) one_ne_zero
      (a := vXi D) (b := actK (u₁⁻¹ * v₁)⁻¹ z)).1 (by rwa [one_smul])
  obtain ⟨u₂, hu₂, v₂, hv₂, c₂, hc₂, hk₂⟩ := S.step_plane hz'In hz'ff hz'col
  have hkz : actK (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂)) (vXi D) = c₂ • z := by
    rw [actK_mul, hk₂, map_smul, actK_actK_inv]
  have hz1 : actK (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂))⁻¹ z = c₂⁻¹ • vXi D := actK_inv_smul_of_eq hc₂ hkz
  have hvXi : InPi0 D (vXi D) := ⟨1, 0, 0, by simp⟩
  have hx'In : InPi0 D (actK (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂))⁻¹ (vXi D)) := by
    rw [mul_inv_rev, actK_mul]
    exact S.inPi0_actK_step_inv hu₂ hv₂ (S.inPi0_actK_step_inv hu₁ hv₁ hvXi)
  have hx'ff : IsFF7 D (actK (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂))⁻¹ (vXi D)) :=
    isFF7_actK D S.h2K _ (isFF7_vXi D S.h2K)
  have hx'col : Col7 D (vXi D) (actK (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂))⁻¹ (vXi D)) := by
    have := (col7_actK D (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂))⁻¹ z (vXi D)).2 h3
    rw [hz1] at this
    exact (col7_smul D (c := c₂⁻¹) (d := 1) (inv_ne_zero hc₂) one_ne_zero
      (a := vXi D) (b := actK (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂))⁻¹ (vXi D))).1 (by rwa [one_smul])
  obtain ⟨u₃, hu₃, v₃, hv₃, c₃, hc₃, hk₃⟩ := S.step_plane hx'In hx'ff hx'col
  have hkξ : actK (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂) * (u₃⁻¹ * v₃)) (vXi D) = c₃ • vXi D := by
    rw [actK_mul, hk₃, map_smul, actK_actK_inv]
  have hmem : u₁⁻¹ * v₁ * (u₂⁻¹ * v₂) * (u₃⁻¹ * v₃) ∈ (E.ι 0).range ⊔ (E.ι 1).range := by
    have hs : ∀ u ∈ (E.ι 1).range, ∀ v ∈ (E.ι 0).range,
        u⁻¹ * v ∈ (E.ι 0).range ⊔ (E.ι 1).range := fun u hu v hv =>
      mul_mem (Subgroup.mem_sup_right (inv_mem hu)) (Subgroup.mem_sup_left hv)
    exact mul_mem (mul_mem (hs u₁ hu₁ v₁ hv₁) (hs u₂ hu₂ v₂ hv₂)) (hs u₃ hu₃ v₃ hv₃)
  exact ⟨u₁, hu₁, v₁, hv₁, u₂, hu₂, v₂, hv₂, u₃, hu₃, v₃, hv₃, c₁, c₂, hc₁, hc₂, hk₁, hkz,
    hc _ hmem ⟨c₃, hc₃, hkξ⟩⟩

end Step

end CFSG.ClassicalInvolution.PhanB3.S
