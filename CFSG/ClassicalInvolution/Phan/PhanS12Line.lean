module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Phan.PhanS11Adj
public import CFSG.ClassicalInvolution.Phan.PhanS2Struct
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan CFSG.Monster.B.Geometry
  CFSG.Monster.B.Geometry.ChamberSystem

section Line

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))} (S : Setup M E D)

include S

theorem Setup.coset_eq_of_smul {g g' : spinGroup (quadOdd 3 (GaloisField p f))}
    {a : GaloisField p (2 * f)} (ha : a ≠ 0)
    (h : actK g' (vXi D) = a • actK g (vXi D)) :
    (g : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) = (g' : _) := by
  refine QuotientGroup.eq.2 (S.mem_parab_iff.2 ⟨a, ha, ?_⟩)
  rw [actK_mul, h, map_smul, ← actK_mul, inv_mul_cancel, actK_one]

omit S [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem adj_zero_of_mem {a u : spinGroup (quadOdd 3 (GaloisField p f))}
    (hu : u ∈ (E.ι 0).range) :
    (phanSystem E).adj 0 (a : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ torusSub E)
      ((a * u : spinGroup (quadOdd 3 (GaloisField p f))) : _) := by
  rw [phanSystem_adj_mk]
  have : a⁻¹ * (a * u) = u := by group
  rw [this]
  exact Lsup_le_parab {0} (by rw [Lsup_singleton]; exact hu)

theorem Setup.null2_line (h0 : PtStep0 E) {gx gy gz : spinGroup (quadOdd 3 (GaloisField p f))}
    (hxy : (ptGraph E).Adj (gx : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) gy)
    (hyz : (ptGraph E).Adj (gy : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) gz)
    (hzx : (ptGraph E).Adj (gz : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) gx)
    (hffz : IsFF7 D (actK gz (vXi D)))
    (hline : ∃ s t : GaloisField p (2 * f),
      actK gz (vXi D) = s • actK gx (vXi D) + t • actK gy (vXi D)) :
    Null2 E h0 (.cons hxy (.cons hyz (.cons hzx .nil))) := by
  have hxy' := (S.adj_iff_col7 gx gy).1 hxy
  have hcol' : Col7 D (vXi D) (actK (gx⁻¹ * gy) (vXi D)) := by
    have := (col7_actK D gx⁻¹ _ _).2 hxy'
    rwa [← actK_mul, ← actK_mul, inv_mul_cancel, actK_one] at this
  obtain ⟨p₁, hp₁, u₂, hu₂, p₂, hp₂, hk⟩ := S.exists_mul_of_col7 hcol'
  obtain ⟨κ₁, hκ₁, h₁⟩ := S.mem_parab_iff.1 hp₁
  obtain ⟨κ₂, hκ₂, h₂⟩ := S.mem_parab_iff.1 hp₂
  obtain ⟨s, t, hst⟩ := hline
  obtain ⟨a, b, hab⟩ := actK_R0_mem_l0 D S.range S.n0 hu₂
  obtain ⟨c, hc⟩ : ∃ c, c = gx * p₁ := ⟨_, rfl⟩
  have hgy : gy = c * u₂ * p₂ := by
    rw [hc]
    calc gy = gx * (gx⁻¹ * gy) := by group
      _ = gx * (p₁ * u₂ * p₂) := by rw [hk]
      _ = _ := by group
  have hvx : actK c (vXi D) = κ₁ • actK gx (vXi D) := by
    rw [hc, actK_mul, h₁, map_smul]
  have hvy : actK gy (vXi D) = κ₂ • actK (c * u₂) (vXi D) := by
    rw [hgy, actK_mul, h₂, map_smul]
  have hgx' : actK gx (vXi D) = κ₁⁻¹ • actK c (vXi D) := by
    rw [hvx, smul_smul, inv_mul_cancel₀ hκ₁, one_smul]
  have hz1 : actK c⁻¹ (actK gz (vXi D)) =
      (s * κ₁⁻¹ + t * (κ₂ * a)) • vXi D + (t * (κ₂ * b)) • vE2 D := by
    rw [hst, hgx', hvy, map_add, map_smul, map_smul, map_smul, map_smul, ← actK_mul,
      ← actK_mul, inv_mul_cancel, inv_mul_cancel_left, actK_one, hab]
    simp only [smul_add, smul_smul, add_smul]
    abel
  have hzff : IsFF7 D ((s * κ₁⁻¹ + t * (κ₂ * a)) • vXi D + (t * (κ₂ * b)) • vE2 D) := by
    rw [← hz1]
    exact isFF7_actK D S.h2K c⁻¹ hffz
  obtain ⟨A, c', hc', hA⟩ := S.n0.move _ _ hzff
  obtain ⟨u₃, hu₃, hAu⟩ : ∃ u ∈ M.R₀, spinAction (quadOdd 3 (GaloisField p f)) u = La0 h2 A := by
    have : La0 h2 A ∈ (fr0 h2).La.range := ⟨A, rfl⟩
    rw [← M.map_eq] at this
    obtain ⟨u, hu, hu'⟩ := this
    exact ⟨u, hu, hu'⟩
  have hu₃' : actK u₃ (vXi D) = c' • actK c⁻¹ (actK gz (vXi D)) := by
    rw [actK_eq_of_spinAction_eq hAu, hA, hz1]
  have hvz : actK (c * u₃) (vXi D) = c' • actK gz (vXi D) := by
    rw [actK_mul, hu₃', map_smul, ← actK_mul, mul_inv_cancel, actK_one]
  have hu₃R : u₃ ∈ (E.ι 0).range := S.R0_mem hu₃
  have ex : (gx : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) = (c : _) := by
    refine QuotientGroup.eq.2 ?_
    have : gx⁻¹ * c = p₁ := by rw [hc]; group
    rw [this]
    exact hp₁
  have ey : (gy : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) =
      ((c * u₂ : spinGroup (quadOdd 3 (GaloisField p f))) : _) := by
    refine QuotientGroup.eq.2 ?_
    have : gy⁻¹ * (c * u₂) = p₂⁻¹ := by rw [hgy]; group
    rw [this]
    exact inv_mem hp₂
  have ez : (gz : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) =
      ((c * u₃ : spinGroup (quadOdd 3 (GaloisField p f))) : _) :=
    S.coset_eq_of_smul hc' hvz
  refine ⟨{0}, by simp, QuotientGroup.mk c,
    [(0, QuotientGroup.mk (c * u₂)), (0, QuotientGroup.mk (c * u₃)), (0, QuotientGroup.mk c)],
    [], ?_, ?_, IsJGallery.nil, by simp, rfl⟩
  ·
    have hP : ∀ (g : spinGroup (quadOdd 3 (GaloisField p f))),
        (phanFib E h0).P (QuotientGroup.mk g) =
          (g : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) := fun g => rfl
    refine ⟨?_, [], QuotientGroup.mk (c * u₂),
      [(0, QuotientGroup.mk (c * u₃)), (0, QuotientGroup.mk c)], rfl, IsJGallery.nil, ?_,
      ?_, [], QuotientGroup.mk (c * u₃), [(0, QuotientGroup.mk c)], rfl, IsJGallery.nil, ?_,
      ?_, [], QuotientGroup.mk c, [], rfl, IsJGallery.nil, ?_, ?_, IsJGallery.nil⟩
    · rw [hP, ex]
    · exact adj_zero_of_mem (E := E) (a := c) hu₂
    · rw [hP, ey]
    · have h4 : (phanSystem E).adj 0 (QuotientGroup.mk (c * u₂) : _)
          (QuotientGroup.mk (c * u₃)) := by
        rw [phanSystem_adj_mk]
        have : (c * u₂)⁻¹ * (c * u₃) = u₂⁻¹ * u₃ := by group
        rw [this]
        exact Lsup_le_parab {0} (by rw [Lsup_singleton]; exact mul_mem (inv_mem hu₂) hu₃R)
      exact h4
    · rw [hP, ez]
    · have h6 : (phanSystem E).adj 0 (QuotientGroup.mk (c * u₃) : _) (QuotientGroup.mk c) := by
        rw [phanSystem_adj_mk]
        have : (c * u₃)⁻¹ * c = u₃⁻¹ := by group
        rw [this]
        exact Lsup_le_parab {0} (by rw [Lsup_singleton]; exact inv_mem hu₃R)
      exact h6
    · rw [hP, ex]
  · intro i hi
    have : i = 0 := by simpa [galleryType] using hi
    rw [this]
    simp

end Line

end CFSG.ClassicalInvolution.PhanB3.S
