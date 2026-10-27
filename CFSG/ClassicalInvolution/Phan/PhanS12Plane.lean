module

public import CFSG.ClassicalInvolution.Phan.PhanS12Line

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan CFSG.Monster.B.Geometry
  CFSG.Monster.B.Geometry.ChamberSystem

section Plane

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))}

@[expose] def InPi0 (D : KDat (GaloisField p f) (GaloisField p (2 * f)))
    (x : W7 (GaloisField p (2 * f))) : Prop :=
  ∃ α β γ : GaloisField p (2 * f), x = α • vXi D + β • vE2 D + γ • vE3 D

@[expose] def PlaneBase (E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f))))
    (D : KDat (GaloisField p f) (GaloisField p (2 * f))) : Prop :=
  ∀ y z : W7 (GaloisField p (2 * f)), InPi0 D y → InPi0 D z → IsFF7 D y → IsFF7 D z →
    Col7 D (vXi D) y → Col7 D y z → Col7 D z (vXi D) →
      ∃ u₁ ∈ (E.ι 1).range, ∃ v₁ ∈ (E.ι 0).range, ∃ u₂ ∈ (E.ι 1).range, ∃ v₂ ∈ (E.ι 0).range,
        ∃ u₃ ∈ (E.ι 1).range, ∃ v₃ ∈ (E.ι 0).range, ∃ c₁ c₂ : GaloisField p (2 * f),
          c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ actK (u₁⁻¹ * v₁) (vXi D) = c₁ • y ∧
            actK (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂)) (vXi D) = c₂ • z ∧
              u₁⁻¹ * v₁ * (u₂⁻¹ * v₂) * (u₃⁻¹ * v₃) ∈ parab E {1}

@[expose] def PlaneMove (D : KDat (GaloisField p f) (GaloisField p (2 * f))) : Prop :=
  ∀ a b c : W7 (GaloisField p (2 * f)), IsFF7 D a → IsFF7 D b → IsFF7 D c → Col7 D a b →
    Col7 D b c → Col7 D c a → det3_7 D a b c ≠ 0 →
      ∃ g : spinGroup (quadOdd 3 (GaloisField p f)), ∃ κ : GaloisField p (2 * f), κ ≠ 0 ∧
        actK g (vXi D) = κ • a ∧ InPi0 D (actK g⁻¹ b) ∧ InPi0 D (actK g⁻¹ c)

variable (S : Setup M E D)

include S

omit S [Algebra (GaloisField p f) (GaloisField p (2 * f))] in
theorem adj_one_of_mem {a u : spinGroup (quadOdd 3 (GaloisField p f))}
    (hu : u ∈ (E.ι 1).range) :
    (phanSystem E).adj 1 (a : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ torusSub E)
      ((a * u : spinGroup (quadOdd 3 (GaloisField p f))) : _) := by
  rw [phanSystem_adj_mk]
  have : a⁻¹ * (a * u) = u := by group
  rw [this]
  exact Lsup_le_parab {1} (by rw [Lsup_singleton]; exact hu)

theorem Setup.null2_plane (hb : PlaneBase E D) (hm : PlaneMove D) (h0 : PtStep0 E)
    {gx gy gz : spinGroup (quadOdd 3 (GaloisField p f))}
    (hxy : (ptGraph E).Adj (gx : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) gy)
    (hyz : (ptGraph E).Adj (gy : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) gz)
    (hzx : (ptGraph E).Adj (gz : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) gx)
    (hdet : det3_7 D (actK gx (vXi D)) (actK gy (vXi D)) (actK gz (vXi D)) ≠ 0) :
    Null2 E h0 (.cons hxy (.cons hyz (.cons hzx .nil))) := by
  have hcxy := (S.adj_iff_col7 gx gy).1 hxy
  have hcyz := (S.adj_iff_col7 gy gz).1 hyz
  have hczx := (S.adj_iff_col7 gz gx).1 hzx
  have hffx := isFF7_actK D S.h2K gx (isFF7_vXi D S.h2K)
  have hffy := isFF7_actK D S.h2K gy (isFF7_vXi D S.h2K)
  have hffz := isFF7_actK D S.h2K gz (isFF7_vXi D S.h2K)
  obtain ⟨g, κ, hκ, hga, hyIn, hzIn⟩ := hm _ _ _ hffx hffy hffz hcxy hcyz hczx hdet
  have ha' : actK g⁻¹ (actK gx (vXi D)) = κ⁻¹ • vXi D := by
    calc actK g⁻¹ (actK gx (vXi D)) = actK g⁻¹ (κ⁻¹ • (κ • actK gx (vXi D))) := by
          rw [smul_smul, inv_mul_cancel₀ hκ, one_smul]
      _ = κ⁻¹ • vXi D := by rw [← hga, map_smul, actK_inv_actK]
  have hffy₀ := isFF7_actK D S.h2K g⁻¹ hffy
  have hffz₀ := isFF7_actK D S.h2K g⁻¹ hffz
  have h1 : Col7 D (vXi D) (actK g⁻¹ (actK gy (vXi D))) := by
    have := (col7_actK D g⁻¹ _ _).2 hcxy
    rw [ha'] at this
    have := (col7_smul D (c := κ⁻¹) (d := 1) (inv_ne_zero hκ) one_ne_zero (a := vXi D)
      (b := actK g⁻¹ (actK gy (vXi D)))).1 (by rwa [one_smul])
    exact this
  have h2' : Col7 D (actK g⁻¹ (actK gy (vXi D))) (actK g⁻¹ (actK gz (vXi D))) :=
    (col7_actK D g⁻¹ _ _).2 hcyz
  have h3 : Col7 D (actK g⁻¹ (actK gz (vXi D))) (vXi D) := by
    have := (col7_actK D g⁻¹ _ _).2 hczx
    rw [ha'] at this
    have := (col7_smul D (c := 1) (d := κ⁻¹) one_ne_zero (inv_ne_zero hκ)
      (a := actK g⁻¹ (actK gz (vXi D))) (b := vXi D)).1 (by rwa [one_smul])
    exact this
  obtain ⟨u₁, hu₁, v₁, hv₁, u₂, hu₂, v₂, hv₂, u₃, hu₃, v₃, hv₃, c₁, c₂, hc₁, hc₂, hk₁, hk₂,
    hcl⟩ := hb _ _ hyIn hzIn hffy₀ hffz₀ h1 h2' h3
  have ex : (gx : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) = (g : _) :=
    S.coset_eq_of_smul hκ hga
  have ey : (gy : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) =
      ((g * (u₁⁻¹ * v₁) : spinGroup (quadOdd 3 (GaloisField p f))) : _) :=
    S.coset_eq_of_smul hc₁ (by rw [actK_mul, hk₁, map_smul, actK_actK_inv])
  have ez : (gz : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) =
      ((g * (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂)) : spinGroup (quadOdd 3 (GaloisField p f))) : _) :=
    S.coset_eq_of_smul hc₂ (by rw [actK_mul, hk₂, map_smul, actK_actK_inv])
  have hK12 : (g : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) =
      ((g * (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂) * (u₃⁻¹ * v₃)) :
        spinGroup (quadOdd 3 (GaloisField p f))) : _) := by
    refine QuotientGroup.eq.2 ?_
    have : g⁻¹ * (g * (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂) * (u₃⁻¹ * v₃))) =
        u₁⁻¹ * v₁ * (u₂⁻¹ * v₂) * (u₃⁻¹ * v₃) := by group
    rw [this]
    exact parab_mono (Set.singleton_subset_iff.2 (by simp)) hcl
  have hclose : (phanSystem E).adj 1
      (QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹ * v₃) :
        spinGroup (quadOdd 3 (GaloisField p f)) ⧸ torusSub E) (QuotientGroup.mk g) := by
    rw [phanSystem_adj_mk]
    have : (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹ * v₃)⁻¹ * g =
        (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂) * (u₃⁻¹ * v₃))⁻¹ := by group
    rw [this]
    exact inv_mem hcl
  have hu₁' : u₁⁻¹ ∈ (E.ι 1).range := inv_mem hu₁
  have hu₂' : u₂⁻¹ ∈ (E.ι 1).range := inv_mem hu₂
  have hu₃' : u₃⁻¹ ∈ (E.ι 1).range := inv_mem hu₃
  have hm1 : (1 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := by simp
  have hP : ∀ (a : spinGroup (quadOdd 3 (GaloisField p f))),
      (phanFib E h0).P (QuotientGroup.mk a) =
        (a : spinGroup (quadOdd 3 (GaloisField p f)) ⧸ parab E {1, 2}) := fun a => rfl
  refine ⟨{0, 1}, pair_encard_le_two 0 1, QuotientGroup.mk g,
    [(1, QuotientGroup.mk (g * u₁⁻¹)), (0, QuotientGroup.mk (g * u₁⁻¹ * v₁)),
      (1, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹)),
      (0, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂)),
      (1, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹)),
      (0, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹ * v₃))],
    [(1, QuotientGroup.mk g)], ?_, ?_, IsJGallery.cons hm1 hclose IsJGallery.nil, ?_, rfl⟩
  · refine ⟨?_, [(1, QuotientGroup.mk (g * u₁⁻¹))], QuotientGroup.mk (g * u₁⁻¹ * v₁),
      [(1, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹)),
        (0, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂)),
        (1, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹)),
        (0, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹ * v₃))], rfl,
      IsJGallery.cons hm1 (adj_one_of_mem (E := E) hu₁') IsJGallery.nil,
      adj_zero_of_mem (E := E) hv₁, ?_,
      [(1, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹))],
      QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂),
      [(1, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹)),
        (0, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹ * v₃))], rfl,
      IsJGallery.cons hm1 (adj_one_of_mem (E := E) hu₂') IsJGallery.nil,
      adj_zero_of_mem (E := E) hv₂, ?_,
      [(1, QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹))],
      QuotientGroup.mk (g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹ * v₃), [], rfl,
      IsJGallery.cons hm1 (adj_one_of_mem (E := E) hu₃') IsJGallery.nil,
      adj_zero_of_mem (E := E) hv₃, ?_,
      IsJGallery.nil⟩
    · rw [hP, ex]
    · have e1 : g * u₁⁻¹ * v₁ = g * (u₁⁻¹ * v₁) := by group
      rw [hP, ey, e1]
    · have e2 : g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ = g * (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂)) := by group
      rw [hP, ez, e2]
    · have e3 : g * u₁⁻¹ * v₁ * u₂⁻¹ * v₂ * u₃⁻¹ * v₃ =
          g * (u₁⁻¹ * v₁ * (u₂⁻¹ * v₂) * (u₃⁻¹ * v₃)) := by group
      rw [hP, ex, e3, ← hK12]
  · intro i hi
    have hi' : i = 1 ∨ i = 0 ∨ i = 1 ∨ i = 0 ∨ i = 1 ∨ i = 0 := by simpa [galleryType] using hi
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i hi
    have : i = 1 := by simpa [galleryType] using hi
    rw [this]
    simp

end Plane

end CFSG.ClassicalInvolution.PhanB3.S
