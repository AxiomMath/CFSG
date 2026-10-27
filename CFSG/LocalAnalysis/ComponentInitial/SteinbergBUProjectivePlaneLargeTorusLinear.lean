module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLargeTorusCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.Open LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {F : Type} [Field F] [Finite F]

theorem linear_projective_nonabelian_plane_delta_centralizes_large_torus {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (D : Subgroup (MulAut (projectiveSL p F))) (hDI : D ≤ linearAutGroup p F)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDp : ∀ x ∈ D, x ^ p = 1)
    (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (conjAut p F), ∀ B ∈ D.comap (conjAut p F), A * B = B * A) :
    D ⊓ (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range ≠ ⊥ ∧
      ∀ d ∈ D ⊓ (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range, d ≠ 1 →
        ∃ U : Subgroup (MulAut (projectiveSL p F)),
          U ≤ linearAutGroup p F ⊓ Subgroup.centralizer {d} ∧
          (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ (∀ x ∈ U, x ^ p = 1) ∧
          Nat.card U = p ^ (p - 1) ∧
          (U.subgroupOf (linearAutGroup p F ⊓ Subgroup.centralizer {d})).Characteristic ∧
          (U.subgroupOf (Subgroup.centralizer {d})).Normal ∧ d ∈ U ∧
          (∃ k, p - 2 ≤ k ∧ Nat.card (U ⊓ (MulAut.conj : projectiveSL p F →*
            MulAut (projectiveSL p F)).range : Subgroup (MulAut (projectiveSL p F))) = p ^ k) ∧
          (∀ x ∈ localDelta p ⊤ D, ∀ u ∈ U, x * u = u * x) ∧
          ∀ H : Subgroup (MulAut (projectiveSL p F)),
            (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range ≤ H → D ≤ H →
            ∀ x ∈ localDelta p H D, ∀ v ∈ (U ⊓ (MulAut.conj : projectiveSL p F →*
              MulAut (projectiveSL p F)).range : Subgroup (MulAut (projectiveSL p F))),
              x * v = v * x := by
  classical
  have := finite_mulAut_projectiveSL (F := F) p
  have hp3 : 3 ≤ p := by omega
  set Inn := (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range with hInn
  have hInnN : Inn.Normal := inner_normal _
  have hcomm := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup
    (K := F) hp3
  have hIN : (conjAut p F).range.Normal := by
    rw [← linearAutGroup_eq_range]
    exact normal_of_commutator_mem hcomm
  have hDL : D ≤ (conjAut p F).range := by
    rw [← linearAutGroup_eq_range]
    exact hDI
  have hDInn : D ⊓ Inn ≠ ⊥ := by
    obtain ⟨hcyc, -⟩ := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_diagonal_outer
      (K := F) (n := p) (by omega)
    have hmap : D.map (QuotientGroup.mk' (inner (projectiveSL p F))) ≤
        ((QuotientGroup.mk' (inner (projectiveSL p F))).comp (conjAut p F)).range := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨A, rfl⟩ := hDL hx
      exact ⟨A, rfl⟩
    have := Subgroup.isCyclic_of_le hmap
    obtain ⟨d, hdD, hd1, hdker⟩ := exists_ne_one_ker_of_isCyclic hp hDp hcard _ this
    intro hbot
    have hdInn : d ∈ Inn := (QuotientGroup.eq_one_iff d).1 hdker
    have hmem : d ∈ D ⊓ Inn := Subgroup.mem_inf.2 ⟨hdD, hdInn⟩
    rw [hbot] at hmem
    exact hd1 hmem
  refine ⟨hDInn, fun d hd hd1 => ?_⟩
  obtain ⟨hdD, ⟨s, hs⟩⟩ := Subgroup.mem_inf.1 hd
  obtain ⟨g, rfl⟩ := proj_surjective p F s
  have hAd : conjAut p F (MonoidHom.id (GL (Fin p) F) (SpecialLinearGroup.toGL g)) = d := by
    rw [MonoidHom.id_apply, conjAut_toGL, hs]
  have hAdet : ((MonoidHom.id (GL (Fin p) F) (SpecialLinearGroup.toGL g) : GL (Fin p) F) :
      Matrix (Fin p) (Fin p) F).det = 1 := g.2
  have hJ : ∀ y : ProjGenLinGroup (Fin p) F, y ∈ (projHom (MonoidHom.id (GL (Fin p) F))).range :=
    fun y => by
      obtain ⟨M, rfl⟩ := mk_surjective y
      exact ⟨M, rfl⟩
  have hframe : ∀ (P : GL (Fin p) F) (ζ : F) (B : GL (Fin p) F), IsPrimitiveRoot ζ p →
      ((MonoidHom.id (GL (Fin p) F) (SpecialLinearGroup.toGL g) : GL (Fin p) F) :
        Matrix (Fin p) (Fin p) F) * (MonoidHom.id (GL (Fin p) F) B : GL (Fin p) F) =
        ζ • (((MonoidHom.id (GL (Fin p) F) B : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *
          (MonoidHom.id (GL (Fin p) F) (SpecialLinearGroup.toGL g) : GL (Fin p) F)) →
      ((MonoidHom.id (GL (Fin p) F) (SpecialLinearGroup.toGL g) : GL (Fin p) F) :
        Matrix (Fin p) (Fin p) F) = (P : Matrix (Fin p) (Fin p) F) *
          diagonal (fun i : Fin p => ζ ^ (i : ℕ)) *
            ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) →
      ∃ P' : GL (Fin p) F, ((MonoidHom.id (GL (Fin p) F) (SpecialLinearGroup.toGL g) :
          GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = (P' : Matrix (Fin p) (Fin p) F) *
            diagonal (fun i : Fin p => ζ ^ (i : ℕ)) *
              ((P'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) ∧
        omegaTorus P' ≤ (projHom (MonoidHom.id (GL (Fin p) F))).range ∧
        ∀ y ∈ detOneTorus P', ∀ hy : y ∈ (projHom (MonoidHom.id (GL (Fin p) F))).range,
          rangeLift (conjAut p F) (MonoidHom.id _) (conjAut_eq_one_iff hp3) ⟨y, hy⟩ ∈ Inn := by
    intro P ζ _ hζ _ hP
    refine ⟨P, hP, fun y _ => hJ y, fun y hy hyJ => ?_⟩
    obtain ⟨f, hf, rfl⟩ := mem_detOneTorus hy
    set X := P * TauCeti.diagGL (fun i => (f i : Fˣ)) * P⁻¹
    have hXdet : (X : Matrix (Fin p) (Fin p) F).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, det_conj P.isUnit,
        TauCeti.diagGL_coe, det_diagonal]
      exact hf
    have hlift : (⟨mk X, hyJ⟩ : (projHom (MonoidHom.id (GL (Fin p) F))).range) =
        (projHom (MonoidHom.id (GL (Fin p) F))).rangeRestrict X := rfl
    rw [hlift, rangeLift_apply]
    set g' : SpecialLinearGroup (Fin p) F := ⟨X, hXdet⟩
    have hg' : SpecialLinearGroup.toGL g' = X := Units.ext rfl
    rw [← hg', conjAut_toGL]
    exact ⟨_, rfl⟩
  obtain ⟨U, hUC, hUab, hUp, hUcard, hchar, hnormal, hdU, hVrank, hΔ, hΔH⟩ :=
    large_torus_of_frame hp hp5 (conjAut p F) (MonoidHom.id _) Function.injective_id
      (conjAut_eq_one_iff hp3) Inn hInnN hIN D hDL hDab hDp hcard hna hdD hd1 hAd hAdet hframe
  rw [← linearAutGroup_eq_range] at hUC hchar
  exact ⟨U, hUC, hUab, hUp, hUcard, hchar, hnormal, hdU, hVrank, hΔ, hΔH⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
