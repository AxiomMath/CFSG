module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateClass
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLargeTorusLinear
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXOneSpareTorus
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCyclePerm

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.Open LinearFlag CFSG.LocalAnalysis.GorensteinLyons
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)

variable {F : Type} [Field F] [Finite F]

theorem conj_injective_projectiveSL {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  obtain ⟨g, rfl⟩ := proj_surjective n F s
  rw [← conjAut_toGL, conjAut_eq_one_iff hn] at hs
  obtain ⟨u, hu⟩ := hs
  have hgu : (g : Matrix (Fin n) (Fin n) F) = scalar (Fin n) (u : F) := by
    have h1 := congrArg (fun M : GL (Fin n) F => (M : Matrix (Fin n) (Fin n) F)) hu
    simpa [GeneralLinearGroup.coe_scalar] using h1
  have hun : u ^ n = 1 := by
    apply Units.ext
    have h1 := g.2
    rw [hgu, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact (QuotientGroup.eq_one_iff g).2 ⟨u, hun, hgu⟩

omit [Finite F] in
@[expose] noncomputable def linearCoordinates (n : ℕ) (P : GL (Fin n) F) :
    projectiveSL n F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) F :=
  (conjAut n F P⁻¹).trans (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n F))

omit [Finite F] in
theorem linearCoordinates_proj {n : ℕ} (P : GL (Fin n) F) (s : SpecialLinearGroup (Fin n) F) :
    linearCoordinates n P (proj n F s) =
      (QuotientGroup.mk (slConjugation n F P⁻¹ s) :
        Matrix.ProjectiveSpecialLinearGroup (Fin n) F) := by
  rw [linearCoordinates, MulEquiv.trans_apply, conjAut_proj]
  rfl

omit [Finite F] in
theorem toGL_diagSLHom {n : ℕ} (v : prodOneUnits F n) :
    SpecialLinearGroup.toGL (diagSLHom F n v) = TauCeti.diagGL (v : Fin n → Fˣ) := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_diagSLHom, TauCeti.diagGL_coe]

theorem linear_projective_nonabelian_plane_delta_centralizes_coordinate_torus {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (D : Subgroup (MulAut (projectiveSL p F)))
    (hDI : D ≤ linearAutGroup p F) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (conjAut p F), ∀ B ∈ D.comap (conjAut p F), A * B = B * A) :
    (∀ A : GL (Fin p) F, conjAut p F A = 1 ↔ ∃ u : Fˣ, A = GeneralLinearGroup.scalar (Fin p) u) ∧
      Function.Injective (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)) ∧
      D ⊓ (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range ≠ ⊥ ∧
      ∀ d ∈ D ⊓ (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range, d ≠ 1 →
        ∃ (ζ : Fˣ) (P : GL (Fin p) F) (g : SpecialLinearGroup (Fin p) F)
          (T U : Subgroup (MulAut (projectiveSL p F))) (w : MulAut (projectiveSL p F))
          (c : Fin (p - 2) → projectiveSL p F)
          (θ : projectiveSL p F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin p) F),
          IsPrimitiveRoot ζ p ∧
          (g : Matrix (Fin p) (Fin p) F) = (P : Matrix (Fin p) (Fin p) F) *
            diagonal (fun i : Fin p => (ζ : F) ^ (i : ℕ)) *
              ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) ∧
          MulAut.conj (proj p F g) = d ∧
          (∀ s : SpecialLinearGroup (Fin p) F, ∃ s' : SpecialLinearGroup (Fin p) F,
            (s' : Matrix (Fin p) (Fin p) F) = ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *
              (s : Matrix (Fin p) (Fin p) F) * (P : Matrix (Fin p) (Fin p) F) ∧
            θ (proj p F s) =
              (QuotientGroup.mk s' : Matrix.ProjectiveSpecialLinearGroup (Fin p) F)) ∧
          (∃ g₀ : SpecialLinearGroup (Fin p) F,
            (g₀ : Matrix (Fin p) (Fin p) F) = diagonal (fun i : Fin p => (ζ : F) ^ (i : ℕ)) ∧
            θ (proj p F g) =
              (QuotientGroup.mk g₀ : Matrix.ProjectiveSpecialLinearGroup (Fin p) F)) ∧
          (∀ α, α ∈ T ↔ ∃ x : Fin p → Fˣ, conjAut p F (P * TauCeti.diagGL x * P⁻¹) = α) ∧
          (∀ α, α ∈ U ↔ α ∈ T ∧ α ^ p = 1) ∧
          w = conjAut p F (P * cycleGL p F * P⁻¹) ∧
          (∀ i : Fin (p - 2), ∃ gi : SpecialLinearGroup (Fin p) F,
            (gi : Matrix (Fin p) (Fin p) F) = (P : Matrix (Fin p) (Fin p) F) *
              diagonal (fun j => ((torusVec ζ ⟨i, by omega⟩ ⟨p - 2, by omega⟩ j : Fˣ) : F)) *
                ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) ∧
            c i = proj p F gi) ∧
          T ≤ linearAutGroup p F ⊓ Subgroup.centralizer {d} ∧
          (T.subgroupOf (linearAutGroup p F ⊓ Subgroup.centralizer {d})).Normal ∧
          w ∈ linearAutGroup p F ⊓ Subgroup.centralizer {d} ∧ orderOf w = p ∧
          T ⊓ Subgroup.zpowers w = ⊥ ∧
          T ⊔ Subgroup.zpowers w = linearAutGroup p F ⊓ Subgroup.centralizer {d} ∧
          (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ (∀ x ∈ U, x ^ p = 1) ∧
          Nat.card U = p ^ (p - 1) ∧ d ∈ U ∧
          (U.subgroupOf (linearAutGroup p F ⊓ Subgroup.centralizer {d})).Characteristic ∧
          (U.subgroupOf (Subgroup.centralizer {d})).Normal ∧
          (∃ k, p - 2 ≤ k ∧ Nat.card (U ⊓ (MulAut.conj : projectiveSL p F →*
            MulAut (projectiveSL p F)).range : Subgroup (MulAut (projectiveSL p F))) = p ^ k) ∧
          (∀ x ∈ Subgroup.closure (Set.range c), ∀ y ∈ Subgroup.closure (Set.range c),
            x * y = y * x) ∧
          (∀ x ∈ Subgroup.closure (Set.range c), x ^ p = 1) ∧
          Nat.card (Subgroup.closure (Set.range c)) = p ^ (p - 2) ∧
          (Subgroup.closure (Set.range c)).map
              (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)) ≤
            U ⊓ (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range ∧
          (Subgroup.closure (Set.range c)).map θ.toMonoidHom =
            Subgroup.closure (Set.range (linearTorusFamily F p (p - 2) (by omega) ζ)) ∧
          (∀ x ∈ localDelta p ⊤ D, ∀ u ∈ U, x * u = u * x) ∧
          ∀ H : Subgroup (MulAut (projectiveSL p F)),
            (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)).range ≤ H → D ≤ H →
            (∀ x ∈ localDelta p H D, ∀ v ∈ (U ⊓ (MulAut.conj : projectiveSL p F →*
              MulAut (projectiveSL p F)).range : Subgroup (MulAut (projectiveSL p F))),
              x * v = v * x) ∧
            ∀ x ∈ localDelta p H D, ∀ a ∈ Subgroup.closure (Set.range c), x a = a := by
  classical
  have := finite_mulAut_projectiveSL (F := F) p
  have hp3 : 3 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
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
  have hinj := conj_injective_projectiveSL (F := F) hp3
  obtain ⟨hDInn, -⟩ :=
    linear_projective_nonabelian_plane_delta_centralizes_large_torus hp hp5 D hDI hDab hDp hcard hna
  refine ⟨conjAut_eq_one_iff hp3, hinj, hDInn, fun d hd hd1 => ?_⟩
  obtain ⟨hdD, ⟨s, hs⟩⟩ := Subgroup.mem_inf.1 hd
  obtain ⟨g, rfl⟩ := proj_surjective p F s
  have hker : ∀ x, conjAut p F x = 1 ↔
      ∃ u : Fˣ, MonoidHom.id (GL (Fin p) F) x = GeneralLinearGroup.scalar (Fin p) u :=
    conjAut_eq_one_iff hp3
  have hAd : conjAut p F (MonoidHom.id (GL (Fin p) F) (SpecialLinearGroup.toGL g)) = d := by
    rw [MonoidHom.id_apply, conjAut_toGL, hs]
  have hAdet : ((MonoidHom.id (GL (Fin p) F) (SpecialLinearGroup.toGL g) : GL (Fin p) F) :
      Matrix (Fin p) (Fin p) F).det = 1 := g.2
  obtain ⟨ζ, -, P, hζ, -, hP⟩ := exists_plane_frame hp hp2 (conjAut p F) (MonoidHom.id _)
    Function.injective_id hker D hDL hDab hDp hcard hna hdD hd1 hAd hAdet
  have hJ : ∀ y : ProjGenLinGroup (Fin p) F, y ∈ (projHom (MonoidHom.id (GL (Fin p) F))).range :=
    fun y => by
      obtain ⟨M, rfl⟩ := mk_surjective y
      exact ⟨M, rfl⟩
  have hιM : ∀ (M : GL (Fin p) F) (hM : mk M ∈ (projHom (MonoidHom.id (GL (Fin p) F))).range),
      rangeLift (conjAut p F) (MonoidHom.id _) hker ⟨mk M, hM⟩ = conjAut p F M := by
    intro M hM
    have h1 : (⟨mk M, hM⟩ : (projHom (MonoidHom.id (GL (Fin p) F))).range) =
        (projHom (MonoidHom.id (GL (Fin p) F))).rangeRestrict M := rfl
    rw [h1, rangeLift_apply]
  have hWinn : ∀ y ∈ detOneTorus P, ∀ hy : y ∈ (projHom (MonoidHom.id (GL (Fin p) F))).range,
      rangeLift (conjAut p F) (MonoidHom.id _) hker ⟨y, hy⟩ ∈ Inn := by
    intro y hy hyJ
    obtain ⟨f, hf, rfl⟩ := mem_detOneTorus hy
    have hXdet : ((P * TauCeti.diagGL (fun i => (f i : Fˣ)) * P⁻¹ : GL (Fin p) F) :
        Matrix (Fin p) (Fin p) F).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, det_conj P.isUnit,
        TauCeti.diagGL_coe, det_diagonal]
      exact hf
    rw [hιM]
    exact ⟨proj p F ⟨_, hXdet⟩,
      (conjAut_toGL ⟨_, hXdet⟩).symm.trans (congrArg (conjAut p F) (Units.ext rfl))⟩
  obtain ⟨hUC, hUab, hUp, hUcard, hchar, hnormal, hdU, hVrank, hWU, hΔ, hΔH⟩ :=
    large_torus_of_given_frame hp hp5 (conjAut p F) (MonoidHom.id _) hker Inn hInnN hIN D hdD hd1
      hAd hζ P hP (fun y _ => hJ y) hWinn
  obtain ⟨hΩ, hTC, hTn, hwC, hword, hinf, hsup⟩ :=
    coordinate_torus_of_given_frame hp (conjAut p F) (MonoidHom.id _) hker hAd hζ P hP
      (cycleGL p F) (cycleGL_mul_diagonal hζ.pow_eq_one) cycleGL_pow (hJ _)
  rw [hιM] at hwC hword hinf hsup
  rw [← linearAutGroup_eq_range] at hUC hchar hTC hTn hwC hsup
  set ζu : Fˣ := Units.mk0 ζ (hζ.ne_zero hp.ne_zero) with hζudef
  have hζu : IsPrimitiveRoot ζu p := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hζval : (fun i : Fin p => (ζu : F) ^ (i : ℕ)) = fun i : Fin p => ζ ^ (i : ℕ) := rfl
  set gi : Fin (p - 2) → SpecialLinearGroup (Fin p) F := fun i =>
    slConjugation p F P (diagSLHom F p
      ⟨torusVec ζu ⟨i, by omega⟩ ⟨p - 2, by omega⟩, torusVec_mem_prodOneUnits ζu _ _⟩) with hgi
  set c : Fin (p - 2) → projectiveSL p F := fun i => proj p F (gi i) with hc
  have hconjc : ∀ i, MulAut.conj (c i) = conjAut p F
      (P * TauCeti.diagGL (torusVec ζu ⟨i, by omega⟩ ⟨p - 2, by omega⟩) * P⁻¹) := by
    intro i
    rw [hc, ← conjAut_toGL, hgi, toGL_slConjugation, toGL_diagSLHom]
  have hcU : ∀ i, MulAut.conj (c i) ∈ frameTorus (conjAut p F) (MonoidHom.id _) hker P ⊓ Inn := by
    intro i
    rw [hconjc, ← hιM _ (hJ _)]
    exact hWU _ (torusHom_torusVec_mem_detOneTorus P hζu.pow_eq_one _ _) (hJ _)
  have hAUInn : (Subgroup.closure (Set.range c)).map
      (MulAut.conj : projectiveSL p F →* MulAut (projectiveSL p F)) ≤
        frameTorus (conjAut p F) (MonoidHom.id _) hker P ⊓ Inn := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hcU i
  set θ := linearCoordinates p P
  have hθc : ∀ i, θ (c i) = linearTorusFamily F p (p - 2) (by omega) ζu i := by
    intro i
    rw [hc, linearCoordinates_proj, hgi, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, MulAut.one_apply]
    rfl
  have hθA : (Subgroup.closure (Set.range c)).map θ.toMonoidHom =
      Subgroup.closure (Set.range (linearTorusFamily F p (p - 2) (by omega) ζu)) := by
    rw [map_closure_range]
    congr 2
    funext i
    exact hθc i
  have hZ : (MonoidHom.id (Matrix.ProjectiveSpecialLinearGroup (Fin p) F)).ker ≤
      Subgroup.center _ := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 Function.injective_id]
    exact bot_le
  obtain ⟨hEA, hEcard, -⟩ := linear_torus_lift_conclusions.{0, 0, 0} hp2 (n := p) (m := p - 2)
    (by omega) F
    (Matrix.ProjectiveSpecialLinearGroup (Fin p) F) (MonoidHom.id _) Function.surjective_id hZ ζu
    hζu.eq_orderOf.symm
  have hAel := elementary_of_map θ.toMonoidHom θ.injective
    (E := Subgroup.closure (Set.range c)) (p := p)
    (by
      rw [hθA]
      intro x hx y hy
      exact congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (by
      rw [hθA]
      intro x hx
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx)
  have hAcard : Nat.card (Subgroup.closure (Set.range c)) = p ^ (p - 2) := by
    rw [← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective, hθA, hEcard]
  refine ⟨ζu, P, g, frameFullTorus (conjAut p F) (MonoidHom.id _) hker P,
    frameTorus (conjAut p F) (MonoidHom.id _) hker P, conjAut p F (P * cycleGL p F * P⁻¹), c, θ,
    hζu, hP, hs, ?_, ?_, ?_, hΩ, rfl, ?_, hTC, hTn, hwC, hword, hinf, hsup, hUab, hUp, hUcard,
    hdU, hchar, hnormal, hVrank, hAel.1, hAel.2, hAcard, hAUInn, hθA, hΔ, fun H hInnH hDH =>
      ⟨hΔH H hInnH hDH, fun x hx a ha => apply_eq_of_commute_conj hinj
        (hΔH H hInnH hDH x hx _ (hAUInn ⟨a, ha, rfl⟩))⟩⟩
  ·
    intro s'
    refine ⟨slConjugation p F P⁻¹ s', ?_,
      linearCoordinates_proj P s'⟩
    rw [coe_slConjugation, inv_inv]
  ·
    refine ⟨slConjugation p F P⁻¹ g, ?_, linearCoordinates_proj P g⟩
    have hg : (g : Matrix (Fin p) (Fin p) F) = (P : Matrix (Fin p) (Fin p) F) *
        diagonal (fun i : Fin p => ζ ^ (i : ℕ)) *
          ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := hP
    have hPP : ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * P = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [coe_slConjugation, inv_inv, hg, hζval]
    simp only [Matrix.mul_assoc, hPP, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  ·
    intro α
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 hj
      refine ⟨x, ?_⟩
      rw [← hιM _ (hJ _)]
      congr 1
      exact Subtype.ext hx
    · rintro ⟨x, rfl⟩
      rw [← hιM _ (hJ _)]
      exact ⟨_, Subgroup.mem_subgroupOf.2 ⟨x, rfl⟩, rfl⟩
  ·
    intro i
    refine ⟨gi i, ?_, rfl⟩
    rw [hgi]
    simp only
    rw [coe_slConjugation, coe_diagSLHom]

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
