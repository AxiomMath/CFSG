module
public import CFSG.LocalAnalysis.StandardType.GGOriginalCoefficientSquare
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OrigCoverSCAction
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux1
public import CFSG.LieType.Steinberg.Isogeny.E6Algebraic
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6MinusculeFixedField

public noncomputable section
namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.SeitzReduction.F4Pilot
set_option allowUnsafeReducibility true in
attribute [local reducible] TwistTag.tag langTag

theorem e6FieldEquivTransport_eq_minBC
    {F K : Type} [Field F] [Field K] (η : F ≃+* K) :
    (RCKRP.rckTw78_Tmin η e6Data e6Data_valid).toMonoidHom =
      minBC e6Data_valid η.toRingHom := by
  apply MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid F)
  rintro _ ⟨i, c, rfl | rfl⟩
  · rw [minBC_xm_single]
    apply Subtype.ext
    exact RCKRP.rckTw78_endUnitMap_xu η e6Data e6Data_valid (Pi.single i 1) c
  · rw [minBC_xm_neg_single]
    apply Subtype.ext
    exact RCKRP.rckTw78_endUnitMap_xu η e6Data e6Data_valid (-Pi.single i 1) c

set_option linter.style.haveILetI false in
theorem TwE6CoverData.exists_original_recipe_source_square
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n) :
    letI := D.fieldK
    letI := D.finiteK
    ∀ ι : D.K ≃+* actualQuadraticSubfield D.lab.n,
    ∃ (η : GaloisField 2 (2 * D.lab.n) ≃+* D.K)
      (T : twistedE6Group 2 D.lab.n ≃* fixedGroup D.K D.σ.toRingHom),
      ((actualQuadraticSubfield D.lab.n).subtype.comp ι.toRingHom).comp η.toRingHom =
        ggRatEmb (2 * D.lab.n) ∧
      (∀ u : twistedE6Group 2 D.lab.n,
        minBC e6Data_valid ((actualQuadraticSubfield D.lab.n).subtype.comp ι.toRingHom)
          (T u : e6Data_valid.minGroup D.K) =
        minBC e6Data_valid (ggRatEmb (2 * D.lab.n))
          (u : e6Data_valid.minGroup (GaloisField 2 (2 * D.lab.n)))) ∧
      ∀ u : twistedE6Group 2 D.lab.n,
        baseChangeGL ((actualQuadraticSubfield D.lab.n).subtype.comp ι.toRingHom)
          ((D.ψ (D.scMap hn3 (T u)) : twistedE6RootGroup D.K D.σ) : ModGL Tag.E6 D.K) =
        ggIotaK .twistedE6 0 D.lab.n D.hn u := by
  letI := D.fieldK
  letI := D.finiteK
  intro ι
  obtain ⟨η, hη⟩ := exists_original_coefficient_square D.hn ι
  have hθ : ∀ c, D.σ (η c) = η (frobQ 2 D.lab.n c) := by
    intro c
    rw [D.hσ, frobQ_apply, map_pow]
  let T : twistedE6Group 2 D.lab.n ≃* fixedGroup D.K D.σ.toRingHom :=
    ((RCKRP.rckTw78_Tmin η e6Data e6Data_valid).subgroupMap
      (fixedGroup (GaloisField 2 (2 * D.lab.n)) (frobQ 2 D.lab.n))).trans
      (MulEquiv.subgroupCongr (RCKRP.rckTw78_fixedGroup_map η
        (frobQ 2 D.lab.n) D.σ.toRingHom hθ))
  let fK := (actualQuadraticSubfield D.lab.n).subtype.comp ι.toRingHom
  have hT (u : twistedE6Group 2 D.lab.n) :
      (T u : e6Data_valid.minGroup D.K) =
      minBC e6Data_valid η.toRingHom
        (u : e6Data_valid.minGroup (GaloisField 2 (2 * D.lab.n))) := by
    change RCKRP.rckTw78_Tmin η e6Data e6Data_valid
      (u : e6Data_valid.minGroup (GaloisField 2 (2 * D.lab.n))) = _
    exact congrArg (fun f => f (u : e6Data_valid.minGroup (GaloisField 2 (2 * D.lab.n))))
      (e6FieldEquivTransport_eq_minBC η)
  have hmin (u : twistedE6Group 2 D.lab.n) :
      minBC e6Data_valid fK (T u : e6Data_valid.minGroup D.K) =
      minBC e6Data_valid (ggRatEmb (2 * D.lab.n))
        (u : e6Data_valid.minGroup (GaloisField 2 (2 * D.lab.n))) := by
    rw [hT]
    have h := congrArg (fun f => f (u : e6Data_valid.minGroup
      (GaloisField 2 (2 * D.lab.n)))) (minBC_comp e6Data_valid η.toRingHom fK)
    have hη' : fK.comp η.toRingHom = ggRatEmb (2 * D.lab.n) := hη
    simpa only [MonoidHom.comp_apply, hη'] using h
  refine ⟨η, T, hη, hmin, ?_⟩
  intro u
  calc
    _ = e6ScToBar D.K fK (T u : e6Data_valid.minGroup D.K) := by
      rw [(D.scMap_spec hn3).2.1]
      change baseChangeGL fK
        (((twistedIsogenyC D.hn D.hK D.σ.toRingHom (fun c => D.hσ c)) (T u)) :
          ModGL TwistTag.E6.tag D.K) = _
      rw [coe_twistedIsogenyC D.hn D.hK D.σ.toRingHom (fun c => D.hσ c) (T u)]
      rfl
    _ = e6IsogenyAlgebraic (minBC e6Data_valid fK
        (T u : e6Data_valid.minGroup D.K)) :=
      (e6IsogenyAlgebraic_minBC D.K fK _).symm
    _ = _ := by
      rw [hmin]
      exact (ggIotaK_twistedE6_eq_isogeny_minBC 0 D.lab.n D.hn u).symm

set_option linter.style.haveILetI false in
theorem TwE6CoverData.psi_kernel_eq_scMap_center_image
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n) :
    letI := D.fieldK
    letI := D.finiteK
    D.ψ.ker = (Subgroup.center ↥(fixedGroup D.K D.σ.toRingHom)).map (D.scMap hn3) := by
  letI := D.fieldK
  letI := D.finiteK
  ext x
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := (D.scMap_spec hn3).1 x
    refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
    rw [← ker_twistedIsogenyC D.hn D.hK D.σ.toRingHom D.hσ]
    change twistedIsogenyC D.hn D.hK D.σ.toRingHom D.hσ u = 1
    rw [← (D.scMap_spec hn3).2.1]
    exact hx
  · rintro ⟨u, hu, rfl⟩
    change D.ψ (D.scMap hn3 u) = 1
    rw [(D.scMap_spec hn3).2.1]
    apply MonoidHom.mem_ker.mp
    rw [ker_twistedIsogenyC D.hn D.hK D.σ.toRingHom D.hσ]
    exact hu

set_option linter.style.haveILetI false in
theorem TwE6CoverData.psi_odd_kernel
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n) :
    letI := D.fieldK
    letI := D.finiteK
    Odd (Nat.card D.ψ.ker) := by
  letI := D.fieldK
  letI := D.finiteK
  have : Finite ↥(fixedGroup D.K D.σ.toRingHom) := by
    have : Finite (Module.End D.K (Fin e6Data.d →₀ D.K)) := Module.finite_of_finite D.K
    infer_instance
  have hZ3 : Nat.card (Subgroup.center ↥(fixedGroup D.K D.σ.toRingHom)) ∣ 3 := by
    rw [(TwistedE6Closed.card_center_fixedGroup D.hK D.hσ).1]
    exact Nat.gcd_dvd_left 3 _
  have h3 : Nat.card D.ψ.ker ∣ 3 := by
    rw [D.psi_kernel_eq_scMap_center_image hn3]
    exact (Subgroup.card_map_dvd _ _).trans hZ3
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · simp only [h]; decide
  · simp only [h]; decide

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
