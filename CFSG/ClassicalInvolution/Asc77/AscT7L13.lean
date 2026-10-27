module

public import CFSG.ClassicalInvolution.Asc77.AscT7L10
public import CFSG.ClassicalInvolution.Asc77.AscE189OrthV
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Frame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec
public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HC3
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.TwinLookup
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.ModelFacts.Orth15 QuadraticMap Matrix
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

namespace T7L

local notation "𝕄[" F "]" => Matrix (Fin 2) (Fin 2) F

section Central

variable {K : Type*} [Group K]

theorem commutator_comm_of_central {R : Subgroup K} {g : K}
    (h : ∀ r ∈ R, ⁅g, r⁆ ∈ Subgroup.center K) {r s : K} (hr : r ∈ R) (hs : s ∈ R) :
    g * ⁅r, s⁆ = ⁅r, s⁆ * g := by
  have hzr := Subgroup.mem_center_iff.mp (h r hr)
  have hzs := Subgroup.mem_center_iff.mp (h s hs)
  set zr := ⁅g, r⁆ with hzr_def
  set zs := ⁅g, s⁆ with hzs_def
  have hgr : g * r * g⁻¹ = zr * r := by simp only [hzr_def, commutatorElement_def]; group
  have hgs : g * s * g⁻¹ = zs * s := by simp only [hzs_def, commutatorElement_def]; group
  have hcc : ∀ (z a b : K), (∀ y, y * z = z * y) → ⁅z * a, b⁆ = ⁅a, b⁆ := by
    intro z a b hz
    simp only [commutatorElement_def]
    have : z * (a * b * a⁻¹) * z⁻¹ = a * b * a⁻¹ := by
      rw [← hz (a * b * a⁻¹)]
      group
    calc z * a * b * (z * a)⁻¹ * b⁻¹ = (z * (a * b * a⁻¹) * z⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [this]
  have hcc' : ∀ (z a b : K), (∀ y, y * z = z * y) → ⁅a, z * b⁆ = ⁅a, b⁆ := by
    intro z a b hz
    simp only [commutatorElement_def]
    have : z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ = a * b * a⁻¹ * b⁻¹ := by
      rw [← hz (a * b * a⁻¹ * b⁻¹)]
      group
    calc a * (z * b) * a⁻¹ * (z * b)⁻¹ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by
          rw [show a * (z * b) * a⁻¹ * (z * b)⁻¹ = (a * z) * (b * a⁻¹ * b⁻¹) * z⁻¹ by group,
            hz a]
          group
      _ = a * b * a⁻¹ * b⁻¹ := this
  have hconj : g * ⁅r, s⁆ * g⁻¹ = ⁅g * r * g⁻¹, g * s * g⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have : g * ⁅r, s⁆ * g⁻¹ = ⁅r, s⁆ := by
    rw [hconj, hgr, hgs, hcc _ _ _ hzr, hcc' _ _ _ hzs]
  calc g * ⁅r, s⁆ = (g * ⁅r, s⁆ * g⁻¹) * g := by group
    _ = ⁅r, s⁆ * g := by rw [this]

theorem commute_of_central_commutator {R : Subgroup K} (hR : R ≤ ⁅R, R⁆) {g : K}
    (h : ∀ r ∈ R, ⁅g, r⁆ ∈ Subgroup.center K) : ∀ r ∈ R, g * r = r * g := by
  have hle : ⁅R, R⁆ ≤ Subgroup.centralizer ({g} : Set K) := by
    rw [Subgroup.commutator_le]
    intro r hr s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commutator_comm_of_central h hr hs).symm
  intro r hr
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hR hr))).symm

end Central

section Frame

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}


theorem r0_mul_D_mul_r0 :
    ((r0 : SL(2, F)) : 𝕄[F]) * !![1, 0; 0, -1] * ((r0 : SL(2, F)) : 𝕄[F]) =
        !![1, 0; 0, -1] ∧
      ((r0 : SL(2, F)) : 𝕄[F]) * !![0, 1; 1, 0] *
        ((r0 : SL(2, F)) : 𝕄[F]) = !![0, 1; 1, 0] := by
  rw [coe_r0]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem conj_mul_fixed (P Q' : SL(2, F)) (D : 𝕄[F]) :
    ((P * r0 * P⁻¹ : SL(2, F)) : 𝕄[F]) *
        ((P : 𝕄[F]) * D * ((Q'⁻¹ : SL(2, F)) : 𝕄[F])) *
      ((Q' * r0 * Q'⁻¹ : SL(2, F)) : 𝕄[F]) =
    (P : 𝕄[F]) *
      (((r0 : SL(2, F)) : 𝕄[F]) * D * ((r0 : SL(2, F)) : 𝕄[F])) *
      ((Q'⁻¹ : SL(2, F)) : 𝕄[F]) := by
  have hP : ((P⁻¹ : SL(2, F)) : 𝕄[F]) * (P : 𝕄[F]) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hQ : ((Q'⁻¹ : SL(2, F)) : 𝕄[F]) * (Q' : 𝕄[F]) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  calc _ = (P : 𝕄[F]) * (((r0 : SL(2, F)) : 𝕄[F]) *
        (((P⁻¹ : SL(2, F)) : 𝕄[F]) * (P : 𝕄[F])) * D *
        (((Q'⁻¹ : SL(2, F)) : 𝕄[F]) * (Q' : 𝕄[F])) *
        ((r0 : SL(2, F)) : 𝕄[F])) * ((Q'⁻¹ : SL(2, F)) : 𝕄[F]) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP, hQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem two_le_finrank_eig_one [Finite F] [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (fr : Frame Q) {A A' : SL(2, F)}
    (hA : (A : 𝕄[F]) * A = -1)
    (hA' : (A' : 𝕄[F]) * A' = -1) :
    2 ≤ Module.finrank F ↥(eigIn (twinInv fr A A') 1 fr.span) := by
  obtain ⟨P, hP⟩ := exists_conj_r0 h2 A hA
  set C : SL(2, F) := Frame.sigmaSL A' with hCdef
  have hCC : (C : 𝕄[F]) * C = -1 := sigmaLin_sq hA'
  obtain ⟨Q', hQ'⟩ := exists_conj_r0 h2 C hCC
  obtain ⟨hD1, hD2⟩ := r0_mul_D_mul_r0 (F := F)
  have hPi : ((P⁻¹ : SL(2, F)) : 𝕄[F]) * (P : 𝕄[F]) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hQi : ((Q'⁻¹ : SL(2, F)) : 𝕄[F]) * (Q' : 𝕄[F]) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hAmat : (A : 𝕄[F]) = ((P * r0 * P⁻¹ : SL(2, F)) : 𝕄[F]) := by
    rw [hP]
  have hCmat : sigmaLin (A' : 𝕄[F]) =
      ((Q' * r0 * Q'⁻¹ : SL(2, F)) : 𝕄[F]) := by
    rw [hQ', hCdef, Frame.coe_sigmaSL]
  set Φ : 𝕄[F] → 𝕄[F] := fun D =>
    (P : 𝕄[F]) * D * ((Q'⁻¹ : SL(2, F)) : 𝕄[F]) with hΦ
  have hfix : ∀ D : 𝕄[F],
      ((r0 : SL(2, F)) : 𝕄[F]) * D * ((r0 : SL(2, F)) : 𝕄[F]) = D →
      fr.incl (Φ D) ∈ eigIn (twinInv fr A A') 1 fr.span := by
    intro D hD
    refine mem_eigIn_iff.mpr ⟨⟨Φ D, rfl⟩, ?_⟩
    rw [twinInv_incl, hAmat, hCmat, hΦ]
    simp only
    rw [conj_mul_fixed, hD, one_smul]
  have hΦlin : ∀ s t : F, ∀ D₁ D₂ : 𝕄[F],
      s • Φ D₁ + t • Φ D₂ = Φ (s • D₁ + t • D₂) := by
    intro s t D₁ D₂
    simp only [hΦ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hΦinj : ∀ D : 𝕄[F], Φ D = 0 → D = 0 := by
    intro D hD
    have h1 : ((P⁻¹ : SL(2, F)) : 𝕄[F]) * Φ D * (Q' : 𝕄[F]) = D := by
      simp only [hΦ]
      calc ((P⁻¹ : SL(2, F)) : 𝕄[F]) * ((P : 𝕄[F]) * D *
            ((Q'⁻¹ : SL(2, F)) : 𝕄[F])) * (Q' : 𝕄[F])
          = (((P⁻¹ : SL(2, F)) : 𝕄[F]) * (P : 𝕄[F])) * D *
            (((Q'⁻¹ : SL(2, F)) : 𝕄[F]) * (Q' : 𝕄[F])) := by
            simp only [Matrix.mul_assoc]
        _ = D := by rw [hPi, hQi]; simp
    rw [← h1, hD]
    simp
  have hli : LinearIndependent F ![fr.incl (Φ !![1, 0; 0, -1]), fr.incl (Φ !![0, 1; 1, 0])] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg fr.coords hst
    rw [map_add, map_smul, map_smul, Frame.coords_incl, Frame.coords_incl, map_zero] at h1
    rw [hΦlin] at h1
    have h3 := hΦinj _ h1
    have e1 := congrFun (congrFun h3 0) 0
    have e2 := congrFun (congrFun h3 0) 1
    simp at e1 e2
    exact ⟨e1, e2⟩
  have hspan : Module.finrank F ↥(Submodule.span F (Set.range ![fr.incl (Φ !![1, 0; 0, -1]),
      fr.incl (Φ !![0, 1; 1, 0])])) = 2 := by
    have := finrank_span_eq_card hli
    simpa using this
  have hle : Submodule.span F (Set.range ![fr.incl (Φ !![1, 0; 0, -1]),
      fr.incl (Φ !![0, 1; 1, 0])]) ≤ eigIn (twinInv fr A A') 1 fr.span := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hfix _ hD1
    · exact hfix _ hD2
  calc 2 = _ := hspan.symm
    _ ≤ _ := Submodule.finrank_mono hle

theorem exists_frame_fixed_by_twinInv [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hV : 7 ≤ Module.finrank F V) (fr : Frame Q)
    {A A' : SL(2, F)} (hA : (A : 𝕄[F]) * A = -1)
    (hA' : (A' : 𝕄[F]) * A' = -1) :
    ∃ F'' : Frame Q, ∀ x ∈ F''.span, twinInv fr A A' x = x := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hT := twinDatum_of_frame fr h2 hQ hA hA' hV
  have hS : PolarNondegOn Q (eigIn (twinInv fr A A') 1 fr.span ⊔ fr.perp) :=
    polarNondegOn_sup hT.nd₂ hT.ndW hT.o₂W
  have h5 : 5 ≤ Module.finrank F ↥(eigIn (twinInv fr A A') 1 fr.span ⊔ fr.perp) := by
    have hdis : Disjoint (eigIn (twinInv fr A A') 1 fr.span) fr.perp :=
      (Frame.isCompl_span_perp fr).disjoint.mono_left fun x hx => (mem_eigIn_iff.mp hx).1
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (eigIn (twinInv fr A A') 1 fr.span)
      fr.perp
    rw [hdis.eq_bot, finrank_bot] at h1
    have h2' := two_le_finrank_eig_one h2 fr hA hA'
    have h3 := Submodule.finrank_add_eq_of_isCompl (Frame.isCompl_span_perp fr)
    rw [finrank_span_eq_four] at h3
    omega
  obtain ⟨F'', hF''⟩ := exists_frame_le_of_five_le hodd hQ hS h5
  exact ⟨F'', fun x hx => hT.fix₁ x (hF'' hx)⟩

theorem twinInv_commute_La (h2 : (2 : F) ≠ 0) (fr F'' : Frame Q) {A A' : SL(2, F)}
    (hfix : ∀ x ∈ F''.span, twinInv fr A A' x = x) (B : SL(2, F)) :
    twinInv fr A A' * F''.La B = F''.La B * twinInv fr A A' :=
  (commute_La_of_scalar_on_span h2 (twinInv_mem_orthogonalGroup fr A A') (c := 1) (by ring)
    (fun x hx => by rw [hfix x hx, one_smul]) B).1

end Frame

section Spin

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

omit [DecidableEq ι] in
theorem exists_fund_comm_ab_of_frame (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hV : 7 ≤ Module.finrank F (ι → F)) {t : StatedLieTag}
    (D : UniversalRootDatum (spinGroup Q))
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) = L)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q)) (fr : Frame Q)
    {R R' : Subgroup (spinGroup Q)} (hR : R.map (spinAction Q) = fr.La.range)
    (hR' : R'.map (spinAction Q) = fr.swap.La.range) {x x' a b : spinGroup Q}
    (hθx : spinAction Q x = fr.La (-1)) (hθx' : spinAction Q x' = fr.swap.La (-1))
    (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x') :
    ∃ R'' ∈ fundamentalSubgroups t D, ∀ r ∈ R'', (a * b) * r = r * (a * b) := by
  classical
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set θ := spinAction Q with hθ
  obtain ⟨A, hA⟩ : θ a ∈ fr.La.range := hR ▸ Subgroup.mem_map_of_mem _ ha
  obtain ⟨A', hA'⟩ : θ b ∈ fr.swap.La.range := hR' ▸ Subgroup.mem_map_of_mem _ hb
  have hAA : (A : 𝕄[F]) * A = -1 := by
    have h1 : fr.La (A * A) = fr.La (-1) := by
      rw [map_mul, hA, ← map_mul, haa, hθx]
    have h3 : A * A = -1 := fr.La_injective h1
    have := congrArg (fun g : SL(2, F) => (g : 𝕄[F])) h3
    simpa using this
  have hA'A' : (A' : 𝕄[F]) * A' = -1 := by
    have h1 : fr.swap.La (A' * A') = fr.swap.La (-1) := by
      rw [map_mul, hA', ← map_mul, hbb, hθx']
    have h3 : A' * A' = -1 := fr.swap.La_injective h1
    have := congrArg (fun g : SL(2, F) => (g : 𝕄[F])) h3
    simpa using this
  obtain ⟨F'', hF''⟩ := exists_frame_fixed_by_twinInv hodd hQ hV fr hAA hA'A'
  have hu : θ (a * b) = twinInv fr A A' := by
    rw [map_mul, ← hA, ← hA']
    rfl
  obtain ⟨R'', hR'', hR''θ⟩ := hsurj F''.La.range ⟨_, IsFundamental.of_frame F''⟩
  refine ⟨R'', hR'', ?_⟩
  have hcen : ∀ r ∈ R'', ⁅a * b, r⁆ ∈ Subgroup.center (spinGroup Q) := by
    intro r hr
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, hu]
    obtain ⟨B, hB⟩ : θ r ∈ F''.La.range := hR''θ ▸ Subgroup.mem_map_of_mem _ hr
    rw [← hB]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (twinInv_commute_La h2 fr F'' hF'' B)
  exact commute_of_central_commutator (hperf R'' hR'') hcen

end Spin

end T7L

end CFSG.ClassicalInvolution.Asc77
