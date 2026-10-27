module

public import CFSG.ClassicalInvolution.RouteD.TWS6D4V
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleWitt
public import CFSG.ClassicalInvolution.RouteD.GapsFrSpin
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Frames

theorem exists_frame_in_perp_plus4 {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (F₁ : OFrame (quadPlus 4 F)) : ∃ G : OFrame (quadPlus 4 F), G.span ≤ F₁.perp := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  exact CFSG.ClassicalInvolution.RouteD.Exotic.exists_frame_in_perp_of_isHypFam (le_refl 4)
    (plusFrame (K := F) (n := 4) (by norm_num)).vec
    (CFSG.ClassicalInvolution.RouteD.Gaps.isHypFam_hypFrame _) F₁

end Frames

section Context

structure SpinCtx8 (t : StatedLieTag) {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    (Q : QuadraticForm F (ι → F)) (D : UniversalRootDatum (spinGroup Q)) : Prop where
  hodd : Odd (Nat.card F)
  h5 : 5 ≤ Nat.card F
  hQ : (polarBilin Q).Nondegenerate
  hrange : (spinAction Q).range = elementaryGroup Q
  perfect : Group.IsPerfect (spinGroup Q)
  hZ : CenterScalar Q
  hV : Module.finrank F (ι → F) = 8
  hfr : ∀ F₁ : OFrame Q, ∃ G : OFrame Q, G.span ≤ F₁.perp
  hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q
  hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) = L
  hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆
  hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1

variable {t : StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
  {Q : QuadraticForm F (ι → F)} {D : UniversalRootDatum (spinGroup Q)}

theorem SpinCtx8.hinj (c : SpinCtx8 t Q D) {R : Subgroup (spinGroup Q)}
    (hR : R ∈ fundamentalSubgroups t D) : ∀ r ∈ R, spinAction Q r = 1 → r = 1 := by
  have := c.perfect
  have hker := ker_spinAction_le_center Q
  exact injOn_of_ker_le_center hker fun r hr hcen =>
    c.hnc R hR r hr (mem_center_of_commutators_central fun y => by
      have := hcen y
      exact this)

theorem SpinCtx8.sq_eq_one (c : SpinCtx8 t Q D) {R : Subgroup (spinGroup Q)}
    (hR : R ∈ fundamentalSubgroups t D) {y : spinGroup Q} (hy : y ∈ R)
    (hcy : ∀ r ∈ R, y * r = r * y) : y * y = 1 :=
  sq_eq_one_of_central_fund (c.hcorr R hR) (c.hinj hR) hy hcy

end Context

section Transport

variable {K : Type*} [Group K]

theorem commutes_map_equiv (σ : K ≃* K) {A B : Subgroup K} :
    Commutes (A.map σ.toMonoidHom) (B.map σ.toMonoidHom) ↔ Commutes A B := by
  constructor
  · intro h a ha b hb
    have := h (σ a) ⟨a, ha, rfl⟩ (σ b) ⟨b, hb, rfl⟩
    exact σ.injective (by rw [map_mul, map_mul]; exact this)
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show σ a * σ b = σ b * σ a
    rw [← map_mul, ← map_mul, h a ha b hb]

theorem map_mem_center (σ : K ≃* K) {g : K} (hg : g ∈ Subgroup.center K) :
    σ g ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at hg ⊢
  intro y
  obtain ⟨y', rfl⟩ := σ.surjective y
  rw [← map_mul, ← map_mul, hg y']

theorem map_map_symm_equiv (σ : K ≃* K) (A : Subgroup K) :
    (A.map σ.toMonoidHom).map σ.symm.toMonoidHom = A := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    simpa using ha
  · intro hy
    exact ⟨σ y, ⟨y, hy, rfl⟩, by simp⟩

theorem map_datum_equiv {t : StatedLieTag} {M : LieUniversal} {R R' : Subgroup M.K}
    {x x' : M.K} (hd : TwinDatumOn t M R R' x x') (σ : M.K ≃* M.K)
    (hσ : ∀ R ∈ fundamentalSubgroups t M.D, R.map σ.toMonoidHom ∈ fundamentalSubgroups t M.D) :
    TwinDatumOn t M (R.map σ.toMonoidHom) (R'.map σ.toMonoidHom) (σ x) (σ x') where
  mem := hσ R hd.mem
  mem' := hσ R' hd.mem'
  ne := fun h => hd.ne (Subgroup.map_injective σ.injective h)
  comm := (commutes_map_equiv σ).mpr hd.comm
  hx := ⟨x, hd.hx, rfl⟩
  hx' := ⟨x', hd.hx', rfl⟩
  cx := by
    rintro _ ⟨r, hr, rfl⟩
    show σ x * σ r = σ r * σ x
    rw [← map_mul, ← map_mul, hd.cx r hr]
  cx' := by
    rintro _ ⟨r, hr, rfl⟩
    show σ x' * σ r = σ r * σ x'
    rw [← map_mul, ← map_mul, hd.cx' r hr]
  nx := fun h => hd.nx (σ.injective (by rw [h, map_one]))
  nx' := fun h => hd.nx' (σ.injective (by rw [h, map_one]))
  same := by
    have := map_mem_center σ hd.same
    simpa [map_mul, map_inv] using this

end Transport

section D4

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]

theorem spinCtx8_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    SpinCtx8 .POmegaPlus (quadPlus 4 (GaloisField p f))
      (plusDatum 4 (GaloisField p f) (by norm_num)) := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hn3), R ≤ ⁅R, R⁆ :=
    Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := 4) (e := f) trivial hadm (by omega)
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) → r = 1 :=
    fund_noncentral_modelUniv (p := p) (e := f) (t := .POmegaPlus) (n := 4) trivial hadm
      (by simp)
  have hcorr := Exotic.fundCorr_plus hp2 hq (le_refl 4)
  exact ⟨hodd, five_le_card_galoisField hq, nondegenerate_polarBilin_quadPlus 4 _,
    range_spinAction_quadPlus hn3, this, centerScalar_quadPlus hn3, hdim,
    fun F₁ => exists_frame_in_perp_plus4 h2 F₁, hcorr.1, hcorr.2, hperf, hnc⟩

theorem preservesFund_symm (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {σ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f))}
    (hσ : PreservesFund p f σ) : PreservesFund p f σ.symm := by
  classical
  obtain ⟨-, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have : Finite (GaloisField p f) := Nat.finite_of_card_ne_zero (by omega)
  have : NeZero 4 := inferInstance
  have : Finite (spinGroup (quadPlus 4 (GaloisField p f))) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _
      coe_ker_spinMatrix_quadPlus
  set 𝒮 : Set (Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))) :=
    {R | R ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num))} with h𝒮
  have hmaps : Set.MapsTo (fun R => R.map σ.toMonoidHom) 𝒮 𝒮 := fun R hR => hσ R hR
  have hinj : Set.InjOn (fun R => R.map σ.toMonoidHom) 𝒮 := fun R _ R' _ h =>
    Subgroup.map_injective σ.injective h
  have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite 𝒮) hmaps).mp hinj
  intro R hR
  obtain ⟨S, hS, hSR⟩ := hbij.surjOn hR
  have hSR' : S.map σ.toMonoidHom = R := hSR
  have : R.map σ.symm.toMonoidHom = S := by
    rw [← hSR']
    exact map_map_symm_equiv σ S
  rw [this]
  exact hS

theorem exists_ordinary_datum (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f)
    {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    {x x' : spinGroup (quadPlus 4 (GaloisField p f))}
    (hd : TwinDatumOn .POmegaPlus ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) (by norm_num)⟩ R R' x x') :
    ∃ σ : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)),
      PreservesFund p f σ ∧ PreservesFund p f σ.symm ∧
        spinAction (quadPlus 4 (GaloisField p f)) (σ x) =
          spinAction (quadPlus 4 (GaloisField p f)) (σ x') := by
  classical
  have c := spinCtx8_plus hp2 hq hadm
  obtain ⟨-, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨-, hF⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  obtain ⟨ρ, hρ⟩ := exists_triality hadm h4 hF
  have hx2 : x * x = 1 := c.sq_eq_one hd.mem hd.hx hd.cx
  have hx'2 : x' * x' = 1 := c.sq_eq_one hd.mem' hd.hx' hd.cx'
  have hc2 : (x * x'⁻¹) * (x * x'⁻¹) = 1 := by
    have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
    have hcomm : x * x' = x' * x := hd.comm x hd.hx x' hd.hx'
    rw [hx'inv]
    calc x * x' * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hcomm]
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx2, hx'2, one_mul]
  obtain ⟨σ, hσ, hθ⟩ := exists_aut_ordinary hp2 hadm ρ hρ hd.same hc2
  refine ⟨σ, hσ, preservesFund_symm hp2 hq hσ, ?_⟩
  rw [map_mul, map_inv, map_mul, map_inv] at hθ
  exact mul_inv_eq_one.mp hθ

end D4

end CFSG.ClassicalInvolution.RouteD.TWS6
