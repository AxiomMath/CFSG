module

public import CFSG.ClassicalInvolution.Q3.Q3TZMax
public import CFSG.ClassicalInvolution.Q3.Q3TZAniso
public import CFSG.ClassicalInvolution.Q3.Q3TZCenter
public import CFSG.ClassicalInvolution.Q3.Q3TY32
public import CFSG.ClassicalInvolution.Q3.Q3TY4
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.TWS8
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinDatumOn)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

section Transport

variable {K S : Type} [Group K] [Group S]

theorem conjSub_mapSubgroup (ε : K ≃* S) (k : K) (J : Subgroup K) :
    conjSub (ε k) (ε.mapSubgroup J) = ε.mapSubgroup (conjSub k J) := by
  show conjSub (ε k) (J.map ε.toMonoidHom) = (conjSub k J).map ε.toMonoidHom
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem conjStabilizer_mapSubgroup_pair (ε : K ≃* S) (R R' : Subgroup K) :
    G2D4Models.conjStabilizer ({ε.mapSubgroup R, ε.mapSubgroup R'} : Set (Subgroup S)) =
      (G2D4Models.conjStabilizer ({R, R'} : Set (Subgroup K))).map ε.toMonoidHom := by
  ext g
  obtain ⟨k, rfl⟩ := ε.surjective g
  have hpair : ∀ A : Subgroup K,
      ε.mapSubgroup A ∈ ({ε.mapSubgroup R, ε.mapSubgroup R'} : Set (Subgroup S)) ↔
        A ∈ ({R, R'} : Set (Subgroup K)) := by
    intro A
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ε.mapSubgroup.injective.eq_iff]
  constructor
  · intro h
    refine Subgroup.mem_map.mpr ⟨k, ?_, rfl⟩
    rw [G2D4Models.mem_conjStabilizer_iff]
    intro J
    rw [← hpair, ← hpair, ← conjSub_mapSubgroup]
    exact (G2D4Models.mem_conjStabilizer_iff.mp h) _
  · intro hk
    obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.mp hk
    obtain rfl : k' = k := ε.injective hkk
    rw [G2D4Models.mem_conjStabilizer_iff]
    intro J
    obtain ⟨J', rfl⟩ := ε.mapSubgroup.surjective J
    rw [conjSub_mapSubgroup, hpair, hpair]
    exact (G2D4Models.mem_conjStabilizer_iff.mp hk') J'

theorem isCoatom_of_conjStabilizer_map (ε : K ≃* S) {R R' : Subgroup K}
    (h : IsCoatom (G2D4Models.conjStabilizer
      ({ε.mapSubgroup R, ε.mapSubgroup R'} : Set (Subgroup S)))) :
    IsCoatom (G2D4Models.conjStabilizer ({R, R'} : Set (Subgroup K))) := by
  rw [conjStabilizer_mapSubgroup_pair] at h
  exact (OrderIso.isCoatom_iff ε.mapSubgroup _).mp h

theorem PairData3.map_equiv (ε : K ≃* S) {𝓕 : Set (Subgroup K)} {R R' : Subgroup K} {x x' : K}
    (h : PairData3 𝓕 R R' x x') :
    PairData3 {L | ∃ R₀ ∈ 𝓕, L = ε.mapSubgroup R₀} (ε.mapSubgroup R) (ε.mapSubgroup R') (ε x)
      (ε x') where
  mem := ⟨R, h.mem, rfl⟩
  mem' := ⟨R', h.mem', rfl⟩
  ne := fun hEq => h.ne (ε.mapSubgroup.injective hEq)
  hx := Subgroup.mem_map_of_mem _ h.hx
  hx' := Subgroup.mem_map_of_mem _ h.hx'
  cx := by
    rintro _ ⟨r, hr, rfl⟩
    show ε x * ε r = ε r * ε x
    rw [← map_mul, ← map_mul, h.cx r hr]
  cx' := by
    rintro _ ⟨r, hr, rfl⟩
    show ε x' * ε r = ε r * ε x'
    rw [← map_mul, ← map_mul, h.cx' r hr]
  nx := fun h1 => h.nx (ε.injective (by rw [h1, map_one]))
  nx' := fun h1 => h.nx' (ε.injective (by rw [h1, map_one]))
  same := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨k, rfl⟩ := ε.surjective s
    have := congrArg ε (Subgroup.mem_center_iff.mp h.same k)
    simpa only [map_mul, map_inv] using this

theorem mem_center_symm (ε : K ≃* S) {n : S} (hn : n ∈ Subgroup.center S) :
    ε.symm n ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at hn ⊢
  intro k
  apply ε.injective
  simpa using hn (ε k)

end Transport

section LongRoot

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan

theorem exists_conjSub_of_mem_longRootSetU {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] {n : ℕ} {hn : 2 ≤ n} {L L' : Subgroup (Su K p f n)}
    (hL : L ∈ longRootSetU hn) (hL' : L' ∈ longRootSetU hn) :
    ∃ g : Su K p f n, L' = conjSub g L := by
  obtain ⟨i, g, hg, -⟩ := hL
  obtain ⟨i', g', hg', -⟩ := hL'
  refine ⟨g' * g⁻¹, ?_⟩
  rw [hg, hg']
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

end LongRoot

section Orth6

open CFSG.GroupTheory.WeirSylow (IsPlusType)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [FiniteDimensional F V] in
theorem f₂_mem_wPlane3 (fr : OFrame Q) : fr.f₂ ∈ wPlane fr :=
  ⟨!![0, 0; 1, 0], by simp [Frame.incl_apply]⟩

theorem aniso_perp_of_not_isPlusType (hP : ¬ IsPlusType Q) (hdim : Module.finrank F V = 6)
    (fr : OFrame Q) : ∀ x ∈ fr.perp, Q x = 0 → x = 0 := by
  intro x hx hQx
  by_contra hx0
  have he₁ := e₁_mem_wPlane fr
  have he₂ := e₂_mem_wPlane fr
  have hf₁ := f₁_mem_wPlane fr
  have hf₂ := f₂_mem_wPlane3 fr
  have hxf₁ : polar Q x fr.f₁ = 0 := polar_perp_wPlane hx hf₁
  have hxf₂ : polar Q x fr.f₂ = 0 := polar_perp_wPlane hx hf₂
  have hxe₁ : polar Q x fr.e₁ = 0 := polar_perp_wPlane hx he₁
  have hxe₂ : polar Q x fr.e₂ = 0 := polar_perp_wPlane hx he₂
  have hex₁ : polar Q fr.e₁ x = 0 := polar_wPlane_perp hx he₁
  have hex₂ : polar Q fr.e₂ x = 0 := polar_wPlane_perp hx he₂
  have hli : LinearIndependent F (![fr.e₁, fr.e₂, x] : Fin 3 → V) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • fr.e₁ + g 1 • fr.e₂ + g 2 • x = 0 := by
      simpa [Fin.sum_univ_three] using hg
    clear hg
    have h1 := congrArg (fun y => polar Q y fr.f₁) hg'
    have h2 := congrArg (fun y => polar Q y fr.f₂) hg'
    simp only [polar_add_left, polar_smul_left_eq, fr.polar_e₁_f₁, fr.polar_e₂_f₁,
      fr.polar_e₁_f₂, fr.polar_e₂_f₂, hxf₁, hxf₂, polar_zero_left, mul_one, mul_zero, add_zero,
      zero_add] at h1 h2
    have g0 : g 0 = 0 := h1
    have g1 : g 1 = 0 := h2
    rw [g0, g1, zero_smul, zero_smul, zero_add, zero_add] at hg'
    have g2 : g 2 = 0 := (smul_eq_zero.mp hg').resolve_right hx0
    intro i
    fin_cases i <;> simp [g0, g1, g2]
  have hTs : ∀ y ∈ Submodule.span F (Set.range (![fr.e₁, fr.e₂, x] : Fin 3 → V)), Q y = 0 := by
    intro y hy
    refine map_eq_zero_of_mem_span (S := Set.range (![fr.e₁, fr.e₂, x] : Fin 3 → V)) ?_ ?_ hy
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [fr.Q_e₁, fr.Q_e₂, hQx]
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      fin_cases i <;> fin_cases j <;>
        simp [polar_self_eq_zero fr.Q_e₁, polar_self_eq_zero fr.Q_e₂, polar_self_eq_zero hQx,
          fr.polar_e₁_e₂, fr.polar_e₂_e₁, hxe₁, hxe₂, hex₁, hex₂]
  have hT3 : Module.finrank F (Submodule.span F (Set.range (![fr.e₁, fr.e₂, x] : Fin 3 → V))) =
      3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  exact hP ⟨_, by rw [hT3, hdim], hTs⟩

theorem elementaryGroup_le_of_not_maps_aniso [Finite F] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hP : ¬ IsPlusType Q) (hdim : Module.finrank F V = 6)
    (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H) (hHE : H ≤ elementaryGroup Q)
    (hh : ∃ h ∈ H, ¬ ∀ y ∈ wPlane fr, h y ∈ wPlane fr) : elementaryGroup Q ≤ H := by
  obtain ⟨h, hhH, hhW⟩ := hh
  have hperp : Module.finrank F fr.perp = 2 := by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    omega
  obtain ⟨k, hk, hke, hkW⟩ := exists_fix hodd hQ fr hH hHE (Or.inl (by omega)) hhH hhW
  obtain ⟨a, ha, ha0, haH⟩ := exists_mixed_of_fix fr hH hk (hHE hk) hke hkW
  exact elementaryGroup_le_of_mixed_aniso hodd hQ fr hH
    (hHE.trans (elementaryGroup_le_orthogonalGroup Q)) hperp
    (aniso_perp_of_not_isPlusType hP hdim fr) ha ha0 haH

end Orth6

section Su4

open CFSG.ClassicalInvolution.Models.TwistedPairs (minusLongBlock fin_zero_ne_one)
open CFSG.LieType.Universal.Spin (spinAction quadMinus ker_spinAction_le_center map_spinAction
  nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.LieType.Universal.Spin.Twisted (minusFrame)
open CFSG.GroupTheory.WeirSylow (not_isPlusType_quadMinus)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)


@[expose] noncomputable def longBlock3 :
    Subgroup (spinGroup (quadMinus 3 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
  (minusLongBlock (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).range

theorem exists_equiv_su4_spin :
    ∃ ε : (modelUniv .PSU 4 3 1 Nat.prime_three).K ≃*
        spinGroup (quadMinus 3 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
      ∀ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
        ∃ w : spinGroup (quadMinus 3 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
          ε.mapSubgroup R = conjSub w longBlock3 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm : StatedLieAdmissible .PSU 4 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨e₁, he₁⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadm
  obtain ⟨e₂, he₂⟩ := WeakCT.SU4.su4SpinMinus_exists (p := 3) (f := 1) hp2 one_ne_zero
    (minusCoeffs_irr 3 1)
  refine ⟨e₁.trans e₂.symm, fun R hR => ?_⟩
  obtain ⟨u, hu⟩ := exists_conjSub_of_mem_longRootSetU he₂ ((he₁ R).mp hR)
  refine ⟨e₂.symm u, ?_⟩
  have hmap : (e₁.trans e₂.symm).mapSubgroup R = e₂.symm.mapSubgroup (e₁.mapSubgroup R) := by
    show R.map (e₁.trans e₂.symm).toMonoidHom = (R.map e₁.toMonoidHom).map e₂.symm.toMonoidHom
    rw [Subgroup.map_map]
    rfl
  have h1 : e₁.mapSubgroup R = e₂.mapSubgroup (conjSub (e₂.symm u) longBlock3) := by
    rw [← conjSub_mapSubgroup]
    simp only [MulEquiv.apply_symm_apply]
    exact hu
  rw [hmap, h1]
  exact e₂.mapSubgroup.symm_apply_apply _

noncomputable abbrev minusForm6 :
    QuadraticForm 𝔽₃ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → 𝔽₃) :=
  quadMinus 3 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2

theorem pairCtx3_su4
    {ε : (modelUniv .PSU 4 3 1 Nat.prime_three).K ≃* spinGroup minusForm6}
    (hε : ∀ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
      ∃ w : spinGroup minusForm6, ε.mapSubgroup R = conjSub w longBlock3) :
    PairCtx3 minusForm6
      {L | ∃ R₀ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
        L = ε.mapSubgroup R₀} := by
  have hirr := minusCoeffs_irr 3 1
  have hY := Q3TY.yData3S_psu4
  have hQnd := nondegenerate_polarBilin_quadMinus_of_finite 3 𝔽₃ hirr
  have hdim : Module.finrank 𝔽₃ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → 𝔽₃) = 2 * 3 :=
    Gaps.finrank_minus 3 1 3 (by omega)
  obtain ⟨fr₀, hfr₀⟩ : ∃ fr₀ : OFrame minusForm6,
      longBlock3.map (spinAction minusForm6) = fr₀.La.range :=
    ⟨(minusFrame 3 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.toFrame fin_zero_ne_one
        true false,
      CFSG.ClassicalInvolution.ModelFacts.map_longSL2_range
        (minusFrame 3 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame fin_zero_ne_one true
        false⟩
  refine ⟨odd_gf3, hQnd, WeakCT.range_spinAction_quadMinus_three hirr,
    Q3TY.isPerfect_spinMinus6_three hirr, centerScalar_of_frame hQnd fr₀, by omega,
    fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj odd_gf3 F₁ F₂ h
      omega, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have hc : n ∈ Subgroup.center (spinGroup minusForm6) := ker_spinAction_le_center minusForm6 hn
    have := hY.cop _ (mem_center_symm ε hc)
    rwa [MulEquiv.orderOf_eq] at this
  · rintro _ ⟨R₀, hR₀, rfl⟩
    obtain ⟨w, hw⟩ := hε R₀ hR₀
    rw [hw]
    have hg : spinAction minusForm6 w ∈ TauCeti.QuadraticMap.orthogonalGroup minusForm6 :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ w v
    have key : (conjSub w longBlock3).map (spinAction minusForm6) =
        fr₀.La.range.map (MulAut.conj (spinAction minusForm6 w)).toMonoidHom := by
      show (longBlock3.map (MulAut.conj w).toMonoidHom).map (spinAction minusForm6) = _
      rw [CFSG.ClassicalInvolution.ModelFacts.map_conj_map, hfr₀]
    rw [key]
    exact ⟨_, IsFundamental.conj hg (IsFundamental.of_frame fr₀)⟩
  · rintro _ ⟨R₀, hR₀, rfl⟩
    exact (hY.pow3 R₀ hR₀).map ε.toMonoidHom
  · rintro _ ⟨R₀, hR₀, rfl⟩ r hr hrc
    obtain ⟨r₀, hr₀, rfl⟩ := Subgroup.mem_map.mp hr
    have h1 : r₀ ∈ Subgroup.center (modelUniv .PSU 4 3 1 Nat.prime_three).K := by
      simpa using mem_center_symm ε hrc
    have := hY.central R₀ hR₀ r₀ hr₀ h1
    rw [this, map_one]

theorem twinPairMax3_psu4 : TwinPairMax3 .PSU 4 := by
  obtain ⟨ε, hε⟩ := exists_equiv_su4_spin
  have hctx := pairCtx3_su4 hε
  have hirr := minusCoeffs_irr 3 1
  have hP : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType minusForm6 :=
    not_isPlusType_quadMinus (by omega) hirr
  have hdim : Module.finrank 𝔽₃ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → 𝔽₃) = 6 :=
    Gaps.finrank_minus 3 1 3 (by omega)
  have hQnd := nondegenerate_polarBilin_quadMinus_of_finite 3 𝔽₃ hirr
  intro R R' x x' hd
  have hd6 := PairData3.map_equiv ε (pairData3_of_datum hd)
  refine isCoatom_of_conjStabilizer_map ε (isCoatom_conjStabilizer3 hctx ?_ ?_ hd6)
  · intro fr
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    omega
  · intro fr H hH hHE hh
    exact elementaryGroup_le_of_not_maps_aniso odd_gf3 hQnd hP hdim fr hH hHE hh

theorem twinYNoCentral3_psu4 : Q3TIY.TwinYNoCentral3On fun t n => t = .PSU ∧ n = 4 :=
  twinYNoCentral3_of_twinPairMax3 fun _ _ _ hl => by
    obtain ⟨rfl, rfl⟩ := hl
    exact twinPairMax3_psu4

end Su4

end CFSG.ClassicalInvolution.Q3.Q3TZ
