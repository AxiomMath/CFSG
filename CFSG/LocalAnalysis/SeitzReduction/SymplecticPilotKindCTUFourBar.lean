module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourTrivial
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Bar

variable {N ε : ℕ} {F : Type} [Field F] {σ : F ≃+* F}

theorem ctuf_bar_mem_ctuBlock (hσ : ∀ c, σ (σ c) = c) {R : Finset (Fin N)}
    {x : SU σ (2 * N + ε)} (hx : x ∈ ctuBlock σ ε R) :
    ctuaBarAut σ hσ (2 * N + ε) x ∈ ctuBlock σ ε R := by
  rw [mem_ctuBlock] at hx ⊢
  intro a b hab
  rw [coe_ctuaBarAut, coe_glAut, Matrix.map_apply, hx a b hab]
  by_cases h : a = b
  · subst h
    rw [one_apply_eq, map_one]
  · rw [one_apply_ne h, map_zero]

end Bar

section Short

variable {N ε : ℕ} {F : Type} [Field F] {σ : F ≃+* F}

theorem ctuf_coord_ne {p p' : Fin N} (h : p ≠ p') :
    ctuCoord N ε (Sum.inl (Sum.inl p)) ≠ ctuCoord N ε (Sum.inl (Sum.inl p')) := by
  rw [Ne, (ctuCoord N ε).injective.eq_iff]
  simpa using h

variable (ε σ) in
@[expose] noncomputable def ctufShort (hε : ε ≤ 1) (hσ : ∀ c, σ (σ c) = c) {p p' : Fin N}
    (h : p ≠ p') : Multiplicative F →* SU σ (2 * N + ε) :=
  rootHom σ hσ (ctuf_coord_ne h) (ctuCoord_inl_ne_rev hε _) (ctuCoord_inl_ne_rev hε _)

variable {hε : ε ≤ 1} {hσ : ∀ c, σ (σ c) = c}

theorem coe_ctufShort {p p' : Fin N} (h : p ≠ p') (c : Multiplicative F) :
    ((ctufShort ε σ hε hσ h c : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        rootMatrix σ (ctuCoord N ε (Sum.inl (Sum.inl p)))
          (ctuCoord N ε (Sum.inl (Sum.inl p'))) c.toAdd := rfl

theorem ctufShort_mem_ctuBlock {p p' : Fin N} (h : p ≠ p') {R : Finset (Fin N)} (hpR : p ∉ R)
    (hp'R : p' ∉ R) (c : Multiplicative F) : ctufShort ε σ hε hσ h c ∈ ctuBlock σ ε R := by
  set i := ctuCoord N ε (Sum.inl (Sum.inl p)) with hi
  set j := ctuCoord N ε (Sum.inl (Sum.inl p')) with hj
  rw [mem_ctuBlock, coe_ctufShort]
  intro a b hab
  have hpl : ∀ u : Fin N ⊕ Fin N, planeOf u ∉ R →
      ctuCoord N ε (Sum.inl u) ∉ ctuPlanes ε R := by
    intro u hu h'
    exact hu (ctuCoord_mem_ctuPlanes.1 h')
  have hri : Fin.rev i ∉ ctuPlanes ε R := by
    rw [hi, ctuCoord_rev hε, ctuPar_inl]
    exact hpl _ (by simpa using hpR)
  have hrj : Fin.rev j ∉ ctuPlanes ε R := by
    rw [hj, ctuCoord_rev hε, ctuPar_inl]
    exact hpl _ (by simpa using hp'R)
  rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply,
    ctua_apply_of_plane hab (hpl _ (by simpa using hpR)) (hpl _ (by simpa using hp'R)),
    ctua_apply_of_plane hab hrj hri, add_zero, sub_zero]

theorem ctufShort_apply {p p' : Fin N} (h : p ≠ p') (c : Multiplicative F) :
    ((ctufShort ε σ hε hσ h c : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε (Sum.inl (Sum.inl p)))
        (ctuCoord N ε (Sum.inl (Sum.inl p'))) = c.toAdd := by
  have hij := ctuf_coord_ne (ε := ε) h
  rw [coe_ctufShort, rootMatrix, Matrix.sub_apply, Matrix.add_apply, one_apply_ne hij,
    single_apply_same, single_apply_of_row_ne, zero_add, sub_zero]
  rw [ctuCoord_rev hε, ctuPar_inl, Ne, (ctuCoord N ε).injective.eq_iff]
  simp [par]

theorem ctufShort_ne_one {p p' : Fin N} (h : p ≠ p') {c : F} (hc : c ≠ 0) :
    ctufShort ε σ hε hσ h (Multiplicative.ofAdd c) ≠ 1 := by
  intro h1
  have h2 := ctufShort_apply (hε := hε) (hσ := hσ) h (Multiplicative.ofAdd c)
  rw [h1] at h2
  simp only [OneMemClass.coe_one, Units.val_one, toAdd_ofAdd] at h2
  rw [one_apply_ne (ctuf_coord_ne h)] at h2
  exact hc h2.symm

theorem ctuaBarAut_ctufShort {p p' : Fin N} (h : p ≠ p') (c : Multiplicative F) :
    ctuaBarAut σ hσ (2 * N + ε) (ctufShort ε σ hε hσ h c) =
      ctufShort ε σ hε hσ h (Multiplicative.ofAdd (σ c.toAdd)) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctuaBarAut, coe_glAut, coe_ctufShort, coe_ctufShort, toAdd_ofAdd]
  ext a b
  simp only [rootMatrix, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, single_apply,
    Matrix.one_apply]
  split_ifs <;> simp [hσ]

theorem ctufShort_mul_diagonal {p p' : Fin N} (h : p ≠ p') (c : Multiplicative F)
    {d : Fin (2 * N + ε) → F}
    (hd : d (ctuCoord N ε (Sum.inl (Sum.inl p))) = d (ctuCoord N ε (Sum.inl (Sum.inl p'))))
    (hd' : d (ctuCoord N ε (Sum.inl (Sum.inr p))) = d (ctuCoord N ε (Sum.inl (Sum.inr p')))) :
    ((ctufShort ε σ hε hσ h c : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) * diagonal d =
        diagonal d * ((ctufShort ε σ hε hσ h c : GL (Fin (2 * N + ε)) F) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases hab : d a = d b
  · rw [hab, mul_comm]
  · have hri : Fin.rev (ctuCoord N ε (Sum.inl (Sum.inl p))) =
        ctuCoord N ε (Sum.inl (Sum.inr p)) := by rw [ctuCoord_rev hε]; rfl
    have hrj : Fin.rev (ctuCoord N ε (Sum.inl (Sum.inl p'))) =
        ctuCoord N ε (Sum.inl (Sum.inr p')) := by rw [ctuCoord_rev hε]; rfl
    have h0 : ((ctufShort ε σ hε hσ h c : GL (Fin (2 * N + ε)) F) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b = 0 := by
      rw [coe_ctufShort, rootMatrix, Matrix.sub_apply, Matrix.add_apply, single_apply,
        single_apply, hri, hrj, Matrix.one_apply, ite_eq_right (fun h' => hab (by rw [h'])),
        ite_eq_right (fun h' => hab (by rw [← h'.1, ← h'.2, hd])),
        ite_eq_right (fun h' => hab (by rw [← h'.1, ← h'.2, hd'])), add_zero, sub_zero]
    rw [h0, zero_mul, mul_zero]

theorem ctufShort_commute_ctuEmbed_diagSp {K : Type} [Field K] [CharP K 2] {ι : K →+* F}
    {hι : ∀ c, σ (ι c) = ι c} {p p' : Fin N} (h : p ≠ p') (c : Multiplicative F)
    {t : Fin N → Kˣ} (ht : t p = t p') :
    ctufShort ε σ hε hσ h c * ctuEmbed ε hε σ ι hι (diagSp K N t) =
      ctuEmbed ε hε σ ι hι (diagSp K N t) * ctufShort ε σ hε hσ h c := by
  apply mat_injective
  rw [map_mul, map_mul, mat_ctuEmbed_diagSp, mat_apply]
  exact ctufShort_mul_diagonal h c (by rw [ctuDiag_inl_inl, ctuDiag_inl_inl, ht])
    (by rw [ctuDiag_inl_inr, ctuDiag_inl_inr, ht])

end Short

section Transport

variable {f m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {K' : Type} [Field K']
  (h : UnitaryFieldData 2 f K')

theorem ctuf_transportMat_map_bar (θ : F ≃+* K') {ι₁ ι₂ : Type*} (τ : ι₁ ≃ ι₂)
    (A : Matrix ι₂ ι₂ F) :
    (transportMat (θ : F →+* K') τ A).map h.bar =
      transportMat (θ : F →+* K') τ (A.map (unitaryInvolution F 2 f)) := by
  ext i j
  simp only [transportMat, Matrix.map_apply, Matrix.submatrix_apply]
  exact (ringEquiv_unitaryInvolution h θ _).symm

omit [Finite F] [CharP F 2] in
theorem ctuBlockEquiv_bar {ε : ℕ} {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (hε : ε ≤ 1)
    (k : Fin (m + 1)) (x : ctuBlock σ ε ({k} : Finset (Fin (m + 1)))) :
    ctuBlockEquiv σ hε k ⟨ctuaBarAut σ hσ _ x, ctuf_bar_mem_ctuBlock hσ x.2⟩ =
      ctuaBarAut σ hσ _ (ctuBlockEquiv σ hε k x) := by
  apply mat_injective
  rw [mat_ctuBlockEquiv, mat_apply, mat_apply, coe_ctuaBarAut, coe_glAut, coe_ctuaBarAut,
    coe_glAut, ← mat_apply, ← mat_apply, mat_ctuBlockEquiv]
  rfl

theorem ctuGramEquiv_bar {C₀ : GL (Fin (2 * m)) K'} (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m) (θ : F ≃+* K')
    (hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c)
    (y : SU (unitaryInvolution F 2 f) (2 * m + 0)) :
    ctuGramEquiv h hC₀ θ (ctuaBarAut _ hσ _ y) =
      primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) (ctuGramEquiv h hC₀ θ y) := by
  apply Subtype.ext
  apply Units.ext
  rw [F4Pilot.coe_primeFormFieldSU, ctuGramEquiv_apply, ctuGramEquiv_apply, coe_ctuGramHom,
    coe_ctuGramHom, coe_ctuaBarAut, coe_glAut]
  have hb : (⇑(UnitaryPilot.barRingEquiv h) : K' → K') = ⇑h.bar :=
    funext (UnitaryPilot.barRingEquiv_apply h)
  rw [hb, ctuf_transportMat_map_bar]

theorem ctuOddGramEquiv_bar [CharP h.fixedField 2] [Finite h.fixedField]
    {C₀ : GL (Fin (2 * m + 1)) K'} (hC : IsPrimeFormGram C₀)
    (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1)
    (θ : F ≃+* K') (P : GL (Fin (2 * m + 1)) h.fixedField)
    (hP : ((P : GL (Fin (2 * m + 1)) h.fixedField) :
      Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField) * antidiag (2 * m + 1) *
        ((P : GL (Fin (2 * m + 1)) h.fixedField) :
          Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField)ᵀ = 1)
    (hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c)
    (y : SU (unitaryInvolution F 2 f) (2 * m + 1)) :
    ctuOddGramEquiv h hC₀ θ P hP (ctuaBarAut _ hσ _ y) =
      primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) (ctuOddGramEquiv h hC₀ θ P hP y) := by
  apply Subtype.ext
  apply Units.ext
  rw [F4Pilot.coe_primeFormFieldSU]
  change oddTransportMat h θ P (mat _ (2 * m + 1) (ctuaBarAut _ hσ _ y)) =
    (oddTransportMat h θ P (mat _ (2 * m + 1) y)).map _
  have hb : (⇑(UnitaryPilot.barRingEquiv h) : K' → K') = ⇑h.bar :=
    funext (UnitaryPilot.barRingEquiv_apply h)
  rw [hb, mat_apply, coe_ctuaBarAut, coe_glAut, oddTransportMat, oddTransportMat,
    Matrix.map_mul, Matrix.map_mul, oddRi, oddR, map_bar_subtype, map_bar_subtype, ← mat_apply,
    ctuf_transportMat_map_bar]

variable {G : Type} [Group G] {L : Subgroup G} {K₀ : Type} [Field K₀] [CharP K₀ 2]
  {ι : K₀ →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp (m + 1) K₀}
  {t : G} {k : Fin (m + 1)} {h} [CharP h.fixedField 2]

theorem ctuParamOfUnitary_conj {C₀ : GL (Fin (2 * m)) K'} {hC : IsPrimeFormGram C₀}
    {hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m}
    {ι' : K₀ ≃+* h.fixedField} (hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c)
    (θ : F ≃+* K') (hθι : ∀ c, θ (ι c) = (ι' c : K'))
    (U : UnitaryNeighbourParam h e t k hC hC₀ ι')
    (x : ctuBlock (unitaryInvolution F 2 f) 0 ({k} : Finset (Fin (m + 1)))) :
    t * (ctuParamOfUnitary (hι := hι) θ hθι U).Φ x * t⁻¹ =
      (ctuParamOfUnitary (hι := hι) θ hθι U).Φ ⟨ctuaBarAut _ hσ _ x, ctuf_bar_mem_ctuBlock hσ x.2⟩ := by
  change t * U.Φ (ctuGramEquiv h hC₀ θ (ctuBlockEquiv _ (Nat.zero_le 1) k x)) * t⁻¹ =
    U.Φ (ctuGramEquiv h hC₀ θ (ctuBlockEquiv _ (Nat.zero_le 1) k
      ⟨ctuaBarAut _ hσ _ x, ctuf_bar_mem_ctuBlock hσ x.2⟩))
  rw [U.N3, ctuBlockEquiv_bar, ctuGramEquiv_bar h hC]

theorem ctuParamOfUnitaryOdd_conj [Finite h.fixedField] {C₀ : GL (Fin (2 * m + 1)) K'}
    {hC : IsPrimeFormGram C₀}
    {hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1}
    {ι' : K₀ ≃+* h.fixedField} (hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c)
    (θ : F ≃+* K') (hθι : ∀ c, θ (ι c) = (ι' c : K')) (P : GL (Fin (2 * m + 1)) h.fixedField)
    (hP : ((P : GL (Fin (2 * m + 1)) h.fixedField) :
      Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField) * antidiag (2 * m + 1) *
        ((P : GL (Fin (2 * m + 1)) h.fixedField) :
          Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField)ᵀ = 1)
    (Pa : UnitaryOddNeighbourParam h e t k hC hC₀ (oddBeta P hP) ι')
    (x : ctuBlock (unitaryInvolution F 2 f) 1 ({k} : Finset (Fin (m + 1)))) :
    t * (ctuParamOfUnitaryOdd (hι := hι) θ hθι P hP Pa).Φ x * t⁻¹ =
      (ctuParamOfUnitaryOdd (hι := hι) θ hθι P hP Pa).Φ
        ⟨ctuaBarAut _ hσ _ x, ctuf_bar_mem_ctuBlock hσ x.2⟩ := by
  change t * Pa.Φ (ctuOddGramEquiv h hC₀ θ P hP (ctuBlockEquiv _ le_rfl k x)) * t⁻¹ =
    Pa.Φ (ctuOddGramEquiv h hC₀ θ P hP (ctuBlockEquiv _ le_rfl k
      ⟨ctuaBarAut _ hσ _ x, ctuf_bar_mem_ctuBlock hσ x.2⟩))
  rw [Pa.N3, ctuBlockEquiv_bar, ctuOddGramEquiv_bar h hC]

end Transport

section Trivial

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem CtuParam.ctufShort_mem_centralizer_siegelTorus (hF : Nat.card F = (2 ^ f) ^ 2)
    {k : Fin N} (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k) {p p' : Fin N}
    (h : p ≠ p') (hpk : p ≠ k) (hp'k : p' ≠ k) (c : Multiplicative F) :
    P.Φ ⟨ctufShort ε (unitaryInvolution F 2 f) hε (unitaryInvolution_involutive hF) h c,
      ctufShort_mem_ctuBlock h (by simpa using hpk) (by simpa using hp'k) c⟩ ∈
        centralizer (modelToG e (siegelTorus K N) : Set G) := by
  set z : ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) :=
    ⟨ctufShort ε (unitaryInvolution F 2 f) hε (unitaryInvolution_involutive hF) h c,
      ctufShort_mem_ctuBlock h (by simpa using hpk) (by simpa using hp'k) c⟩ with hz
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨d, ⟨s, rfl⟩, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
  change ((e.symm (diagSp K N (fun _ => s)) : L) : G) * P.Φ z =
    P.Φ z * ((e.symm (diagSp K N (fun _ => s)) : L) : G)
  rw [diagSp_eq_rootTorusHom_mul (fun _ => s) k, map_mul, Subgroup.coe_mul]
  have h1 : P.Φ z ∈ centralizer (modelToG e (rootTorusSp K k) : Set G) := by
    have : P.Φ z ∈ neighbourCore e k := P.range_eq ▸ ⟨z, rfl⟩
    exact F4Pilot.centralizerPerfectCore_le_centralizer _ this
  have h2 := mem_centralizer_iff.1 h1 _ (UnitaryPilot.symm_mem_modelToG e ⟨s, rfl⟩)
  have hd := diagSp_update_mem_spBlock_compl (K := K) (fun _ => s) k
  have h3 : ((e.symm (diagSp K N (Function.update (fun _ => s) k 1)) : L) : G) =
      P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι
        (diagSp K N (Function.update (fun _ => s) k 1)), ctuEmbed_mem_ctuBlock_iff.2 hd⟩ :=
    (P.N1 _ hd).symm
  have hzc := ctufShort_commute_ctuEmbed_diagSp (hε := hε) (hσ := unitaryInvolution_involutive hF)
    (ι := ι) (hι := hι) h c (t := Function.update (fun _ => s) k 1)
    (by rw [Function.update_of_ne hpk, Function.update_of_ne hp'k])
  have h4 : P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι
      (diagSp K N (Function.update (fun _ => s) k 1)), ctuEmbed_mem_ctuBlock_iff.2 hd⟩ * P.Φ z =
      P.Φ z * P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι
        (diagSp K N (Function.update (fun _ => s) k 1)), ctuEmbed_mem_ctuBlock_iff.2 hd⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hzc.symm
  rw [h3]
  calc ((e.symm (rootTorusHom K N k s) : L) : G) * P.Φ ⟨_, _⟩ * P.Φ z
      = ((e.symm (rootTorusHom K N k s) : L) : G) * (P.Φ z * P.Φ ⟨_, _⟩) := by
        rw [mul_assoc, h4]
    _ = P.Φ z * (((e.symm (rootTorusHom K N k s) : L) : G) * P.Φ ⟨_, _⟩) := by
        rw [← mul_assoc, h2, mul_assoc]

theorem orderOf_ctufShort {p p' : Fin N} (h : p ≠ p') {hσ : ∀ c, unitaryInvolution F 2 f
    (unitaryInvolution F 2 f c) = c} {d : F} (hd : d ≠ 0) :
    orderOf (ctufShort ε (unitaryInvolution F 2 f) hε hσ h (Multiplicative.ofAdd d)) = 2 := by
  refine orderOf_eq_prime ?_ (ctufShort_ne_one h hd)
  rw [sq, ← map_mul, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero, map_one]

variable [Finite G]

theorem false_of_siegel_normal_of_ctuParam (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hN : 4 ≤ N)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {k : Fin N}
    (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (hP : ∀ x, t * P.Φ x * t⁻¹ = P.Φ ⟨ctuaBarAut _ (unitaryInvolution_involutive hF) _ x,
      ctuf_bar_mem_ctuBlock _ x.2⟩)
    (htX : t ∈ centralizer (modelToG e (siegelTorus K N) : Set G))
    (hnorm : (((modelToG e (siegelLevi K N)).subgroupOf
      (centralizer (modelToG e (siegelTorus K N) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K N) : Set G))))).Normal) : False := by
  have hcen := mk_mem_center_of_siegel_normal hset hKc hf (by omega) e htC ht htX hnorm
  have hcard : 2 < ({k} : Finset (Fin N))ᶜ.card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨p, hp, p', hp', l, hl, hpp', hpl, hp'l⟩ := Finset.two_lt_card.1 hcard
  have hpk : p ≠ k := by simpa using hp
  have hp'k : p' ≠ k := by simpa using hp'
  have hlk : l ≠ k := by simpa using hl
  obtain ⟨c, hc⟩ := exists_unitaryInvolution_ne_ctua hF (by omega)
  have hσ := unitaryInvolution_involutive hF
  set u := ctufShort ε (unitaryInvolution F 2 f) hε hσ hpp' with hu
  have hyH := P.ctufShort_mem_centralizer_siegelTorus hF hpp' hpk hp'k (Multiplicative.ofAdd c)
  set d := unitaryInvolution F 2 f c - c with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hc
  have hcomm : t * P.Φ ⟨u (Multiplicative.ofAdd c), ctufShort_mem_ctuBlock hpp'
      (by simpa using hpk) (by simpa using hp'k) _⟩ * t⁻¹ *
      (P.Φ ⟨u (Multiplicative.ofAdd c), ctufShort_mem_ctuBlock hpp' (by simpa using hpk)
        (by simpa using hp'k) _⟩)⁻¹ =
      P.Φ ⟨u (Multiplicative.ofAdd d), ctufShort_mem_ctuBlock hpp' (by simpa using hpk)
        (by simpa using hp'k) _⟩ := by
    rw [hP, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    change ctuaBarAut _ hσ _ (u (Multiplicative.ofAdd c)) * (u (Multiplicative.ofAdd c))⁻¹ =
      u (Multiplicative.ofAdd d)
    rw [hu, ctuaBarAut_ctufShort, ← map_inv, ← map_mul, toAdd_ofAdd, hd, sub_eq_add_neg,
      ofAdd_add, ofAdd_neg]
  have hkl : k ≠ l := Ne.symm hlk
  have hc3 : ({k} : Finset (Fin N))ᶜ.card = N - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hq : (2 * ({k} : Finset (Fin N))ᶜ.card + ε, 2 ^ f) ≠ (3, 2) := by
    rw [hc3]
    intro h'
    have := (Prod.mk.inj h').1
    omega
  have hinj := P.injective_overlap hF hkl (by rw [hc3]; omega) hq
  have hw : u (Multiplicative.ofAdd d) ∈
      ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) :=
    ctufShort_mem_ctuBlock hpp' (by simp [hpk, hpl]) (by simp [hp'k, hp'l]) _
  have hord : orderOf (P.Φ ⟨u (Multiplicative.ofAdd d), ctufShort_mem_ctuBlock hpp'
      (by simpa using hpk) (by simpa using hp'k) _⟩) = 2 := by
    have h1 := orderOf_injective _ hinj ⟨u (Multiplicative.ofAdd d), hw⟩
    rw [Subgroup.orderOf_mk, orderOf_ctufShort hpp' hd0] at h1
    exact h1
  exact false_of_mk_mem_center_of_orderOf_commutator htX hyH (hcomm ▸ hord) hcen

end Trivial

end CFSG.SeitzReduction.SymplecticPilot
