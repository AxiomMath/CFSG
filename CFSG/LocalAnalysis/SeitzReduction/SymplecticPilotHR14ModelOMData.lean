module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OPNonembed
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.LieType.Universal.Spin (quadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv coordinateMinusIsometry coordinateMinusWitnessEquiv)

section Transport

theorem exists_omegaMinusData_of_le {G Y : Type} [Group G] [Group Y] {Ω Q₁ X' : Subgroup G}
    (e : Y ≃* Ω) (hQΩ : Q₁ ≤ Ω) (hXΩ : X' ≤ Ω) (hQ : IsPGroup 2 Q₁) (hQne : Q₁ ≠ ⊥)
    (hXN : X' ≤ normalizer (Q₁ : Set G)) (hXs : IsSimpleGroup X') (hZ : center X' = ⊥)
    {x y : G} (hx : x ∈ X') (hy : y ∈ X') (hxy : x * y = y * x) (hy1 : y ≠ 1) {k : ℕ}
    (hyk : y ^ k = 1) {ℓ : ℕ} (hxℓ : x ^ ℓ = 1) (hx1 : x ≠ 1) :
    ∃ (Q₁' X'' : Subgroup Y) (x' y' : Y), IsPGroup 2 Q₁' ∧ Q₁' ≠ ⊥ ∧
      X'' ≤ normalizer (Q₁' : Set Y) ∧ IsSimpleGroup X'' ∧ center X'' = ⊥ ∧ x' ∈ X'' ∧
      y' ∈ X'' ∧ x' * y' = y' * x' ∧ y' ≠ 1 ∧ y' ^ k = 1 ∧ x' ^ ℓ = 1 ∧ x' ≠ 1 := by
  set φ : Y →* G := Ω.subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ := Ω.subtype_injective.comp e.injective
  have hφapp : ∀ z (hz : z ∈ Ω), φ (e.symm ⟨z, hz⟩) = z := fun z hz => by
    simp [hφ]
  have hXr : X' ≤ φ.range := fun z hz => ⟨e.symm ⟨z, hXΩ hz⟩, hφapp z _⟩
  have hmap : (X'.comap φ).map φ = X' := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hXr]
  let eX : X'.comap φ ≃* X' :=
    ((X'.comap φ).equivMapOfInjective φ hφinj).trans (MulEquiv.subgroupCongr hmap)
  have heX : ∀ z : X'.comap φ, (eX z : G) = φ z := fun z => rfl
  have : IsSimpleGroup (X'.comap φ) := eX.isSimpleGroup
  refine ⟨Q₁.comap φ, X'.comap φ, e.symm ⟨x, hXΩ hx⟩, e.symm ⟨y, hXΩ hy⟩,
    hQ.comap_of_injective φ hφinj, ?_, ?_, this, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hQne)
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨e.symm ⟨q, hQΩ q.2⟩, ?_⟩, ?_⟩
    · show φ _ ∈ Q₁
      rw [hφapp]
      exact q.2
    · intro h
      apply hq1
      have h1 := congrArg (fun w : Q₁.comap φ => φ w) h
      simp only [OneMemClass.coe_one, map_one, hφapp] at h1
      exact Subtype.ext h1
  · intro z hz
    rw [mem_normalizer_iff]
    intro w
    have h := (mem_normalizer_iff.1 (hXN hz)) (φ w)
    simp only [mem_comap, map_mul, map_inv]
    exact h
  · rw [eq_bot_iff]
    intro z hz
    rw [mem_bot]
    have hc : eX z ∈ center X' := by
      rw [mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := eX.surjective w
      rw [← map_mul, ← map_mul, (mem_center_iff.1 hz) w']
    rw [hZ, mem_bot, MulEquiv.map_eq_one_iff] at hc
    exact hc
  · show φ _ ∈ X'
    rw [hφapp]
    exact hx
  · show φ _ ∈ X'
    rw [hφapp]
    exact hy
  · apply hφinj
    rw [map_mul, map_mul, hφapp, hφapp]
    exact hxy
  · intro h
    apply hy1
    have h1 := congrArg φ h
    rwa [hφapp, map_one] at h1
  · apply hφinj
    rw [map_pow, hφapp, map_one]
    exact hyk
  · apply hφinj
    rw [map_pow, hφapp, map_one]
    exact hxℓ
  · intro h
    apply hx1
    have h1 := congrArg φ h
    rwa [hφapp, map_one] at h1

end Transport

section Simple

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {R : QuadraticForm K V}

theorem isSimpleGroup_orthDerived_and_center_eq_bot (hR : (polarBilin R).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0) :
    IsSimpleGroup (orthDerived R) ∧ center (orthDerived R) = ⊥ := by
  obtain ⟨-, hc, -, hsimple, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hR hT
  have : Nontrivial V := by
    obtain ⟨T, hT3, -⟩ := hT
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : finrank K T = 0 := by
      rw [Submodule.finrank_eq_zero]
      exact Subsingleton.elim _ _
    omega
  have hbot := OmegaPilot.center_orthDerived_eq_bot' hR hT
    (CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hR)
  let e : orthDerived R ≃* ProjOrthDerived R :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq (hbot.symm.trans hc))
  exact ⟨MulEquiv.isSimpleGroup e, hbot⟩

end Simple

@[expose] def OmegaMinusUnitaryPairInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (g n : ℕ), 1 ≤ g → Nat.card K = 2 ^ g →
    Odd n → 5 ≤ n → ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∃ (x y : orthDerived (quadMinus n K b c)) (ℓ : ℕ), x * y = y * x ∧ y ≠ 1 ∧
        y ^ (2 ^ g + 1) = 1 ∧ CFSG.Timmesfeld.IsPrimitivePrimeDivisor ℓ (2 * g * n) ∧
        x ^ ℓ = 1 ∧ x ≠ 1

section Data

open OmegaPilot (perpSub extendLin IsHypCoord isHypCoord_coordinateQuadMinus regular_minusPerp
  minusPerpIsometry orthDerivedCongr orthDerivedProjEquiv)

theorem lagCenter_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : center B = ⊥) : center A = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  have hc : e z ∈ center B := by
    rw [mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hz) w']
  rw [h, mem_bot, MulEquiv.map_eq_one_iff] at hc
  exact hc

theorem extendLin_injective {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {a b : ι}
    (hab : a ≠ b) : Function.Injective (extendLin (K := K) hab) := by
  intro g g' h
  ext u
  have := congrArg (fun f : (ι → K) ≃ₗ[K] (ι → K) => f u) h
  simp only [OmegaPilot.extendLin_apply_perp] at this
  exact congrFun this _

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {a b : ι}

omit [DecidableEq ι] in
theorem isPGroup_rootGroup [CharP K 2] (u : ι → K) : IsPGroup 2 (rootGroup Q u) := by
  intro g
  obtain ⟨w, hw, hg⟩ := mem_rootGroup.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two, ← hg, eichler_mul hw hw,
    omegaInv_add_self K w, eichler_zero_right]

theorem rootGroup_ne_bot (h : IsHypCoord Q a b) {c : ι} (hca : c ≠ a) (hcb : c ≠ b) :
    rootGroup Q (Pi.single a 1) ≠ ⊥ := by
  have hw : polar Q (Pi.single a 1) (Pi.single c 1) = 0 := by
    rw [h.polar_left]
    simp [Ne.symm hcb]
  refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨_, eichler_mem_rootGroup hw⟩, fun h1 => ?_⟩
  have h2 := congrArg (fun g : rootGroup Q (Pi.single a 1) =>
    (g : (ι → K) ≃ₗ[K] (ι → K)) (Pi.single b 1)) h1
  simp only [OneMemClass.coe_one, LinearEquiv.coe_one, id_eq] at h2
  rw [eichler_apply h.map_left hw, h.polar_right, h.polar_right] at h2
  have h3 := congrFun h2 c
  simp [hca, hcb] at h3

omit [DecidableEq ι] in
theorem le_normalizer_rootGroup {X : Subgroup ((ι → K) ≃ₗ[K] (ι → K))}
    (hXO : X ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {u : ι → K} (hXu : ∀ g ∈ X, g u = u) :
    X ≤ normalizer (rootGroup Q u : Set ((ι → K) ≃ₗ[K] (ι → K))) := by
  intro g hg
  have hconj : ∀ g ∈ X, ∀ z ∈ rootGroup Q u, g * z * g⁻¹ ∈ rootGroup Q u := fun g hg z hz =>
    conj_mem_rootGroup_of_apply_eq_smul (hXO hg) (c := 1) (by rw [one_smul, hXu g hg]) hz
  rw [mem_normalizer_iff]
  intro z
  refine ⟨hconj g hg z, fun h => ?_⟩
  have := hconj g⁻¹ (inv_mem hg) _ h
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

end Data

section Main

open OmegaPilot (perpSub extendLin IsHypCoord isHypCoord_coordinateQuadMinus regular_minusPerp
  minusPerpIsometry orthDerivedCongr orthDerivedProjEquiv)

theorem omegaMinusNonembeddingDataInput_of_pair (hpair : OmegaMinusUnitaryPairInput) :
    OmegaMinusNonembeddingDataInput := by
  intro Y _ N g hN hNe hg hY
  obtain ⟨⟨-, -, hN4⟩, K, _, _, hK, b, c, hirr, ⟨eE⟩⟩ :=
    CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel (by decide) hY
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hnd, hT⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      N K b c (by omega) hirr
  set k₀ : Fin (N - 1) := ⟨0, by omega⟩ with hk₀
  have hH := isHypCoord_coordinateQuadMinus (K := K) hN1 b c k₀
  set εY : Y ≃* orthDerived (coordinateQuadMinus N K hN1 b c) :=
    (coordinateMinusWitnessEquiv K hN1 b c eE).trans (orthDerivedProjEquiv _ hH.exists_ne_zero).symm
  obtain ⟨hRnd, hRT⟩ := regular_minusPerp (K := K) (by omega : 5 ≤ N) hirr k₀
  obtain ⟨hXs, hXZ⟩ := isSimpleGroup_orthDerived_and_center_eq_bot hRnd hRT
  have hodd : Odd (N - 1) := by
    obtain ⟨t, ht⟩ := hNe
    exact ⟨t - 1, by omega⟩
  obtain ⟨x₀, y₀, ℓ, hxy, hy1, hyr, hℓ, hxℓ, hx1⟩ :=
    hpair K g (N - 1) hg hK hodd (by omega) b c hirr
  set e₁ := (orthDerivedCongr (coordinateMinusIsometry (K := K) (n := N - 1) (by omega) b c)).trans
    (orthDerivedCongr (minusPerpIsometry (K := K) (n := N) (by omega) b c k₀).symm) with he₁
  set R := (coordinateQuadMinus N K hN1 b c).comp
    (perpSub K (minusIndexEquiv N hN1 (.inl k₀)) (minusIndexEquiv N hN1 (.inr (.inl k₀)))).subtype
    with hR
  set X' := (orthDerived R).map (extendLin hH.ne) with hX'
  set ext : orthDerived (quadMinus (N - 1) K b c) →* ((Fin (2 * N) → K) ≃ₗ[K] (Fin (2 * N) → K)) :=
    (extendLin hH.ne).comp ((orthDerived R).subtype.comp e₁.toMonoidHom) with hext
  have hext_inj : Function.Injective ext :=
    (extendLin_injective hH.ne).comp ((orthDerived R).subtype_injective.comp e₁.injective)
  have hext_mem : ∀ z, ext z ∈ X' := fun z => ⟨_, (e₁ z).2, rfl⟩
  let eX : orthDerived R ≃* X' :=
    (orthDerived R).equivMapOfInjective (extendLin hH.ne) (extendLin_injective hH.ne)
  have hXsimple : IsSimpleGroup X' := eX.symm.isSimpleGroup
  have hXcenter : center X' = ⊥ := lagCenter_eq_bot_of_mulEquiv eX.symm hXZ
  have hXΩ : X' ≤ orthDerived (coordinateQuadMinus N K hN1 b c) := by
    rintro _ ⟨h', hh', rfl⟩
    exact hH.extendLin_mem_orthDerived hh'
  have hXN : X' ≤ normalizer (rootGroup (coordinateQuadMinus N K hN1 b c)
      (Pi.single (minusIndexEquiv N hN1 (.inl k₀)) 1) : Set _) := by
    refine le_normalizer_rootGroup (hXΩ.trans (Subgroup.commutator_le_self _)) ?_
    rintro _ ⟨h', -, rfl⟩
    exact (OmegaPilot.extendLin_mem_stabSub hH.ne h').1
  have hQΩ : rootGroup (coordinateQuadMinus N K hN1 b c)
      (Pi.single (minusIndexEquiv N hN1 (.inl k₀)) 1) ≤
      orthDerived (coordinateQuadMinus N K hN1 b c) :=
    (rootGroup_le_elementaryGroup _ _).trans
      (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hnd hT).1.ge
  have hQne := rootGroup_ne_bot hH (c := minusIndexEquiv N hN1 (.inr (.inr 0)))
    (by simp [(minusIndexEquiv N hN1).injective.eq_iff])
    (by simp [(minusIndexEquiv N hN1).injective.eq_iff])
  have hxy' : ext x₀ * ext y₀ = ext y₀ * ext x₀ := by rw [← map_mul, ← map_mul, hxy]
  have hy1' : ext y₀ ≠ 1 := fun h => hy1 (hext_inj (by rw [h, map_one]))
  have hx1' : ext x₀ ≠ 1 := fun h => hx1 (hext_inj (by rw [h, map_one]))
  have hyr' : ext y₀ ^ (2 ^ g + 1) = 1 := by rw [← map_pow, hyr, map_one]
  have hxℓ' : ext x₀ ^ ℓ = 1 := by rw [← map_pow, hxℓ, map_one]
  obtain ⟨Q₁', X'', x', y', hQ', hQne', hXN', hXs', hXZ', hx', hy', hxy'', hy1'', hyr'', hxℓ'',
    hx1''⟩ := exists_omegaMinusData_of_le εY hQΩ hXΩ (isPGroup_rootGroup _) hQne hXN hXsimple
    hXcenter (hext_mem x₀) (hext_mem y₀) hxy' hy1' hyr' hxℓ' hx1'
  have hk : 0 < 2 * g * (N - 1) := Nat.mul_pos (by omega) (by omega)
  refine ⟨Q₁', X'', x', y', ℓ, hQ', hQne', hXN', hXs', hXZ', hx', hy', hxy'', hy1'', hyr'',
    hℓ.prime, hℓ.ne_two hk, hxℓ'', hx1'', fun j hj hjN hdvd => ?_, fun i hi hiN hdvd => ?_⟩
  · rw [← pow_mul] at hdvd
    have h1 : 2 * g * (N - 1) ∣ 2 * g * (2 * j) := (hℓ.dvd_sub_one_iff hk _).1 hdvd
    have h2 : N - 1 ∣ 2 * j := Nat.dvd_of_mul_dvd_mul_left (k := 2 * g) (by omega) h1
    have hcop : Nat.Coprime (N - 1) 2 := Nat.coprime_two_right.2 hodd
    have h3 : N - 1 ∣ j := hcop.dvd_of_dvd_mul_left h2
    have := Nat.le_of_dvd (by omega) h3
    omega
  · rw [← pow_mul] at hdvd
    have h1 : 2 * g * (N - 1) ∣ 2 * g * i := (hℓ.dvd_sub_one_iff hk _).1 hdvd
    have h2 : N - 1 ∣ i := Nat.dvd_of_mul_dvd_mul_left (k := 2 * g) (by omega) h1
    have := Nat.le_of_dvd (by omega) h2
    omega

end Main

end CFSG.SeitzReduction.SymplecticPilot
