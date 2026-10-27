module

public import CFSG.LocalAnalysis.SteinbergSFOddSymplecticRootCentralizer
public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticLocalComponentPaired

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.OddSymplectic

open Subgroup Module CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.ComponentClassification.CatalogueBOrthogonalDescent
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.SymplecticFourStandard

section TwoGroups

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_mul_self {a : G} (ha : a * a = 1) : IsPGroup 2 (zpowers a) := by
  have h : orderOf a ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact ha)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

theorem exists_isPGroup_two_le_of_commute [Finite G] {H : Subgroup G} {a b : G} (haH : a ∈ H)
    (hbH : b ∈ H) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) :
    ∃ Q : Subgroup G, Q ≤ H ∧ IsPGroup 2 Q ∧ 3 ≤ Nat.card Q := by
  refine ⟨zpowers a ⊔ zpowers b, sup_le ((zpowers_le).mpr haH) ((zpowers_le).mpr hbH),
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self ha)
      (isPGroup_zpowers_of_mul_self hb) ?_,
    three_le_card (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers b)) ha1 hb1 hne⟩
  rw [zpowers_le, mem_normalizer_iff]
  have hc : ∀ k : ℤ, a * b ^ k * a⁻¹ = b ^ k := fun k => by
    rw [(Commute.zpow_right hab k).eq, mul_inv_cancel_right]
  intro x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (hc k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 : a * x * a⁻¹ = a * b ^ k * a⁻¹ := by rw [hc k]; exact hk.symm
    simpa using h1.symm

end TwoGroups

section Config

@[expose] def FixedRootConfigRankOne {P : Type*} [Group P] (β : MulAut P) (K : Type*) [Field K] :
    Prop :=
  ∃ S : Subgroup (fixedSubgroup β), S.Normal ∧ IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
    FixedRootRankOne β (S.map (fixedSubgroup β).subtype)

theorem mem_range_conj_of_mulEquiv {P P' : Type*} [Group P] [Group P'] (e : P ≃* P')
    {β : MulAut P} {β' : MulAut P'} (hint : ∀ x, e (β x) = β' (e x))
    (h : β' ∈ (MulAut.conj : P' →* MulAut P').range) :
    β ∈ (MulAut.conj : P →* MulAut P).range := by
  obtain ⟨p', hp'⟩ := h
  refine ⟨e.symm p', MulEquiv.ext fun x => e.injective ?_⟩
  rw [hint, ← hp', MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem FixedRootConfigRankOne.of_mulEquiv {P P' : Type*} [Group P] [Group P'] {K : Type*}
    [Field K] (e : P ≃* P') {β : MulAut P} {β' : MulAut P'} (hint : ∀ x, e (β x) = β' (e x))
    (h : FixedRootConfigRankOne β K) : FixedRootConfigRankOne β' K := by
  obtain ⟨S, hSn, hSs, ⟨a, b, hab⟩, ⟨φ⟩, hr⟩ := h
  have hfix := OddClassSelector.map_fixedSubgroup_of_comm e β β' hint
  let eF : fixedSubgroup β ≃* fixedSubgroup β' :=
    ((fixedSubgroup β).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hfix)
  let eS : S ≃* S.map eF.toMonoidHom := S.equivMapOfInjective eF.toMonoidHom eF.injective
  have hmapS : (S.map eF.toMonoidHom).map (fixedSubgroup β').subtype =
      (S.map (fixedSubgroup β).subtype).map e.toMonoidHom := by
    rw [map_map, map_map]
    rfl
  have hinf : fixedSubgroup β' ⊓ centralizer (((S.map eF.toMonoidHom).map
      (fixedSubgroup β').subtype : Subgroup P') : Set P') =
      (fixedSubgroup β ⊓ centralizer ((S.map (fixedSubgroup β).subtype : Subgroup P) :
        Set P)).map e.toMonoidHom := by
    rw [hmapS, ← map_centralizer_mulEquiv, ← hfix, ← map_inf_eq _ _ _ e.injective]
  refine ⟨S.map eF.toMonoidHom, hSn.map _ eF.surjective, eS.symm.isSimpleGroup,
    ⟨eS a, eS b, fun h' => hab (eS.injective (by rw [map_mul, map_mul, h']))⟩,
    ⟨eS.symm.trans φ⟩, fun Q hQ hQp => ?_⟩
  have hQ' : Q.map e.symm.toMonoidHom ≤ fixedSubgroup β ⊓
      centralizer ((S.map (fixedSubgroup β).subtype : Subgroup P) : Set P) := by
    have h1 := Subgroup.map_mono (f := e.symm.toMonoidHom) (hQ.trans hinf.le)
    rwa [map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id P by
      ext x; exact e.symm_apply_apply x, map_id] at h1
  obtain ⟨hcard, hout⟩ := hr _ hQ' (hQp.map _)
  refine ⟨by rwa [card_map_of_injective e.symm.injective] at hcard, fun hβ' => ?_⟩
  have h1 := hout fun hβ => hβ' ?_
  · rw [map_eq_bot_iff_of_injective _ e.symm.injective] at h1
    exact h1
  · obtain ⟨p, hp⟩ := hβ
    exact mem_range_conj_of_mulEquiv e.symm (β := β') (β' := β) (fun x => by
      apply e.injective
      rw [hint, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]) ⟨p, hp⟩

end Config

section Lift

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {B : LinearMap.BilinForm F V}

theorem exists_lift_rankOne [Finite F] [FiniteDimensional F V] {K : Type*} [Field K]
    (φ : MulAut (isometryGroup B)) (hφZ : (scalarSigns B).map φ.toMonoidHom = scalarSigns B)
    (hφφ : ∀ g, φ (φ g) = g)
    (h : FixedRootConfigRankOne (CatalogueBFixedCentralQuotient.onQuotient (scalarSigns B) φ hφZ)
      K) :
    ∃ Y : Subgroup (isometryGroup B), CFSG.Assembly.IsComponentOf Y (fixedSubgroup φ) ∧
      (∃ (A : Subgroup Y) (_ : A.Normal), (∀ a ∈ A, (a : isometryGroup B) ∈ scalarSigns B) ∧
        Nonempty (Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
      (∀ z₁ z₂ : isometryGroup B, (∀ y ∈ Y, y * z₁ = z₁ * y) → (∀ y ∈ Y, y * z₂ = z₂ * y) →
        z₁⁻¹ * φ z₁ ∈ scalarSigns B → z₂⁻¹ * φ z₂ ∈ scalarSigns B → z₁ * z₁ ∈ scalarSigns B →
        z₂ * z₂ ∈ scalarSigns B → z₁ * z₂ * (z₂ * z₁)⁻¹ ∈ scalarSigns B →
        z₁ ∉ scalarSigns B → z₂ ∉ scalarSigns B → z₁ * z₂⁻¹ ∉ scalarSigns B → False) ∧
      (CatalogueBFixedCentralQuotient.onQuotient (scalarSigns B) φ hφZ ∉
          (MulAut.conj : projectiveSymplectic B →* MulAut (projectiveSymplectic B)).range →
        ∀ z : isometryGroup B, (∀ y ∈ Y, y * z = z * y) → z⁻¹ * φ z ∈ scalarSigns B →
          z * z ∈ scalarSigns B → z ∉ scalarSigns B → False) := by
  classical
  set β := CatalogueBFixedCentralQuotient.onQuotient (scalarSigns B) φ hφZ with hβ
  obtain ⟨S, hSn, hSs, hSnab, ⟨eS⟩, hr⟩ := h
  set X := S.map (fixedSubgroup β).subtype with hXdef
  have hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup β) :=
    isComponentOf_map_subtype S hSn hSs hSnab
  have : Finite V := Module.finite_of_finite F
  have : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun g : V ≃ₗ[F] V => (g : V → V)) DFunLike.coe_injective
  obtain ⟨Y, hY, ⟨σY, hσYs, -, hσY⟩, -⟩ := OddClassSelector.central_lift (scalarSigns B)
    (scalarSigns_central B) φ hφZ hφφ hX
  set π := QuotientGroup.mk' (scalarSigns B)
  have hmem : ∀ z : isometryGroup B, (∀ y ∈ Y, y * z = z * y) → z⁻¹ * φ z ∈ scalarSigns B →
      π z ∈ fixedSubgroup β ⊓ centralizer (X : Set (projectiveSymplectic B)) := by
    intro z hzY hzφ
    refine mem_inf.mpr ⟨?_, ?_⟩
    · change β (π z) = π z
      rw [hβ, CatalogueBFixedCentralQuotient.onQuotient_mk]
      have h1 : π (z⁻¹ * φ z) = 1 := (QuotientGroup.eq_one_iff _).mpr hzφ
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1.symm
    · rw [mem_centralizer_iff]
      intro s hs
      obtain ⟨y, hy⟩ := hσYs ⟨s, hs⟩
      have hs' : s = (σY y : projectiveSymplectic B) := congrArg Subtype.val hy.symm
      rw [hs', hσY, ← map_mul, ← map_mul, hzY y y.2]
  have hπZ : ∀ z : isometryGroup B, π z = 1 ↔ z ∈ scalarSigns B := fun z =>
    QuotientGroup.eq_one_iff z
  refine ⟨Y, hY, ⟨σY.ker, inferInstance, fun a ha => ?_, ⟨?_⟩⟩, ?_, ?_⟩
  · have h1 : π (a : isometryGroup B) = 1 := by
      rw [← hσY a, ha]
      rfl
    exact (hπZ _).mp h1
  · exact (QuotientGroup.quotientKerEquivOfSurjective σY hσYs).trans
      ((S.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eS)
  · intro z₁ z₂ hz₁ hz₂ hφ₁ hφ₂ h₁₁ h₂₂ hcomm hn₁ hn₂ hn₁₂
    obtain ⟨Q, hQ, hQp, hQ3⟩ := exists_isPGroup_two_le_of_commute (hmem z₁ hz₁ hφ₁)
      (hmem z₂ hz₂ hφ₂) (by rw [← map_mul]; exact (hπZ _).mpr h₁₁)
      (by rw [← map_mul]; exact (hπZ _).mpr h₂₂)
      (by
        have h1 := (hπZ _).mpr hcomm
        rw [map_mul, map_inv, mul_inv_eq_one] at h1
        rw [← map_mul, ← map_mul]
        exact h1)
      (fun h => hn₁ ((hπZ _).mp h)) (fun h => hn₂ ((hπZ _).mp h))
      (fun h => hn₁₂ ((hπZ _).mp (by rw [map_mul, map_inv, h, mul_inv_cancel])))
    have := (hr Q hQ hQp).1
    omega
  · intro hout z hz hφz hzz hnz
    have hQ : zpowers (π z) ≤ fixedSubgroup β ⊓ centralizer (X : Set (projectiveSymplectic B)) :=
      (zpowers_le).mpr (hmem z hz hφz)
    have h1 := (hr _ hQ (isPGroup_zpowers_of_mul_self (by
      rw [← map_mul]; exact (hπZ _).mpr hzz))).2 hout
    rw [zpowers_eq_bot] at h1
    exact hnz ((hπZ _).mp h1)

end Lift

section Reflection

open Matrix

variable {E : Type*} [Field E] (σ : E ≃+* E)

@[expose] def coordReflection (x : Fin 2 → E) : Fin 2 → E := ![-σ (x 0), σ (x 1)]

theorem coordReflection_add (x y : Fin 2 → E) :
    coordReflection σ (x + y) = coordReflection σ x + coordReflection σ y := by
  ext i
  fin_cases i <;> simp [coordReflection, add_comm]

theorem coordReflection_smul (c : E) (x : Fin 2 → E) :
    coordReflection σ (c • x) = σ c • coordReflection σ x := by
  ext i
  fin_cases i <;> simp [coordReflection]

theorem coordReflection_coordReflection (hσ : ∀ x, σ (σ x) = x) (x : Fin 2 → E) :
    coordReflection σ (coordReflection σ x) = x := by
  ext i
  fin_cases i <;> simp [coordReflection, hσ]

theorem hyperbolicForm_coordReflection (hσ : ∀ x, σ (σ x) = x) (x y : Fin 2 → E) :
    CatalogueBUnitaryTwo.hyperbolicForm σ (coordReflection σ x) (coordReflection σ y) =
      -σ (CatalogueBUnitaryTwo.hyperbolicForm σ x y) := by
  rw [CatalogueBUnitaryTwo.hyperbolicForm_apply, CatalogueBUnitaryTwo.hyperbolicForm_apply]
  simp [coordReflection, hσ]
  ring

theorem coordReflection_mulVec {M : Matrix (Fin 2) (Fin 2) E} (h00 : σ (M 0 0) = M 0 0)
    (h11 : σ (M 1 1) = M 1 1) (h01 : σ (M 0 1) = -M 0 1) (h10 : σ (M 1 0) = -M 1 0)
    (x : Fin 2 → E) : coordReflection σ (M *ᵥ x) = M *ᵥ coordReflection σ x := by
  ext i
  fin_cases i
  · simp [coordReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h01]
    ring
  · simp [coordReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h11, h10]

end Reflection

section Plane

open Matrix

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {E : Type*} [Field E]
  [Module E V] [Algebra F E] [IsScalarTower F E V]

theorem coeff_eq_of_eq {σ : E ≃+* E} (hσF : ∀ a : F, σ (algebraMap F E a) = algebraMap F E a)
    {s : E} (hσs : σ s = -s) (hs0 : s ≠ 0) (h2 : (2 : E) ≠ 0) {a b a' b' : F}
    (h : algebraMap F E a + algebraMap F E b * s = algebraMap F E a' + algebraMap F E b' * s) :
    b = b' := by
  have h' := congrArg σ h
  rw [map_add, map_add, map_mul, map_mul, hσF, hσF, hσF, hσF, hσs] at h'
  have h3 : (2 * s) * (algebraMap F E b - algebraMap F E b') = 0 := by linear_combination h - h'
  exact (algebraMap F E).injective
    (sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hs0)))

theorem exists_galois_reflection (B : BilinForm F V) (T : V →ₗ[F] V) {σ : E ≃+* E}
    (hσσ : ∀ x, σ (σ x) = x) (hσF : ∀ a : F, σ (algebraMap F E a) = algebraMap F E a)
    {s : E} (hTs : ∀ v, T v = s • v) (hσs : σ s = -s) (hs0 : s ≠ 0) (h2 : (2 : E) ≠ 0)
    (h : V →ₛₗ[σ.toRingHom] V →ₗ[E] E)
    (hh : ∀ v w, h v w = algebraMap F E (B v (T w)) + algebraMap F E (B v w) * s)
    (Bc : (Fin 2 → E) ≃ₗ[E] V)
    (hBc : ∀ x y, h (Bc x) (Bc y) = CatalogueBUnitaryTwo.hyperbolicForm σ x y) :
    ∃ ρ : V ≃ₗ[F] V, (∀ v w, B (ρ v) (ρ w) = B v w) ∧ (∀ v, ρ (ρ v) = v) ∧
      (∀ v, ρ (T v) = -T (ρ v)) ∧
      (∀ (g : V →ₗ[E] V) (M : Matrix (Fin 2) (Fin 2) E), (∀ x, Bc.symm (g (Bc x)) = M *ᵥ x) →
        σ (M 0 0) = M 0 0 → σ (M 1 1) = M 1 1 → σ (M 0 1) = -M 0 1 → σ (M 1 0) = -M 1 0 →
        ∀ v, ρ (g v) = g (ρ v)) ∧
      ρ (Bc (Pi.single 0 1)) = -Bc (Pi.single 0 1) ∧
        ρ (Bc (Pi.single 1 1)) = Bc (Pi.single 1 1) := by
  classical
  let ρf : V → V := fun v => Bc (coordReflection σ (Bc.symm v))
  have hρadd : ∀ v w, ρf (v + w) = ρf v + ρf w := fun v w => by
    simp only [ρf, map_add, coordReflection_add]
  have hρsmulE : ∀ (c : E) v, ρf (c • v) = σ c • ρf v := fun c v => by
    simp only [ρf, map_smul, coordReflection_smul]
  have hρsmul : ∀ (a : F) v, ρf (a • v) = a • ρf v := fun a v => by
    rw [← algebraMap_smul E a v, hρsmulE, hσF, algebraMap_smul]
  have hρρ : ∀ v, ρf (ρf v) = v := fun v => by
    simp only [ρf, LinearEquiv.symm_apply_apply, coordReflection_coordReflection σ hσσ,
      LinearEquiv.apply_symm_apply]
  let ρL : V →ₗ[F] V := { toFun := ρf, map_add' := hρadd, map_smul' := hρsmul }
  have hinv : Function.Involutive ρL := hρρ
  refine ⟨LinearEquiv.ofInvolutive ρL hinv, fun v w => ?_, hρρ, fun v => ?_,
    fun g M hM h00 h11 h01 h10 v => ?_, ?_, ?_⟩
  · change B (ρf v) (ρf w) = B v w
    have h1 : h (ρf v) (ρf w) = -σ (h v w) := by
      have := hyperbolicForm_coordReflection σ hσσ (Bc.symm v) (Bc.symm w)
      rw [← hBc, ← hBc, Bc.apply_symm_apply, Bc.apply_symm_apply] at this
      exact this
    rw [hh, hh, map_add, map_mul, hσF, hσF, hσs] at h1
    refine coeff_eq_of_eq hσF hσs hs0 h2 (a := B (ρf v) (T (ρf w))) (a' := -B v (T w)) ?_
    rw [h1, map_neg]
    ring
  · change ρf (T v) = -T (ρf v)
    rw [hTs, hρsmulE, hσs, hTs, neg_smul]
  · change ρf (g v) = g (ρf v)
    obtain ⟨x, rfl⟩ := Bc.surjective v
    simp only [ρf, LinearEquiv.symm_apply_apply]
    rw [hM, coordReflection_mulVec σ h00 h11 h01 h10, ← hM, LinearEquiv.apply_symm_apply]
  · change Bc (coordReflection σ (Bc.symm (Bc (Pi.single 0 1)))) = -Bc (Pi.single 0 1)
    rw [LinearEquiv.symm_apply_apply, ← map_neg]
    congr 1
    ext i
    fin_cases i <;> simp [coordReflection]
  · change Bc (coordReflection σ (Bc.symm (Bc (Pi.single 1 1)))) = Bc (Pi.single 1 1)
    rw [LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    fin_cases i <;> simp [coordReflection]

end Plane

section UnitaryReflection

open Matrix

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {E : Type} [Field E]
  [Finite E] [Module E V] [FiniteDimensional E V] [Algebra F E] [IsScalarTower F E V]

open CFSG.LocalAnalysis.ComponentInitial in
theorem exists_unitary_reflection (B : BilinForm F V) (T : V →ₗ[F] V) {ℓ e : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hq3 : ℓ ^ e ≠ 3)
    {sigma : E ≃+* E} (hsig : ∀ x, sigma x = x ^ (ℓ ^ e)) (hσσ : ∀ x, sigma (sigma x) = x)
    (hσF : ∀ a : F, sigma (algebraMap F E a) = algebraMap F E a)
    {s : E} (hTs : ∀ v, T v = s • v) (hσs : sigma s = -s) (hs0 : s ≠ 0)
    (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hh : ∀ v w, h v w = algebraMap F E (B v (T w)) + algebraMap F E (B v w) * s)
    (hdim : finrank E V = 2) {H : Type*} [Group H]
    (Φ : H ≃* CatalogueBUnitaryIsometry.isometryGroup h) {Y : Subgroup H}
    (hY : CFSG.IsComponent Y) :
    ∃ ρ : V ≃ₗ[F] V, (∀ v w, B (ρ v) (ρ w) = B v w) ∧ (∀ v, ρ (ρ v) = v) ∧
      (∀ v, ρ (T v) = -T (ρ v)) ∧
      (∀ y ∈ Y, ∀ v, ρ (((Φ y : CatalogueBUnitaryIsometry.isometryGroup h) : V ≃ₗ[E] V) v) =
        ((Φ y : CatalogueBUnitaryIsometry.isometryGroup h) : V ≃ₗ[E] V) (ρ v)) ∧
      ∃ v w : V, v ≠ 0 ∧ w ≠ 0 ∧ ρ v = -v ∧ ρ w = w := by
  classical
  obtain rfl : sigma = CatalogueBUnitaryTwo.unitaryFieldConjugation ℓ e hE :=
    RingEquiv.ext fun x => by rw [hsig, CatalogueBUnitaryTwo.unitaryFieldConjugation_apply]
  obtain ⟨-, -, hnonsmall⟩ :=
    CatalogueBUnitaryTwo.odd_unitary_all_dimensional_isometry_p_components ℓ e hℓ2 he hE h hsym
      hnd (by omega)
  have hL' := isComponent_map_of_isComponent Φ hY
  obtain ⟨hq, -⟩ := hnonsmall ⟨by omega, fun h' => hq3 (by
    have := congrArg Prod.snd h'
    exact this)⟩
  have : Finite V := Module.finite_of_finite E
  have : Finite (V ≃ₗ[E] V) :=
    Finite.of_injective (fun g : V ≃ₗ[E] V => (g : V → V)) DFunLike.coe_injective
  have hsolv : Group.IsSolvable (CatalogueBUnitaryIsometry.isometryGroup h ⧸
      CatalogueBUnitaryIsometry.specialIsometry h) :=
    Group.isSolvable_of_isSolvable_injective
      (QuotientGroup.kerLift_injective (CatalogueBUnitaryIsometry.isometryDeterminant h))
  have hSU : Y.map Φ.toMonoidHom = CatalogueBUnitaryIsometry.specialIsometry h :=
    CentralQuotientLift.component_eq_of_quasisimple_normal _ hq hsolv hL'
  obtain ⟨-, Bc, t, eSU, hBc, -, ht, hmat, -⟩ :=
    CatalogueBUnitaryTwo.odd_unitary_two_special_linear_isomorphism ℓ e hℓ2 he hE h hsym hnd
      hdim
  have h2 : (2 : E) ≠ 0 := by
    have : CharP E ℓ := finite_field_prime_power_characteristic (Fact.out : ℓ.Prime)
      (by omega : 1 ≤ e * 2) (by rw [hE, ← pow_mul])
    exact Ring.two_ne_zero (by rw [ringChar.eq E ℓ]; exact hℓ2)
  obtain ⟨ρ, hρB, hρρ, hρT, hρg, hρ0, hρ1⟩ :=
    exists_galois_reflection B T hσσ hσF hTs hσs hs0 h2 h hh Bc hBc
  refine ⟨ρ, hρB, hρρ, hρT, fun y hy v => ?_, Bc (Pi.single 0 1), Bc (Pi.single 1 1), ?_, ?_,
    hρ0, hρ1⟩
  · have hyS : Φ y ∈ CatalogueBUnitaryIsometry.specialIsometry h := hSU ▸ ⟨y, hy, rfl⟩
    set g : CatalogueBUnitaryIsometry.specialIsometry h := ⟨Φ y, hyS⟩
    set M := LinearMap.toMatrix' ((Bc.trans g.val.val).trans Bc.symm).toLinearMap with hM
    have hN := hmat g
    set N := (CatalogueBUnitaryTwo.fixedSLMap _ (eSU g)).val with hNdef
    have hfix : ∀ i j, CatalogueBUnitaryTwo.unitaryFieldConjugation ℓ e hE (N i j) = N i j :=
      fun i j => (CatalogueBLinearTwoDescent.mem_fixedSubfield E _ _).mp ((eSU g).val i j).property
    have hNe : ∀ i j, N i j = ((CatalogueBUnitaryTwo.diagonalGL t)⁻¹.val * M *
        (CatalogueBUnitaryTwo.diagonalGL t).val) i j := fun i j => by rw [hN]
    have e00 : N 0 0 = M 0 0 := by
      rw [hNe, CatalogueBUnitaryTwo.diagonalGL_inv_val, CatalogueBUnitaryTwo.diagonalGL_val]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
      field_simp
    have e11 : N 1 1 = M 1 1 := by
      rw [hNe, CatalogueBUnitaryTwo.diagonalGL_inv_val, CatalogueBUnitaryTwo.diagonalGL_val]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have e01 : N 0 1 = ((t⁻¹ : Eˣ) : E) * M 0 1 := by
      rw [hNe, CatalogueBUnitaryTwo.diagonalGL_inv_val, CatalogueBUnitaryTwo.diagonalGL_val]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have e10 : N 1 0 = M 1 0 * (t : E) := by
      rw [hNe, CatalogueBUnitaryTwo.diagonalGL_inv_val, CatalogueBUnitaryTwo.diagonalGL_val]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have hM01 : M 0 1 = (t : E) * N 0 1 := by rw [e01, ← mul_assoc, Units.mul_inv, one_mul]
    have hM10 : M 1 0 = N 1 0 * ((t⁻¹ : Eˣ) : E) := by
      rw [e10, mul_assoc, Units.mul_inv, mul_one]
    have hσt : CatalogueBUnitaryTwo.unitaryFieldConjugation ℓ e hE ((t⁻¹ : Eˣ) : E) =
        -((t⁻¹ : Eˣ) : E) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_neg]
    have hMv : ∀ x, Bc.symm ((g.val.val : V ≃ₗ[E] V).toLinearMap (Bc x)) = M *ᵥ x := fun x => by
      rw [hM, LinearMap.toMatrix'_mulVec]
      rfl
    refine hρg (g.val.val : V ≃ₗ[E] V).toLinearMap M hMv (by rw [← e00, hfix]) (by rw [← e11, hfix])
      ?_ ?_ v
    · rw [hM01, map_mul, ht, hfix]
      ring
    · rw [hM10, map_mul, hσt, hfix]
      ring
  · exact (LinearEquiv.map_ne_zero_iff Bc).mpr (by simp)
  · exact (LinearEquiv.map_ne_zero_iff Bc).mpr (by simp)

end UnitaryReflection

theorem exists_sq_eq_multiplierUnit_of_mem_range {r : ℕ} (hr : 1 ≤ r) {F : Type} [Field F]
    [Finite F] (A : gsp r F)
    (h : SymplecticHigher.conjAut r F A ∈
      (MulAut.conj : StatedProj (StatedSp r F) →* MulAut (StatedProj (StatedSp r F))).range) :
    ∃ c : F, c ^ 2 = (multiplierUnit A : F) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨g, rfl⟩ := proj_surjective p
  have h1 : SymplecticHigher.conjAut r F (A * ⟨g, statedSp_le_gsp g.2⟩⁻¹) * fieldAut r F 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, conjAut_statedSp, hp, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := (conjAut_mul_fieldAut_eq_one_iff hr _ _).mp h1
  have hA : ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      (c : F) • ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
    have h2 : (A : GL (Fin r ⊕ Fin r) F) =
        Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c * (g : GL (Fin r ⊕ Fin r) F) := by
      rw [← hc]
      simp
    rw [h2, Matrix.smul_eq_diagonal_mul]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hspec := multiplierUnit_spec A
  rw [hA, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    SymplecticTorusWeyl.mem_statedSp_iff.mp g.2] at hspec
  have : NeZero r := ⟨by omega⟩
  exact ⟨c, by rw [sq]; exact smul_formJ_injective r hspec⟩

section Linear

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {B : LinearMap.BilinForm F V}

theorem paired_small_four_false (hB : B.IsAlt) {c : F} (hc : c ^ 2 = -1) (T : V ≃ₗ[F] V) (μ : Fˣ)
    (hsim : ∀ x y, B (T x) (T y) = (μ : F) * B x y)
    (hnonscalar : ∀ a : F, T.toLinearMap ≠ a • (1 : Module.End F V)) {l : F} (hl0 : l ≠ 0)
    (hμ : (μ : F) = -l ^ 2) {P M : Submodule F V} (hPT : ∀ v ∈ P, T v = l • v)
    (hMT : ∀ w ∈ M, T w = -(l • w)) (hisoP : ∀ v ∈ P, ∀ w ∈ P, B v w = 0)
    (hisoM : ∀ v ∈ M, ∀ w ∈ M, B v w = 0)
    (hpair : ∀ w ∈ M, (∀ v ∈ P, B v w = 0) → w = 0) (bP : Basis (Fin 2) F P)
    (hdM : finrank F M = 2) (hdV : finrank F V = 4) {Y : Subgroup (isometryGroup B)}
    (hYT : ∀ y ∈ Y, ∀ x, (y : V ≃ₗ[F] V) (T x) = T ((y : V ≃ₗ[F] V) x))
    (hYM : ∀ y ∈ Y, ∀ w ∈ M, (y : V ≃ₗ[F] V) w ∈ M)
    (hdet : ∀ y ∈ Y, ∃ m : Matrix (Fin 2) (Fin 2) F, m.det = 1 ∧
      ∀ j, (y : V ≃ₗ[F] V) (bP j) = m 0 j • (bP 0 : V) + m 1 j • (bP 1 : V))
    (hfour : ∀ z₁ z₂ : isometryGroup B, (∀ y ∈ Y, y * z₁ = z₁ * y) →
      (∀ y ∈ Y, y * z₂ = z₂ * y) → z₁⁻¹ * similitudeConjugation B T μ hsim z₁ ∈ scalarSigns B →
      z₂⁻¹ * similitudeConjugation B T μ hsim z₂ ∈ scalarSigns B → z₁ * z₁ ∈ scalarSigns B →
      z₂ * z₂ ∈ scalarSigns B → z₁ * z₂ * (z₂ * z₁)⁻¹ ∈ scalarSigns B →
      z₁ ∉ scalarSigns B → z₂ ∉ scalarSigns B → z₁ * z₂⁻¹ ∉ scalarSigns B → False) : False := by
  classical
  set b : Fin 2 → V := fun i => (bP i : V) with hbdef
  have hbP : ∀ i, b i ∈ P := fun i => (bP i).2
  have hpair' : ∀ w ∈ M, (∀ v ∈ P, B w v = 0) → w = 0 := fun w hw h0 =>
    hpair w hw fun v hv => by rw [← hB.neg_eq w v, h0 v hv, neg_zero]
  have hdP : finrank F P = 2 := by rw [Module.finrank_eq_card_basis bP, Fintype.card_fin]
  have hex : ∀ j : Fin 2, ∃ w ∈ M, ∀ v : P, B w v = (-bP.coord j) v := fun j =>
    ProjectiveSymplectic.exists_bilin_eq_of_pairing hpair' (hdM.trans hdP.symm) (-bP.coord j)
  choose d hdM' hdB using hex
  have hbb : ∀ i j, B (b i) (b j) = 0 := fun i j => hisoP _ (hbP i) _ (hbP j)
  have hdd : ∀ i j, B (d i) (d j) = 0 := fun i j => hisoM _ (hdM' i) _ (hdM' j)
  have hdb : ∀ i j, B (d i) (b j) = -(if i = j then 1 else 0) := fun i j => by
    rw [hdB i (bP j), LinearMap.neg_apply, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply]
    exact congrArg Neg.neg (if_congr eq_comm rfl rfl)
  have hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0 := fun i j => by
    rw [← hB.neg_eq, hdb j i, neg_neg]
    exact if_congr eq_comm rfl rfl
  obtain ⟨bV, hbV⟩ : ∃ bV : Basis (Fin 2 ⊕ Fin 2) F V, ⇑bV = Sum.elim b d :=
    ⟨basisOfLinearIndependentOfCardEqFinrank
      (ProjectiveSymplectic.linearIndependent_sumElim' hbb hdd hbd hdb)
      (by rw [Fintype.card_sum, Fintype.card_fin, hdV]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hbVl : ∀ i, bV (Sum.inl i) = b i := fun i => by rw [hbV]; rfl
  have hbVr : ∀ i, bV (Sum.inr i) = d i := fun i => by rw [hbV]; rfl
  have hMexp : ∀ w ∈ M, w = B (b 0) w • d 0 + B (b 1) w • d 1 := by
    intro w hw
    set w' := w - (B (b 0) w • d 0 + B (b 1) w • d 1) with hw'def
    have hw' : w' ∈ M :=
      sub_mem hw (add_mem (M.smul_mem _ (hdM' 0)) (M.smul_mem _ (hdM' 1)))
    have hk : ∀ k, B (b k) w' = 0 := by
      intro k
      rw [hw'def, map_sub, map_add, map_smul, map_smul, hbd, hbd, smul_eq_mul, smul_eq_mul]
      fin_cases k <;> simp
    have h0 : ∀ v ∈ P, B v w' = 0 := by
      intro v hv
      have hv' : v = bP.repr ⟨v, hv⟩ 0 • b 0 + bP.repr ⟨v, hv⟩ 1 • b 1 := by
        have h1 := congrArg Subtype.val (bP.sum_repr ⟨v, hv⟩)
        rw [Fin.sum_univ_two] at h1
        simpa only [Submodule.coe_add, Submodule.coe_smul] using h1.symm
      rw [hv', map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hk, hk, smul_zero, smul_zero, add_zero]
    exact sub_eq_zero.mp (hpair _ hw' h0)
  have hTb : ∀ i, T (b i) = l • b i := fun i => hPT _ (hbP i)
  have hTd : ∀ i, T (d i) = -(l • d i) := fun i => hMT _ (hdM' i)
  have hTT : ∀ v, T (T v) = (l ^ 2) • v := by
    have h : T.toLinearMap.comp T.toLinearMap = (l ^ 2) • LinearMap.id := bV.ext fun c => by
      rcases c with i | i
      · rw [hbVl, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hTb, map_smul, hTb,
          smul_smul, LinearMap.smul_apply, LinearMap.id_apply, sq]
      · rw [hbVr, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hTd, map_neg, map_smul, hTd,
          smul_neg, neg_neg, smul_smul, LinearMap.smul_apply, LinearMap.id_apply, sq]
    intro v
    exact LinearMap.congr_fun h v
  set f : Fin 2 ⊕ Fin 2 → V := Sum.elim ![d 1, -d 0] ![-b 1, b 0] with hf
  set ys : V →ₗ[F] V := bV.constr F f with hys
  have hys_b0 : ys (b 0) = d 1 := by rw [← hbVl, hys, Basis.constr_basis]; rfl
  have hys_b1 : ys (b 1) = -d 0 := by rw [← hbVl, hys, Basis.constr_basis]; rfl
  have hys_d0 : ys (d 0) = -b 1 := by rw [← hbVr, hys, Basis.constr_basis]; rfl
  have hys_d1 : ys (d 1) = b 0 := by rw [← hbVr, hys, Basis.constr_basis]; rfl
  have hys2 : Function.Involutive ys := by
    have h : ys.comp ys = LinearMap.id := bV.ext fun c => by
      rcases c with i | i <;> fin_cases i <;>
        simp [hbVl, hbVr, hys_b0, hys_b1, hys_d0, hys_d1]
    intro v
    exact LinearMap.congr_fun h v
  have hysB : ∀ u v, B (ys u) (ys v) = B u v := by
    have h : B.compl₁₂ ys ys = B := LinearMap.BilinForm.ext_basis bV fun i j => by
      rw [LinearMap.compl₁₂_apply]
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [hbVl, hbVr, hys_b0, hys_b1, hys_d0, hys_d1, hbb, hdd, hbd, hdb]
    intro u v
    rw [← LinearMap.compl₁₂_apply, h]
  have hysT : ∀ v, ys (T v) = -T (ys v) := by
    have h : ys.comp T.toLinearMap = -(T.toLinearMap.comp ys) := bV.ext fun c => by
      rcases c with i | i <;> fin_cases i <;>
        simp [hbVl, hbVr, hTb, hTd, hys_b0, hys_b1, hys_d0, hys_d1]
    intro v
    exact LinearMap.congr_fun h v
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_eq_neg] at hc
    exact one_ne_zero hc
  obtain ⟨a, ha⟩ : ∃ a : F, a = c * l⁻¹ := ⟨_, rfl⟩
  have hal : a * l = c := by rw [ha, mul_assoc, inv_mul_cancel₀ hl0, mul_one]
  have ha2 : a ^ 2 * l ^ 2 = -1 := by rw [← mul_pow, hal, hc]
  have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero hc0 (inv_ne_zero hl0)
  set xsL : V →ₗ[F] V := a • T.toLinearMap with hxsL
  have hxs : ∀ v, xsL v = a • T v := fun v => rfl
  have hxs2 : ∀ v, xsL (xsL v) = -v := fun v => by
    rw [hxs, hxs, map_smul, hTT, smul_smul, smul_smul,
      show a * a * l ^ 2 = a ^ 2 * l ^ 2 by ring, ha2, neg_one_smul]
  let xsE : V ≃ₗ[F] V := LinearEquiv.ofLinearMap xsL (-xsL)
    (LinearMap.ext fun v => by simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg, hxs2,
      neg_neg, LinearMap.id_apply])
    (LinearMap.ext fun v => by simp only [LinearMap.comp_apply, LinearMap.neg_apply,
      hxs2, neg_neg, LinearMap.id_apply])
  have hxsB : ∀ u v, B (xsL u) (xsL v) = B u v := fun u v => by
    rw [hxs, hxs, map_smul, map_smul, LinearMap.smul_apply, hsim, hμ, smul_eq_mul, smul_eq_mul]
    linear_combination (B u v) * (-ha2)
  let z₁ : isometryGroup B := ⟨xsE, (mem_isometryGroup_iff B _).mpr hxsB⟩
  let ysE : V ≃ₗ[F] V := LinearEquiv.ofInvolutive ys hys2
  let z₂ : isometryGroup B := ⟨ysE, (mem_isometryGroup_iff B _).mpr hysB⟩
  have hz₁ : ∀ v, (z₁ : V ≃ₗ[F] V) v = a • T v := fun v => rfl
  have hz₂ : ∀ v, (z₂ : V ≃ₗ[F] V) v = ys v := fun v => rfl
  have hz₂z₂ : z₂ * z₂ = 1 := Subtype.ext (LinearEquiv.ext fun v => hys2 v)
  have hz₂inv : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂z₂
  refine hfour z₁ z₂ (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ ?_ (Or.inl hz₂z₂) ?_ ?_ ?_ ?_
  ·
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    change (y : V ≃ₗ[F] V) ((z₁ : V ≃ₗ[F] V) v) = (z₁ : V ≃ₗ[F] V) ((y : V ≃ₗ[F] V) v)
    rw [hz₁, hz₁, map_smul, hYT y hy]
  ·
    obtain ⟨m, hmdet, hmexp⟩ := hdet y hy
    set N : Fin 2 → Fin 2 → F := fun i j => B (b i) ((y : V ≃ₗ[F] V) (d j)) with hN
    have hyd : ∀ j, (y : V ≃ₗ[F] V) (d j) = N 0 j • d 0 + N 1 j • d 1 := fun j =>
      hMexp _ (hYM y hy _ (hdM' j))
    have hyb : ∀ j, (y : V ≃ₗ[F] V) (b j) = m 0 j • b 0 + m 1 j • b 1 := hmexp
    have horth : ∀ k j, m 0 k * N 0 j + m 1 k * N 1 j = if k = j then 1 else 0 := by
      intro k j
      have h1 := (mem_isometryGroup_iff B _).mp y.2 (b k) (d j)
      rw [hyb k, hbd] at h1
      rw [← h1, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have hdet2 : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hmdet
    have h00 : m 0 0 * N 0 0 + m 1 0 * N 1 0 = 1 := by
      have h := horth 0 0
      rwa [ite_eq_left rfl] at h
    have h01 : m 0 0 * N 0 1 + m 1 0 * N 1 1 = 0 := by
      have h := horth 0 1
      rwa [ite_eq_right (by decide)] at h
    have h10 : m 0 1 * N 0 0 + m 1 1 * N 1 0 = 0 := by
      have h := horth 1 0
      rwa [ite_eq_right (by decide)] at h
    have h11 : m 0 1 * N 0 1 + m 1 1 * N 1 1 = 1 := by
      have h := horth 1 1
      rwa [ite_eq_left rfl] at h
    have hN00 : N 0 0 = m 1 1 := by
      linear_combination -N 0 0 * hdet2 + m 1 1 * h00 - m 1 0 * h10
    have hN01 : N 0 1 = -m 1 0 := by
      linear_combination -N 0 1 * hdet2 + m 1 1 * h01 - m 1 0 * h11
    have hN10 : N 1 0 = -m 0 1 := by
      linear_combination -N 1 0 * hdet2 + m 0 0 * h10 - m 0 1 * h00
    have hN11 : N 1 1 = m 0 0 := by
      linear_combination -N 1 1 * hdet2 + m 0 0 * h11 - m 0 1 * h01
    have hcomm : (y : V ≃ₗ[F] V).toLinearMap.comp ys = ys.comp (y : V ≃ₗ[F] V).toLinearMap :=
      bV.ext fun c => by
        rcases c with i | i <;> fin_cases i
        · simp only [hbVl, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Fin.zero_eta,
            Fin.isValue, hys_b0, hyd, hyb, map_add, map_smul, hys_b1, hN01, hN11]
          module
        · simp only [hbVl, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Fin.mk_one,
            Fin.isValue, hys_b1, map_neg, hyd, hyb, map_add, map_smul, hys_b0, hN00, hN10]
          module
        · simp only [hbVr, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Fin.zero_eta,
            Fin.isValue, hys_d0, map_neg, hyb, hyd, map_add, map_smul, hys_d1, hN00, hN10]
          module
        · simp only [hbVr, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Fin.mk_one,
            Fin.isValue, hys_d1, hyb, hyd, map_add, map_smul, hys_d0, hN01, hN11]
          module
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    change (y : V ≃ₗ[F] V) ((z₂ : V ≃ₗ[F] V) v) = (z₂ : V ≃ₗ[F] V) ((y : V ≃ₗ[F] V) v)
    rw [hz₂, hz₂]
    exact LinearMap.congr_fun hcomm v
  ·
    have h1 : similitudeConjugation B T μ hsim z₁ = z₁ := by
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      rw [similitudeConjugation_apply, hz₁, hz₁, map_smul, LinearEquiv.apply_symm_apply]
    rw [h1, inv_mul_cancel]
    exact one_mem _
  ·
    have h1 : similitudeConjugation B T μ hsim z₂ = negIsometry B * z₂ := by
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      rw [similitudeConjugation_apply, hz₂]
      change T (ys (T.symm v)) = -(ys v)
      have h2 := hysT (T.symm v)
      rw [LinearEquiv.apply_symm_apply] at h2
      rw [h2, neg_neg]
    rw [h1, ← mul_assoc, (Subgroup.mem_center_iff.mp (negIsometry_central B) z₂⁻¹),
      mul_assoc, inv_mul_cancel, mul_one]
    exact Or.inr rfl
  ·
    refine Or.inr (Subtype.ext (LinearEquiv.ext fun v => ?_))
    exact hxs2 v
  ·
    have h1 : z₁ * z₂ = negIsometry B * (z₂ * z₁) := by
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      change a • T (ys v) = -(ys (a • T v))
      rw [map_smul, hysT, smul_neg, neg_neg]
    rw [h1, mul_inv_cancel_right]
    exact Or.inr rfl
  ·
    rintro (h | h)
    · apply hnonscalar a⁻¹
      refine LinearMap.ext fun v => ?_
      have h1 : a • T v = v := congrArg (fun z : isometryGroup B => (z : V ≃ₗ[F] V) v) h
      rw [LinearEquiv.coe_toLinearMap, LinearMap.smul_apply, Module.End.one_apply]
      calc T v = a⁻¹ • (a • T v) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
        _ = a⁻¹ • v := by rw [h1]
    · apply hnonscalar (-a⁻¹)
      refine LinearMap.ext fun v => ?_
      have h1 : a • T v = -v := congrArg (fun z : isometryGroup B => (z : V ≃ₗ[F] V) v) h
      rw [LinearEquiv.coe_toLinearMap, LinearMap.smul_apply, Module.End.one_apply]
      calc T v = a⁻¹ • (a • T v) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
        _ = (-a⁻¹) • v := by rw [h1, smul_neg, neg_smul]
  ·
    have h1 : B (b 1) (ys (b 0)) = 1 := by rw [hys_b0, hbd]; rfl
    rintro (h | h)
    · have h2 : ys (b 0) = b 0 := congrArg (fun z : isometryGroup B => (z : V ≃ₗ[F] V) (b 0)) h
      rw [h2, hbb] at h1
      exact zero_ne_one h1
    · have h2 : ys (b 0) = -b 0 :=
        congrArg (fun z : isometryGroup B => (z : V ≃ₗ[F] V) (b 0)) h
      rw [h2, map_neg, hbb, neg_zero] at h1
      exact zero_ne_one h1
  ·
    rw [hz₂inv]
    have h1 : ((z₁ * z₂ : isometryGroup B) : V ≃ₗ[F] V) (b 0) = -(c • d 1) := by
      change (z₁ : V ≃ₗ[F] V) ((z₂ : V ≃ₗ[F] V) (b 0)) = _
      rw [hz₂, hys_b0, hz₁, hTd, smul_neg, smul_smul, hal]
    have h3 : B (b 1) (-(c • d 1)) = -c := by rw [map_neg, map_smul, hbd]; simp
    rintro (h | h)
    · rw [h] at h1
      have h1' : b 0 = -(c • d 1) := h1
      rw [← h1', hbb, zero_eq_neg] at h3
      exact hc0 h3
    · rw [h, negIsometry_apply] at h1
      rw [← h1, map_neg, hbb, neg_zero, zero_eq_neg] at h3
      exact hc0 h3


theorem linear_case_rankOne_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) {r : ℕ} (hr : 2 ≤ r) (hdim : finrank F V = 2 * r)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (T : V ≃ₗ[F] V) (d μ : Fˣ)
    (hsquare : ∀ x, T (T x) = (d : F) • x) (hsim : ∀ x y, B (T x) (T y) = (μ : F) * B x y)
    (hnonscalar : ∀ c : F, T.toLinearMap ≠ c • (1 : Module.End F V))
    {Y : Subgroup (isometryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (symplecticOperatorCentralizer B T.toLinearMap))
    (A : Subgroup Y) [A.Normal] (hAZ : ∀ a ∈ A, (a : isometryGroup B) ∈ scalarSigns B)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hfour : ∀ z₁ z₂ : isometryGroup B, (∀ y ∈ Y, y * z₁ = z₁ * y) →
      (∀ y ∈ Y, y * z₂ = z₂ * y) → z₁⁻¹ * similitudeConjugation B T μ hsim z₁ ∈ scalarSigns B →
      z₂⁻¹ * similitudeConjugation B T μ hsim z₂ ∈ scalarSigns B → z₁ * z₁ ∈ scalarSigns B →
      z₂ * z₂ ∈ scalarSigns B → z₁ * z₂ * (z₂ * z₁)⁻¹ ∈ scalarSigns B →
      z₁ ∉ scalarSigns B → z₂ ∉ scalarSigns B → z₁ * z₂⁻¹ ∉ scalarSigns B → False)
    (hone : (¬ ∃ c : F, c ^ 2 = μ) → ∀ z : isometryGroup B, (∀ y ∈ Y, y * z = z * y) →
      z⁻¹ * similitudeConjugation B T μ hsim z ∈ scalarSigns B → z * z ∈ scalarSigns B →
      z ∉ scalarSigns B → False) : False := by
  classical
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F ℓ]; exact hℓ2)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
  set Agl : LinearMap.GeneralLinearGroup F V := LinearMap.GeneralLinearGroup.ofLinearEquiv T
    with hAgl
  have hAA : (Agl : Module.End F V) * (Agl : Module.End F V) = (d : F) • 1 :=
    LinearMap.ext fun x => hsquare x
  obtain ⟨hε, hsplit, hnonsplit⟩ :=
    UnitaryHigher.odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 he hF (by omega)
      hdim hB hnd (A := Agl) hnonscalar (Units.ne_zero d) hAA hsim
  have hY' : CFSG.Assembly.IsComponentOf Y
      (symplecticOperatorCentralizer B (Agl : Module.End F V)) := hY
  have hYC : Y ≤ symplecticOperatorCentralizer B (Agl : Module.End F V) := hY'.1
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hYC).mp hY'
  let eY : Y.subgroupOf (symplecticOperatorCentralizer B (Agl : Module.End F V)) ≃* Y :=
    Subgroup.subgroupOfEquivOfLe hYC
  obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map eY.symm A eQ
  have hA₁Z : ∀ a ∈ A.map eY.symm.toMonoidHom,
      ((a : symplecticOperatorCentralizer B (Agl : Module.End F V)) : isometryGroup B) ∈
        scalarSigns B := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAZ a ha
  have hYT : ∀ y ∈ Y, ∀ x, (y : V ≃ₗ[F] V) (T x) = T ((y : V ≃ₗ[F] V) x) := fun y hy x =>
    (mem_symplecticOperatorCentralizer_iff B _ y).mp (hYC hy) x
  by_cases hsq : ∃ l : F, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hl
      exact Units.ne_zero d hl.symm
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    rcases hε with h1 | h1
    ·
      obtain ⟨-, -, -, hndP, hndM, e, he'⟩ := hpos h1
      let Φ := ((centralizerSimilitudeEquiv B Agl).trans e).trans
        (MulEquiv.prodCongr (sesqUnitaryIsometryEquiv _) (sesqUnitaryIsometryEquiv _))
      have hΦ1 : ∀ (g : symplecticOperatorCentralizer B (Agl : Module.End F V))
          (x : eigenPlus l (Agl : Module.End F V)),
          (((Φ g).1.val x : eigenPlus l (Agl : Module.End F V)) : V) =
            (g : isometryGroup B).val x := fun g x =>
        LinearMap.congr_fun (he' (centralizerSimilitudeEquiv B Agl g)).1 x
      have hΦ2 : ∀ (g : symplecticOperatorCentralizer B (Agl : Module.End F V))
          (x : eigenMinus l (Agl : Module.End F V)),
          (((Φ g).2.val x : eigenMinus l (Agl : Module.End F V)) : V) =
            (g : isometryGroup B).val x := fun g x =>
        LinearMap.congr_fun (he' (centralizerSimilitudeEquiv B Agl g)).2 x
      rcases CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
          (isComponent_map_of_isComponent Φ hY₁) with h2' | h1'
      · have h2'' : ∀ x ∈ Y.subgroupOf (symplecticOperatorCentralizer B
            (Agl : Module.End F V)), (Φ x).2 = 1 := fun x hx => h2' _ (mem_map_of_mem _ hx)
        obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := OddClassSelector.restrict_component Φ hY₁ h2''
        refine split_half_false hodd h2 hB hndP hP hM ρ₁ hρ₁i hρ₁c (fun y hy w hw => ?_) _
          hA₁Z hn hK eQ₁
        have h3 := hΦ2 y ⟨w, hw⟩
        rw [h2'' y hy] at h3
        exact h3.symm
      · have h1'' : ∀ x ∈ Y.subgroupOf (symplecticOperatorCentralizer B
            (Agl : Module.End F V)), ((Φ.trans MulEquiv.prodComm) x).2 = 1 := fun x hx =>
          h1' _ (mem_map_of_mem _ hx)
        obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ :=
          OddClassSelector.restrict_component (Φ.trans MulEquiv.prodComm) hY₁ h1''
        refine split_half_false hodd h2 hB hndM hM hP ρ₁ hρ₁i hρ₁c (fun y hy w hw => ?_) _
          hA₁Z hn hK eQ₁
        have h3 := hΦ1 y ⟨w, hw⟩
        rw [show (Φ y).1 = 1 from h1'' y hy] at h3
        exact h3.symm
    ·
      obtain ⟨hisoP, hisoM, hdP, hdM, -, hpairMP, e, heP, -⟩ := hneg h1
      obtain ⟨bP⟩ : Nonempty (Basis (Fin r) F (eigenPlus l (Agl : Module.End F V))) :=
        ⟨Module.finBasisOfFinrankEq F _ hdP⟩
      let Fm : symplecticOperatorCentralizer B (Agl : Module.End F V) ≃* GL (Fin r) F :=
        ((centralizerSimilitudeEquiv B Agl).trans e).trans
          (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)
      have hres : ∀ (g : symplecticOperatorCentralizer B (Agl : Module.End F V))
          (v : eigenPlus l (Agl : Module.End F V)),
          ((((e (centralizerSimilitudeEquiv B Agl g) : LinearMap.GeneralLinearGroup F
            (eigenPlus l (Agl : Module.End F V))) : Module.End F
              (eigenPlus l (Agl : Module.End F V))) v : eigenPlus l (Agl : Module.End F V)) :
            V) = (g : isometryGroup B).val v := fun g v =>
        LinearMap.congr_fun (heP (centralizerSimilitudeEquiv B Agl g)) v
      have hFm : ∀ (g : symplecticOperatorCentralizer B (Agl : Module.End F V)) (i j : Fin r),
          ((Fm g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
            bP.repr (((e (centralizerSimilitudeEquiv B Agl g) : LinearMap.GeneralLinearGroup F
              (eigenPlus l (Agl : Module.End F V))) : Module.End F
                (eigenPlus l (Agl : Module.End F V))) (bP j)) i := fun g i j =>
        LinearMap.toMatrixAlgEquiv_apply bP _ i j
      have hA₁sc : ∀ a ∈ A.map eY.symm.toMonoidHom, ∃ c : F,
          ((Fm a : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = c • 1 := by
        intro a ha
        obtain ⟨c, hc⟩ : ∃ c : F, ∀ v,
            ((a : symplecticOperatorCentralizer B (Agl : Module.End F V)) :
              isometryGroup B).val v = c • v := by
          rcases hA₁Z a ha with h | h
          · exact ⟨1, fun v => by rw [h, one_smul]; rfl⟩
          · exact ⟨-1, fun v => by rw [h, negIsometry_apply, neg_one_smul]⟩
        refine ⟨c, Matrix.ext fun i j => ?_⟩
        rw [hFm]
        have h3 : ((e (centralizerSimilitudeEquiv B Agl a) : LinearMap.GeneralLinearGroup F
            (eigenPlus l (Agl : Module.End F V))) : Module.End F
              (eigenPlus l (Agl : Module.End F V))) (bP j) = c • bP j :=
          Subtype.ext (by rw [hres, hc]; rfl)
        rw [h3, map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
          Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, smul_eq_mul]
        exact congrArg (c * ·) (if_congr eq_comm rfl rfl)
      obtain ⟨hr2, hF5, hSL⟩ := gl_component_quotient hodd hr Fm hY₁ _ hA₁sc hn hK eQ₁
      subst hr2
      obtain ⟨c, hc⟩ : ∃ c : F, c ^ 2 = -1 := by
        have := Fintype.ofFinite F
        obtain ⟨c, hc⟩ : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.mpr (by
          rw [← Nat.card_eq_fintype_card, hF5]; decide)
        exact ⟨c, by rw [sq, ← hc]⟩
      have hμ : (μ : F) = -l ^ 2 := by
        rw [hl]
        field_simp at h1
        linear_combination h1
      have hPT : ∀ v ∈ eigenPlus l (Agl : Module.End F V), T v = l • v := fun v hv => by
        have h3 : l⁻¹ • T v - v = 0 := LinearMap.mem_ker.mp hv
        rw [sub_eq_zero] at h3
        calc T v = l • (l⁻¹ • T v) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
          _ = l • v := by rw [h3]
      have hMT : ∀ w ∈ eigenMinus l (Agl : Module.End F V), T w = -(l • w) := fun w hw => by
        have h3 : l⁻¹ • T w + w = 0 := LinearMap.mem_ker.mp hw
        rw [add_eq_zero_iff_eq_neg] at h3
        calc T w = l • (l⁻¹ • T w) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
          _ = -(l • w) := by rw [h3, smul_neg]
      have hYM : ∀ y ∈ Y, ∀ w ∈ eigenMinus l (Agl : Module.End F V),
          (y : V ≃ₗ[F] V) w ∈ eigenMinus l (Agl : Module.End F V) := fun y hy w hw =>
        UnitaryHigher.mapsTo_eigenMinus_of_mem l
          (centralizer_mem_similitudeCentralizer B Agl ⟨y, hYC hy⟩) hw
      have hdet : ∀ y ∈ Y, ∃ m : Matrix (Fin 2) (Fin 2) F, m.det = 1 ∧
          ∀ j, (y : V ≃ₗ[F] V) (bP j) = m 0 j • (bP 0 : V) + m 1 j • (bP 1 : V) := by
        intro y hy
        refine ⟨((Fm ⟨y, hYC hy⟩ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), ?_, fun j => ?_⟩
        · have hmem : Fm ⟨y, hYC hy⟩ ∈ CatalogueBGeneralLinear.specialLinearRange 2 F := by
            rw [← hSL]
            exact ⟨⟨y, hYC hy⟩, hy, rfl⟩
          obtain ⟨s, hs⟩ := hmem
          rw [← hs]
          exact s.2
        · have h4 : ((((e (centralizerSimilitudeEquiv B Agl ⟨y, hYC hy⟩) :
              LinearMap.GeneralLinearGroup F (eigenPlus l (Agl : Module.End F V))) :
                Module.End F (eigenPlus l (Agl : Module.End F V))) (bP j) :
                  eigenPlus l (Agl : Module.End F V)) : V) = (y : V ≃ₗ[F] V) (bP j) :=
            hres ⟨y, hYC hy⟩ (bP j)
          have h3 := bP.sum_repr (((e (centralizerSimilitudeEquiv B Agl ⟨y, hYC hy⟩) :
            LinearMap.GeneralLinearGroup F (eigenPlus l (Agl : Module.End F V))) :
              Module.End F (eigenPlus l (Agl : Module.End F V))) (bP j))
          rw [Fin.sum_univ_two] at h3
          rw [← h4, hFm, hFm]
          conv_lhs => rw [← h3]
          rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
      have hdV : finrank F V = 4 := by rw [hdim]
      exact paired_small_four_false hB hc T μ hsim hnonscalar hl0 hμ hPT hMT hisoP hisoM hpairMP
        bP hdM hdV hYT hYM hdet hfour
  · push Not at hsq
    obtain ⟨-, hFld, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField (Agl : Module.End F V)) := hFld.toField
    have hEodd : Odd (Nat.card (scalarSquareField (Agl : Module.End F V))) := by
      rw [hcard]
      exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField (Agl : Module.End F V)) V :=
      CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (Agl : Module.End F V)
    have hscal : ∀ a ∈ A.map eY.symm.toMonoidHom,
        ∃ c : scalarSquareField (Agl : Module.End F V), ∀ v,
          ((a : symplecticOperatorCentralizer B (Agl : Module.End F V)) :
            isometryGroup B).val v = c • v := by
      intro a ha
      rcases hA₁Z a ha with h | h
      · exact ⟨1, fun v => by rw [h, one_smul]; rfl⟩
      · exact ⟨-1, fun v => by rw [h, negIsometry_apply, neg_one_smul]⟩
    have hℓ3 : 3 ≤ ℓ ^ e := by
      have := hℓ.two_le
      have : ℓ ≤ ℓ ^ e := Nat.le_self_pow (by omega) ℓ
      have : ℓ ≠ 2 := hℓ2
      omega
    rcases hε with h1 | h1
    ·
      obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos h1
      obtain ⟨-, h5, -⟩ := sp_component_quotient hEodd hBEalt hBEnd (by omega)
        (evaluationIsometryEquiv B Agl (isometryGroup BE)
          (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w) (mem_isometryGroup_iff BE) hiff)
        hY₁ _ hscal hn hK eQ₁
      rw [hcard] at h5
      nlinarith
    ·
      obtain ⟨h, hhE, hsymm, hsep, hiff⟩ := hneg h1
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (Agl : Module.End F V)]
        scalarSquareField (Agl : Module.End F V) := h
      have hnd' : h'.Nondegenerate :=
        ⟨hsep, fun y hy => hsep y fun x => by
          rw [← hsymm.eq x y]
          exact (congrArg bar (hy x)).trans (map_zero bar)⟩
      have : Fact ℓ.Prime := ⟨hℓ⟩
      let Φ := evaluationIsometryEquiv B Agl (CatalogueBUnitaryIsometry.isometryGroup h')
        (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
        (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff
      obtain ⟨hdimE, h5⟩ := unitary_component_quotient hℓ2 he hcard (sigma := sigma)
        (fun x => hpow x) h' hsymm hnd' (by omega) Φ hY₁ _ hscal hn hK eQ₁
      have hμsq : ¬ ∃ c : F, c ^ 2 = μ := by
        rintro ⟨c, hc⟩
        have := Fintype.ofFinite F
        obtain ⟨i, hi⟩ : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.mpr (by
          rw [← Nat.card_eq_fintype_card, hF, h5]; decide)
        have hμd : (μ : F) = -(d : F) := by
          field_simp at h1
          linear_combination h1
        exact hsq (i * c) (by rw [mul_pow, hc, hμd, sq i, ← hi]; ring)
      have hsE : (Agl : Module.End F V) ∈ scalarSquareField (Agl : Module.End F V) :=
        Algebra.subset_adjoin (Set.mem_singleton _)
      set sE : scalarSquareField (Agl : Module.End F V) := ⟨Agl, hsE⟩ with hsEdef
      have hTs : ∀ v, T.toLinearMap v = sE • v := fun v => rfl
      have hσs : sigma sE = -sE := Subtype.ext (by
        change (bar sE : Module.End F V) = -(Agl : Module.End F V)
        rw [hbar sE 0 1 (by simp [sE]), zero_smul, one_smul, zero_sub])
      have hσF : ∀ a : F, sigma (algebraMap F _ a) = algebraMap F _ a := fun a =>
        Subtype.ext (by
          change (bar (algebraMap F _ a) : Module.End F V) = algebraMap F (Module.End F V) a
          rw [hbar _ a 0 (by simp [Algebra.algebraMap_eq_smul_one]), zero_smul, sub_zero,
            Algebra.algebraMap_eq_smul_one])
      have hs0 : sE ≠ 0 := fun h0 => by
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        apply hv
        have h3 : T v = 0 := congrArg (fun x : scalarSquareField (Agl : Module.End F V) =>
          (x : Module.End F V) v) h0
        exact (LinearEquiv.map_eq_zero_iff T).mp h3
      have hhE' : ∀ v w, h' v w = algebraMap F _ (B v (T.toLinearMap w)) +
          algebraMap F _ (B v w) * sE := fun v w => Subtype.ext (by
        change (h v w : Module.End F V) = _
        rw [hhE]
        simp [Algebra.algebraMap_eq_smul_one, sE]
        rfl)
      obtain ⟨ρ, hρB, hρρ, hρT, hρY, v₀, w₀, hv₀, hw₀, hρv, hρw⟩ :=
        exists_unitary_reflection B T.toLinearMap hℓ2 he hcard (by omega) (sigma := sigma)
          (fun x => hpow x) hbarbar hσF hTs hσs hs0 h' hsymm hnd' hhE' hdimE Φ hY₁
      let z : isometryGroup B := ⟨ρ, (mem_isometryGroup_iff B _).mpr hρB⟩
      have hzz : z * z = 1 := Subtype.ext (LinearEquiv.ext fun v => hρρ v)
      have hφz : similitudeConjugation B T μ hsim z = negIsometry B * z := by
        refine Subtype.ext (LinearEquiv.ext fun v => ?_)
        rw [similitudeConjugation_apply]
        change T (ρ (T.symm v)) = -(ρ v)
        have h3 := hρT (T.symm v)
        change ρ (T (T.symm v)) = -T (ρ (T.symm v)) at h3
        rw [LinearEquiv.apply_symm_apply] at h3
        rw [h3, neg_neg]
      refine hone hμsq z (fun y hy => ?_) ?_ (by rw [hzz]; exact one_mem _) ?_
      · refine Subtype.ext (LinearEquiv.ext fun v => ?_)
        change (y : V ≃ₗ[F] V) (ρ v) = ρ ((y : V ≃ₗ[F] V) v)
        exact (hρY ⟨y, hYC hy⟩ (mem_subgroupOf.mpr hy) v).symm
      · rw [hφz, ← mul_assoc, (Subgroup.mem_center_iff.mp (negIsometry_central B) z⁻¹), mul_assoc,
          inv_mul_cancel, mul_one]
        exact Or.inr rfl
      · rintro (h' | h')
        · have h3 : ρ v₀ = v₀ := congrArg (fun g : isometryGroup B => (g : V ≃ₗ[F] V) v₀) h'
          rw [hρv] at h3
          apply hv₀
          have h4 : (2 : F) • v₀ = 0 := by
            rw [two_smul]
            nth_rewrite 1 [← h3]
            exact neg_add_cancel v₀
          exact (smul_eq_zero.mp h4).resolve_left h2
        · have h3 : ρ w₀ = -w₀ := congrArg (fun g : isometryGroup B => (g : V ≃ₗ[F] V) w₀) h'
          rw [hρw] at h3
          apply hw₀
          have h4 : (2 : F) • w₀ = 0 := by
            rw [two_smul]
            nth_rewrite 2 [h3]
            exact add_neg_cancel w₀
          exact (smul_eq_zero.mp h4).resolve_left h2

end Linear

theorem statedSp_rankOne_false {F : Type} [Field F] [Finite F] {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = ℓ ^ e) {r : ℕ} (hr : 2 ≤ r) {K : Type*}
    [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (StatedProj (StatedSp r F)))
    (hα : orderOf α = 2) (h : FixedRootConfigRankOne α K) : False := by
  classical
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have hr1 : 1 ≤ r := by omega
  have hαα : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    omega
  obtain ⟨A, σ, hα', hσ2, ⟨d, hd⟩, hlin, -⟩ :=
    (odd_symplectic_automorphism_semilinear_representation hchar hr).2.2 α hαα hα1
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  have hBalt := SymplecticFlag.pairedSympForm_isAlt (K := F) (r := r)
  have hBnd := SymplecticFlag.pairedSympForm_nondegenerate (K := F) (r := r)
  have hdim := SymplecticFlag.finrank_standard (K := F) (r := r)
  by_cases hσ : σ = 1
  · subst hσ
    have hint : ∀ x, projectiveStatedEquiv hr1 (α x) =
        projectiveConjugation (pairedSympForm F r) (matrixLinIso (A : GL (Fin r ⊕ Fin r) F)) μ
          (matrix_similitude _ μ hμ) (projectiveStatedEquiv hr1 x) := by
      intro x
      rw [hα', map_one, mul_one]
      exact projectiveStatedEquiv_conjAut hr1 A μ hμ x
    have hsquare : ∀ x, matrixLinIso (A : GL (Fin r ⊕ Fin r) F)
        (matrixLinIso (A : GL (Fin r ⊕ Fin r) F) x) = (d : F) • x :=
      semilinearCoordMap_sq _ 1 hσ2 d hd
    have hinv : ∀ x, (matrixLinIso (A : GL (Fin r ⊕ Fin r) F)).symm
        ((matrixLinIso (A : GL (Fin r ⊕ Fin r) F)).symm x) = (d : F)⁻¹ • x := fun x => by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, hsquare, smul_smul,
        mul_inv_cancel₀ (Units.ne_zero d), one_smul]
    have hφφ : ∀ g, similitudeConjugation (pairedSympForm F r)
        (matrixLinIso (A : GL (Fin r ⊕ Fin r) F)) μ (matrix_similitude _ μ hμ)
          (similitudeConjugation (pairedSympForm F r) (matrixLinIso (A : GL (Fin r ⊕ Fin r) F))
            μ (matrix_similitude _ μ hμ) g) = g := by
      intro g
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [similitudeConjugation_apply, similitudeConjugation_apply, hinv, map_smul, hsquare,
        smul_smul, mul_inv_cancel₀ (Units.ne_zero d), one_smul]
    obtain ⟨Y, hY, ⟨Ak, _, hAZ, ⟨eQ⟩⟩, hfour, hout⟩ := exists_lift_rankOne _
      (scalarSigns_invariant _ _ μ (matrix_similitude _ μ hμ)) hφφ
      (h.of_mulEquiv (projectiveStatedEquiv hr1) hint)
    rw [fixed_similitudeConjugation_eq] at hY
    refine linear_case_rankOne_false hℓ hℓ2 he hF hr hdim hBalt hBnd _ d μ hsquare
      (matrix_similitude _ μ hμ) (matrixLinIso_ne_smul_one _ (hlin rfl)) hY Ak hAZ hn hK eQ
      hfour fun hμsq => hout fun hin => hμsq ?_
    have hin' := mem_range_conj_of_mulEquiv (projectiveStatedEquiv hr1) hint hin
    rw [hα', map_one, mul_one] at hin'
    exact exists_sq_eq_multiplierUnit_of_mem_range hr1 A hin'
  · have hint : ∀ x, projectiveStatedEquiv hr1 (α x) =
        projectiveSemilinearConjugation (pairedSympForm F r) σ
          (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ) μ (semilinearCoordMap_smul _ σ)
          (semilinearCoordMap_form _ σ μ hμ) (projectiveStatedEquiv hr1 x) := by
      intro x
      rw [hα']
      exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x
    have hsquare := semilinearCoordMap_sq (A : GL (Fin r ⊕ Fin r) F) σ hσ2 d hd
    have hinv : ∀ x, (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ).symm
        ((semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ).symm x) = (d : F)⁻¹ • x :=
      fun x => by
        rw [AddEquiv.symm_apply_eq, AddEquiv.symm_apply_eq, hsquare, smul_smul,
          mul_inv_cancel₀ (Units.ne_zero d), one_smul]
    have hφφ : ∀ g, semilinearConjugation (pairedSympForm F r) σ
        (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ) μ (semilinearCoordMap_smul _ σ)
          (semilinearCoordMap_form _ σ μ hμ) (semilinearConjugation (pairedSympForm F r) σ
            (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ) μ (semilinearCoordMap_smul _ σ)
            (semilinearCoordMap_form _ σ μ hμ) g) = g := by
      intro g
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [semilinearConjugation_apply, semilinearConjugation_apply, hinv, map_smul, hsquare,
        smul_smul, mul_inv_cancel₀ (Units.ne_zero d), one_smul]
    obtain ⟨Y, hY, ⟨Ak, _, hAZ, ⟨eQ⟩⟩, -, -⟩ := exists_lift_rankOne _
      (semilinear_scalarSigns_invariant _ σ _ μ _ _) hφφ
      (h.of_mulEquiv (projectiveStatedEquiv hr1) hint)
    rw [fixed_semilinearConjugation_eq] at hY
    exact field_case_false hℓ hℓ2 he hF hr hdim hBalt hBnd σ hσ2 hσ _ μ d
      (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ) hsquare hY Ak hAZ hn hK eQ


end CFSG.LocalAnalysis.EvenBN.GMSK.OddSymplectic

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Assembly.LowTwoRank OddSymplectic
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem odd_symplectic_fixed_root_rankOne_exclusion (K : Type*) [Field K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {D : Type} [Group D] (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) (hr : FixedRootRankOne α S)
    (p f r : ℕ) (hp : p ≠ 2) : ¬ StatedClassicalModel D .PSp r p f := by
  rintro ⟨⟨hprime, hf, hr2, -⟩, F, _, _, hF, ⟨e⟩⟩
  obtain ⟨φ⟩ := hSK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    sl2_isSimpleGroup (two_eq_zero_of_card (by omega) hK') (by
      rw [hK']
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  obtain ⟨a, b, hab⟩ := sl2_exists_mul_ne (K := K)
  let eS : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K := (Subgroup.subgroupOfEquivOfLe hSα).trans φ
  have hnab : ∃ x y : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)), x * y ≠ y * x :=
    ⟨eS.symm a, eS.symm b, fun h => hab (by
      have h1 := congrArg eS h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1)⟩
  have h0 : FixedRootConfigRankOne α K := by
    refine ⟨S.subgroupOf _, hSn, eS.isSimpleGroup, hnab, ⟨eS⟩, ?_⟩
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (show S ≤ fixedSubgroup α from hSα)]
    exact hr
  exact statedSp_rankOne_false hprime hp hf hF hr2 hn hK (MulAut.congr e α)
    (by rw [MulEquiv.orderOf_eq]; exact hα)
    (h0.of_mulEquiv e fun x => by
      change e (α x) = e (α (e.symm (e x)))
      rw [MulEquiv.symm_apply_apply])

theorem fixedRootSelector_oddSymplectic :
    FixedRootSelector fun D _ => ∃ r p f : ℕ, p ≠ 2 ∧ StatedClassicalModel D .PSp r p f := by
  intro D _ _ _ ⟨r, p, f, hp, hmodel⟩ n hn K _ _ hK α hα S hSα hSn hSK hr
  exact (odd_symplectic_fixed_root_rankOne_exclusion K hn (by rw [Nat.card_eq_fintype_card, hK])
    α hα S hSα hSn hSK hr p f r hp hmodel).elim

theorem statedClassicalModel_PSp_of_lieModel {D : Type} [Group D] {r p f : ℕ}
    (h : CFSG.Blueprint.LieModel D .PSp r p f) : StatedClassicalModel D .PSp r p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem fixedRootSelector_oddSymplectic_lieModel :
    FixedRootSelector fun D _ => ∃ r p f : ℕ, p ≠ 2 ∧ CFSG.Blueprint.LieModel D .PSp r p f :=
  fixedRootSelector_oddSymplectic.mono fun _ _ _ _ ⟨r, p, f, hp, h⟩ =>
    ⟨r, p, f, hp, statedClassicalModel_PSp_of_lieModel h⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
