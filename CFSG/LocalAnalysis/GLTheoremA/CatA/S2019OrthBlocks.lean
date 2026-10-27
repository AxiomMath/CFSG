module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SpModels
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

section Pull

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_orth_of_modelPair {R : Type*} [CommRing R] {W : Submodule K V} [Module R W]
    {Γ : Subgroup (LinearMap.GeneralLinearGroup R W)} {A : Subgroup (V ≃ₗ[K] V)} (φ : A ≃* Γ)
    (hφ : ∀ (g : A) (v : V) (hv : v ∈ W),
      ((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) ⟨v, hv⟩ : V) =
        (g : V ≃ₗ[K] V) v)
    (hpair : SpBlock.ModelPair Γ) :
    ∃ uA u'A : A, (uA : V ≃ₗ[K] V) ∈ ⁅A, A⁆ ∧ (u'A : V ≃ₗ[K] V) ∈ ⁅A, A⁆ ∧
      ((((φ uA : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) ^ 2 = 0 ∧
      (∀ v ∈ W, ((((uA : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ^ 2 : V →ₗ[K] V) v = 0) ∧
      ∃ m ∈ W, ((uA : V ≃ₗ[K] V) * (u'A : V ≃ₗ[K] V)) m ≠
          ((u'A : V ≃ₗ[K] V) * (uA : V ≃ₗ[K] V)) m ∧
        ((uA : V ≃ₗ[K] V) * (u'A : V ≃ₗ[K] V)) m ≠
          -(((u'A : V ≃ₗ[K] V) * (uA : V ≃ₗ[K] V)) m) := by
  obtain ⟨d, hd, τ, hτ, τ', hτ', hsq, m, hne1, hne2⟩ := hpair
  set dA := φ.symm ⟨d, hd⟩
  set τA := φ.symm ⟨τ, hτ⟩
  set τ'A := φ.symm ⟨τ', hτ'⟩
  set uA : A := ⁅dA, τA⁆ with huA
  set u'A : A := ⁅dA, τ'A⁆ with hu'A
  have hφu : ((φ uA : Γ) : LinearMap.GeneralLinearGroup R W) = ⁅d, τ⁆ := by
    rw [huA, map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  have hφu' : ((φ u'A : Γ) : LinearMap.GeneralLinearGroup R W) = ⁅d, τ'⁆ := by
    rw [hu'A, map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  have hact : ∀ (g : A) (v : W), (g : V ≃ₗ[K] V) (v : V) =
      ((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) v : V) := by
    intro g v
    rw [← hφ g v v.2]
  have hsub : ∀ (g : A) (v : W), (((g : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) (v : V) =
      (((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) v : V) := by
    intro g v
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, hact,
      LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub]
  refine ⟨uA, u'A, Subgroup.commutator_mem_commutator dA.2 τA.2,
    Subgroup.commutator_mem_commutator dA.2 τ'A.2, by rw [hφu]; exact hsq, ?_, m, m.2, ?_, ?_⟩
  · intro v hv
    rw [sq, Module.End.mul_apply, hsub uA ⟨v, hv⟩, hsub uA, ← Module.End.mul_apply, ← sq, hφu, hsq,
      LinearMap.zero_apply, Submodule.coe_zero]
  · intro h
    apply hne1
    apply Subtype.ext
    have e1 : ((uA : V ≃ₗ[K] V) * (u'A : V ≃ₗ[K] V)) m =
        ((((⁅d, τ⁆ * ⁅d, τ'⁆ : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) m : W) : V) := by
      rw [LinearEquiv.mul_apply, hact u'A m, hact uA ⟨_, _⟩, Units.val_mul, Module.End.mul_apply,
        hφu, hφu']
    have e2 : ((u'A : V ≃ₗ[K] V) * (uA : V ≃ₗ[K] V)) m =
        ((((⁅d, τ'⁆ * ⁅d, τ⁆ : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) m : W) : V) := by
      rw [LinearEquiv.mul_apply, hact uA m, hact u'A ⟨_, _⟩, Units.val_mul, Module.End.mul_apply,
        hφu, hφu']
    rw [← e1, ← e2, h]
  · intro h
    apply hne2
    apply Subtype.ext
    have e1 : ((uA : V ≃ₗ[K] V) * (u'A : V ≃ₗ[K] V)) m =
        ((((⁅d, τ⁆ * ⁅d, τ'⁆ : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) m : W) : V) := by
      rw [LinearEquiv.mul_apply, hact u'A m, hact uA ⟨_, _⟩, Units.val_mul, Module.End.mul_apply,
        hφu, hφu']
    have e2 : ((u'A : V ≃ₗ[K] V) * (uA : V ≃ₗ[K] V)) m =
        ((((⁅d, τ'⁆ * ⁅d, τ⁆ : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) m : W) : V) := by
      rw [LinearEquiv.mul_apply, hact uA m, hact u'A ⟨_, _⟩, Units.val_mul, Module.End.mul_apply,
        hφu, hφu']
    rw [Submodule.coe_neg, ← e1, ← e2, h]

theorem exists_orth_of_modelPair_top {R : Type*} [CommRing R] {W : Submodule K V} [Module R W]
    {A : Subgroup (V ≃ₗ[K] V)} (φ : A ≃* LinearMap.GeneralLinearGroup R W)
    (hφ : ∀ (g : A) (v : V) (hv : v ∈ W),
      (((φ g : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) ⟨v, hv⟩ : V) = (g : V ≃ₗ[K] V) v)
    (hpair : SpBlock.ModelPair (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W))) :
    ∃ uA u'A : A, (uA : V ≃ₗ[K] V) ∈ ⁅A, A⁆ ∧ (u'A : V ≃ₗ[K] V) ∈ ⁅A, A⁆ ∧
      (((φ uA : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) ^ 2 = 0 ∧
      (∀ v ∈ W, ((((uA : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ^ 2 : V →ₗ[K] V) v = 0) ∧
      ∃ m ∈ W, ((uA : V ≃ₗ[K] V) * (u'A : V ≃ₗ[K] V)) m ≠
          ((u'A : V ≃ₗ[K] V) * (uA : V ≃ₗ[K] V)) m ∧
        ((uA : V ≃ₗ[K] V) * (u'A : V ≃ₗ[K] V)) m ≠
          -(((u'A : V ≃ₗ[K] V) * (uA : V ≃ₗ[K] V)) m) := by
  obtain ⟨uA, u'A, h1, h2, h3, h4, h5⟩ :=
    exists_orth_of_modelPair (φ.trans Subgroup.topEquiv.symm) (fun g v hv => hφ g v hv) hpair
  exact ⟨uA, u'A, h1, h2, h3, h4, h5⟩

end Pull

section Paired

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem sq_inv_sub_one_eq_zero' {R : Type*} [Ring R] (u : Rˣ) (hu : ((u : R) - 1) ^ 2 = 0) :
    (((u⁻¹ : Rˣ) : R) - 1) ^ 2 = 0 := by
  have hab : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  have hba : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := u.inv_mul
  have e1 : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * ((u⁻¹ : Rˣ) : R)) := by
    rw [sub_mul, hab, one_mul, neg_sub]
  have e2 : ((u⁻¹ : Rˣ) : R) * ((u : R) - 1) = ((u : R) - 1) * ((u⁻¹ : Rˣ) : R) := by
    rw [mul_sub, sub_mul, hba, hab, mul_one, one_mul]
  calc (((u⁻¹ : Rˣ) : R) - 1) ^ 2
      = ((u : R) - 1) * (((u⁻¹ : Rˣ) : R) * ((u : R) - 1)) * ((u⁻¹ : Rˣ) : R) := by
        rw [sq, e1, neg_mul_neg, mul_assoc, mul_assoc, mul_assoc]
    _ = ((u : R) - 1) ^ 2 * (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) := by
        rw [e2, sq, mul_assoc, mul_assoc, mul_assoc]
    _ = 0 := by rw [hu, zero_mul]

private theorem sq_inv_sub_one_eq_zero_gl' {E M : Type*} [CommRing E] [AddCommGroup M] [Module E M]
    (u : LinearMap.GeneralLinearGroup E M) (hu : ((u : M →ₗ[E] M) - 1) ^ 2 = 0) :
    (((u⁻¹ : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) - 1) ^ 2 = 0 :=
  sq_inv_sub_one_eq_zero' u hu

private theorem eq_zero_of_orbit_others (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {f : V →ₗ[K] V}
    (h1 : ∀ v ∈ primaryComponent x.toLinearMap h, f v = 0)
    (h2 : ∀ v ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h), f v = 0)
    (h3 : ∀ v ∈ othersSpace x.toLinearMap h, f v = 0) : f = 0 := by
  have hle : orbitSpace x.toLinearMap h ⊔ othersSpace x.toLinearMap h ≤ LinearMap.ker f :=
    sup_le (sup_le (fun v hv => LinearMap.mem_ker.2 (h1 v hv))
      (fun v hv => LinearMap.mem_ker.2 (h2 v hv))) (fun v hv => LinearMap.mem_ker.2 (h3 v hv))
  rw [(hx.isCompl_orbit_others hh).sup_eq_top, top_le_iff, LinearMap.ker_eq_top] at hle
  exact hle

theorem exists_quad_specialBlock_paired (hx : OddOrderIsometry Q p x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne : h ≠ reciprocalPolynomial h) (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (hl2 : l ^ 2 ≠ 1) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    ∃ u ∈ specialBlock Q x h, ∃ u' ∈ specialBlock Q x h,
      ((u : V →ₗ[K] V) - 1) ^ 2 = 0 ∧
        ∃ m : V, (u * u') m ≠ (u' * u) m ∧ (u * u') m ≠ -((u' * u) m) := by
  set φ := pairedBlockEquiv hx hh hne
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  have hij : (⟨0, by omega⟩ : Fin (primaryMultiplicity x.toLinearMap h)) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  have h2E : (2 : AdjoinRoot h) ≠ 0 := by
    have := (algebraMap K (AdjoinRoot h)).injective.ne h2
    rwa [map_ofNat, map_zero] at this
  have hlE : algebraMap K (AdjoinRoot h) l ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K _).injective]
    exact hl
  have hl2E : (algebraMap K (AdjoinRoot h) l) ^ 2 ≠ 1 := by
    rw [← map_pow, Ne, ← map_one (algebraMap K (AdjoinRoot h)), (algebraMap K _).injective.eq_iff]
    exact hl2
  have hpair := SpBlock.modelPair_lin b h2E hij hlE hl2E
  obtain ⟨uA, u'A, hu, hu', hγ, hWq, m, hmW, hne1, hne2⟩ :=
    exists_orth_of_modelPair_top φ (fun g v hv => coe_blockGL h g ⟨v, hv⟩) hpair
  refine ⟨uA, commutator_supportedBlock_le_specialBlock h hu, u'A,
    commutator_supportedBlock_le_specialBlock h hu', ?_, m, hne1, hne2⟩
  have huA := uA.2
  rw [mem_supportedBlock, mem_isometryCentralizer] at huA
  obtain ⟨⟨hiso, hcx⟩, hoth⟩ := huA
  have hmemO : (uA : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hcomm : Commute ((uA : V ≃ₗ[K] V) : V →ₗ[K] V) x.toLinearMap :=
    LinearMap.ext fun v => hcx v
  have hGi := sq_inv_sub_one_eq_zero_gl' (φ uA) hγ
  have hinvact : ∀ v (hv : v ∈ primaryComponent x.toLinearMap h),
      (uA : V ≃ₗ[K] V).symm v = (((((φ uA)⁻¹ : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) ⟨v, hv⟩ :
          primaryComponent x.toLinearMap h) : V) := by
    intro v hv
    have := coe_blockGL h uA⁻¹ ⟨v, hv⟩
    rw [show blockGL Q x h uA⁻¹ = (φ uA)⁻¹ from map_inv _ _] at this
    rw [this]
    rfl
  have key : ∀ y ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h),
      ∀ v (hv : v ∈ primaryComponent x.toLinearMap h),
      QuadraticMap.polar Q v ((((uA : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) y) =
        QuadraticMap.polar Q ((((((φ uA)⁻¹ : BlockGL x h) :
          Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) - 1) ⟨v, hv⟩ :
            primaryComponent x.toLinearMap h) : V) y := by
    intro y hy v hv
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hmemO
      ((uA : V ≃ₗ[K] V).symm v) y
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
      QuadraticMap.polar_sub_right, h1, hinvact v hv, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_sub, QuadraticMap.polar_sub_left]
  have hpres : ∀ y ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h),
      (((uA : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) y ∈
        primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
    fun y hy => Submodule.sub_mem _ (apply_mem_primaryComponent hcomm hy) hy
  apply eq_zero_of_orbit_others hx hh
  · exact hWq
  · intro w hw
    apply hx.eq_zero_of_polar_paired_right hh
      (by rw [sq, Module.End.mul_apply]; exact hpres _ (hpres w hw))
    intro v hv
    rw [sq, Module.End.mul_apply, key _ (hpres w hw) v hv, key w hw _ (Subtype.prop _)]
    simp only [Subtype.coe_eta]
    rw [← Module.End.mul_apply, ← sq, hGi, LinearMap.zero_apply, Submodule.coe_zero,
      QuadraticMap.polar_zero_left]
  · intro v hv
    have h1 : (uA : V ≃ₗ[K] V) v = v := hoth v hv
    have h0 : (((uA : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) v = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, h1, sub_self]
    rw [sq, Module.End.mul_apply, h0, map_zero]

end Paired

section SelfDual

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_quad_specialBlock_selfDual (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    ∃ u ∈ specialBlock Q x h, ∃ u' ∈ specialBlock Q x h,
      ((u : V →ₗ[K] V) - 1) ^ 2 = 0 ∧
        ∃ m : V, (u * u') m ≠ (u' * u) m ∧ (u * u') m ≠ -((u' * u) m) := by
  classical
  haveI := Fintype.ofFinite K
  have hirr : Irreducible h := Fact.out
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd1 : 1 ≤ d := by
    have := Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hirr)
    omega
  have hfinE : Module.finrank K (AdjoinRoot h) = h.natDegree :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim _)
  have hcardE : Nat.card (AdjoinRoot h) = ℓ ^ (2 * (f * d)) := by
    haveI : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
    haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
    haveI := Fintype.ofFinite (AdjoinRoot h)
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hfinE, hdeg,
      Fintype.card_eq_nat_card, hK, ← pow_mul]
    ring_nf
  let hE : UnitaryFieldData ℓ (f * d) (AdjoinRoot h) := ⟨hℓ, Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by omega) (by omega)), hcardE⟩
  have hbarσ : ∀ z, hE.bar z = frobPow K (AdjoinRoot h) d z := by
    intro z
    rw [hE.bar_apply, frobPow_apply, hK, ← pow_mul]
  let Hb : primaryComponent x.toLinearMap h →ₛₗ[hE.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hE.bar (RingHom.id _) H hadd₁ (fun c u w => by rw [hsm₁, hbarσ, smul_eq_mul])
      hadd₂ (fun c u w => by rw [hsm₂, RingHom.id_apply, smul_eq_mul])
  have hHb : ∀ u w, Hb u w = H u w := fun u w => rfl
  have hsymmB : Hb.IsSymm := ⟨fun u w => by rw [hHb, hHb, hbarσ]; exact (hsymm u w).symm⟩
  have hsepB : Hb.SeparatingLeft := by
    intro u hu
    apply Subtype.ext
    apply hx.eq_zero_of_polar_paired_left hh u.2
    intro w hw
    rw [← hself] at hw
    have h1 := htr u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    rw [← h1, ← hHb, hu, map_zero]
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hsymmB hsepB
  have hm1 : (-1 : AdjoinRoot h) ∈ hE.fixedField := by
    rw [hE.mem_fixedField, map_neg, map_one]
  obtain ⟨μ, hμ'⟩ := hE.normHom_surjective ⟨-1, hm1⟩
  have hμ : μ * hE.bar μ = -1 := congrArg Subtype.val hμ'
  obtain ⟨c₀, hc₀⟩ := hE.exists_bar_ne
  have hη0 : c₀ - hE.bar c₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hc₀)
  have hη : hE.bar (c₀ - hE.bar c₀) = -(c₀ - hE.bar c₀) := by rw [map_sub, hE.bar_bar, neg_sub]
  set i₀ : Fin (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) := ⟨0, by
    change 0 < primaryMultiplicity x.toLinearMap h
    omega⟩
  set i₁ : Fin (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) := ⟨1, by
    change 1 < primaryMultiplicity x.toLinearMap h
    omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h00 : Hb (e i₀) (e i₀) = 1 := by rw [he, if_pos rfl]
  have h11 : Hb (e i₁) (e i₁) = 1 := by rw [he, if_pos rfl]
  have h01' : Hb (e i₀) (e i₁) = 0 := by rw [he, if_neg h01]
  have h10' : Hb (e i₁) (e i₀) = 0 := by rw [he, if_neg h01.symm]
  have h2E : (2 : AdjoinRoot h) ≠ 0 := by
    have := (algebraMap K (AdjoinRoot h)).injective.ne h2
    rwa [map_ofNat, map_zero] at this
  have hvv : Hb (e i₀ + μ • e i₁) (e i₀ + μ • e i₁) = 0 := by
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
      smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    linear_combination hμ
  have hww : Hb ((2 : AdjoinRoot h)⁻¹ • (e i₀ - μ • e i₁))
      ((2 : AdjoinRoot h)⁻¹ • (e i₀ - μ • e i₁)) = 0 := by
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul,
      smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    linear_combination (hE.bar (2 : AdjoinRoot h)⁻¹ * (2 : AdjoinRoot h)⁻¹) * hμ
  have hvw : Hb (e i₀ + μ • e i₁) ((2 : AdjoinRoot h)⁻¹ • (e i₀ - μ • e i₁)) = 1 := by
    simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, map_smul, smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    field_simp
    linear_combination -hμ
  have hlE : algebraMap K (AdjoinRoot h) l ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K _).injective]
    exact hl
  have hl2E : (algebraMap K (AdjoinRoot h) l) ^ 2 ≠ 1 := by
    rw [← map_pow, Ne, ← map_one (algebraMap K (AdjoinRoot h)), (algebraMap K _).injective.eq_iff]
    exact hl2
  have hσl : hE.bar (algebraMap K (AdjoinRoot h) l) = algebraMap K (AdjoinRoot h) l := by
    rw [hbarσ, AlgEquiv.commutes]
  have hpair := SpBlock.modelPair_herm hsymmB hvv hww hvw h2E hlE hl2E hσl hη0 hη
  have hrange : (blockGL Q x h).range = sesqUnitaryGroup Hb := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H htr γ, mem_sesqUnitaryGroup]
    rfl
  let φ : ↥(supportedBlock Q x h) ≃* ↥(sesqUnitaryGroup Hb) :=
    (MonoidHom.ofInjective (hx.blockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)
  obtain ⟨uA, u'A, hu, hu', -, hWq, m, -, hne1', hne2'⟩ :=
    exists_orth_of_modelPair φ (fun g v hv => coe_blockGL h g ⟨v, hv⟩) hpair
  refine ⟨uA, commutator_supportedBlock_le_specialBlock h hu, u'A,
    commutator_supportedBlock_le_specialBlock h hu', ?_, m, hne1', hne2'⟩
  have hoth := (mem_supportedBlock.1 uA.2).2
  apply eq_zero_of_orbit_others hx hh hWq
  · rw [← hself]
    exact hWq
  · intro v hv
    have h1 : (uA : V ≃ₗ[K] V) v = v := hoth v hv
    have h0 : (((uA : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) v = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, h1, sub_self]
    rw [sq, Module.End.mul_apply, h0, map_zero]

end SelfDual

end CFSG.LocalAnalysis.GLTheoremA.S2019
