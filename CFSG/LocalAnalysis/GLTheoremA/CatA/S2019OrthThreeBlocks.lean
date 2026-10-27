module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SpModelsThree
import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

@[expose] def OrthBlockThree {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Subgroup (V ≃ₗ[K] V)) : Prop :=
  ∃ P : Subgroup (V ≃ₗ[K] V), P ≤ F ∧ IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
    (∀ u ∈ P, (∀ j ∈ F, u * j = j * u) → u = 1) ∧
    ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 → ((u : V →ₗ[K] V) - 1) ^ 2 = 0

section Pull

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem mem_commutator_subtype' {G : Type*} [Group G] {Γ : Subgroup G} {y : Γ}
    (hy : (y : G) ∈ ⁅Γ, Γ⁆) : y ∈ commutator Γ := by
  rw [← Subgroup.map_subtype_commutator] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [show y = z from Subtype.ext hzy.symm]

private theorem map_commutator_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
    (MonoidHom.range_eq_top (f := e.toMonoidHom)).2 e.surjective]

theorem exists_three_of_modelThree_orth {R : Type*} [Field R] {W : Submodule K V} [Module R W]
    {Γ : Subgroup (LinearMap.GeneralLinearGroup R W)} {A : Subgroup (V ≃ₗ[K] V)} (φ : A ≃* Γ)
    (hφ : ∀ (g : A) (v : V) (hv : v ∈ W),
      ((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) ⟨v, hv⟩ : V) =
        (g : V ≃ₗ[K] V) v)
    (hM : SpBlock.ModelThree Γ) :
    ∃ P : Subgroup (V ≃ₗ[K] V), P ≤ ⁅A, A⁆ ∧ IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
      (∀ u ∈ P, (∀ j ∈ ⁅A, A⁆, u * j = j * u) → u = 1) ∧
      ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 → ∃ hu : u ∈ A,
        ((((φ ⟨u, hu⟩ : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) ^ 2 = 0 ∧
        ∀ v ∈ W, ((((u : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ^ 2 : V →ₗ[K] V) v = 0 := by
  obtain ⟨P₀, hP₀Γ, hP₀3, hP₀9, hP₀Z, hP₀q⟩ := hM
  have hP₀le : P₀ ≤ Γ := hP₀Γ.trans (Subgroup.commutator_le_self Γ)
  set ψ : Γ →* (V ≃ₗ[K] V) := A.subtype.comp φ.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := A.subtype_injective.comp φ.symm.injective
  have hψcomm : ∀ y : Γ, y ∈ commutator Γ → ψ y ∈ ⁅A, A⁆ := by
    intro y hy
    rw [← Subgroup.map_subtype_commutator]
    refine ⟨φ.symm y, ?_, rfl⟩
    rw [← map_commutator_mulEquiv' φ.symm]
    exact ⟨y, hy, rfl⟩
  refine ⟨(P₀.subgroupOf Γ).map ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hψcomm y (mem_commutator_subtype' (hP₀Γ (Subgroup.mem_subgroupOf.1 hy)))
  · exact (hP₀3.of_equiv (Subgroup.subgroupOfEquivOfLe hP₀le).symm).map ψ
  · rw [Subgroup.card_map_of_injective hψinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀le).toEquiv]
    exact hP₀9
  · rintro _ ⟨y, hy, rfl⟩ hcomm
    have hy1 : (y : LinearMap.GeneralLinearGroup R W) = 1 := by
      refine hP₀Z _ (Subgroup.mem_subgroupOf.1 hy) fun j hj => ?_
      have hjΓ : j ∈ Γ := Subgroup.commutator_le_self Γ hj
      have hz := hψcomm ⟨j, hjΓ⟩ (mem_commutator_subtype' hj)
      have h1 := hcomm _ hz
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hψinj h1)
    rw [show y = 1 from Subtype.ext hy1, map_one]
  · rintro _ ⟨y, hy, rfl⟩ hcent hcube
    have hyP₀ : (y : LinearMap.GeneralLinearGroup R W) ∈ P₀ := Subgroup.mem_subgroupOf.1 hy
    have hcent' : ∀ w ∈ P₀, (y : LinearMap.GeneralLinearGroup R W) * w = w * y := by
      intro w hw
      have h1 := hcent (ψ ⟨w, hP₀le hw⟩) ⟨⟨w, hP₀le hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hψinj h1)
    have hcube' : (y : LinearMap.GeneralLinearGroup R W) ^ 3 = 1 := by
      have h1 : ψ (y ^ 3) = ψ 1 := by rw [map_pow, hcube, map_one]
      rw [← Subgroup.coe_pow, hψinj h1, Subgroup.coe_one]
    have hq := hP₀q _ hyP₀ hcent' hcube'
    have hφy : φ ⟨ψ y, (φ.symm y).2⟩ = y := by
      rw [show (⟨ψ y, (φ.symm y).2⟩ : A) = φ.symm y from Subtype.ext rfl,
        MulEquiv.apply_symm_apply]
    refine ⟨(φ.symm y).2, by rw [hφy]; exact hq, fun v hv => ?_⟩
    have hsub : ∀ (z : W), ((((ψ y : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) (z : V)) =
        ((((y : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) z : V) := by
      intro z
      have h1 := hφ ⟨ψ y, (φ.symm y).2⟩ z z.2
      rw [hφy] at h1
      rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.sub_apply, Module.End.one_apply,
        Submodule.coe_sub, LinearEquiv.coe_coe]
      rw [← h1]
    rw [sq, Module.End.mul_apply, hsub ⟨v, hv⟩, hsub, ← Module.End.mul_apply, ← sq, hq,
      LinearMap.zero_apply, Submodule.coe_zero]

theorem exists_three_of_modelThree_orth_top {R : Type*} [Field R] {W : Submodule K V}
    [Module R W] {A : Subgroup (V ≃ₗ[K] V)} (φ : A ≃* LinearMap.GeneralLinearGroup R W)
    (hφ : ∀ (g : A) (v : V) (hv : v ∈ W),
      (((φ g : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) ⟨v, hv⟩ : V) = (g : V ≃ₗ[K] V) v)
    (hM : SpBlock.ModelThree (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W))) :
    ∃ P : Subgroup (V ≃ₗ[K] V), P ≤ ⁅A, A⁆ ∧ IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
      (∀ u ∈ P, (∀ j ∈ ⁅A, A⁆, u * j = j * u) → u = 1) ∧
      ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 → ∃ hu : u ∈ A,
        (((φ ⟨u, hu⟩ : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) ^ 2 = 0 ∧
        ∀ v ∈ W, ((((u : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ^ 2 : V →ₗ[K] V) v = 0 := by
  obtain ⟨P, h1, h2, h3, h4, h5⟩ :=
    exists_three_of_modelThree_orth (φ.trans Subgroup.topEquiv.symm) (fun g v hv => hφ g v hv) hM
  exact ⟨P, h1, h2, h3, h4, h5⟩

end Pull

section Special

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem sq_inv_sub_one_eq_zero_three {R : Type*} [Ring R] (u : Rˣ)
    (hu : ((u : R) - 1) ^ 2 = 0) : (((u⁻¹ : Rˣ) : R) - 1) ^ 2 = 0 := by
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

private theorem sq_inv_sub_one_eq_zero_gl_three {E M : Type*} [CommRing E] [AddCommGroup M]
    [Module E M] (u : LinearMap.GeneralLinearGroup E M) (hu : ((u : M →ₗ[E] M) - 1) ^ 2 = 0) :
    (((u⁻¹ : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) - 1) ^ 2 = 0 :=
  sq_inv_sub_one_eq_zero_three u hu

private theorem eq_zero_of_orbit_others' (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {f : V →ₗ[K] V}
    (h1 : ∀ v ∈ primaryComponent x.toLinearMap h, f v = 0)
    (h2 : ∀ v ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h), f v = 0)
    (h3 : ∀ v ∈ othersSpace x.toLinearMap h, f v = 0) : f = 0 := by
  have hle : orbitSpace x.toLinearMap h ⊔ othersSpace x.toLinearMap h ≤ LinearMap.ker f :=
    sup_le (sup_le (fun v hv => LinearMap.mem_ker.2 (h1 v hv))
      (fun v hv => LinearMap.mem_ker.2 (h2 v hv))) (fun v hv => LinearMap.mem_ker.2 (h3 v hv))
  rw [(hx.isCompl_orbit_others hh).sup_eq_top, top_le_iff, LinearMap.ker_eq_top] at hle
  exact hle

private theorem nine_le_card_of_ne_three' {F : Type*} [Field F] [Finite F] [CharP F 3]
    (h : Nat.card F ≠ 3) : 9 ≤ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 3
  rw [Nat.card_eq_fintype_card, hn] at h ⊢
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra hlt
    exact h (by rw [show (n : ℕ) = 1 by have := n.pos; omega, pow_one])
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2

private theorem dvd_card_sub_one_of_orderOf_unit {E : Type*} [Field E] [Finite E] {u : Eˣ} {p : ℕ}
    (hu : orderOf u = p) : p ∣ Nat.card E - 1 := by
  classical
  haveI := Fintype.ofFinite E
  have h2 := orderOf_dvd_card (G := Eˣ) (x := u)
  rw [hu, Fintype.card_units, ← Nat.card_eq_fintype_card] at h2
  exact h2

theorem orthBlockThree_paired [CharP K 3] (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) : OrthBlockThree (specialBlock Q x h) := by
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  haveI : CharP (AdjoinRoot h) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 3
  set φ := pairedBlockEquiv hx hh hne
  have hE9 : 9 ≤ Nat.card (AdjoinRoot h) := by
    refine nine_le_card_of_ne_three' fun h3 => ?_
    obtain ⟨hl0, hord⟩ := hx.orderOf_root hp hh hne1
    have hdvd := dvd_card_sub_one_of_orderOf_unit hord
    rw [h3] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  obtain ⟨l, hl, hl2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card _
    (by omega : 4 ≤ Nat.card (AdjoinRoot h))
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  have hij : (⟨0, by omega⟩ : Fin (primaryMultiplicity x.toLinearMap h)) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  have hM := SpBlock.modelThree_lin b hij hl hl2 hE9
  obtain ⟨P, hPA, hP3, hP9, hPZ, hPq⟩ :=
    exists_three_of_modelThree_orth_top φ (fun g v hv => coe_blockGL h g ⟨v, hv⟩) hM
  refine ⟨P, hPA.trans (commutator_supportedBlock_le_specialBlock h), hP3, hP9,
    fun u hu hc => hPZ u hu fun j hj => hc j (commutator_supportedBlock_le_specialBlock h hj),
    fun u hu hcent hcube => ?_⟩
  obtain ⟨huA, hγ, hWq⟩ := hPq u hu hcent hcube
  set uA : supportedBlock Q x h := ⟨u, huA⟩ with huA'
  have huA2 := uA.2
  rw [mem_supportedBlock, mem_isometryCentralizer] at huA2
  obtain ⟨⟨hiso, hcx⟩, hoth⟩ := huA2
  have hmemO : (u : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hcomm : Commute ((u : V ≃ₗ[K] V) : V →ₗ[K] V) x.toLinearMap :=
    LinearMap.ext fun v => hcx v
  have hGi := sq_inv_sub_one_eq_zero_gl_three (φ uA) hγ
  have hinvact : ∀ v (hv : v ∈ primaryComponent x.toLinearMap h),
      (u : V ≃ₗ[K] V).symm v = (((((φ uA)⁻¹ : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) ⟨v, hv⟩ :
          primaryComponent x.toLinearMap h) : V) := by
    intro v hv
    have := coe_blockGL h uA⁻¹ ⟨v, hv⟩
    rw [show blockGL Q x h uA⁻¹ = (φ uA)⁻¹ from map_inv _ _] at this
    rw [this]
    rfl
  have key : ∀ y ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h),
      ∀ v (hv : v ∈ primaryComponent x.toLinearMap h),
      QuadraticMap.polar Q v ((((u : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) y) =
        QuadraticMap.polar Q ((((((φ uA)⁻¹ : BlockGL x h) :
          Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) - 1) ⟨v, hv⟩ :
            primaryComponent x.toLinearMap h) : V) y := by
    intro y hy v hv
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hmemO
      ((u : V ≃ₗ[K] V).symm v) y
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
      QuadraticMap.polar_sub_right, h1, hinvact v hv, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_sub, QuadraticMap.polar_sub_left]
  have hpres : ∀ y ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h),
      (((u : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) y ∈
        primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
    fun y hy => Submodule.sub_mem _ (apply_mem_primaryComponent hcomm hy) hy
  apply eq_zero_of_orbit_others' hx hh
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
    have h1 : (u : V ≃ₗ[K] V) v = v := hoth v hv
    have h0 : (((u : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) v = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, h1, sub_self]
    rw [sq, Module.End.mul_apply, h0, map_zero]

open CFSG.LocalAnalysis.ComponentInitial

theorem orthBlockThree_selfDual [CharP K 3] (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    OrthBlockThree (specialBlock Q x h) := by
  classical
  haveI := Fintype.ofFinite K
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hirr : Irreducible h := Fact.out
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  haveI : CharP (AdjoinRoot h) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 3
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd1 : 1 ≤ d := by
    have := Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hirr)
    omega
  have hfinE : Module.finrank K (AdjoinRoot h) = h.natDegree :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim _)
  have hcardE : Nat.card (AdjoinRoot h) = 3 ^ (2 * (f * d)) := by
    haveI : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
    haveI := Fintype.ofFinite (AdjoinRoot h)
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hfinE, hdeg,
      Fintype.card_eq_nat_card, hK, ← pow_mul]
    ring_nf
  let hE : UnitaryFieldData 3 (f * d) (AdjoinRoot h) := ⟨Nat.prime_three, Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by omega) (by omega)), hcardE⟩
  have hbarσ : ∀ z, hE.bar z = frobPow K (AdjoinRoot h) d z := by
    intro z
    rw [hE.bar_apply, frobPow_apply, hK, ← pow_mul]
  haveI : Finite hE.fixedField := Finite.of_injective _ Subtype.val_injective
  have hE₀9 : 9 ≤ Nat.card hE.fixedField := by
    refine nine_le_card_of_ne_three' fun h3 => ?_
    rw [UnitaryFieldData.card_fixedField] at h3
    obtain ⟨hl0, hord⟩ := hx.orderOf_root hp hh hne1
    have hdvd := dvd_card_sub_one_of_orderOf_unit hord
    rw [hcardE, mul_comm 2 (f * d), pow_mul, h3] at hdvd
    have h8 : p ∣ 2 ^ 3 := hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h8))
  obtain ⟨l₀, hl₀, hl₀2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card _
    (by omega : 4 ≤ Nat.card hE.fixedField)
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
    intro h0
    have h3 : (3 : AdjoinRoot h) = 0 := by exact_mod_cast CharP.cast_eq_zero (AdjoinRoot h) 3
    exact one_ne_zero (by linear_combination h3 - h0 : (1 : AdjoinRoot h) = 0)
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
  have hM := SpBlock.modelThree_herm hsymmB hvv hww hvw hE.fixedField
    (fun t ht => (hE.mem_fixedField).1 ht) hE₀9 (l := (l₀ : AdjoinRoot h)) l₀.2
    (fun h0 => hl₀ (Subtype.ext h0)) (fun h1 => hl₀2 (Subtype.ext (by simpa using h1))) hη0 hη
  have hrange : (blockGL Q x h).range = sesqUnitaryGroup Hb := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H htr γ, mem_sesqUnitaryGroup]
    rfl
  let φ : ↥(supportedBlock Q x h) ≃* ↥(sesqUnitaryGroup Hb) :=
    (MonoidHom.ofInjective (hx.blockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)
  obtain ⟨P, hPA, hP3, hP9, hPZ, hPq⟩ :=
    exists_three_of_modelThree_orth φ (fun g v hv => coe_blockGL h g ⟨v, hv⟩) hM
  refine ⟨P, hPA.trans (commutator_supportedBlock_le_specialBlock h), hP3, hP9,
    fun u hu hc => hPZ u hu fun j hj => hc j (commutator_supportedBlock_le_specialBlock h hj),
    fun u hu hcent hcube => ?_⟩
  obtain ⟨huA, -, hWq⟩ := hPq u hu hcent hcube
  have hoth := (mem_supportedBlock.1 huA).2
  apply eq_zero_of_orbit_others' hx hh hWq
  · rw [← hself]
    exact hWq
  · intro v hv
    have h1 : (u : V ≃ₗ[K] V) v = v := hoth v hv
    have h0 : (((u : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) v = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, h1, sub_self]
    rw [sq, Module.End.mul_apply, h0, map_zero]

end Special

end CFSG.LocalAnalysis.GLTheoremA.S2019
