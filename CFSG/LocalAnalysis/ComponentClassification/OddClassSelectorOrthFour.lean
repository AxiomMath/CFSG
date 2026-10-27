module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthExt
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthPlus
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponent

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped commutatorElement

theorem exists_rotation (F : Type*) [Field F] :
    ∃ J : SpecialLinearGroup (Fin 2) F, (J : Matrix (Fin 2) (Fin 2) F) * J = -1 ∧
      ∀ a : F, (J : Matrix (Fin 2) (Fin 2) F) ≠ a • 1 := by
  refine ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, ?_, fun a h => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have h01 := congrFun (congrFun h 0) 1
    simp at h01

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] in
theorem false_of_neg_one_witness {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 5 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hYΩ : Y ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hYq : CFSG.Assembly.IsQuasisimple Y)
    {R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hRp : ⁅R, R⁆ = R)
    (hRY : ∀ r ∈ R, ∀ y ∈ Y, (r : V ≃ₗ[K] V) * y = y * r)
    {T : TauCeti.QuadraticMap.orthogonalGroup Q} (hTR : T ∈ R)
    (hTT : ∀ v, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) v) = -v)
    (hTns : ∀ c : K, (T : V ≃ₗ[K] V).toLinearMap ≠ c • 1)
    (hN : ∀ t s : V ≃ₗ[K] V,
      t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      (∃ c : K, ((t * t : V ≃ₗ[K] V) : V →ₗ[K] V) = c • LinearMap.id) →
      (∀ c : K, (t : V →ₗ[K] V) ≠ c • LinearMap.id) → (∀ y ∈ Y, y * t = t * y) →
      s * t = t * s → s ∈ normalizer (Y : Set (V ≃ₗ[K] V))) : False := by
  classical
  have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hneg : ∀ v : V, -v = v → v = 0 := fun v h => by
    have h3 : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel v
    exact (smul_eq_zero.mp h3).resolve_left h2
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hR1 : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hTR
    have h1 := hTT v₀
    rw [hTR] at h1
    exact hv₀ (hneg v₀ h1.symm)
  have hRΩ : R ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    calc R = ⁅R, R⁆ := hRp.symm
      _ ≤ ⁅⊤, ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = _ := (_root_.commutator_def _).symm
  have hTΩ : (T : V ≃ₗ[K] V) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    have h1 : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
          ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← h1]
    exact ⟨T, hRΩ hTR, rfl⟩
  have hTY : ∀ y ∈ Y, y * (T : V ≃ₗ[K] V) = (T : V ≃ₗ[K] V) * y := fun y hy =>
    (hRY T hTR y hy).symm
  have hNT : ∀ s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, s * (T : V ≃ₗ[K] V) = (T : V ≃ₗ[K] V) * s →
        s ∈ normalizer (Y : Set (V ≃ₗ[K] V)) := by
    intro s hs hst
    refine hN T s hTΩ hs ⟨-1, LinearMap.ext fun v => ?_⟩ (fun c h => hTns c h) hTY hst
    rw [LinearMap.smul_apply, LinearMap.id_apply, neg_one_smul]
    exact hTT v
  have hYMΩ : Y ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ ⊓ centralizer {(T : V ≃ₗ[K] V)} := fun y hy =>
    ⟨hYΩ hy, mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact (hTY y hy).symm⟩
  have hnY : (Y.subgroupOf (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ ⊓ centralizer {(T : V ≃ₗ[K] V)})).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgN := hNT g.1 g.2.1 (mem_centralizer_iff.mp g.2.2 _ (Set.mem_singleton _)).symm
    rw [mem_normalizer_iff] at hgN
    exact (hgN n).mp hn
  have hnΩ : ((⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ ⊓ centralizer {(T : V ≃ₗ[K] V)}).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ centralizer {(T : V ≃ₗ[K] V)})).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2.2 hn.2) (Subgroup.inv_mem _ g.2.2)⟩
    have h1 : ((g * n * g⁻¹ : ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        centralizer {(T : V ≃ₗ[K] V)})) : V ≃ₗ[K] V) =
          ⁅(g : V ≃ₗ[K] V), (n : V ≃ₗ[K] V)⁆ * n := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator g.2.1
      (Subgroup.commutator_le_self _ hn.1)) hn.1
  have hYM : CFSG.Assembly.IsComponentOf Y
      (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ centralizer {(T : V ≃ₗ[K] V)}) :=
    isComponentOf_of_normal_le ⟨hYMΩ, CFSG.Assembly.IsSubnormal.step hYMΩ hnY
      (CFSG.Assembly.IsSubnormal.refl _), hYq⟩
      (inf_le_inf_right _ (Subgroup.commutator_le_self _)) hnΩ
  have hY₂ := isComponentOf_comap_of_le_range (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective hYM
    (by rw [Subgroup.range_subtype]; exact inf_le_left)
  have hC : (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ centralizer {(T : V ≃ₗ[K] V)}).comap
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = centralizer {T} := by
    ext u
    rw [Subgroup.mem_comap, Subgroup.mem_inf, mem_centralizer_iff, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨u.2, congrArg Subtype.val h⟩⟩
  rw [hC] at hY₂
  have hL := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hY₂.1).mp hY₂
  have hR : R ≤ centralizer ((((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (centralizer {T})).map (centralizer {T}).subtype : Subgroup _) :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    intro r hr
    rw [mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.subgroupOf_map_subtype] at hh
    exact Subtype.ext (hRY r hr h hh.1).symm
  have hT1 := LocalAnalysis.ComponentInitial.ProjectiveOrthogonal.sq_eq_one_of_isComponent hℓ hℓ2
    he hK hd hQ hTns (Or.inr hTT) hL hR hRp hR1 v₀
  rw [hTT] at hT1
  exact hv₀ (hneg v₀ hT1)

omit [Finite K] in
theorem split_four_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 5 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    {E : Type} [Field E] [Finite E] [Algebra K E] [Module E V] [IsScalarTower K E V]
    [FiniteDimensional E V] (hE2 : Nat.card E ≠ 2) (hE3 : Nat.card E ≠ 3)
    {QE : QuadraticForm E V} (hQE : QE.polarBilin.Nondegenerate) (hE4 : finrank E V = 4)
    (hS : ∃ S : Submodule E V, finrank E S = 2 ∧ ∀ x ∈ S, QE x = 0)
    {C : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (eO : C ≃* TauCeti.QuadraticMap.orthogonalGroup QE)
    (heO : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) x, (eO.symm g).val.val x = g.val x)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hYC : Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype ≤ C)
    (hY₁ : CFSG.IsComponent
      ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf C))
    (hYΩ : Y ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hYq : CFSG.Assembly.IsQuasisimple Y)
    (hN : ∀ t s : V ≃ₗ[K] V,
      t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      (∃ c : K, ((t * t : V ≃ₗ[K] V) : V →ₗ[K] V) = c • LinearMap.id) →
      (∀ c : K, (t : V →ₗ[K] V) ≠ c • LinearMap.id) → (∀ y ∈ Y, y * t = t * y) →
      s * t = t * s → s ∈ normalizer (Y : Set (V ≃ₗ[K] V))) : False := by
  classical
  obtain ⟨-, -, -, hsplit, -, -, -⟩ :=
    LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
      QE hQE (Or.inr (Or.inr ⟨hE4, hS⟩))
  obtain ⟨ψ, eD, -, heD, hsup, hq₁, hq₂, hn₁, hn₂, hcomm⟩ := hsplit hE4 hS hE2 hE3
  have hL' := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent eO hY₁
  have hact : ∀ z v, (eD.symm (specialRho z)).val v =
      ψ.symm (z.1.val * ψ v * (z.2⁻¹ : SpecialLinearGroup (Fin 2) E).val) := by
    intro z v
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply, ← specialRho_apply z (ψ v)]
    have h1 := heD (eD.symm (specialRho z)) (ψ v)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    exact h1.symm
  obtain ⟨J, hJJ, hJs⟩ := exists_rotation E
  have hone : (1 : SpecialLinearGroup (Fin 2) E).val = 1 := rfl
  have hJns : ∀ (t : TauCeti.QuadraticMap.orthogonalGroup QE),
      (t : V ≃ₗ[E] V) (ψ.symm 1) = ψ.symm J → ∀ c : K, ∃ v, (t : V ≃ₗ[E] V) v ≠ c • v := by
    intro t ht c
    refine ⟨ψ.symm 1, fun h => hJs (algebraMap K E c) (ψ.symm.injective ?_)⟩
    rw [← ht, h, ← algebraMap_smul (A := E) c, LinearEquiv.map_smul]
  obtain ⟨R₂, t₂, hR₂p, hcomm', ht₂R, ht₂t, ht₂ns⟩ :
      ∃ (R₂ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup QE))
        (t₂ : TauCeti.QuadraticMap.orthogonalGroup QE), ⁅R₂, R₂⁆ = R₂ ∧
        (∀ x ∈ ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf C).map
          eO.toMonoidHom, ∀ y ∈ R₂, x * y = y * x) ∧ t₂ ∈ R₂ ∧
        (∀ v, (t₂ : V ≃ₗ[E] V) ((t₂ : V ≃ₗ[E] V) v) = -v) ∧
        ∀ c : K, ∃ v, (t₂ : V ≃ₗ[E] V) v ≠ c • v := by
    rcases LocalAnalysis.ComponentInitial.eq_or_eq_of_isComponent_of_commutator_eq_sup hL' hsup
      hq₁ hq₂ hn₁ hn₂ with h | h
    · refine ⟨_, eD.symm (specialRho (1, J⁻¹)), Subgroup.isPerfect_iff.mp hq₂.1, ?_,
        ⟨specialRho (1, J⁻¹), ⟨J⁻¹, rfl⟩, rfl⟩, fun v => ?_, hJns _ ?_⟩
      · rw [h]
        exact hcomm
      · rw [hact, hact, LinearEquiv.apply_symm_apply]
        simp only [inv_inv, hone, Matrix.one_mul, Matrix.mul_assoc, hJJ, Matrix.mul_neg,
          Matrix.mul_one, map_neg, LinearEquiv.symm_apply_apply]
      · rw [hact, LinearEquiv.apply_symm_apply]
        simp only [inv_inv, hone, Matrix.one_mul]
    · refine ⟨_, eD.symm (specialRho (J, 1)), Subgroup.isPerfect_iff.mp hq₁.1, ?_,
        ⟨specialRho (J, 1), ⟨J, rfl⟩, rfl⟩, fun v => ?_, hJns _ ?_⟩
      · rw [h]
        exact fun x hx y hy => (hcomm y hy x hx).symm
      · rw [hact, hact, LinearEquiv.apply_symm_apply]
        simp only [inv_one, hone, Matrix.mul_one, ← Matrix.mul_assoc, hJJ, Matrix.neg_mul,
          Matrix.one_mul, map_neg, LinearEquiv.symm_apply_apply]
      · rw [hact, LinearEquiv.apply_symm_apply]
        simp only [inv_one, hone, Matrix.mul_one]
  have hφ : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) v,
      (((C.subtype.comp eO.symm.toMonoidHom) g : TauCeti.QuadraticMap.orthogonalGroup Q) :
        V ≃ₗ[K] V) v = (g : V ≃ₗ[E] V) v := fun g v => heO g v
  refine false_of_neg_one_witness hℓ hℓ2 he hK hd hQ hYΩ hYq
    (R := R₂.map (C.subtype.comp eO.symm.toMonoidHom)) ?_ ?_ ⟨t₂, ht₂R, rfl⟩ (fun v => ?_)
    (fun c h => ?_) hN
  · rw [← Subgroup.map_commutator, hR₂p]
  · rintro _ ⟨r, hr, rfl⟩ y hy
    have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self _ (hYΩ hy)
    have hyC : (⟨y, hyO⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ C := hYC hy
    have h1 := hcomm' (eO ⟨⟨y, hyO⟩, hyC⟩) ⟨⟨⟨y, hyO⟩, hyC⟩, hy, rfl⟩ r hr
    have h2 := congrArg (fun g => (((C.subtype.comp eO.symm.toMonoidHom) g :
      TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V)) h1
    simp only [map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype, Subgroup.coe_mul] at h2
    exact h2.symm
  · rw [hφ, hφ]
    exact ht₂t v
  · obtain ⟨v, hv⟩ := ht₂ns c
    apply hv
    have h1 := LinearMap.congr_fun h v
    rw [LinearEquiv.coe_coe, hφ, LinearMap.smul_apply, Module.End.one_apply] at h1
    exact h1

theorem orth_ext_small_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ finrank K V) (hd9 : finrank K V ≤ 9)
    (hU : finrank K V = 8 → ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0)
    (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (hnsq : ¬ IsSquare (d : K)) (hμ : (μ : K) / (d : K) = 1)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap))
    (hYΩ : Y ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hN : ∀ t s : V ≃ₗ[K] V,
      t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      (∃ c : K, ((t * t : V ≃ₗ[K] V) : V →ₗ[K] V) = c • LinearMap.id) →
      (∀ c : K, (t : V →ₗ[K] V) ≠ c • LinearMap.id) → (∀ y ∈ Y, y * t = t * y) →
      s * t = t * s → s ∈ normalizer (Y : Set (V ≃ₗ[K] V))) : False := by
  classical
  have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ he hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk2
  obtain ⟨-, hadj0, -, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A d μ hsquare hsim hnonscalar
  have h4 := hns4 hnsq
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let : Field (scalarAlgebra A.toLinearMap) := scalarField A.toLinearMap d hnsq
    (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare)
  let : Module (scalarAlgebra A.toLinearMap) V := evaluationModule A.toLinearMap
  obtain ⟨⟨-, hfin, hgen, -, -, hcoord, -, -, hcard, -, -, -, -, -, -, -, hsmul, -, htower, hfinE,
    hfinrank, -⟩, hpos, -⟩ := h4
  obtain ⟨hBEs, -, -, hQEnd, hBE, hQE, eO, -, heO2, -, -⟩ := hpos hμ
  have := hfin
  have : IsScalarTower K (scalarAlgebra A.toLinearMap) V := htower
  have : FiniteDimensional (scalarAlgebra A.toLinearMap) V := hfinE
  have h8 : finrank K V = 8 := by omega
  have hE4 : finrank (scalarAlgebra A.toLinearMap) V = 4 := by omega
  obtain ⟨U, hU4, hUQ⟩ := hU h8
  have hμd : (μ : K) = d := (div_eq_one_iff_eq (Units.ne_zero d)).mp hμ
  have hQA : ∀ x, Q (A x) = (d : K) * Q x := by
    intro x
    have h1 := hsim x x
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_self, polar_self, two_smul,
      two_smul, hμd] at h1
    have h3 : (2 : K) * (Q (A x) - (d : K) * Q x) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2)
  have hadj : ∀ x y, Q.polarBilin (A x) y = Q.polarBilin x (A y) := fun x y => by
    rw [hadj0, hμ, one_mul]
  have hE : ∀ z : scalarAlgebra A.toLinearMap, ∃ a b : K,
      z = algebraMap K _ a + algebraMap K _ b * generator A.toLinearMap := by
    intro z
    obtain ⟨⟨a, b⟩, hab, -⟩ := hcoord z
    refine ⟨a, b, ?_⟩
    rw [← hab]
    simp only [coordinateElement, Algebra.smul_def]
  have hcardE : Nat.card (scalarAlgebra A.toLinearMap) = Nat.card K ^ 2 := by rw [hcard, hK]
  have hℓ3 : 3 ≤ ℓ := Nat.lt_of_le_of_ne hℓ.two_le (Ne.symm hℓ2)
  have h9 : 9 ≤ Nat.card (scalarAlgebra A.toLinearMap) := by
    rw [hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ (ℓ ^ e) ^ 2 := Nat.pow_le_pow_left (hℓ3.trans (Nat.le_self_pow (by omega) ℓ)) 2
  obtain ⟨S, hS2, hSQ⟩ := exists_split_of_totallySingular hk2 hcardE hQ h8 (A := A.toLinearMap)
    (Units.ne_zero d) (fun x => hsquare x) hQA hadj (generator A.toLinearMap)
    (fun v => by rw [hsmul, hgen]) hE hBEs hBE hQE hU4 hUQ
  obtain ⟨hle, hY₁, -⟩ := isComponent_operatorCentralizer hY
  exact split_four_false hℓ hℓ2 he hK (by omega) hQ (by omega) (by omega) hQEnd hE4
    ⟨S, hS2, hSQ⟩ eO heO2 hle hY₁ hYΩ hY.2.2 hN

end CFSG.ComponentClassification.OddClassSelector
