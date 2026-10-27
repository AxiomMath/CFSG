module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement MatrixGroups

theorem derivedSeries_two_semidirectProduct {N G : Type*} [CommGroup N] [Group G]
    (φ : G →* MulAut N) (hG : ∀ a b : G, a * b = b * a) : derivedSeries (N ⋊[φ] G) 2 = ⊥ := by
  have h1 : derivedSeries (N ⋊[φ] G) 1 ≤ SemidirectProduct.inl.range := by
    rw [derivedSeries_one, _root_.commutator_def, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact Subgroup.commutator_le.2 fun x _ y _ => by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hG _ _
  rw [derivedSeries_succ, eq_bot_iff]
  refine (Subgroup.commutator_mono h1 h1).trans (Subgroup.commutator_le.2 ?_)
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul, mul_comm]

variable (K : Type*) [Field K]

@[expose] def unitsRingAut : RingAut K →* MulAut Kˣ where
  toFun σ := Units.mapEquiv σ.toMulEquiv
  map_one' := MulEquiv.ext fun _ => Units.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Units.ext rfl

@[expose] def scalarSemilinearHom : Kˣ ⋊[unitsRingAut K] RingAut K →* Equiv.Perm K where
  toFun x :=
    { toFun := fun c => x.left * x.right c
      invFun := fun c => x.right.symm (((x.left⁻¹ : Kˣ) : K) * c)
      left_inv := fun c => by simp
      right_inv := fun c => by simp }
  map_one' := Equiv.ext fun c => by
    change ((1 : Kˣ) : K) * c = c
    rw [Units.val_one, one_mul]
  map_mul' x y := Equiv.ext fun c => by
    change ((x.left * unitsRingAut K x.right y.left : Kˣ) : K) * x.right (y.right c) =
      x.left * x.right (y.left * y.right c)
    rw [Units.val_mul, map_mul, mul_assoc]
    rfl

theorem ringAut_mul_comm [Finite K] (σ τ : RingAut K) : σ * τ = τ * σ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hK⟩ := FiniteField.card' K
  have hcyc := (card_ringAut_and_isCyclic hp K (by rw [Nat.card_eq_fintype_card, hK])).2
  exact hcyc.commGroup.mul_comm σ τ

theorem derivedSeries_two_scalarSemilinearPerm [Finite K] :
    derivedSeries (scalarSemilinearPerm K) 2 = ⊥ := by
  let f := (scalarSemilinearHom K).codRestrict (scalarSemilinearPerm K)
    fun x => ⟨x.left, x.right, fun _ => rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨π, a, σ, h⟩
    exact ⟨⟨a, σ⟩, Subtype.ext (Equiv.ext fun c => (h c).symm)⟩
  rw [← map_derivedSeries_eq hf, derivedSeries_two_semidirectProduct _ (ringAut_mul_comm K),
    Subgroup.map_bot]

theorem exceptional_central_SL2_pair_stabilizer {K : Type*} [Field K] [Finite K]
    {L : Type*} [Group L] (ρ : SL(2, K) →* L) (hρ : Function.Surjective ρ)
    (hker : ∀ g : SL(2, K), ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) :
    derivedSeries (pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ)) 2 = ⊥ := by
  obtain ⟨-, Φ, hΦ, -⟩ := central_SL2_root_pair_semilinear_parameters ρ hρ hker
  have h := map_derivedSeries_le_derivedSeries Φ 2
  rwa [derivedSeries_two_scalarSemilinearPerm, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ hΦ] at h

@[expose] def scalarAddAut : Subgroup (Multiplicative (AddAut K)) where
  carrier := {f | ∃ c : Kˣ, ∀ x, f.toAdd x = c * x}
  one_mem' := ⟨1, fun x => by simp⟩
  mul_mem' := by
    rintro f g ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun x => ?_⟩
    change f.toAdd (g.toAdd x) = _
    rw [hd, hc, Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro f ⟨c, hc⟩
    refine ⟨c⁻¹, fun x => ?_⟩
    change f.toAdd.symm x = _
    rw [AddEquiv.symm_apply_eq, hc, Units.mul_inv_cancel_left]

variable {K}

theorem conj_scalarAddAut {f : Multiplicative (AddAut K)} {a : Kˣ} {σ : K ≃+* K}
    (hf : ∀ x, f.toAdd x = a * σ x) (c : K) (y : K) :
    f.toAdd (c * f.toAdd.symm y) = σ c * y := by
  have hy : (a : K) * σ (f.toAdd.symm y) = y := by rw [← hf, AddEquiv.apply_symm_apply]
  rw [hf, map_mul]
  conv_rhs => rw [← hy]
  ring

theorem mem_normalizer_scalarAddAut_iff [Finite K] (f : Multiplicative (AddAut K)) :
    f ∈ Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) ↔
      ∃ (a : Kˣ) (σ : K ≃+* K), ∀ x, f.toAdd x = a * σ x := by
  constructor
  · intro hN
    have hψ : ∀ c : Kˣ, ∃ d : K, ∀ x, f.toAdd (c * x) = d * f.toAdd x := by
      intro c
      have hc : Multiplicative.ofAdd (AddAut.mulLeft c) ∈ scalarAddAut K := ⟨c, fun x => rfl⟩
      obtain ⟨d, hd⟩ := (Subgroup.mem_normalizer_iff.1 hN _).1 hc
      refine ⟨d, fun x => ?_⟩
      have := hd (f.toAdd x)
      change f.toAdd (c • f.toAdd.symm (f.toAdd x)) = _ at this
      rwa [AddEquiv.symm_apply_apply, Units.smul_def, smul_eq_mul] at this
    have hf0 : f.toAdd 0 = 0 := map_zero _
    have hf1 : f.toAdd 1 ≠ 0 := fun h => one_ne_zero (f.toAdd.injective (h.trans hf0.symm))
    have hmul : ∀ c x : K, (f.toAdd 1)⁻¹ * f.toAdd (c * x) =
        ((f.toAdd 1)⁻¹ * f.toAdd c) * ((f.toAdd 1)⁻¹ * f.toAdd x) := by
      intro c x
      by_cases hc : c = 0
      · rw [hc, zero_mul, hf0, mul_zero, zero_mul]
      · obtain ⟨d, hd⟩ := hψ (Units.mk0 c hc)
        have h1 := hd 1
        rw [Units.val_mk0, mul_one] at h1
        rw [Units.val_mk0] at hd
        rw [hd, h1]
        field_simp
    let σr : K →+* K :=
      { toFun := fun x => (f.toAdd 1)⁻¹ * f.toAdd x
        map_one' := inv_mul_cancel₀ hf1
        map_mul' := hmul
        map_zero' := by rw [hf0, mul_zero]
        map_add' := fun x y => by rw [map_add, mul_add] }
    refine ⟨Units.mk0 _ hf1, RingEquiv.ofBijective σr
      ⟨σr.injective, Finite.surjective_of_injective σr.injective⟩, fun x => ?_⟩
    change f.toAdd x = f.toAdd 1 * ((f.toAdd 1)⁻¹ * f.toAdd x)
    rw [mul_inv_cancel_left₀ hf1]
  · rintro ⟨a, σ, hf⟩
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      refine ⟨Units.map σ.toMonoidHom c, fun y => ?_⟩
      change f.toAdd (h.toAdd (f.toAdd.symm y)) = _
      rw [hc, conj_scalarAddAut hf]
      rfl
    · rintro ⟨d, hd⟩
      refine ⟨Units.map σ.symm.toMonoidHom d, fun y => ?_⟩
      have hy := hd (f.toAdd y)
      change f.toAdd (h.toAdd (f.toAdd.symm (f.toAdd y))) = _ at hy
      rw [AddEquiv.symm_apply_apply, hf, hf] at hy
      have hy' : σ (h.toAdd y) = d * σ y := mul_left_cancel₀ a.ne_zero (by rw [hy]; ring)
      have hσ := congrArg σ.symm hy'
      rw [RingEquiv.symm_apply_apply, map_mul, RingEquiv.symm_apply_apply] at hσ
      rw [hσ]
      rfl

theorem small_Ree_additive_scalar_normalizer (p n : ℕ) (hp : p.Prime) (_hn : 1 ≤ n)
    (K : Type*) [Field K] (hK : Nat.card K = p ^ n) :
    (∀ f : Multiplicative (AddAut K),
      f ∈ Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) ↔
        ∃ (a : Kˣ) (σ : K ≃+* K), ∀ x, f.toAdd x = a * σ x) ∧
    derivedSeries (Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))) 2 =
      ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero n hp.ne_zero)
  refine ⟨mem_normalizer_scalarAddAut_iff, ?_⟩
  set N := Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))
  have hmem : ∀ f : N, ((f : Multiplicative (AddAut K)).toAdd.toEquiv : Equiv.Perm K) ∈
      scalarSemilinearPerm K := fun f => (mem_normalizer_scalarAddAut_iff _).1 f.2
  let Ψ : N →* scalarSemilinearPerm K :=
    { toFun := fun f => ⟨(f : Multiplicative (AddAut K)).toAdd.toEquiv, hmem f⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hΨ : Function.Injective Ψ := fun f g h => Subtype.ext (by
    have h' := congrArg (fun π : scalarSemilinearPerm K => ((π : Equiv.Perm K) : K → K)) h
    exact congrArg Multiplicative.ofAdd (AddEquiv.ext fun x => congrFun h' x))
  have h := map_derivedSeries_le_derivedSeries Ψ 2
  rwa [derivedSeries_two_scalarSemilinearPerm, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ hΨ] at h

theorem scalarSemilinearHom_injective (K : Type*) [Field K] :
    Function.Injective (scalarSemilinearHom K) := by
  rintro ⟨a, σ⟩ ⟨b, τ⟩ h
  have h1 := DFunLike.congr_fun h 1
  change a * σ 1 = b * τ 1 at h1
  rw [map_one, mul_one, map_one, mul_one] at h1
  have hab : a = b := Units.ext h1
  have hστ : σ = τ := by
    apply RingEquiv.ext
    intro c
    have hc := DFunLike.congr_fun h c
    change a * σ c = b * τ c at hc
    rw [← hab] at hc
    exact mul_left_cancel₀ a.ne_zero hc
  exact SemidirectProduct.ext hab hστ

theorem scalarSemilinearHom_range (K : Type*) [Field K] :
    (scalarSemilinearHom K).range = scalarSemilinearPerm K := by
  ext π
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.left, x.right, fun c => rfl⟩
  · rintro ⟨a, σ, h⟩
    refine ⟨⟨a, σ⟩, ?_⟩
    ext c
    exact (h c).symm

theorem isCyclic_and_card_dvd_of_isPGroup_two_semidirectProduct
    {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (H : Subgroup (Kˣ ⋊[unitsRingAut K] RingAut K))
    (hH2 : IsPGroup 2 H) :
    IsCyclic H ∧ Nat.card H ∣ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAut := card_ringAut_and_isCyclic Nat.prime_two K hcard
  have : IsCyclic (RingAut K) := hAut.2
  have hn0 : n ≠ 0 := by omega
  have : Finite (Kˣ ⋊[unitsRingAut K] RingAut K) :=
    Nat.finite_of_card_ne_zero (by
      rw [SemidirectProduct.card, Nat.card_units, hcard, hAut.1]
      exact mul_ne_zero (by
        have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow hn0
        exact (Nat.sub_pos_of_lt h1).ne') (by omega))
  have : Finite H :=
    Finite.of_injective (fun h : H => (h : Kˣ ⋊[unitsRingAut K] RingAut K))
      Subtype.coe_injective
  let f : Kˣ ⋊[unitsRingAut K] RingAut K →* RingAut K := SemidirectProduct.rightHom
  have hker_eq : f.ker =
      (SemidirectProduct.inl : Kˣ →* Kˣ ⋊[unitsRingAut K] RingAut K).range := by
    simpa [f] using (SemidirectProduct.range_inl_eq_ker_rightHom
      (φ := unitsRingAut K)).symm
  have hker_card : Nat.card f.ker = Nat.card Kˣ := by
    rw [hker_eq, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (K := ⊤) (SemidirectProduct.inl_injective)]
    simp
  have hOdd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' hn0).2 even_two) odd_one
  obtain ⟨m, hm⟩ := hH2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card f.ker) (Nat.card H) := by
    rw [hker_card, Nat.card_units, hcard, hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hOdd)
  have hdisj : Disjoint f.ker H := by
    rw [disjoint_iff]
    exact Subgroup.inf_eq_bot_of_coprime hcop
  have hker_bot : f.ker.subgroupOf H = ⊥ :=
    Subgroup.subgroupOf_eq_bot.mpr hdisj
  have hg_inj : Function.Injective (f.domRestrict H) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, hker_bot]
  refine ⟨?_, ?_⟩
  · exact isCyclic_of_injective (f.domRestrict H) hg_inj
  · have hrange_card : Nat.card (f.domRestrict H).range = Nat.card H := by
      rw [MonoidHom.range_eq_map]
      rw [Subgroup.card_map_of_injective (K := ⊤) hg_inj]
      simp
    have hcard_dvd : Nat.card H ∣ Nat.card (RingAut K) := by
      rw [← hrange_card]
      exact Subgroup.card_subgroup_dvd_card (f.domRestrict H).range
    rwa [hAut.1] at hcard_dvd

theorem isCyclic_and_card_dvd_of_isPGroup_two_range_scalarSemilinear
    {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card K = 2 ^ n)
    {A : Type*} [Group A]
    (rho : A →* Equiv.Perm K) (hA2 : IsPGroup 2 A)
    (hrange : rho.range ≤ scalarSemilinearPerm K) :
    IsCyclic rho.range ∧ Nat.card rho.range ∣ n := by
  have hrho2 : IsPGroup 2 rho.range := by
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (hA2.to_subgroup (⊤ : Subgroup A)) rho
  let K0 : Subgroup (Kˣ ⋊[unitsRingAut K] RingAut K) :=
    rho.range.comap (scalarSemilinearHom K)
  have hK0map : K0.map (scalarSemilinearHom K) = rho.range := by
    change (rho.range.comap (scalarSemilinearHom K)).map (scalarSemilinearHom K) = rho.range
    apply Subgroup.map_comap_eq_self
    rw [scalarSemilinearHom_range K]
    exact hrange
  let f0 : K0 →* Equiv.Perm K := (scalarSemilinearHom K).domRestrict K0
  have hf0_inj : Function.Injective f0 := by
    intro x y h
    exact Subtype.ext (scalarSemilinearHom_injective K (by simpa [f0] using h))
  have hf0_range : f0.range = rho.range := by
    rw [MonoidHom.domRestrict_range, hK0map]
  let g : K0 →* rho.range := f0.codRestrict rho.range fun x => by
    rw [← hf0_range]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hg_inj : Function.Injective g := by
    intro x y h
    apply hf0_inj
    exact congrArg Subtype.val h
  have hg_surj : Function.Surjective g := by
    intro y
    have hy : (y : Equiv.Perm K) ∈ f0.range := by
      rw [hf0_range]
      exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  have hK02 : IsPGroup 2 K0 := hrho2.of_injective g hg_inj
  obtain ⟨hcycK0, hcardK0⟩ :=
    isCyclic_and_card_dvd_of_isPGroup_two_semidirectProduct hn hcard K0 hK02
  let : IsCyclic K0 := hcycK0
  let e : K0 ≃* rho.range := MulEquiv.ofBijective g ⟨hg_inj, hg_surj⟩
  refine ⟨?_, ?_⟩
  · exact isCyclic_of_injective e.symm.toMonoidHom e.symm.injective
  · rw [← Nat.card_congr e.toEquiv]
    exact hcardK0

theorem isCyclic_and_card_dvd_of_isPGroup_two_subgroup_scalarSemilinear
    {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (E : Subgroup (Equiv.Perm K)) (hE : E ≤ scalarSemilinearPerm K)
    (hE2 : IsPGroup 2 E) :
    IsCyclic E ∧ Nat.card E ∣ n := by
  have h := isCyclic_and_card_dvd_of_isPGroup_two_range_scalarSemilinear
    hn hcard (E.subtype : E →* Equiv.Perm K) hE2 (by
      rwa [Subgroup.range_subtype])
  let e : E ≃* (E.subtype : E →* Equiv.Perm K).range :=
    MonoidHom.ofInjective E.subtype_injective
  refine ⟨?_, ?_⟩
  · exact e.isCyclic.mpr h.1
  · rw [Nat.card_congr e.toEquiv]
    exact h.2

theorem exists_semilinear_of_mem_normalizer_zpowers [Finite K]
    {R : Type*} [Group R] (e : R ≃* Multiplicative K) (delta : MulAut R) (mu : Kˣ)
    (hmu : orderOf mu = Nat.card Kˣ)
    (hdelta : ∀ r : R, (e (delta r)).toAdd = (mu : K) * (e r).toAdd)
    (f : MulAut R)
    (hf : f ∈ Subgroup.normalizer (Subgroup.zpowers delta : Set (MulAut R))) :
    ∃ (a : Kˣ) (sigma : K ≃+* K),
      ∀ r : R, (e (f r)).toAdd = (a : K) * sigma ((e r).toAdd) := by
  let Φ : MulAut R ≃* Multiplicative (AddAut K) :=
    (MulAut.congr e).trans (MulAutMultiplicative K)
  have hΦapply : ∀ (g : MulAut R) (r : R),
      (Φ g).toAdd ((e r).toAdd) = (e (g r)).toAdd := by
    intro g r
    change (e (g (e.symm (e r)))).toAdd = (e (g r)).toAdd
    rw [MulEquiv.symm_apply_apply]
  have hΦdelta_apply : ∀ x : K, (Φ delta).toAdd x = (mu : K) * x := by
    intro x
    change (e (delta (e.symm (Multiplicative.ofAdd x)))).toAdd = (mu : K) * x
    rw [hdelta, MulEquiv.apply_symm_apply]
    rfl
  have hΦdelta : Φ delta = AddAut.mulLeft mu := by
    apply Multiplicative.ext
    apply AddEquiv.ext
    intro x
    rw [hΦdelta_apply x]
    rfl
  have hrange : scalarAddAut K = (AddAut.mulLeft (R := K)).range := by
    apply SetLike.ext
    intro g
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      apply Multiplicative.ext
      apply AddEquiv.ext
      intro x
      change (c : K) * x = g.toAdd x
      exact (hc x).symm
    · rintro ⟨c, rfl⟩
      exact ⟨c, fun x => rfl⟩
  have hmu_top : Subgroup.zpowers mu = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, hmu]
  have hgen : Subgroup.zpowers (AddAut.mulLeft (R := K) mu) = scalarAddAut K := by
    rw [← MonoidHom.map_zpowers (AddAut.mulLeft (R := K)) mu, hmu_top, Subgroup.map_top]
    exact hrange.symm
  have hfΦ : Φ f ∈ Subgroup.normalizer
      (scalarAddAut K : Set (Multiplicative (AddAut K))) := by
    have hmem : Φ f ∈ (Subgroup.normalizer
        (Subgroup.zpowers delta : Set (MulAut R))).map Φ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨f, hf, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq (Subgroup.zpowers delta) Φ,
      MonoidHom.map_zpowers (Φ.toMonoidHom) delta] at hmem
    change Φ f ∈ Subgroup.normalizer
      (Subgroup.zpowers (Φ delta) : Set (Multiplicative (AddAut K))) at hmem
    rw [hΦdelta, hgen] at hmem
    exact hmem
  obtain ⟨a, sigma, hsigma⟩ :=
    (mem_normalizer_scalarAddAut_iff (K := K) (Φ f)).1 hfΦ
  refine ⟨a, sigma, fun r => ?_⟩
  rw [← hΦapply f r]
  exact hsigma ((e r).toAdd)


theorem isCyclic_and_card_dvd_of_isPGroup_two_root_centralizer_quotient
    {K G : Type*} [Field K] [Finite K] [Group G]
    {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card K = 2 ^ n)
    {R U : Subgroup G} (hUR : U ≤ Subgroup.normalizer (R : Set G))
    (e : R ≃ K) (hU2 : IsPGroup 2 U)
    (hrho :
      ((Equiv.permCongrHom e).toMonoidHom.comp
        ((MulAut.toPerm R).comp
          ((R.normalizerMonoidHom).comp (Subgroup.inclusion hUR)))).range
        ≤ scalarSemilinearPerm K) :
    ((R.normalizerMonoidHom).comp (Subgroup.inclusion hUR)).ker =
        (Subgroup.centralizer (R : Set G)).subgroupOf U ∧
      IsCyclic (U ⧸ ((R.normalizerMonoidHom).comp
        (Subgroup.inclusion hUR)).ker) ∧
      Nat.card (U ⧸ ((R.normalizerMonoidHom).comp
        (Subgroup.inclusion hUR)).ker) ∣ n := by
  let theta : U →* MulAut R :=
    (R.normalizerMonoidHom).comp (Subgroup.inclusion hUR)
  let rho : U →* Equiv.Perm K :=
    (Equiv.permCongrHom e).toMonoidHom.comp ((MulAut.toPerm R).comp theta)
  have htheta_ker : theta.ker =
      (Subgroup.centralizer (R : Set G)).subgroupOf U := by
    rw [show theta = (R.normalizerMonoidHom).comp (Subgroup.inclusion hUR) from rfl,
      ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf]
  have hrho_le : rho.range ≤ scalarSemilinearPerm K := by
    change ((Equiv.permCongrHom e).toMonoidHom.comp
        ((MulAut.toPerm R).comp
          ((R.normalizerMonoidHom).comp (Subgroup.inclusion hUR)))).range
      ≤ scalarSemilinearPerm K
    exact hrho
  have hres := isCyclic_and_card_dvd_of_isPGroup_two_range_scalarSemilinear
    (K := K) (n := n) hn hcard (A := U) rho hU2 hrho_le
  have htoPerm_inj : Function.Injective (MulAut.toPerm R) := by
    intro f g h
    exact MulEquiv.ext fun r => DFunLike.congr_fun h r
  have hrho_ker : rho.ker = theta.ker := by
    rw [show rho = (Equiv.permCongrHom e).toMonoidHom.comp
        ((MulAut.toPerm R).comp theta) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (Equiv.permCongrHom e).injective,
      MonoidHom.ker_comp_of_injective _ _ htoPerm_inj]
  let eQ : U ⧸ theta.ker ≃* rho.range :=
    (QuotientGroup.quotientMulEquivOfEq hrho_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange rho)
  have hquot_cyc : IsCyclic (U ⧸ theta.ker) := eQ.isCyclic.mpr hres.1
  have hquot_card : Nat.card (U ⧸ theta.ker) ∣ n := by
    rw [Nat.card_congr eQ.toEquiv]
    exact hres.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [theta] using htheta_ker
  · simpa [theta] using hquot_cyc
  · simpa [theta] using hquot_card


end CFSG.LocalAnalysis.ComponentInitial
