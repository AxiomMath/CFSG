module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelLagBasis
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelLagCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OPNonembed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OPLagrangian
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelToral
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagAssembly
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagMain
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix Subgroup Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (spJ transpose_mul_mul_of_mem_statedSp)
open scoped MatrixGroups

section Transport

variable {F : Type} [Field F]

@[expose] def lagConj {M V : Type} [AddCommGroup M] [Module F M] [AddCommGroup V] [Module F V]
    (ι : M ≃ₗ[F] V) : (M ≃ₗ[F] M) ≃* (V ≃ₗ[F] V) where
  toFun g := ι.symm.trans (g.trans ι)
  invFun h := ι.trans (h.trans ι.symm)
  left_inv g := by
    ext x
    simp
  right_inv h := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [LinearEquiv.mul_apply]

theorem lagConj_apply {M V : Type} [AddCommGroup M] [Module F M] [AddCommGroup V] [Module F V]
    (ι : M ≃ₗ[F] V) (g : M ≃ₗ[F] M) (x : M) : lagConj ι g (ι x) = ι (g x) := by
  simp [lagConj]

variable (F) in
@[expose] noncomputable def lagMatEquiv (ι : Type) [Fintype ι] [DecidableEq ι] :
    GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))

theorem lagMatEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι F) (v : ι → F) :
    lagMatEquiv F ι g v = (g : Matrix ι ι F) *ᵥ v := by
  simp [lagMatEquiv, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin]

end Transport

section SplitForm

variable {m : ℕ} {F : Type} [Field F]

@[expose] def lagQ (v : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → F) : F :=
  ∑ a, v (Sum.inl a) * v (Sum.inr a)

theorem lagQ_eq_dotProduct (v : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → F) :
    lagQ v = (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := rfl

theorem dotProduct_mulVec_self_of_mem_lagAlt [CharP F 2]
    {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F} (hC : C ∈ lagAlt m F)
    (y : Fin m ⊕ Fin m → F) : y ⬝ᵥ (C *ᵥ y) = 0 := by
  rw [eq_lagUpper_add_transpose hC, add_mulVec, dotProduct_add, mulVec_transpose,
    dotProduct_comm y (y ᵥ* lagUpper C), ← dotProduct_mulVec, CharTwo.add_self_eq_zero]

theorem lagQ_lagRad [CharP F 2] {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hC : C ∈ lagAlt m F) (v : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → F) :
    lagQ ((lagRad m F (Multiplicative.ofAdd C)).1 *ᵥ v) = lagQ v := by
  rw [coe_lagRad, toAdd_ofAdd, lagQ_eq_dotProduct, lagQ_eq_dotProduct, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, zero_mulVec, zero_add]
  rw [add_dotProduct, dotProduct_comm (C *ᵥ _), dotProduct_mulVec_self_of_mem_lagAlt hC, add_zero]

theorem mul_spJ_mul_transpose [CharP F 2] (A : StatedSp m F) :
    mat m F A * spJ m F * (mat m F A)ᵀ = spJ m F := by
  have hA := transpose_mul_mul_of_mem_statedSp A.2
  rw [← mat_apply] at hA
  have h1 : (spJ m F * (mat m F A)ᵀ * spJ m F) * mat m F A = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (mat m F A)ᵀ, hA,
      spJ_mul_spJ_of_charTwo]
  have h2 : mat m F A * (spJ m F * (mat m F A)ᵀ * spJ m F) = 1 := mul_eq_one_comm.1 h1
  calc mat m F A * spJ m F * (mat m F A)ᵀ =
      mat m F A * (spJ m F * (mat m F A)ᵀ * spJ m F) * spJ m F := by
        simp only [Matrix.mul_assoc, spJ_mul_spJ_of_charTwo, Matrix.mul_one]
    _ = spJ m F := by rw [h2, Matrix.one_mul]

theorem lagQ_lagLevi [CharP F 2] (A : StatedSp m F) (v : (Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → F) :
    lagQ ((lagLevi m F A).1 *ᵥ v) = lagQ v := by
  have hA := transpose_mul_mul_of_mem_statedSp A.2
  rw [← mat_apply] at hA
  rw [coe_lagLevi, lagQ_eq_dotProduct, lagQ_eq_dotProduct, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hA, spJ_mul_spJ_of_charTwo, one_mulVec, dotProduct_comm]

theorem lagP_le_centralizer [CharP F 2] :
    lagP m F ≤ centralizer {lagRad m F (Multiplicative.ofAdd (spJ m F))} := by
  apply sup_le
  · rintro _ ⟨C, -, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul (lagRad m F), ← map_mul (lagRad m F), ← ofAdd_add,
      ← ofAdd_add, add_comm]
  · rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_singleton_iff, lagLevi_mul_lagRad, mul_spJ_mul_transpose]

end SplitForm

section CoreLe

variable {K : Type} [Field K]

theorem card_le_of_lagrangian_core_of_le [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
    {P R X : Subgroup G} (hRP : R ≤ P) (hXP : X ≤ P) {m n : ℕ} (hm : 1 ≤ m)
    (hn : n + 1 = 2 * m) (ψ : P →* StatedSp n K) (hψ : Function.Injective ψ)
    (hR : IsPGroup 2 R) (hXN : X ≤ normalizer (R : Set G)) [IsSimpleGroup X]
    (hXp : Group.IsPerfect X) (hRX : ⁅R, X⁆ = R)
    (hC : ∀ r ∈ R, (∀ x ∈ X, x * r = r * x) → r = 1) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hxℓ : x ^ ℓ = 1)
    (hord : ∀ j, 1 ≤ j → j < 2 * m → ¬ ℓ ∣ Nat.card K ^ j - 1) :
    Nat.card R ≤ Nat.card K ^ (2 * m * (m - 1)) := by
  have eR : R.subgroupOf P ≃* R := Subgroup.subgroupOfEquivOfLe hRP
  have eX : X.subgroupOf P ≃* X := Subgroup.subgroupOfEquivOfLe hXP
  have : IsSimpleGroup (X.subgroupOf P) := eX.isSimpleGroup
  have := hXp
  have hXp' : Group.IsPerfect (X.subgroupOf P) :=
    Group.IsPerfect.ofSurjective (f := eX.symm.toMonoidHom) eX.symm.surjective
  have hR' : IsPGroup 2 (R.subgroupOf P) := hR.of_equiv eR.symm
  have hXN' : X.subgroupOf P ≤ normalizer ((R.subgroupOf P : Subgroup P) : Set P) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.1 (hXN hg) h
  have hRX' : ⁅R.subgroupOf P, X.subgroupOf P⁆ = R.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hRP, inf_of_le_left hXP, hRX]
  have hC' : ∀ r ∈ R.subgroupOf P, (∀ y ∈ X.subgroupOf P, y * r = r * y) → r = 1 := by
    intro r hr hrX
    refine Subtype.ext (hC r hr fun y hy => ?_)
    exact congrArg Subtype.val (hrX ⟨y, hXP hy⟩ hy)
  rw [← Nat.card_congr eR.toEquiv]
  exact card_le_of_lagrangian_core hm hn ψ hψ _ _ hR' hXN' hXp' hRX' hC' (x := ⟨x, hXP hx⟩) hx
    (fun h => hx1 (congrArg Subtype.val h)) hℓ hℓ2 (Subtype.ext (by simp [hxℓ])) hord

end CoreLe

section Aux

variable {m : ℕ} {F : Type} [Field F]

theorem lag_commutator_le_self {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem exists_ne_zero_ne_one_of_four_le [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ κ : F, κ ≠ 0 ∧ κ ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun κ _ => by
    by_cases h0 : κ = 0
    · simp [h0]
    · simp [h κ h0]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

theorem spJ_apply_of_charTwo [CharP F 2] (i d : Fin m ⊕ Fin m) :
    spJ m F i d = if i = d.swap then 1 else 0 := by
  rcases i with i | i <;> rcases d with d | d <;>
    simp [spJ, Matrix.one_apply, CharTwo.neg_eq, Sum.swap, eq_comm]

theorem lagRadJ_mulVec_inl [CharP F 2] (a : Fin m ⊕ Fin m) :
    (lagRad m F (Multiplicative.ofAdd (spJ m F))).1 *ᵥ Pi.single (Sum.inl a) 1 =
      Pi.single (Sum.inl a) 1 := by
  rw [coe_lagRad, toAdd_ofAdd, mulVec_single_one]
  ext x
  rcases x with x | x <;> simp [Matrix.col_apply, Matrix.one_apply, Pi.single_apply]

theorem lagRadJ_mulVec_inr [CharP F 2] (d : Fin m ⊕ Fin m) :
    (lagRad m F (Multiplicative.ofAdd (spJ m F))).1 *ᵥ Pi.single (Sum.inr d) 1 =
      Pi.single (Sum.inr d) 1 + Pi.single (Sum.inl d.swap) 1 := by
  rw [coe_lagRad, toAdd_ofAdd, mulVec_single_one]
  ext x
  rcases x with x | x
  · simp [Matrix.col_apply, spJ_apply_of_charTwo, Pi.single_apply]
  · simp [Matrix.col_apply, Matrix.one_apply, Pi.single_apply]

end Aux

section Main

theorem omegaLagrangianATwoModelInput_holds : OmegaLagrangianATwoModelInput := by
  intro F _ _ _ V _ _ _ Q hF4 hnd N hN4 hN5 hdim s hss hlag hQW
  classical
  have hsO : (s : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    lag_commutator_le_self _ s.2
  have hss' : (s : V ≃ₗ[F] V) * s = 1 := congrArg Subtype.val hss
  obtain ⟨m, rfl⟩ : ∃ m, N = 2 * m := ⟨N / 2, by omega⟩
  have hmo : Odd m := ⟨m / 2, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hdimW : finrank F (omegaInvSpace (s : V ≃ₗ[F] V)) = 2 * m := by omega
  have hdimV : finrank F V = 2 * (2 * m) := by omega
  obtain ⟨b, hbQ, hbll, hbrr, hblr, hsl, hsr⟩ := exists_lagBasis hnd hsO hss' hdimW hdimV hQW
  set ι : ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → F) ≃ₗ[F] V := b.equivFun.symm with hιdef
  set Φ : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F ≃* (V ≃ₗ[F] V) :=
    (lagMatEquiv F _).trans (lagConj ι) with hΦdef
  have hΦapp : ∀ (g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) v, Φ g (ι v) = ι (g.1 *ᵥ v) :=
    fun g v => by
    rw [hΦdef, MulEquiv.trans_apply, lagConj_apply, lagMatEquiv_apply]
  have hbx : ∀ x, ι (Pi.single x 1) = b x := fun x => by
    rw [hιdef, Basis.equivFun_symm_apply]
    simp [Pi.single_apply]
  have hQι : ∀ v, Q (ι v) = lagQ v := by
    intro v
    rw [hιdef, Basis.equivFun_symm_apply, Fintype.sum_sum_type, QuadraticMap.map_add Q,
      lag_map_sum_eq_zero _ _ _ (fun a _ => hbQ _) (fun a _ a' _ => hbll a a'),
      lag_map_sum_eq_zero _ _ _ (fun a _ => hbQ _) (fun a _ a' _ => hbrr a a'), zero_add, zero_add,
      lag_polar_sum_left]
    simp_rw [lag_polar_sum_right, polar_smul_left, polar_smul_right, hblr]
    simp [lagQ]
  have hΦO : ∀ g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F,
      (∀ v, lagQ (g.1 *ᵥ v) = lagQ v) → Φ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro g hg
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    obtain ⟨v, rfl⟩ := ι.surjective x
    rw [hΦapp, hQι, hQι, hg]
  have hΦs : Φ (lagRad m F (Multiplicative.ofAdd (spJ m F))) = s := by
    apply LinearEquiv.toLinearMap_injective
    refine b.ext fun x => ?_
    simp only [LinearEquiv.coe_coe]
    rw [← hbx, hΦapp]
    rcases x with a | d
    · rw [lagRadJ_mulVec_inl, hbx, hsl]
    · rw [lagRadJ_mulVec_inr, map_add, hbx, hbx, hsr]
  obtain ⟨κ, hκ0, hκ1⟩ := exists_ne_zero_ne_one_of_four_le hF4
  have : Group.IsPerfect (StatedSp m F) := by
    have := CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin F m (Or.inl (Or.inr hF4))
    exact Group.IsPerfect.ofSurjective
      (f := (CFSG.LieType.Universal.Symplectic.equivStatedSp m F).toMonoidHom)
      (CFSG.LieType.Universal.Symplectic.equivStatedSp m F).surjective
  have hPperf : ⁅lagP m F, lagP m F⁆ = lagP m F := commutator_lagP hm1 hκ0 hκ1
  set PV := (lagP m F).map Φ.toMonoidHom with hPVdef
  have hPVO : PV ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hPVdef, Subgroup.map_le_iff_le_comap]
    apply sup_le
    · rintro _ ⟨C, hC, rfl⟩
      exact hΦO _ (lagQ_lagRad hC.1)
    · rintro _ ⟨A, rfl⟩
      exact hΦO _ (lagQ_lagLevi A)
  have hPVΩ : PV ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    have h1 : ⁅PV, PV⁆ = PV := by rw [hPVdef, ← Subgroup.map_commutator, hPperf]
    rw [← h1]
    exact Subgroup.commutator_mono hPVO hPVO
  set eP : lagP m F ≃* PV.subgroupOf ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    ((lagP m F).equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
      (Subgroup.subgroupOfEquivOfLe hPVΩ).symm with heP
  refine ⟨PV.subgroupOf ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
    TauCeti.QuadraticMap.orthogonalGroup Q⁆, ?_, ?_, ?_⟩
  · have : Group.IsPerfect (lagP m F) := Subgroup.isPerfect_iff.2 hPperf
    exact commutator_top_transfer eP Group.IsPerfect.commutator_eq_top
  · intro p hp
    obtain ⟨g, hg, hgp⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hp)
    have hc := mem_centralizer_singleton_iff.1 (lagP_le_centralizer hg)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hgp, ← hΦs]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hc]
  · intro K _ _ hK ψ hψ
    have := Fintype.ofFinite F
    obtain ⟨f, -, hfF⟩ := FiniteField.card F 2
    have hFf : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hfF]
    have hf2 : 2 ≤ (f : ℕ) := by
      by_contra hf
      have : 2 ^ (f : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨hcharK, -⟩ := charP_two_and_four_le_of_card (hK.trans hFf) hf2
    obtain ⟨ℓ, hℓ⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := (f : ℕ) * (2 * m))
      (by nlinarith) (by nlinarith)
    have hℓp : ℓ.Prime := hℓ.prime
    have : Fact ℓ.Prime := ⟨hℓp⟩
    have hℓ2 : ℓ ≠ 2 := hℓ.ne_two (by positivity)
    have hdvd : ℓ ∣ Nat.card (StatedSp m F) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
      refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _
        (Finset.mem_Icc.2 ⟨hm1, le_rfl⟩ : m ∈ Finset.Icc 1 m))) _
      rw [hFf, ← pow_mul]
      exact hℓ.dvd
    have := Fintype.ofFinite (StatedSp m F)
    obtain ⟨A₀, hA₀⟩ := exists_prime_orderOf_dvd_card (G := StatedSp m F) ℓ
      (by rwa [← Nat.card_eq_fintype_card])
    have hxℓ : lagLevi m F A₀ ^ ℓ = 1 := by rw [← map_pow, ← hA₀, pow_orderOf_eq_one, map_one]
    have hx1 : lagLevi m F A₀ ≠ 1 := by
      intro h
      rw [← map_one (lagLevi m F)] at h
      have h1 := lagLevi_injective h
      rw [h1, orderOf_one] at hA₀
      exact hℓp.one_lt.ne hA₀
    have hord : ∀ j, 1 ≤ j → j < 2 * m → ¬ ℓ ∣ Nat.card K ^ j - 1 := by
      intro j hj hjm
      rw [hK, hFf, ← pow_mul]
      exact hℓ.2.2 _ (by positivity) (by nlinarith)
    have : IsSimpleGroup (StatedSp m F) := isSimpleGroup_statedSp_of_four_le hF4 hm1
    have : IsSimpleGroup (lagX m F) := (lagXEquiv m F).symm.isSimpleGroup
    have hXp : Group.IsPerfect (lagX m F) := Group.IsPerfect.range _
    have hR0 := card_le_of_lagrangian_core_of_le (K := K) (P := lagP m F) le_sup_left le_sup_right
      hm1 (by omega : 2 * m - 1 + 1 = 2 * m) (ψ.comp eP.toMonoidHom) (hψ.comp eP.injective)
      isPGroup_lagR0Grp lagX_le_normalizer hXp (commutator_lagR0Grp_lagX hm1 hκ0 hκ1)
      (fun r hr hrX => eq_one_of_commute_lagX hmo hκ0 hκ1 hr hrX) ⟨A₀, rfl⟩ hx1 hℓp hℓ2 hxℓ hord
    rw [hK] at hR0
    have hlow := card_lagR0Grp_lower (F := F) hm1
    have hq : 1 < Nat.card F := by omega
    have e1 : 2 * m * (2 * m + 1) / 2 = m * (2 * m + 1) := by
      rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [e1] at hlow
    have h3 : Nat.card F ^ (m * (2 * m + 1)) ≤ Nat.card F ^ (2 * m * (m - 1) + 1 + 2 * m) := by
      calc Nat.card F ^ (m * (2 * m + 1))
          ≤ Nat.card (lagR0Grp m F) * Nat.card F * Nat.card F ^ (2 * m) := hlow
        _ ≤ Nat.card F ^ (2 * m * (m - 1)) * Nat.card F * Nat.card F ^ (2 * m) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hR0)
        _ = Nat.card F ^ (2 * m * (m - 1) + 1 + 2 * m) := by rw [pow_add, pow_add, pow_one]
    have h4 := (Nat.pow_le_pow_iff_right hq).1 h3
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
    have e2 : t + 3 - 1 = t + 2 := by omega
    rw [e2] at h4
    nlinarith

end Main

end CFSG.SeitzReduction.SymplecticPilot
