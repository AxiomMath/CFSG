module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Inner

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Actors

variable {K : Type} [Field K]

theorem exactNormalAut_one_mul_one_E6 (ρ ρ' : K ≃+* K) (ε ε' : ℕ) :
    exactNormalAut .E6 K 1 ρ ε * exactNormalAut .E6 K 1 ρ' ε' =
      exactNormalAut .E6 K 1 (ρ * ρ') (ε + ε') := by
  rw [exactNormalAut_mul]
  congr 1
  funext j
  simp only [Pi.one_apply, map_one, mul_one]

theorem exactNormalAut_one_one_zero_E6 : exactNormalAut .E6 K 1 1 0 = 1 := by
  rw [FieldGraphFieldPointwise.exactNormalAut_one_zero_eq, entrywiseAdjointAut_one]

theorem exactNormalAut_mod_two_E6 (a : Fin Tag.E6.rank → Kˣ) (ρ : K ≃+* K) (ε : ℕ) :
    exactNormalAut .E6 K a ρ (ε % 2) = exactNormalAut .E6 K a ρ ε :=
  exactNormalAut_mod a ρ ε

theorem exactNormalAut_one_pow_E6 (ρ : K ≃+* K) (ε k : ℕ) :
    exactNormalAut .E6 K 1 ρ ε ^ k = exactNormalAut .E6 K 1 (ρ ^ k) (k * ε) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, zero_mul, exactNormalAut_one_one_zero_E6]
  | succ k ih => rw [pow_succ, ih, exactNormalAut_one_mul_one_E6, ← pow_succ, add_mul, one_mul]

theorem exactNormalAut_one_inv_E6 (ρ : K ≃+* K) (ε : ℕ) :
    (exactNormalAut .E6 K 1 ρ ε)⁻¹ = exactNormalAut .E6 K 1 ρ⁻¹ ε := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [exactNormalAut_one_mul_one_E6, mul_inv_cancel, ← exactNormalAut_mod_two_E6,
    show (ε + ε) % 2 = 0 by omega, exactNormalAut_one_one_zero_E6]

theorem exactNormalAut_eq_diag_mul_E6 (b : Fin Tag.E6.rank → Kˣ) (ρ : K ≃+* K) (ε : ℕ) :
    exactNormalAut .E6 K b ρ ε = exactNormalAut .E6 K b 1 0 * exactNormalAut .E6 K 1 ρ ε := by
  rw [exactNormalAut_diag_mul, mul_one]

theorem exactNormalAut_one_mul_entrywise_E6 {τ σ : K ≃+* K} (h : τ * σ = σ * τ) (ε : ℕ) :
    exactNormalAut .E6 K 1 τ ε * entrywiseAdjointAut .E6 σ =
      entrywiseAdjointAut .E6 σ * exactNormalAut .E6 K 1 τ ε := by
  rw [← FieldGraphFieldPointwise.exactNormalAut_one_zero_eq, exactNormalAut_one_mul_one_E6,
    exactNormalAut_one_mul_one_E6, h, add_zero, zero_add]

theorem exactNormalAut_diag_mul_entrywise_E6 {σ : K ≃+* K} {c : Fin Tag.E6.rank → Kˣ}
    (hc : ∀ i, σ (c i : K) = c i) :
    exactNormalAut .E6 K c 1 0 * entrywiseAdjointAut .E6 σ =
      entrywiseAdjointAut .E6 σ * exactNormalAut .E6 K c 1 0 := by
  rw [← FieldGraphFieldPointwise.exactNormalAut_one_zero_eq, exactNormalAut_mul,
    exactNormalAut_mul, one_mul, mul_one, exactPerm_zero]
  congr 1
  funext j
  refine Units.ext ?_
  simp only [Pi.one_apply, map_one, mul_one, one_mul, Units.coe_map]
  exact (hc j).symm

theorem exists_exactNormalAut_cartanChar_eq_conj_E6 (t : Fin Tag.E6.rank → Kˣ) :
    ∃ x : adjointGroup .E6 K, exactNormalAut .E6 K (cartanChar t) 1 0 = MulAut.conj x := by
  have hmem : rootDiagUnit .E6 (cartanChar t) ∈ adjointGroup .E6 K := by
    rw [← list_prod_torusElt_eq_rootDiagUnit]
    exact Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
      exact torusElt_mem_adjointGroup j _
  refine ⟨⟨_, hmem⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [coe_exactNormalAut, exactQ_zero, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv,
    show Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL .E6 K) = h from
      Units.ext (entrywise_id _)]
  simp only [mul_one, inv_one]

end Actors

section Cubes

variable {K : Type} [Field K]

@[expose] def cubeE6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6;
    4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

theorem cubeE6_mul_cartan :
    cubeE6 * Tag.E6.cartan = Matrix.diagonal (fun _ : Fin Tag.E6.rank => (3 : ℤ)) := by
  decide +kernel

theorem sum_cubeE6_mul_cartan (j l : Fin Tag.E6.rank) :
    ∑ i, cubeE6 j i * Tag.E6.cartan i l = if j = l then 3 else 0 := by
  have h := congrFun (congrFun cubeE6_mul_cartan j) l
  rw [Matrix.mul_apply] at h
  rw [h, Matrix.diagonal_apply]

theorem cartanChar_cube_E6 (d : Fin Tag.E6.rank → Kˣ) :
    cartanChar (τ := .E6) (fun i => ∏ j, d j ^ cubeE6 j i) = d ^ 3 := by
  funext l
  calc cartanChar (τ := .E6) (fun i => ∏ j, d j ^ cubeE6 j i) l
      = ∏ i, ∏ j, d j ^ (cubeE6 j i * Tag.E6.cartan i l) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_zpow]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← zpow_mul]
    _ = ∏ j, ∏ i, d j ^ (cubeE6 j i * Tag.E6.cartan i l) := Finset.prod_comm
    _ = ∏ j, d j ^ (if j = l then (3 : ℤ) else 0) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← sum_cubeE6_mul_cartan j l, prod_zpow_eq_zpow_sum]
    _ = (d ^ 3) l := by
        rw [Finset.prod_eq_single l
          (fun j _ hj => by rw [ite_eq_right_iff.2 (fun h => absurd h hj), zpow_zero])
          (fun h => absurd (Finset.mem_univ l) h), ite_eq_left_iff.2 (fun h => absurd rfl h),
          Pi.pow_apply]
        exact zpow_ofNat _ 3

theorem exists_fixed_mul_cube {f : ℕ} (hf : Even f) {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (y : Kˣ) : ∃ c d : Kˣ, σ (c : K) = c ∧ y = c * d ^ 3 := by
  obtain ⟨m, rfl⟩ := hf
  have h3 : 2 ^ (m + m) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  obtain ⟨s, hs⟩ : ∃ s, 2 ^ (m + m) + 1 = 3 * s + 2 := by
    refine ⟨2 ^ (m + m) / 3, ?_⟩
    have := Nat.div_add_mod (2 ^ (m + m)) 3
    generalize 2 ^ (m + m) = x at h3 this ⊢
    omega
  refine ⟨(y ^ (2 ^ (m + m) + 1)) ^ 2, (y ^ (2 * s + 1))⁻¹, ?_, ?_⟩
  · have h1 : σ ((y : K) ^ (2 ^ (m + m) + 1)) = (y : K) ^ (2 ^ (m + m) + 1) := by
      rw [pow_succ, ← hσ, map_mul, hσσ, mul_comm]
    simp only [Units.val_pow_eq_pow_val, map_pow, h1]
  · rw [inv_pow, ← pow_mul, ← pow_mul, hs,
      show (3 * s + 2) * 2 = (2 * s + 1) * 3 + 1 by ring, pow_add, pow_one,
      mul_comm (y ^ _) y, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_fixed_mul_cartanChar_E6 {f : ℕ} (hf : Even f) {σ : K ≃+* K}
    (hσσ : ∀ c, σ (σ c) = c) (hσ : ∀ c, σ c = c ^ 2 ^ f) (b : Fin Tag.E6.rank → Kˣ) :
    ∃ c t : Fin Tag.E6.rank → Kˣ, (∀ i, σ (c i : K) = c i) ∧ b = c * cartanChar t := by
  choose c d hc hcd using fun i => exists_fixed_mul_cube hf hσσ hσ (b i)
  refine ⟨c, fun i => ∏ j, d j ^ cubeE6 j i, hc, ?_⟩
  rw [cartanChar_cube_E6]
  funext i
  rw [Pi.mul_apply, Pi.pow_apply]
  exact hcd i

end Cubes

section Conj

variable {K : Type} [Field K] [Finite K]

theorem exists_conj_eq_conj_entrywise_E6 {f : ℕ} (hf : Even f) (hK : Nat.card K = 2 ^ (2 * f))
    {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (h : MulAut (adjointGroup .E6 K)) :
    ∃ w : adjointGroup .E6 K, h * entrywiseAdjointAut .E6 σ * h⁻¹ =
      MulAut.conj w * entrywiseAdjointAut .E6 σ * (MulAut.conj w)⁻¹ := by
  obtain ⟨-, hcyc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK
  have hcomm : ∀ a b : RingAut K, a * b = b * a := (IsCyclic.commGroup).mul_comm
  obtain ⟨g, b, τ, ε, rfl⟩ := exists_conj_mul_exactNormalAut (τ := .E6) (Or.inl rfl) h
  obtain ⟨c, t, hc, rfl⟩ := exists_fixed_mul_cartanChar_E6 hf hσσ hσ b
  obtain ⟨x, hx⟩ := exists_exactNormalAut_cartanChar_eq_conj_E6 t
  set ν := exactNormalAut .E6 K c 1 0 * exactNormalAut .E6 K 1 τ ε with hν
  have hN : exactNormalAut .E6 K (c * cartanChar t) τ ε = MulAut.conj x * ν := by
    rw [exactNormalAut_eq_diag_mul_E6, mul_comm c, ← exactNormalAut_diag_mul (cartanChar t) c 1 0,
      hx, hν, mul_assoc]
  have hνσ : ν * entrywiseAdjointAut .E6 σ = entrywiseAdjointAut .E6 σ * ν := by
    rw [hν, mul_assoc, exactNormalAut_one_mul_entrywise_E6 (hcomm τ σ), ← mul_assoc,
      exactNormalAut_diag_mul_entrywise_E6 hc, mul_assoc]
  refine ⟨g * x, ?_⟩
  rw [hN, map_mul]
  calc MulAut.conj g * (MulAut.conj x * ν) * entrywiseAdjointAut .E6 σ *
        (MulAut.conj g * (MulAut.conj x * ν))⁻¹
      = MulAut.conj g * MulAut.conj x * (ν * entrywiseAdjointAut .E6 σ * ν⁻¹) *
          (MulAut.conj g * MulAut.conj x)⁻¹ := by group
    _ = MulAut.conj g * MulAut.conj x * entrywiseAdjointAut .E6 σ *
          (MulAut.conj g * MulAut.conj x)⁻¹ := by rw [hνσ, mul_inv_cancel_right]

end Conj

section Std

theorem exists_fieldGraphCoordinate_E6 (K : Type) [Field K] [Finite K] :
    ∃ Θ : MulAut (adjointGroup .E6 K) →* (K ≃+* K) × Multiplicative (ZMod 2),
      ∀ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ) (ρ : K ≃+* K) (ε : ℕ),
        Θ (MulAut.conj g * exactNormalAut .E6 K a ρ ε) =
          (ρ, Multiplicative.ofAdd (ε : ZMod 2)) := by
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  refine ⟨Θ, fun g a ρ ε => ?_⟩
  have h2 : ε % 2 < exactE .E6 := Nat.mod_lt _ (by decide)
  have h := hΘ (MulAut.conj g * exactNormalAut .E6 K a ρ (ε % 2)) g a ρ ⟨ε % 2, h2⟩ fun h => by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  rw [exactNormalAut_mod_two_E6] at h
  refine h.trans ?_
  change ((ρ, Multiplicative.ofAdd (((ε % 2 : ℕ) : ZMod 2))) :
      (K ≃+* K) × Multiplicative (ZMod 2)) = (ρ, Multiplicative.ofAdd (ε : ZMod 2))
  rw [ZMod.natCast_mod]

variable {K : Type} [Field K]

@[expose] noncomputable def innerStdE6 (K : Type) [Field K] :
    Subgroup (MulAut (adjointGroup .E6 K)) where
  carrier := {α | ∃ (x : adjointGroup .E6 K) (ρ : K ≃+* K) (ε : ℕ),
    α = MulAut.conj x * exactNormalAut .E6 K 1 ρ ε}
  one_mem' := ⟨1, 1, 0, by rw [map_one, one_mul, exactNormalAut_one_one_zero_E6]⟩
  mul_mem' := by
    rintro _ _ ⟨x, ρ, ε, rfl⟩ ⟨y, ρ', ε', rfl⟩
    refine ⟨x * exactNormalAut .E6 K 1 ρ ε y, ρ * ρ', ε + ε', ?_⟩
    rw [map_mul, ← exactNormalAut_one_mul_one_E6]
    calc MulAut.conj x * exactNormalAut .E6 K 1 ρ ε *
          (MulAut.conj y * exactNormalAut .E6 K 1 ρ' ε')
        = MulAut.conj x * (exactNormalAut .E6 K 1 ρ ε * MulAut.conj y) *
            exactNormalAut .E6 K 1 ρ' ε' := by group
      _ = _ := by rw [CFSG.LieType.Chevalley.mulAut_mul_conj]; group
  inv_mem' := by
    rintro _ ⟨x, ρ, ε, rfl⟩
    refine ⟨exactNormalAut .E6 K 1 ρ⁻¹ ε x⁻¹, ρ⁻¹, ε, ?_⟩
    rw [mul_inv_rev, exactNormalAut_one_inv_E6, ← map_inv MulAut.conj,
      CFSG.LieType.Chevalley.mulAut_mul_conj]

theorem range_conj_le_innerStdE6 :
    (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ innerStdE6 K := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x, 1, 0, by rw [exactNormalAut_one_one_zero_E6, mul_one]⟩

theorem exactNormalAut_one_mem_innerStdE6 (ρ : K ≃+* K) (ε : ℕ) :
    exactNormalAut .E6 K 1 ρ ε ∈ innerStdE6 K :=
  ⟨1, ρ, ε, by rw [map_one, one_mul]⟩

@[expose] noncomputable def diagAutHomE6 (K : Type) [Field K] :
    (Fin Tag.E6.rank → Kˣ) →* MulAut (adjointGroup .E6 K) where
  toFun a := exactNormalAut .E6 K a 1 0
  map_one' := exactNormalAut_one_one_zero_E6
  map_mul' a b := (exactNormalAut_diag_mul a b 1 0).symm

variable [Finite K]

theorem finite_mulAut_E6 : Finite (MulAut (adjointGroup .E6 K)) :=
  Finite.of_injective (fun f : MulAut (adjointGroup .E6 K) => (f : adjointGroup .E6 K → _))
    DFunLike.coe_injective

theorem two_not_dvd_index_innerStdE6 {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    ¬ 2 ∣ (innerStdE6 K).index := by
  have := finite_mulAut_E6 (K := K)
  obtain ⟨Θ, hΘ⟩ := exists_fieldGraphCoordinate_E6 K
  set 𝒟 := Θ.ker with h𝒟def
  set I := (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range with hI
  set D := (diagAutHomE6 K).range with hD
  have hIn : I.Normal := by
    constructor
    rintro _ ⟨x, rfl⟩ α
    exact ⟨α x, MulEquiv.ext fun y => by
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]⟩
  have hsup : innerStdE6 K ⊔ 𝒟 = ⊤ := by
    refine eq_top_iff.2 fun α _ => ?_
    obtain ⟨g, a, ρ, ε, rfl⟩ := exists_conj_mul_exactNormalAut (τ := .E6) (Or.inl rfl) α
    rw [exactNormalAut_eq_diag_mul_E6, ← mul_assoc, sup_comm]
    refine mul_mem_sup ?_ (exactNormalAut_one_mem_innerStdE6 ρ ε)
    rw [h𝒟def, MonoidHom.mem_ker, hΘ]
    simp
  have hidx : (innerStdE6 K).index = (innerStdE6 K).relIndex 𝒟 := by
    have h1 := Subgroup.relIndex_sup_right (innerStdE6 K) 𝒟
    rw [hsup, Subgroup.relIndex_top_right] at h1
    have h2 := Subgroup.index_inf (H := innerStdE6 K) (K := 𝒟)
    have h3 := Subgroup.index_inf (H := 𝒟) (K := innerStdE6 K)
    rw [inf_comm, h3, ← h1] at h2
    have hD0 : 𝒟.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [mul_comm 𝒟.index] at h2
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hD0) h2
  have hI𝒟 : I ≤ 𝒟 := by
    rintro _ ⟨x, rfl⟩
    rw [h𝒟def, MonoidHom.mem_ker]
    have h := hΘ x 1 1 0
    rw [exactNormalAut_one_one_zero_E6, mul_one] at h
    rw [h]
    simp
  have h𝒟 : 𝒟 ≤ I ⊔ D := by
    intro α hα
    obtain ⟨g, a, ρ, ε, rfl⟩ := exists_conj_mul_exactNormalAut (τ := .E6) (Or.inl rfl) α
    rw [h𝒟def, MonoidHom.mem_ker, hΘ] at hα
    have hρ : ρ = 1 := congrArg Prod.fst hα
    have hε : (((ε : ℕ) : ZMod 2)) = 0 := congrArg (fun x => Multiplicative.toAdd x.2) hα
    have hε2 : (ε : ℕ) % 2 = 0 := by
      have := (ZMod.natCast_eq_zero_iff _ _).1 hε
      omega
    rw [hρ, ← exactNormalAut_mod_two_E6, hε2]
    exact mul_mem_sup ⟨g, rfl⟩ ⟨a, rfl⟩
  have h1 : I.relIndex 𝒟 ∣ I.relIndex (I ⊔ D) :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex I 𝒟 (I ⊔ D) hI𝒟 h𝒟)
  have h2 : I.relIndex (I ⊔ D) = I.relIndex D := Subgroup.relIndex_sup_left D I
  have h3 : I.relIndex D ∣ Nat.card D := Subgroup.relIndex_dvd_card I D
  have h4 : Nat.card D ∣ Nat.card (Fin Tag.E6.rank → Kˣ) := Subgroup.card_range_dvd _
  have h5 : Odd (Nat.card (Fin Tag.E6.rank → Kˣ)) := by
    rw [Nat.card_fun, Nat.card_units, hK]
    refine Odd.pow ?_
    have hn : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at this
      exact lt_irrefl 1 this
    obtain ⟨r, hr⟩ : Even (2 ^ n) := (Nat.even_pow' hn).2 even_two
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact ⟨r - 1, by omega⟩
  have h6 : (innerStdE6 K).relIndex 𝒟 ∣ I.relIndex 𝒟 :=
    Subgroup.relIndex_dvd_of_le_left 𝒟 range_conj_le_innerStdE6
  intro h2dvd
  rw [hidx] at h2dvd
  rw [h2] at h1
  exact (Nat.not_even_iff_odd.2 h5)
    (even_iff_two_dvd.2 (h2dvd.trans (h6.trans (h1.trans (h3.trans h4)))))

theorem exists_conj_mem_innerStdE6 {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {W : Subgroup (MulAut (adjointGroup .E6 K))} (hW : IsPGroup 2 W) :
    ∃ g : MulAut (adjointGroup .E6 K), ∀ w ∈ W, g⁻¹ * w * g ∈ innerStdE6 K := by
  have := finite_mulAut_E6 (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (innerStdE6 K)) := inferInstance
  set P := (S₀ : Subgroup (innerStdE6 K)).map (innerStdE6 K).subtype with hP
  have hPp : IsPGroup 2 P := S₀.isPGroup'.map _
  have hPidx : ¬ 2 ∣ P.index := by
    rw [hP, Subgroup.index_map_subtype]
    exact (Fact.out : (2 : ℕ).Prime).not_dvd_mul S₀.not_dvd_index
      (two_not_dvd_index_innerStdE6 hK)
  set S := hPp.toSylow hPidx with hS
  obtain ⟨S', hS'⟩ := hW.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut (adjointGroup .E6 K)) S S'
  refine ⟨g, fun w hw => ?_⟩
  have hw' : w ∈ ((g • S : Sylow 2 _) : Subgroup (MulAut (adjointGroup .E6 K))) := hg ▸ hS' hw
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hw'
  obtain ⟨p, hpS, rfl⟩ := hw'
  have hpP : p ∈ P := hpS
  obtain ⟨q, -, rfl⟩ := hpP
  have hconj : MulAut.conj g • ((innerStdE6 K).subtype q) =
      g * ((innerStdE6 K).subtype q) * g⁻¹ := rfl
  rw [hconj, show g⁻¹ * (g * ((innerStdE6 K).subtype q) * g⁻¹) * g = (innerStdE6 K).subtype q
    by group]
  exact q.2

theorem exists_exact_lift_E6 {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {Θ : MulAut (adjointGroup .E6 K) →* (K ≃+* K) × Multiplicative (ZMod 2)}
    (hΘ : ∀ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ) (ρ : K ≃+* K) (ε : ℕ),
      Θ (MulAut.conj g * exactNormalAut .E6 K a ρ ε) = (ρ, Multiplicative.ofAdd (ε : ZMod 2)))
    {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) {𝒜 : Subgroup (MulAut (adjointGroup .E6 K))}
    (hI : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ 𝒜)
    {w : MulAut (adjointGroup .E6 K)} (hw𝒜 : w ∈ 𝒜) (hw : IsPGroup 2 (zpowers w)) {c : ℕ}
    (hc : 2 ≤ c) (hwo : orderOf (Θ w).1 = 2 ^ c) :
    ∃ ξ ∈ 𝒜, orderOf ξ = 2 ^ c ∧ (Θ ξ).1 = (Θ w).1 ∧
      ∃ h : MulAut (adjointGroup .E6 K), ξ ^ 2 ^ (c - 1) = h * entrywiseAdjointAut .E6 σ * h⁻¹ := by
  obtain ⟨-, hcyc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)
  have hcomm : ∀ a b : RingAut K, a * b = b * a := (IsCyclic.commGroup).mul_comm
  set χ : MulAut (adjointGroup .E6 K) →* (K ≃+* K) := (MonoidHom.fst _ _).comp Θ with hχdef
  have hχ : ∀ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ) (ρ : K ≃+* K) (ε : ℕ),
      χ (MulAut.conj g * exactNormalAut .E6 K a ρ ε) = ρ := fun g a ρ ε => by
    rw [hχdef, MonoidHom.comp_apply, hΘ]
    rfl
  have hχw : χ w = (Θ w).1 := rfl
  have hχconj : ∀ α β : MulAut (adjointGroup .E6 K), χ (β * α * β⁻¹) = χ α := fun α β => by
    rw [map_mul, map_mul, map_inv, hcomm (χ β), mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨h, hh⟩ := exists_conj_mem_innerStdE6 hK hw
  obtain ⟨s, ρ, ε, hs⟩ := hh w (mem_zpowers w)
  have hρ : ρ = (Θ w).1 := by
    have h1 := hχ s 1 ρ ε
    rw [← hs, show h⁻¹ * w * h = h⁻¹ * w * h⁻¹⁻¹ by rw [inv_inv], hχconj] at h1
    rw [← h1, hχw]
  set γ := exactNormalAut .E6 K 1 ρ ε with hγ
  set ξ := h * γ * h⁻¹ with hξ
  have hξw : ξ = MulAut.conj (h s)⁻¹ * w := by
    have hw' : w = h * MulAut.conj s * h⁻¹ * ξ := by
      rw [hξ]
      calc w = h * (h⁻¹ * w * h) * h⁻¹ := by group
        _ = h * MulAut.conj s * h⁻¹ * (h * γ * h⁻¹) := by rw [hs, hγ]; group
    rw [hw', CFSG.LieType.Chevalley.mulAut_mul_conj, mul_inv_cancel_right, map_inv,
      inv_mul_cancel_left]
  have hξA : ξ ∈ 𝒜 := by
    rw [hξw]
    exact mul_mem (hI ⟨_, rfl⟩) hw𝒜
  have hρo : orderOf ρ = 2 ^ c := by rw [hρ, hwo]
  have hγo : orderOf γ = 2 ^ c := by
    have h1 : γ ^ 2 ^ c = 1 := by
      rw [hγ, exactNormalAut_one_pow_E6, ← hρo, pow_orderOf_eq_one, hρo,
        ← exactNormalAut_mod_two_E6,
        show 2 ^ c * ε % 2 = 0 by
          rw [Nat.mul_mod, Nat.pow_mod]
          simp [show c ≠ 0 by omega],
        exactNormalAut_one_one_zero_E6]
    have h2 : 2 ^ c ∣ orderOf γ := by
      have := orderOf_map_dvd χ γ
      rwa [hγ, show exactNormalAut .E6 K 1 ρ ε = MulAut.conj 1 * exactNormalAut .E6 K 1 ρ ε by
        rw [map_one, one_mul], hχ, hρo] at this
    exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h1) h2
  have hξo : orderOf ξ = 2 ^ c := by
    rw [hξ, show h * γ * h⁻¹ = MulAut.conj h γ from rfl, MulEquiv.orderOf_eq, hγo]
  have hξχ : (Θ ξ).1 = (Θ w).1 := by
    change χ ξ = _
    rw [hξ, hχconj, hγ, show exactNormalAut .E6 K 1 ρ ε = MulAut.conj 1 * exactNormalAut .E6 K 1 ρ ε
      by rw [map_one, one_mul], hχ, hρ]
  have hρpow : ρ ^ 2 ^ (c - 1) = σ := by
    have h2c : 2 ^ c = 2 ^ (c - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    refine EPilot.eq_of_sq_eq_one_of_ne_one_of_isCyclic ?_ hσ2 ?_ hσ1
    · rw [← pow_mul, ← h2c, ← hρo, pow_orderOf_eq_one]
    · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hρo]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine ⟨ξ, hξA, hξo, hξχ, h, ?_⟩
  rw [hξ, conj_pow, hγ, exactNormalAut_one_pow_E6, hρpow, ← exactNormalAut_mod_two_E6,
    show 2 ^ (c - 1) * ε % 2 = 0 by
      rw [Nat.mul_mod, Nat.pow_mod]
      simp [show c - 1 ≠ 0 by omega],
    FieldGraphFieldPointwise.exactNormalAut_one_zero_eq]

end Std

end CFSG.SeitzReduction.E6Pilot
