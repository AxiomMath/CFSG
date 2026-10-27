module

public import CFSG.ClassicalGroups.UnitaryFlag.NaturalModulePerp
public import CFSG.ClassicalGroups.UnitaryFlag.SU3OddOrderEigen
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreInvol
public import CFSG.ClassicalGroups.UnitaryFlag.PointSylow

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Quasithin
open CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts
open scoped Pointwise

variable {m : ℕ} {K : Type} [Field K]

theorem involution_mem_isotropicTransvectionGroup (h : UnitaryFieldData 2 m K)
    {t : unitarySU 2 m K 3} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    LinearMap.range (subOne t) ∈ isotropicLines h 3 ∧
      t ∈ isotropicTransvectionGroup h 3 (LinearMap.range (subOne t)) ∧
      LinearMap.ker (subOne t) = hermPerp h (LinearMap.range (subOne t)) := by
  have : Finite (unitarySU 2 m K 3) := model3U4_finite_group h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ht ht1, pow_one])
  obtain ⟨R, hR⟩ := hT.exists_le_sylow
  obtain ⟨L, hL, hΩ⟩ := omegaOneOf_sylow_eq_isotropicTransvectionGroup (h := h) R
  have htΩ : t ∈ omegaOneOf (R : Subgroup (unitarySU 2 m K 3)) :=
    Subgroup.subset_closure ⟨hR (Subgroup.mem_zpowers t), ht⟩
  rw [hΩ] at htΩ
  rw [range_subOne_of_mem_isotropicTransvectionGroup hL htΩ ht1]
  exact ⟨hL, htΩ, ker_subOne_of_mem_isotropicTransvectionGroup hL htΩ ht1⟩

theorem isPGroup_isotropicTransvectionGroup (h : UnitaryFieldData 2 m K)
    {L : Submodule K (Fin 3 → K)} (hL : L ∈ isotropicLines h 3) :
    IsPGroup 2 (isotropicTransvectionGroup h 3 L) := by
  obtain ⟨R, hR⟩ := exists_sylow_omegaOneOf_eq_isotropicTransvectionGroup hL
  rw [← hR]
  exact R.isPGroup'.to_le ((Subgroup.closure_le _).mpr fun x hx => hx.1)

theorem range_subOne_conj (h : UnitaryFieldData 2 m K) (g t : unitarySU 2 m K 3) :
    LinearMap.range (subOne (g * t * g⁻¹)) = g • LinearMap.range (subOne t) := by
  ext x
  rw [LinearMap.mem_range]
  refine Iff.trans ?_ (Submodule.mem_smul_pointwise_iff_exists x g _).symm
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨subOne t (g⁻¹ • y), LinearMap.mem_range_self _ _, ?_⟩
    rw [subOne_apply h, subOne_apply h, smul_sub, smul_inv_smul, mul_smul, mul_smul]
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨g • z, ?_⟩
    rw [subOne_apply h, subOne_apply h, smul_sub, mul_smul, mul_smul, inv_smul_smul]

theorem range_subOne_eq_of_commute (h : UnitaryFieldData 2 m K) {t z : unitarySU 2 m K 3}
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) (hz : z ^ 2 = 1) (hz1 : z ≠ 1) (htz : t * z = z * t) :
    LinearMap.range (subOne t) = LinearMap.range (subOne z) := by
  have : Finite (unitarySU 2 m K 3) := model3U4_finite_group h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : ∀ y : unitarySU 2 m K 3, y ^ 2 = 1 → y ≠ 1 → IsPGroup 2 (Subgroup.zpowers y) :=
    fun y hy hy1 =>
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hy hy1, pow_one])
  have hzN : z ∈ Subgroup.normalizer
      ((Subgroup.zpowers t : Subgroup (unitarySU 2 m K 3)) : Set (unitarySU 2 m K 3)) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨k, rfl⟩
    exact (Commute.zpow_left htz k).eq
  have hE : IsPGroup 2 ↥(Subgroup.zpowers t ⊔ Subgroup.zpowers z : Subgroup (unitarySU 2 m K 3)) :=
    IsPGroup.to_sup_of_normal_left' (hT2 t ht ht1) (hT2 z hz hz1) (Subgroup.zpowers_le.mpr hzN)
  obtain ⟨R, hR⟩ := hE.exists_le_sylow
  obtain ⟨L, hL, hΩ⟩ := omegaOneOf_sylow_eq_isotropicTransvectionGroup (h := h) R
  have hmem : ∀ y, y ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers z → y ^ 2 = 1 → y ≠ 1 →
      LinearMap.range (subOne y) = L := by
    intro y hy hy2 hy1
    have hyΩ : y ∈ omegaOneOf (R : Subgroup (unitarySU 2 m K 3)) :=
      Subgroup.subset_closure ⟨hR hy, hy2⟩
    rw [hΩ] at hyΩ
    exact range_subOne_of_mem_isotropicTransvectionGroup hL hyΩ hy1
  rw [hmem t (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)) ht ht1,
    hmem z (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)) hz hz1]

theorem odd_orderOf_mul_of_range_subOne_ne (h : UnitaryFieldData 2 m K)
    {t u : unitarySU 2 m K 3} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hne : LinearMap.range (subOne t) ≠ LinearMap.range (subOne u)) :
    Odd (orderOf (t * u)) := by
  have : Finite (unitarySU 2 m K 3) := model3U4_finite_group h
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hpos : 0 < orderOf (t * u) := orderOf_pos (t * u)
  have hk0 : 0 < k := by omega
  have hw2 : ((t * u) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, show k * 2 = k + k by ring, ← hk, pow_orderOf_eq_one]
  have hw1 : (t * u) ^ k ≠ 1 := by
    intro h1
    have := orderOf_le_of_pow_eq_one hk0 h1
    omega
  have ht' : t * t = 1 := by rw [← pow_two]; exact ht
  have hu' : u * u = 1 := by rw [← pow_two]; exact hu
  have hwinv : ((t * u) ^ k)⁻¹ = (t * u) ^ k :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hw2)
  have hut : (u * t) ^ k = (t * u) ^ k := by
    rw [show u * t = (t * u)⁻¹ by
      rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right ht', inv_eq_of_mul_eq_one_right hu'],
      inv_pow, hwinv]
  have hst : SemiconjBy t (t * u) (u * t) := by
    change t * (t * u) = u * t * t
    rw [← mul_assoc, ht', one_mul, mul_assoc, ht', mul_one]
  have hsu : SemiconjBy u (t * u) (u * t) := (mul_assoc u t u).symm
  have hct : t * (t * u) ^ k = (t * u) ^ k * t := by
    have := (hst.pow_right k).eq
    rwa [hut] at this
  have hcu : u * (t * u) ^ k = (t * u) ^ k * u := by
    have := (hsu.pow_right k).eq
    rwa [hut] at this
  exact hne ((range_subOne_eq_of_commute h ht ht1 hw2 hw1 hct).trans
    (range_subOne_eq_of_commute h hu hu1 hw2 hw1 hcu).symm)

theorem exists_conj_of_range_subOne_ne (h : UnitaryFieldData 2 m K)
    {Y : Subgroup (unitarySU 2 m K 3)} {t₁ u₁ t : unitarySU 2 m K 3}
    (ht₁Y : t₁ ∈ Y) (hu₁Y : u₁ ∈ Y) (htY : t ∈ Y)
    (ht₁ : t₁ ^ 2 = 1) (ht₁1 : t₁ ≠ 1) (hu₁ : u₁ ^ 2 = 1) (hu₁1 : u₁ ≠ 1)
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hne : LinearMap.range (subOne t₁) ≠ LinearMap.range (subOne u₁)) :
    ∃ y ∈ Y, y * t₁ * y⁻¹ = t := by
  have key : ∀ x x' : unitarySU 2 m K 3, x ∈ Y → x' ∈ Y → x ^ 2 = 1 → x ≠ 1 → x' ^ 2 = 1 →
      x' ≠ 1 → LinearMap.range (subOne x) ≠ LinearMap.range (subOne x') →
      ∃ y ∈ Y, y * x * y⁻¹ = x' := by
    intro x x' hx hx' hx2 hx1 hx'2 hx'1 hxx'
    obtain ⟨k, hk⟩ := CFSG.ClassicalInvolution.Asc77.T3Core.exists_conj_of_mul_mem_odd
      (by rw [← pow_two]; exact hx2) (by rw [← pow_two]; exact hx'2)
      (odd_orderOf_mul_of_range_subOne_ne h hx2 hx1 hx'2 hx'1 hxx')
    exact ⟨(x * x') ^ k, Y.pow_mem (Y.mul_mem hx hx') k, hk⟩
  by_cases hc : LinearMap.range (subOne t₁) = LinearMap.range (subOne t)
  · have h1 : LinearMap.range (subOne u₁) ≠ LinearMap.range (subOne t) :=
      fun he => hne (hc.trans he.symm)
    obtain ⟨y₁, hy₁, e₁⟩ := key t₁ u₁ ht₁Y hu₁Y ht₁ ht₁1 hu₁ hu₁1 hne
    obtain ⟨y₂, hy₂, e₂⟩ := key u₁ t hu₁Y htY hu₁ hu₁1 ht ht1 h1
    refine ⟨y₂ * y₁, Y.mul_mem hy₂ hy₁, ?_⟩
    rw [← e₂, ← e₁]
    group
  · exact key t₁ t ht₁Y htY ht₁ ht₁1 ht ht1 hc

theorem hermPerp_eq_span_pair (h : UnitaryFieldData 2 m K) {L : Submodule K (Fin 3 → K)}
    (hL : L ∈ isotropicLines h 3) {e z : Fin 3 → K} (he : L = K ∙ e) (hz : z ∈ hermPerp h L)
    (hzL : z ∉ L) : hermPerp h L = Submodule.span K {e, z} := by
  have he0 : e ≠ 0 := by
    intro he0
    have h1 := (mem_isotropicLines.mp hL).1
    rw [he, he0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot] at h1
    exact zero_ne_one h1
  have hind : LinearIndependent K ![e, z] := by
    rw [LinearIndependent.pair_iff' he0]
    intro c hc
    apply hzL
    rw [he, ← hc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
  have hfin : Module.finrank K (Submodule.span K {e, z}) = 2 := by
    have := finrank_span_eq_card hind
    rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
  have hle : Submodule.span K {e, z} ≤ hermPerp h L := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact le_hermPerp_self hL (he ▸ Submodule.mem_span_singleton_self x)
    · exact hz
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, finrank_hermPerp hL])).symm

theorem stdHermForm_self_ne_zero_of_mem_hermPerp (h : UnitaryFieldData 2 m K)
    {L : Submodule K (Fin 3 → K)} (hL : L ∈ isotropicLines h 3) {z : Fin 3 → K}
    (hz : z ∈ hermPerp h L) (hzL : z ∉ L) : stdHermForm h 3 z z ≠ 0 := by
  have : Finite K := h.finite
  intro hzz
  obtain ⟨e, -, hee, hLe⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_eq_span_of_mem_isotropicLines hL
  have hez : stdHermForm h 3 e z = 0 :=
    (mem_hermPerp.mp hz) e (hLe ▸ Submodule.mem_span_singleton_self e)
  have hze : stdHermForm h 3 z e = 0 := by
    rw [← (stdHermForm_isSymm h 3).eq e z, hez, map_zero]
  have hspan := hermPerp_eq_span_pair h hL hLe hz hzL
  have hiso : ∀ y ∈ hermPerp h L, ∀ w ∈ hermPerp h L, stdHermForm h 3 y w = 0 := by
    rw [hspan]
    intro y hy w hw
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
    obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hw
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul,
      hee, hez, hze, hzz, smul_zero, add_zero]
  have hle := finrank_le_one_of_stdHermForm_eq_zero h hiso
  rw [finrank_hermPerp hL] at hle
  omega

theorem exists_orthogonal_completion (h : UnitaryFieldData 2 m K) {v w : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (hw : stdHermForm h 3 w w ≠ 0)
    (hvw : stdHermForm h 3 v w = 0) :
    ∃ u : Fin 3 → K, stdHermForm h 3 u u ≠ 0 ∧ stdHermForm h 3 v u = 0 ∧
      stdHermForm h 3 w u = 0 ∧ ∀ x : Fin 3 → K,
        x = (stdHermForm h 3 u x / stdHermForm h 3 u u) • u +
          (stdHermForm h 3 w x / stdHermForm h 3 w w) • w +
          (stdHermForm h 3 v x / stdHermForm h 3 v v) • v := by
  have hsymm : ∀ x y : Fin 3 → K, stdHermForm h 3 x y = 0 → stdHermForm h 3 y x = 0 :=
    fun x y hxy => by rw [← (stdHermForm_isSymm h 3).eq x y, hxy, map_zero]
  let f : (Fin 3 → K) →ₗ[K] K × K := (stdHermForm h 3 v).prod (stdHermForm h 3 w)
  have hker : 1 ≤ Module.finrank K (LinearMap.ker f) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 := Submodule.finrank_le (LinearMap.range f)
    rw [Module.finrank_prod, Module.finrank_self] at h2
    rw [Module.finrank_fin_fun] at h1
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := LinearMap.ker f) (by
    intro hbot
    rw [hbot, finrank_bot] at hker
    omega)
  have hfu : stdHermForm h 3 v u = 0 ∧ stdHermForm h 3 w u = 0 := by
    have h0 := LinearMap.mem_ker.mp hu
    rw [LinearMap.prod_apply, Prod.mk_eq_zero] at h0
    exact h0
  obtain ⟨hvu, hwu⟩ := hfu
  have hind : LinearIndependent K ![u, w, v] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have e2 : g 2 = 0 := by
      have h0 := congrArg (stdHermForm h 3 v) hg
      simp only [map_add, map_smul, hvu, hvw, zero_add, smul_eq_mul, map_zero,
        mul_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_right hv
    have e1 : g 1 = 0 := by
      have h0 := congrArg (stdHermForm h 3 w) hg
      simp only [map_add, map_smul, hwu, hsymm v w hvw, zero_add, add_zero,
        smul_eq_mul, map_zero, mul_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_right hw
    have e0 : g 0 = 0 := by
      rw [e1, e2, zero_smul, zero_smul, add_zero, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right hu0
    intro i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
  have hspan : Submodule.span K (Set.range ![u, w, v]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hind, Fintype.card_fin, Module.finrank_fin_fun]
  have hzero : ∀ y : Fin 3 → K, stdHermForm h 3 y u = 0 → stdHermForm h 3 y w = 0 →
      stdHermForm h 3 y v = 0 → y = 0 := by
    intro y h0 h1 h2
    have hext : stdHermForm h 3 y = 0 := LinearMap.ext_on_range hspan fun i => by
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
    exact stdHermForm_separatingLeft h 3 y fun z => by rw [hext, LinearMap.zero_apply]
  have huu : stdHermForm h 3 u u ≠ 0 := fun huu =>
    hu0 (hzero u huu (hsymm w u hwu) (hsymm v u hvu))
  refine ⟨u, huu, hvu, hwu, fun x => ?_⟩
  set y := x - ((stdHermForm h 3 u x / stdHermForm h 3 u u) • u +
    (stdHermForm h 3 w x / stdHermForm h 3 w w) • w +
    (stdHermForm h 3 v x / stdHermForm h 3 v v) • v) with hy
  have hyu : stdHermForm h 3 u y = 0 := by
    simp only [hy, map_sub, map_add, map_smul, smul_eq_mul, hsymm w u hwu, hsymm v u hvu,
      mul_zero, add_zero, div_mul_cancel₀ _ huu, sub_self]
  have hyw : stdHermForm h 3 w y = 0 := by
    simp only [hy, map_sub, map_add, map_smul, smul_eq_mul, hwu, hsymm v w hvw, mul_zero,
      add_zero, zero_add, div_mul_cancel₀ _ hw, sub_self]
  have hyv : stdHermForm h 3 v y = 0 := by
    simp only [hy, map_sub, map_add, map_smul, smul_eq_mul, hvu, hvw, mul_zero, zero_add,
      div_mul_cancel₀ _ hv, sub_self]
  have hy0 := hzero y (hsymm u y hyu) (hsymm w y hyw) (hsymm v y hyv)
  rw [hy, sub_eq_zero] at hy0
  exact hy0

theorem exists_orthogonal_completion_of_isotropic (h : UnitaryFieldData 2 m K)
    {v w : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0)
    (hww : stdHermForm h 3 w w = 0) (hvw : stdHermForm h 3 v w ≠ 0) :
    ∃ (β : K) (w₀ u₀ : Fin 3 → K), β ≠ 0 ∧
      stdHermForm h 3 v w = β * stdHermForm h 3 v v ∧ w = w₀ + β • v ∧
      stdHermForm h 3 v w₀ = 0 ∧ stdHermForm h 3 w₀ w₀ ≠ 0 ∧
      stdHermForm h 3 u₀ u₀ ≠ 0 ∧ stdHermForm h 3 v u₀ = 0 ∧
      stdHermForm h 3 w₀ u₀ = 0 ∧ stdHermForm h 3 w u₀ = 0 ∧
      ∀ x : Fin 3 → K, x = (stdHermForm h 3 u₀ x / stdHermForm h 3 u₀ u₀) • u₀ +
        (stdHermForm h 3 w₀ x / stdHermForm h 3 w₀ w₀) • w₀ +
        (stdHermForm h 3 v x / stdHermForm h 3 v v) • v := by
  set β : K := stdHermForm h 3 v w / stdHermForm h 3 v v with hβ
  have hβ0 : β ≠ 0 := div_ne_zero hvw hv
  set w₀ : Fin 3 → K := w - β • v with hw₀def
  have hw_def : w = w₀ + β • v := by
    rw [hw₀def]
    exact (sub_add_cancel w (β • v)).symm
  have hβw : stdHermForm h 3 v w = β * stdHermForm h 3 v v := by
    rw [hβ, div_mul_cancel₀ _ hv]
  have hvw₀ : stdHermForm h 3 v w₀ = 0 := by
    rw [hw₀def, map_sub, map_smul, smul_eq_mul, hβw, sub_self]
  have hw₀v : stdHermForm h 3 w₀ v = 0 := by
    rw [← (stdHermForm_isSymm h 3).eq v w₀, hvw₀, map_zero]
  have hbarβ0 : h.bar β ≠ 0 := fun h0 => hβ0 (h.bar_eq_zero_iff.mp h0)
  have hw₀w₀ : stdHermForm h 3 w₀ w₀ ≠ 0 := by
    intro h0
    have hww' : stdHermForm h 3 w w = h.bar β * β * stdHermForm h 3 v v := by
      rw [hw_def]
      simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul,
        smul_eq_mul, hvw₀, hw₀v, h0]
      ring
    rw [hww] at hww'
    exact (mul_ne_zero (mul_ne_zero hbarβ0 hβ0) hv) hww'.symm
  obtain ⟨u₀, hu₀, hvu₀, hw₀u₀, hexp⟩ :=
    exists_orthogonal_completion h hv hw₀w₀ hvw₀
  have hwu₀ : stdHermForm h 3 w u₀ = 0 := by
    rw [hw_def, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, hw₀u₀, hvu₀,
      smul_eq_mul, mul_zero, add_zero]
  exact ⟨β, w₀, u₀, hβ0, hβw, hw_def, hvw₀, hw₀w₀, hu₀, hvu₀, hw₀u₀, hwu₀, hexp⟩

theorem stdHermForm_self_ne_zero_of_homology_eigen (h : UnitaryFieldData 2 m K)
    {a : unitarySU 2 m K 3} {v w₀ u₀ e : Fin 3 → K} {c d μ : K}
    (hv : stdHermForm h 3 v v ≠ 0) (hw₀w₀ : stdHermForm h 3 w₀ w₀ ≠ 0)
    (hvw₀ : stdHermForm h 3 v w₀ = 0)
    (hexp : ∀ x : Fin 3 → K, x = (stdHermForm h 3 u₀ x / stdHermForm h 3 u₀ u₀) • u₀ +
      (stdHermForm h 3 w₀ x / stdHermForm h 3 w₀ w₀) • w₀ +
      (stdHermForm h 3 v x / stdHermForm h 3 v v) • v)
    (hu₀e : stdHermForm h 3 u₀ e = 0) (he : e ≠ 0) (hcd : c ≠ d)
    (hae : a • e = μ • e) (haw₀ : a • w₀ = c • w₀) (hav : a • v = d • v) :
    stdHermForm h 3 e e ≠ 0 := by
  set x : K := stdHermForm h 3 w₀ e / stdHermForm h 3 w₀ w₀ with hxdef
  set y : K := stdHermForm h 3 v e / stdHermForm h 3 v v with hydef
  have hdecomp : e = x • w₀ + y • v := by
    have h0 := hexp e
    rw [hu₀e, zero_div, zero_smul, zero_add] at h0
    exact h0
  have hw₀v : stdHermForm h 3 w₀ v = 0 := by
    rw [← (stdHermForm_isSymm h 3).eq v w₀, hvw₀, map_zero]
  have hae' : a • e = (c * x) • w₀ + (d * y) • v := by
    rw [hdecomp, smul_add, smul_comm a x w₀, smul_comm a y v, haw₀, hav,
      smul_smul, smul_smul, mul_comm x c, mul_comm y d]
  have hμe : μ • e = (μ * x) • w₀ + (μ * y) • v := by
    rw [hdecomp, smul_add, smul_smul, smul_smul]
  have hEq : (c * x) • w₀ + (d * y) • v = (μ * x) • w₀ + (μ * y) • v :=
    hae'.symm.trans (hae.trans hμe)
  have hcx : (c - μ) * x = 0 := by
    have hB := congrArg (stdHermForm h 3 w₀) hEq
    simp only [map_add, map_smul, hw₀v, smul_eq_mul, mul_zero, add_zero] at hB
    have h' : c * x = μ * x := mul_right_cancel₀ hw₀w₀ hB
    rw [sub_mul, h', sub_self]
  have hdy : (d - μ) * y = 0 := by
    have hB := congrArg (stdHermForm h 3 v) hEq
    simp only [map_add, map_smul, hvw₀, smul_eq_mul, mul_zero, zero_add] at hB
    have h' : d * y = μ * y := mul_right_cancel₀ hv hB
    rw [sub_mul, h', sub_self]
  have hxy : x = 0 ∨ y = 0 := by
    rcases mul_eq_zero.mp hcx with hc | hx
    · rcases mul_eq_zero.mp hdy with hd | hy
      · exact absurd ((sub_eq_zero.mp hc).trans (sub_eq_zero.mp hd).symm) hcd
      · exact Or.inr hy
    · exact Or.inl hx
  have hself : stdHermForm h 3 e e =
      h.bar x * x * stdHermForm h 3 w₀ w₀ + h.bar y * y * stdHermForm h 3 v v := by
    rw [hdecomp]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
      hw₀v, hvw₀]
    ring
  intro h0
  rw [h0] at hself
  rcases hxy with hx | hy
  · have hy0 : y ≠ 0 := by
      intro hy0
      apply he
      rw [hdecomp, hx, hy0, zero_smul, zero_smul, add_zero]
    have hne : h.bar y * y * stdHermForm h 3 v v ≠ 0 :=
      mul_ne_zero (mul_ne_zero (fun hbar => hy0 (h.bar_eq_zero_iff.mp hbar)) hy0) hv
    rw [hx] at hself
    simp only [map_zero, zero_mul, zero_add] at hself
    exact hne hself.symm
  · have hx0 : x ≠ 0 := by
      intro hx0
      apply he
      rw [hdecomp, hx0, hy, zero_smul, zero_smul, add_zero]
    have hne : h.bar x * x * stdHermForm h 3 w₀ w₀ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (fun hbar => hx0 (h.bar_eq_zero_iff.mp hbar)) hx0) hw₀w₀
    rw [hy] at hself
    simp only [map_zero, zero_mul, add_zero] at hself
    exact hne hself.symm

end CFSG.ClassicalGroups.UnitaryFlag
