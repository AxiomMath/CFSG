module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Fixed

variable {G : Type} [Group G]

@[expose] def fixedSubgroup (θ : MulAut G) : Subgroup G where
  carrier := {x | θ x = x}
  mul_mem' := fun {a b} ha hb => by
    show θ (a * b) = a * b
    rw [map_mul, show θ a = a from ha, show θ b = b from hb]
  one_mem' := map_one θ
  inv_mem' := fun {a} ha => by
    show θ a⁻¹ = a⁻¹
    rw [map_inv, show θ a = a from ha]

theorem mem_fixedSubgroup {θ : MulAut G} {x : G} : x ∈ fixedSubgroup θ ↔ θ x = x := Iff.rfl

theorem fixedSubgroup_conj (Ψ θ : MulAut G) :
    fixedSubgroup (Ψ * θ * Ψ⁻¹) = (fixedSubgroup θ).map Ψ.toMonoidHom := by
  ext x
  rw [mem_fixedSubgroup, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨Ψ⁻¹ x, ?_, by simp⟩
    rw [mem_fixedSubgroup]
    have h' : Ψ (θ (Ψ⁻¹ x)) = x := h
    apply Ψ.injective
    rw [h']
    exact (MulAut.apply_inv_self G Ψ x).symm
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fixedSubgroup] at hy
    simp [MulAut.mul_apply, hy]

@[expose] noncomputable def fixedSubgroupConjEquiv (Ψ θ : MulAut G) :
    fixedSubgroup θ ≃* fixedSubgroup (Ψ * θ * Ψ⁻¹) :=
  (Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
    (MulEquiv.subgroupCongr (fixedSubgroup_conj Ψ θ).symm)

@[expose] def residual (H : Type) [Group H] : Subgroup H := ⨅ k, derivedSeries H k

theorem card_residual_congr {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    Nat.card (residual H) = Nat.card (residual H') := by
  have hmap : (residual H).map e.toMonoidHom = residual H' := by
    ext x
    simp only [residual, Subgroup.mem_map, Subgroup.mem_iInf]
    constructor
    · rintro ⟨y, hy, rfl⟩ k
      rw [← map_derivedSeries_eq (f := e.toMonoidHom) e.surjective k]
      exact ⟨y, hy k, rfl⟩
    · intro hx
      refine ⟨e.symm x, fun k => ?_, by simp⟩
      have := hx k
      rw [← map_derivedSeries_eq (f := e.toMonoidHom) e.surjective k] at this
      obtain ⟨y, hy, hyx⟩ := this
      have : y = e.symm x := by rw [← hyx]; simp
      rwa [← this]
  rw [← hmap]
  exact (Subgroup.card_map_of_injective e.injective).symm

theorem residual_eq_of_stable {H : Type} [Group H] {N : ℕ}
    (h : derivedSeries H (N + 1) = derivedSeries H N) : residual H = derivedSeries H N := by
  have hge : ∀ j, derivedSeries H (N + j) = derivedSeries H N := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← add_assoc, derivedSeries_succ, ih, ← derivedSeries_succ, h]
  refine le_antisymm (iInf_le _ N) (le_iInf fun k => ?_)
  rcases le_total k N with hk | hk
  · exact derivedSeries_antitone H hk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [hge j]

theorem residual_eq_top_of_perfect {H : Type} [Group H] (hH : Group.IsPerfect H) :
    residual H = ⊤ := by
  have h1 : ∀ k, derivedSeries H k = ⊤ := by
    intro k
    induction k with
    | zero => exact derivedSeries_zero H
    | succ k ih =>
      rw [derivedSeries_succ, ih]
      exact hH.commutator_eq_top
  simp [residual]

end Fixed

section EvenFixed

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem antiSpEquiv_pow_two_mul {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2) (m : ℕ) (x : antiSp K) :
    antiSpEquiv K ((minorAut K ^ (2 * m)) x) = fieldSp 2 K (Fr ^ m) (antiSpEquiv K x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have h : minorAut K ^ (2 * (m + 1)) = minorAut K ^ (2 * m) * minorAut K ^ 2 := by
      rw [← pow_add, Nat.mul_succ]
    rw [h, MulAut.mul_apply, minorAut_pow_two, ih, antiSpEquiv_frobHom hFr, pow_succ, map_mul,
      MulAut.mul_apply]

theorem exists_even_fixed {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m)) :
    ∃ (k : Subfield K) (_ : CharP k 2) (lift : antiSp k →* antiSp K),
      Nat.card k = 2 ^ m ∧ Function.Injective lift ∧
        lift.range = fixedSubgroup (minorAut K ^ (2 * m)) := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data (by omega) hK
  set σ : K ≃+* K := Fr ^ m with hσdef
  have hσ1 : σ ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hσσ : σ * σ = 1 := by
    rw [hσdef, ← pow_add, ← two_mul]
    have := pow_orderOf_eq_one Fr
    rwa [hord] at this
  have haa : fieldAut 2 K σ * fieldAut 2 K σ = 1 := by rw [← map_mul, hσσ, map_one]
  obtain ⟨-, -, hcard, -⟩ := even_symplectic_quadratic_involution_descent (r := 2) (f := 2 * m)
    (by norm_num) (by omega) hK (a := fieldAut 2 K σ) haa 1 σ
    (by change fieldAut 2 K σ = spInner 2 K 1 * fieldAut 2 K σ; rw [map_one, one_mul]) hσ1
  have hcard' : Nat.card (descentField σ) = 2 ^ m := by
    rw [hcard]; congr 1; omega
  have hcp : CharP (descentField σ) 2 := inferInstance
  refine ⟨descentField σ, hcp, ((antiSpEquiv K).symm : StatedSp 2 K ≃* antiSp K).toMonoidHom.comp
    ((subfieldSpHom 2 (descentField σ)).comp (antiSpEquiv (descentField σ)).toMonoidHom),
    hcard', ?_, ?_⟩
  · exact (antiSpEquiv K).symm.injective.comp ((subfieldSpHom_injective _).comp
      (antiSpEquiv (descentField σ)).injective)
  · ext x
    rw [MonoidHom.mem_range, mem_fixedSubgroup]
    constructor
    · rintro ⟨y, rfl⟩
      apply (antiSpEquiv K).injective
      rw [antiSpEquiv_pow_two_mul hFr m]
      change fieldSp 2 K σ (antiSpEquiv K ((antiSpEquiv K).symm _)) = antiSpEquiv K ((antiSpEquiv K).symm _)
      rw [MulEquiv.apply_symm_apply]
      exact fieldSp_subfieldSpHom _
    · intro h
      have h1 : fieldSp 2 K σ (antiSpEquiv K x) = antiSpEquiv K x := by
        rw [← antiSpEquiv_pow_two_mul hFr m, h]
      obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq h1
      refine ⟨(antiSpEquiv (descentField σ)).symm g₀, ?_⟩
      change (antiSpEquiv K).symm (subfieldSpHom 2 (descentField σ)
        (antiSpEquiv (descentField σ) ((antiSpEquiv (descentField σ)).symm g₀))) = x
      rw [MulEquiv.apply_symm_apply, hg₀, MulEquiv.symm_apply_apply]

end EvenFixed

section OddFixed

open CFSG.Blueprint

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem fixedSubgroup_eta
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    fixedSubgroup (minorAut K ^ (2 * m + 1)) = (suzukiGroup m K).subgroupOf (antiSp K) := by
  ext g
  rw [mem_fixedSubgroup, Subgroup.mem_subgroupOf]
  exact eta_apply_eq_iff hK g

@[expose] noncomputable def fixedSubgroupEtaEquiv
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    fixedSubgroup (minorAut K ^ (2 * m + 1)) ≃* suzukiGroup m K :=
  (MulEquiv.subgroupCongr (fixedSubgroup_eta hK)).trans
    (Subgroup.subgroupOfEquivOfLe (suzukiGroup_le_antiSp hK))

theorem card_fixedSubgroup_eta
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nat.card (fixedSubgroup (minorAut K ^ (2 * m + 1))) =
      (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) := by
  rw [Nat.card_congr (fixedSubgroupEtaEquiv hK).toEquiv]
  exact CFSG.LieType.Ree.suzuki_order hK

theorem odd_rank_bound
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) (E : Subgroup (antiSp K))
    (hE : E ≤ fixedSubgroup (minorAut K ^ (2 * m + 1))) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ (2 * (2 * m + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hsq x x.2⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hdvd : Nat.card E ∣ Nat.card (fixedSubgroup (minorAut K ^ (2 * m + 1))) :=
    Subgroup.card_dvd_of_le hE
  rw [card_fixedSubgroup_eta hK, hk] at hdvd
  set q := 2 ^ (2 * m + 1) with hq
  have hq2 : 2 ≤ q := Nat.le_self_pow (by omega) 2
  have hev : Even q := by rw [hq]; exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have h1 : Odd (q - 1) := by
    obtain ⟨r, hr⟩ := hev
    exact ⟨r - 1, by omega⟩
  have h2 : Odd (q ^ 2 + 1) := (hev.pow_of_ne_zero (n := 2) two_ne_zero).add_one
  have hodd : Odd ((q - 1) * (q ^ 2 + 1)) := h1.mul h2
  have hcop : Nat.Coprime (2 ^ k) ((q - 1) * (q ^ 2 + 1)) :=
    Nat.Coprime.pow_left k hodd.coprime_two_left
  have hdvd' : 2 ^ k ∣ q ^ 2 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [← Nat.mul_assoc]
    exact hdvd
  rw [hk]
  calc 2 ^ k ≤ q ^ 2 := Nat.le_of_dvd (by positivity) hdvd'
    _ = 2 ^ (2 * (2 * m + 1)) := by rw [hq, ← pow_mul, mul_comm]

end OddFixed

section EvenRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem even_rank_bound {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m))
    (E : Subgroup (antiSp K)) (hE : E ≤ fixedSubgroup (minorAut K ^ (2 * m)))
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ (3 * m) := by
  obtain ⟨k, hcp, lift, hcard, hinj, hrange⟩ := exists_even_fixed hm hK
  have := hcp
  let _ : Fintype k := Fintype.ofFinite k
  let E' : Subgroup (antiSp k) := E.comap lift
  have hmap : E'.map lift = E := by
    rw [Subgroup.map_comap_eq, hrange]
    exact inf_eq_right.mpr hE
  have hE'card : Nat.card E = Nat.card E' := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective hinj
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    apply hinj
    rw [map_mul, map_one]
    exact hsq _ hx
  rw [hE'card]
  exact (elementary_abelian_card_le (F := k) hcard E' hE'sq).1

end EvenRank

section Residual

theorem commutator_self_of_perfect {X : Type} [Group X] (C : Subgroup X) (hC : Group.IsPerfect C) :
    ⁅C, C⁆ = C := by
  have h1 : ⁅(⊤ : Subgroup C), (⊤ : Subgroup C)⁆ = ⊤ := by
    rw [← commutator_def]
    exact hC.commutator_eq_top
  have h2 := Subgroup.map_commutator (⊤ : Subgroup C) ⊤ C.subtype
  have h3 : (⊤ : Subgroup C).map C.subtype = C := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype C
  rw [h1, h3] at h2
  exact h2.symm

theorem card_residual_sympFour :
    Nat.card (residual CFSG.ComponentClassification.PresentationLocal.sympFour) = 360 := by
  have hC := CFSG.ComponentClassification.PresentationLocal.isPerfect_commutator_sympFour
  have hstable : derivedSeries CFSG.ComponentClassification.PresentationLocal.sympFour (1 + 1) =
      derivedSeries CFSG.ComponentClassification.PresentationLocal.sympFour 1 := by
    rw [derivedSeries_succ, derivedSeries_one]
    exact commutator_self_of_perfect _ hC
  rw [residual_eq_of_stable hstable, derivedSeries_one]
  rw [Nat.card_congr
    CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating.toEquiv,
    Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

section TwoElements

open Matrix

variable {k l : Type} [Field k] [Field l]

@[expose] def glCongr (ε : k ≃+* l) : GL (Fin 4) k ≃* GL (Fin 4) l :=
  Units.mapEquiv (ε.mapMatrix : Matrix (Fin 4) (Fin 4) k ≃+* Matrix (Fin 4) (Fin 4) l).toMulEquiv

theorem glMat_glCongr (ε : k ≃+* l) (x : GL (Fin 4) k) : glMat (glCongr ε x) = (glMat x).map ε :=
  rfl

theorem glCongr_mem_antiSp_iff (ε : k ≃+* l) (x : GL (Fin 4) k) :
    glCongr ε x ∈ antiSp l ↔ x ∈ antiSp k := by
  show (glMat (glCongr ε x))ᵀ * minorJ l * glMat (glCongr ε x) = minorJ l ↔
    (glMat x)ᵀ * minorJ k * glMat x = minorJ k
  rw [glMat_glCongr]
  have hJ : (minorJ k).map ε = minorJ l := by
    ext i j
    simp [minorJ_apply, apply_ite ε]
  rw [← hJ, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective ε.injective).eq_iff

@[expose] noncomputable def antiSpCongr (ε : k ≃+* l) : antiSp k ≃* antiSp l :=
  ((glCongr ε).subgroupMap (antiSp k)).trans (MulEquiv.subgroupCongr (by
    ext y
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (glCongr_mem_antiSp_iff ε x).mpr hx
    · intro hy
      refine ⟨(glCongr ε).symm y, ?_, (glCongr ε).apply_symm_apply y⟩
      rw [← glCongr_mem_antiSp_iff ε, (glCongr ε).apply_symm_apply]
      exact hy))

end TwoElements

theorem residual_antiSp_two_even {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    Even (Nat.card (residual (antiSp k))) := by
  let _ : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 := by rwa [← Nat.card_eq_fintype_card]
  let ε : ZMod 2 ≃+* k := ZMod.ringEquivOfPrime k Nat.prime_two hk'
  have hJ : antiSp (ZMod 2) = CFSG.ComponentClassification.PresentationLocal.sympFour := by
    ext g
    rfl
  let e : antiSp k ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (antiSpCongr ε.symm).trans (MulEquiv.subgroupCongr hJ)
  rw [card_residual_congr e, card_residual_sympFour]
  exact ⟨180, rfl⟩

end Residual

section Assembly

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem even_card_antiSp (k : Type) [Field k] [CharP k 2] [Finite k] :
    Even (Nat.card (antiSp k)) := by
  rw [even_iff_two_dvd]
  have h : orderOf (invX k) = 2 := orderOf_eq_prime (by rw [sq]; exact invX_mul_self) invX_ne_one
  rw [← h]
  exact orderOf_dvd_natCard _

theorem residual_fixed_even {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m)) :
    Even (Nat.card (residual (fixedSubgroup (minorAut K ^ (2 * m))))) := by
  obtain ⟨k, hcp, lift, hcard, hinj, hrange⟩ := exists_even_fixed hm hK
  have := hcp
  let _ : Fintype k := Fintype.ofFinite k
  let e : antiSp k ≃* fixedSubgroup (minorAut K ^ (2 * m)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  rw [← card_residual_congr e]
  by_cases hm2 : 2 ≤ m
  · have hperf : Group.IsPerfect (antiSp k) :=
      antiSp_isPerfect (by rw [← Nat.card_eq_fintype_card]; exact hcard) hm2
    rw [residual_eq_top_of_perfect hperf, Subgroup.card_top]
    exact even_card_antiSp k
  · have hm1 : m = 1 := by omega
    subst hm1
    exact residual_antiSp_two_even (by simpa using hcard)

theorem residual_fixed_odd
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Even (Nat.card (residual (fixedSubgroup (minorAut K ^ (2 * m + 1))))) := by
  have hperf : Group.IsPerfect (fixedSubgroup (minorAut K ^ (2 * m + 1))) := by
    have : Group.IsPerfect (CFSG.Blueprint.suzukiGroup m K) :=
      (CFSG.LieType.Ree.suzuki_perfect hm hK).2
    exact Group.IsPerfect.ofSurjective (f := (fixedSubgroupEtaEquiv hK).symm.toMonoidHom)
      (fixedSubgroupEtaEquiv hK).symm.surjective
  rw [residual_eq_top_of_perfect hperf, Subgroup.card_top, card_fixedSubgroup_eta hK]
  have hev : Even (2 ^ (2 * m + 1) : ℕ) := Nat.even_pow.2 ⟨even_two, by omega⟩
  exact ((hev.pow_of_ne_zero (n := 2) two_ne_zero).mul_right _).mul_right _

omit [Finite K] [CharP K 2] in
theorem rank_bound_of_conj {G : Type} [Group G] {θ₀ θ : MulAut G} (c : G)
    (hθ : θ = MulAut.conj c * θ₀ * (MulAut.conj c)⁻¹) {b : ℕ}
    (h₀ : ∀ E : Subgroup G, E ≤ fixedSubgroup θ₀ → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ b)
    (E : Subgroup G) (hE : E ≤ fixedSubgroup θ) (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ b := by
  set Ψ : MulAut G := MulAut.conj c with hΨ
  have hfix : fixedSubgroup θ = (fixedSubgroup θ₀).map Ψ.toMonoidHom := by
    rw [hθ]
    exact fixedSubgroup_conj Ψ θ₀
  let E₀ : Subgroup G := E.comap Ψ.toMonoidHom
  have hE₀ : E₀ ≤ fixedSubgroup θ₀ := by
    intro x hx
    have : Ψ x ∈ fixedSubgroup θ := hE hx
    rw [hfix] at this
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Ψ.injective hyx
    rwa [← this]
  have hmap : E₀.map Ψ.toMonoidHom = E := Subgroup.map_comap_eq_self_of_surjective Ψ.surjective E
  have hcard : Nat.card E = Nat.card E₀ := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective Ψ.injective
  rw [hcard]
  refine h₀ E₀ hE₀ fun x hx => ?_
  apply Ψ.injective
  rw [map_mul, map_one]
  exact hsq _ hx

theorem even_symplectic_four_outer_involution_rank_and_perfect_residual
    {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    Function.Injective (MulAut.conj : antiSp K →* MulAut (antiSp K)) ∧
    IsCyclic (Outer (antiSp K)) ∧ Nat.card (Outer (antiSp K)) = 2 * n ∧
    ∀ θ : MulAut (antiSp K), θ * θ = 1 → θ ∉ inner (antiSp K) →
      (∀ φ : MulAut (antiSp K), φ * φ = 1 → φ * θ⁻¹ ∈ inner (antiSp K) →
        ∃ c : antiSp K, φ = MulAut.conj c * θ * (MulAut.conj c)⁻¹) ∧
      (∀ E : Subgroup (antiSp K), E ≤ fixedSubgroup θ → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 2 ^ (if Even n then 3 * (n / 2) else 2 * n)) ∧
      Even (Nat.card (residual (fixedSubgroup θ))) := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data (by omega) hK
  obtain ⟨-, -, -, -, hcyc, hcard, -⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  let eO := CFSG.ComponentClassification.OuterAutomorphisms.equivalence (antiProjEquiv K)
  refine ⟨conj_injective, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective eO.symm.toMonoidHom eO.symm.surjective
  · rw [Nat.card_congr eO.toEquiv]
    exact hcard
  intro θ hθ hθinn
  have key : ∀ θ : MulAut (antiSp K), θ * θ = 1 → θ ∉ inner (antiSp K) →
      ∃ c : antiSp K, θ = MulAut.conj c * minorAut K ^ n * (MulAut.conj c)⁻¹ :=
    fun θ hθ hθinn => outer_involution_conj hn hK θ hθ hθinn
  obtain ⟨c, hc⟩ := key θ hθ hθinn
  refine ⟨?_, ?_, ?_⟩
  · intro φ hφ hφθ
    have hφinn : φ ∉ inner (antiSp K) := by
      intro h
      apply hθinn
      have : θ = (φ * θ⁻¹)⁻¹ * φ := by group
      rw [this]
      exact mul_mem (inv_mem hφθ) h
    obtain ⟨d, hd⟩ := key φ hφ hφinn
    refine ⟨d * c⁻¹, ?_⟩
    rw [hd, hc]
    simp only [map_mul, map_inv]
    group
  · intro E hE hsq
    by_cases hev : Even n
    · obtain ⟨m, hm⟩ := hev
      have hn2 : n = 2 * m := by omega
      subst hn2
      have hm1 : 1 ≤ m := by omega
      have hev' : Even (2 * m) := ⟨m, by ring⟩
      simp only [hev', ↓reduceIte]
      rw [show 2 * m / 2 = m by omega]
      exact rank_bound_of_conj c hc (b := 2 ^ (3 * m))
        (fun E' hE' hsq' => even_rank_bound hm1 hK E' hE' hsq') E hE hsq
    · obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hev
      subst hm
      simp only [hev, ↓reduceIte]
      exact rank_bound_of_conj c hc (b := 2 ^ (2 * (2 * m + 1)))
        (fun E' hE' hsq' => odd_rank_bound hK E' hE' hsq') E hE hsq
  · have h := card_residual_congr (fixedSubgroupConjEquiv (MulAut.conj c) (minorAut K ^ n))
    rw [← hc] at h
    rw [← h]
    by_cases hev : Even n
    · obtain ⟨m, hm⟩ := hev
      have hn2 : n = 2 * m := by omega
      subst hn2
      exact residual_fixed_even (by omega) hK
    · obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hev
      subst hm
      exact residual_fixed_odd (by omega) hK

end Assembly

end CFSG.QuasithinUnique.Setup.X7b
