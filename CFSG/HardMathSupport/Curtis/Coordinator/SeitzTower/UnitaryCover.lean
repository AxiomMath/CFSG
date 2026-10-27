module

public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharDetCover

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open Matrix CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_zpow_mem_primeFormD {ℓ f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    {N : ℕ} (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ ℓ ^ f = 2)) :
    ∃ γ₀ : MulAut (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)),
      ∀ α : MulAut (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)),
        ∃ i : ℤ, α * γ₀ ^ i ∈ primeFormD hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  have : Finite K := hU.finite
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨-, -, -, -, -, -, hFsurj, hFker, -⟩ :=
    unitary_prime_form_full_semilinear_realization hU
      (UnitaryHigher.isPrimeFormGram_one (n := N)) hN hq
  set F := primeFormFieldFactor hU (UnitaryHigher.isPrimeFormGram_one (n := N) (K := K)) hN hq
  obtain ⟨σ₀, hσ₀⟩ := hcyc.exists_generator
  obtain ⟨γ₀, hγ₀⟩ := hFsurj σ₀
  refine ⟨γ₀, fun α => ?_⟩
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (hσ₀ (F α))
  refine ⟨-a, ?_⟩
  rw [← hFker, MonoidHom.mem_ker, map_mul, map_zpow, hγ₀, ← ha, _root_.zpow_neg, mul_inv_cancel]

theorem mem_inner_of_pow_eq_one_primeFormD {ℓ f : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData ℓ f K) {N : ℕ} (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hq1 : ¬ p ∣ ℓ ^ f + 1)
    {δ : MulAut (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))}
    (hδ : δ ∈ primeFormD hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) (hδp : δ ^ p = 1) :
    δ ∈ (MulAut.conj : primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) →*
      MulAut (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))).range := by
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order hU hN hq
  set D := primeFormD hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  set I := inner (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))
  have : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
  have hxp : x ^ p = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, hδp]
    exact I.one_mem
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have h2 : orderOf x ∣ Nat.gcd N (ℓ ^ f + 1) := hcard ▸ orderOf_dvd_natCard x
  have h3 : orderOf x = 1 := by
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      exact hq1 (h2.trans (Nat.gcd_dvd_right _ _))
  rw [orderOf_eq_one_iff, hx, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

private theorem neg_pow_eq_one_iff_sub_eq_zero {R : Type*} [CommRing R] (x : R) (N : ℕ) :
    (-x) ^ N = 1 ↔ x ^ N - (-1) ^ N = 0 := by
  have hs : ((-1 : R) ^ N) * ((-1 : R) ^ N) = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  have h1 : (-x) ^ N = (-1) ^ N * x ^ N := by rw [neg_eq_neg_one_mul, mul_pow]
  rw [h1, sub_eq_zero]
  constructor
  · intro h
    linear_combination ((-1 : R) ^ N) * h - (x ^ N) * hs
  · intro h
    rw [h]
    exact hs

private theorem neg_pow_eq_one_iff_dvd_sub (p N ℓ f : ℕ) [Fact p.Prime] :
    (-((ℓ : ZMod p) ^ f)) ^ N = 1 ↔ (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ N - (-1) ^ N := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact neg_pow_eq_one_iff_sub_eq_zero _ N

theorem exists_isPGroup_map_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Z : Subgroup G) [Z.Normal] (P : Subgroup (G ⧸ Z)) (hP : IsPGroup p P) :
    ∃ Q : Subgroup G, IsPGroup p Q ∧ ∀ x ∈ P, ∃ s ∈ Q, (s : G ⧸ Z) = x := by
  classical
  set π := QuotientGroup.mk' Z with hπ
  set Q₀ := P.comap π with hQ₀
  let φ : Q₀ →* P := π.subgroupComap P
  have hφ : Function.Surjective φ := π.subgroupComap_surjective P (QuotientGroup.mk'_surjective Z)
  obtain ⟨S⟩ : Nonempty (Sylow p Q₀) := inferInstance
  have hT : ((S.mapSurjective hφ : Sylow p P) : Subgroup P) = ⊤ :=
    ((S.mapSurjective hφ).is_maximal' (hP.of_equiv Subgroup.topEquiv.symm) le_top).symm
  rw [Sylow.coe_mapSurjective] at hT
  refine ⟨(S : Subgroup Q₀).map Q₀.subtype, S.isPGroup'.map _, fun x hx => ?_⟩
  have hmem : (⟨x, hx⟩ : P) ∈ (S : Subgroup Q₀).map φ := by
    rw [hT]
    exact Subgroup.mem_top _
  obtain ⟨s, hs, hsx⟩ := hmem
  exact ⟨(s : G), ⟨s, hs, rfl⟩, congrArg Subtype.val hsx⟩

theorem exists_fixed_normOne_vector {ℓ f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    {N : ℕ} (hN : 1 ≤ N) {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (hqN : ¬ (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ N - (-1) ^ N)
    (P : Subgroup (GL (Fin N) K)) (hP : IsPGroup p P)
    (hPU : P ≤ primeFormUnitary hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) :
    ∃ v : Fin N → K, gramForm hU (1 : Matrix (Fin N) (Fin N) K) v v = 1 ∧
      ∀ a ∈ P, ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v := by
  classical
  have hfin : Finite K := hU.finite
  have hB : (gramForm hU (1 : Matrix (Fin N) (Fin N) K)).IsSymm := gramForm_isSymm hU (by simp)
  have hBl : (gramForm hU (1 : Matrix (Fin N) (Fin N) K)).SeparatingLeft :=
    gramForm_separatingLeft hU (by simp)
  have hcount := (CFSG.LinearGroups.unitary_hermitian_vector_count hU hB hBl (n := N)
    (by simp) hN).2.1 1 hU.fixedField.one_mem one_ne_zero
  let S : SubMulAction P (Fin N → K) :=
    { carrier := {v | gramForm hU (1 : Matrix (Fin N) (Fin N) K) v v = 1}
      smul_mem' := fun a v hv => by
        have hiso := (gramForm_isometry_iff hU (1 : Matrix (Fin N) (Fin N) K)
          ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)).2
          (by simpa using mem_primeFormUnitary.mp (hPU a.2)) v v
        change gramForm hU (1 : Matrix (Fin N) (Fin N) K) _ _ = 1
        exact hiso.trans hv }
  have : Finite S := Finite.of_injective (fun x : S => (x : Fin N → K)) Subtype.val_injective
  have hmod := hP.card_modEq_card_fixedPoints S
  have hcardS : Nat.card S =
      Nat.card {v : Fin N → K // gramForm hU (1 : Matrix (Fin N) (Fin N) K) v v = 1} := rfl
  have hnd : ¬ (p : ℤ) ∣ (Nat.card S : ℤ) := by
    rw [hcardS, hcount]
    intro hd
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
    rcases hpz.dvd_or_dvd hd with h | h
    · apply hpℓ
      have h1 : p ∣ (ℓ ^ f) ^ (N - 1) := by exact_mod_cast h
      exact (Nat.prime_dvd_prime_iff_eq Fact.out hU.prime).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow ((Fact.out : p.Prime).dvd_of_dvd_pow h1))
    · exact hqN h
  by_cases hne : (MulAction.fixedPoints P S).Nonempty
  · obtain ⟨x, hx⟩ := hne
    refine ⟨(x : Fin N → K), x.2, fun a ha => ?_⟩
    have := congrArg Subtype.val (hx ⟨a, ha⟩)
    exact this
  · exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card (MulAction.fixedPoints P S) = 0 := by
      rw [hne]
      simp
    rw [h0] at hmod
    apply hnd
    exact_mod_cast (Nat.modEq_zero_iff_dvd.mp hmod)

theorem exists_isometry_commute_det_eq {ℓ f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    {N : ℕ} {v : Fin N → K} (hv : gramForm hU (1 : Matrix (Fin N) (Fin N) K) v v = 1)
    {μ : K} (hμ : hU.norm μ = 1) (P : Subgroup (GL (Fin N) K))
    (hPU : P ≤ primeFormUnitary hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))
    (hPv : ∀ a ∈ P, ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v) :
    ∃ c : GL (Fin N) K,
      c ∈ primeFormUnitary hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ∧
      (∀ a ∈ P, c * a = a * c) ∧ ((c : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det = μ := by
  classical
  have hBsymm : (gramForm hU (1 : Matrix (Fin N) (Fin N) K)).IsSymm :=
    gramForm_isSymm hU (by simp)
  set B := gramForm hU (1 : Matrix (Fin N) (Fin N) K) with hB
  have hBapply : ∀ x y, B x y = (fun a => hU.bar (x a)) ⬝ᵥ y := fun x y => by
    rw [hB, gramForm_apply, one_mulVec]
  set w : Fin N → K := fun i => hU.bar (v i) with hw
  have hwv : w ⬝ᵥ v = 1 := by rw [← hv, hBapply]
  set u : Fin N → K := (μ - 1) • v with hu
  set M : Matrix (Fin N) (Fin N) K := 1 + vecMulVec u w with hM
  have hμ0 : μ ≠ 0 := left_ne_zero_of_mul_eq_one hμ
  have hdet : M.det = μ := by
    have h0 : M.det = 1 + w ⬝ᵥ u := by
      rw [hM, vecMulVec_eq (Fin 1)]
      exact det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) u w
    rw [h0, hu, dotProduct_smul, hwv, smul_eq_mul, mul_one]
    ring
  have hMx : ∀ x, M *ᵥ x = x + ((μ - 1) * B v x) • v := by
    intro x
    rw [hM, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hu, smul_smul,
      hBapply v x]
    simp only [hw, mul_comm]
  have hiso : ∀ x y, B (M *ᵥ x) (M *ᵥ y) = B x y := by
    intro x y
    rw [hMx, hMx]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← hBsymm.eq v x, hv, map_mul, map_sub, map_one]
    have hμ' : μ * hU.bar μ = 1 := hμ
    linear_combination (B v y * hU.bar (B v x)) * hμ'
  have hMu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_iff_ne_zero.2 hμ0
  refine ⟨hMu.unit, ?_, fun a ha => ?_, hdet⟩
  · exact (gramForm_isometry_iff hU (1 : Matrix (Fin N) (Fin N) K) M).1 hiso
  · have hia := (gramForm_isometry_iff hU (1 : Matrix (Fin N) (Fin N) K)
      ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)).2 (hPU ha)
    apply Units.ext
    change M * ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * M
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← mulVec_mulVec, ← mulVec_mulVec, hMx, hMx, mulVec_add, mulVec_smul, hPv a ha]
    have h1 := hia v x
    rw [hPv a ha] at h1
    rw [h1]

theorem exists_conj_agree_of_isPGroup_unitary {ℓ f : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData ℓ f K) {N : ℕ} (hN : 1 ≤ N) {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (hqN : ¬ (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ N - (-1) ^ N)
    (P : Subgroup (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))
    (hP : IsPGroup p P)
    (A : primeFormUnitary hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) :
    ∃ k : primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K),
      ∀ x ∈ P, primeFormConjHom hU _ A x = k * x * k⁻¹ := by
  classical
  have : Finite K := hU.finite
  obtain ⟨Q, hQ, hlift⟩ := exists_isPGroup_map_eq (p := p)
    (normOneScalars hU (gramSU hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) N) P hP
  set P' : Subgroup (GL (Fin N) K) :=
    Q.map (gramSU hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)).subtype with hP'
  have hP'p : IsPGroup p P' := hQ.map _
  have hP'U : P' ≤ primeFormUnitary hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2.1
  obtain ⟨v, hv1, hvP⟩ := exists_fixed_normOne_vector hU hN hpℓ hqN P' hP'p hP'U
  have hAnorm := norm_det_eq_one hU (1 : GL (Fin N) K) A.2
  obtain ⟨c, hcU, hcP, hcdet⟩ := exists_isometry_commute_det_eq hU hv1 hAnorm P' hP'U hvP
  have hμ0 : ((A : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det ≠ 0 :=
    left_ne_zero_of_mul_eq_one hAnorm
  have hdetb : (((A * c⁻¹ : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K).det = 1 := by
    have h1 : (((A * c⁻¹ : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K).det *
        ((c : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det =
        ((A : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel_right]
    rw [hcdet] at h1
    exact mul_right_cancel₀ hμ0 (h1.trans (one_mul _).symm)
  let b : gramSU hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) :=
    ⟨A * c⁻¹, (mem_gramSU_iff_unitary hU).2 ⟨mul_mem A.2 (inv_mem hcU), hdetb⟩⟩
  refine ⟨(b : primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)), fun x hx => ?_⟩
  obtain ⟨s, hs, rfl⟩ := hlift x hx
  have hsP' : ((s : gramSU hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) :
      GL (Fin N) K) ∈ P' := Subgroup.mem_map_of_mem _ hs
  have hcs := hcP _ hsP'
  rw [primeFormConjHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin N) K) * (s : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ =
    (A * c⁻¹) * (s : GL (Fin N) K) * (A * c⁻¹)⁻¹
  have e : c⁻¹ * (s : GL (Fin N) K) * c = (s : GL (Fin N) K) := by
    rw [mul_assoc, ← hcs, inv_mul_cancel_left]
  calc (A : GL (Fin N) K) * (s : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹
      = (A : GL (Fin N) K) * (c⁻¹ * (s : GL (Fin N) K) * c) * (A : GL (Fin N) K)⁻¹ := by rw [e]
    _ = (A * c⁻¹) * (s : GL (Fin N) K) * (A * c⁻¹)⁻¹ := by group

theorem detCoverAt_primeFormP {ℓ f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    {N : ℕ} (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ ℓ ^ f = 2)) {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (hqN : (-((ℓ : ZMod p) ^ f)) ^ N ≠ 1) :
    DetCoverAt (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) p := by
  have hp : p.Prime := Fact.out
  have hqN' : ¬ (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ N - (-1) ^ N := fun h =>
    hqN ((neg_pow_eq_one_iff_dvd_sub p N ℓ f).2 h)
  have hq1 : ¬ p ∣ ℓ ^ f + 1 := by
    intro h
    apply hqN
    have h0 : ((ℓ ^ f + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    push_cast at h0
    have h1 : -((ℓ : ZMod p) ^ f) = 1 := neg_eq_of_add_eq_zero_right h0
    rw [h1, one_pow]
  refine ⟨primeFormD hU _, fun α β => OuterDerived.commutator_mem_primeFormD hU hN hq α β, ?_,
    fun δ hδ hδp => mem_inner_of_pow_eq_one_primeFormD hU hN hq hp hq1 hδ hδp,
    fun P hP δ hδ => ?_⟩
  · obtain ⟨γ₀, hγ₀⟩ := exists_zpow_mem_primeFormD hU hN hq
    exact ⟨γ₀, fun α _ => hγ₀ α⟩
  · obtain ⟨A, rfl⟩ := hδ
    exact exists_conj_agree_of_isPGroup_unitary hU (by omega) hpℓ hqN' P hP A

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
