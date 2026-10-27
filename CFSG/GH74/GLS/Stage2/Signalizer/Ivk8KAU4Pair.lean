module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUDef
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KACover
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.Burgoyne.PSL (commutator_eq_self_of_isQuasisimple
  eq_scalar_of_commute_single)
open scoped MatrixGroups commutatorElement

section Cover

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem kaPr_ker_central (z : StatedSU n (p ^ f) K)
    (hz : z ∈ (projH (StatedSU n (p ^ f) K)).ker) (g : StatedSU n (p ^ f) K) :
    g * z = z * g := by
  have hz' : z ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) := by
    rwa [QuotientGroup.ker_mk'] at hz
  exact Subgroup.mem_center_iff.1 (scalars_subgroupOf_le_center hz') g

end Cover

section Pair

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m : ℕ}

@[expose] def kaPrDet (l : K) (g : Matrix (Fin (m + m)) (Fin (m + m)) K) : K :=
  ((prEv m l g).toBlocks₁₁).det

theorem kaPrDet_one (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) :
    kaPrDet l (1 : Matrix (Fin (m + m)) (Fin (m + m)) K) = 1 := by
  rw [kaPrDet, prEv_one h2 hl, ← fromBlocks_one, toBlocks_fromBlocks₁₁, det_one]

theorem kaPrDet_mul (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    {g g' : Matrix (Fin (m + m)) (Fin (m + m)) K} (hg : prA m l * g = g * prA m l)
    (hg' : prA m l * g' = g' * prA m l) :
    kaPrDet l (g * g') = kaPrDet l g * kaPrDet l g' := by
  obtain ⟨G, G', rfl⟩ := exists_prPhi_of_commute h2 hl hg.symm
  obtain ⟨H, H', rfl⟩ := exists_prPhi_of_commute h2 hl hg'.symm
  rw [kaPrDet, kaPrDet, kaPrDet, prPhi_mul h2 hl, prEv_prPhi h2 hl, prEv_prPhi h2 hl,
    prEv_prPhi h2 hl, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁,
    det_mul]

@[expose] def kaPrDetG (l : K) (g : StatedSU (m + m) (p ^ f) K) : K :=
  kaPrDet l ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K)

theorem kaPr_comm_of_mem (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {g : StatedSU (m + m) (p ^ f) K}
    (hg : g ∈ kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1)) :
    prA m l * ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) * prA m l := by
  have := (uLift_one_eq_iff h (uPairA (m := m) h h2 hl hN) g).1 (mem_kaFix.1 hg)
  rwa [coe_uPairA] at this

theorem kaPr_range_le (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    (prSLHom (m := m) h h2 hl hN).range ≤ kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1) := by
  rintro _ ⟨G, rfl⟩
  refine mem_kaFix.2 ((uLift_one_eq_iff h _ _).2 ?_)
  rw [coe_uPairA, coe_prSLHom, prPhi_commute_prA h2 hl]

theorem kaPrDetG_mul (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1)
    {x y : StatedSU (m + m) (p ^ f) K}
    (hx : x ∈ kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1))
    (hy : y ∈ kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1)) :
    kaPrDetG l (x * y) = kaPrDetG l x * kaPrDetG l y :=
  kaPrDet_mul h2 hl (kaPr_comm_of_mem h h2 hl hN hx) (kaPr_comm_of_mem h h2 hl hN hy)

theorem kaPrDetG_one (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) :
    kaPrDetG l (1 : StatedSU (m + m) (p ^ f) K) = 1 :=
  kaPrDet_one h2 hl

theorem kaPr_commutator_le (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    ⁅kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1),
      kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1)⁆ ≤ (prSLHom (m := m) h h2 hl hN).range := by
  set C := kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1) with hC
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : ⁅a, b⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)
  have hdinv : ∀ x ∈ C, kaPrDetG l x * kaPrDetG l x⁻¹ = 1 := fun x hx => by
    rw [← kaPrDetG_mul h h2 hl hN hx (C.inv_mem hx), mul_inv_cancel, kaPrDetG_one h2 hl]
  have hdcomm : kaPrDetG l ⁅a, b⁆ = 1 := by
    rw [commutatorElement_def,
      kaPrDetG_mul h h2 hl hN (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb),
      kaPrDetG_mul h h2 hl hN (C.mul_mem ha hb) (C.inv_mem ha), kaPrDetG_mul h h2 hl hN ha hb]
    calc kaPrDetG l a * kaPrDetG l b * kaPrDetG l a⁻¹ * kaPrDetG l b⁻¹ =
        (kaPrDetG l a * kaPrDetG l a⁻¹) * (kaPrDetG l b * kaPrDetG l b⁻¹) := by ring
      _ = 1 := by rw [hdinv a ha, hdinv b hb, one_mul]
  exact mem_range_prSLHom h h2 hl hN (kaPr_comm_of_mem h h2 hl hN hab) hdcomm

theorem kaPr_commutator_eq [Finite K] (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m) {l : K}
    (hl : l ≠ 0) (hN : h.norm l = -1) :
    ⁅kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1),
      kaFix (uLift h (uPairA (m := m) h h2 hl hN) 1)⁆ = (prSLHom (m := m) h h2 hl hN).range := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [h.card]
    have := h.prime.two_le
    have := h.one_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)
  have hQ := isQuasisimple_range_prSLHom h h2 hl hN hm hK4
  refine le_antisymm (kaPr_commutator_le h h2 hl hN) ?_
  calc (prSLHom (m := m) h h2 hl hN).range = ⁅(prSLHom (m := m) h h2 hl hN).range,
        (prSLHom (m := m) h h2 hl hN).range⁆ := (commutator_eq_self_of_isQuasisimple hQ).symm
    _ ≤ _ := Subgroup.commutator_mono (kaPr_range_le h h2 hl hN) (kaPr_range_le h h2 hl hN)

theorem kaPr_form [Finite K] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m) {l : K} (hl : l ≠ 0)
    (hN : h.norm l = -1) {D : uU h (m + m)} {τ : K ≃+* K} {k : ℕ} (hk : Odd k)
    (hpow : (uConjAut h (by omega) D * uFieldAut h (by omega) τ) ^ k = 1)
    (hcomm : (uConjAut h (by omega) D * uFieldAut h (by omega) τ) *
        uConjAut h (by omega) (uPairA (m := m) h h2 hl hN) =
      uConjAut h (by omega) (uPairA (m := m) h h2 hl hN) *
        (uConjAut h (by omega) D * uFieldAut h (by omega) τ))
    (hfix : ∀ g ∈ (prSLHom (m := m) h h2 hl hN).range,
      (uConjAut h (by omega) D * uFieldAut h (by omega) τ :
        MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))
        (projH (StatedSU (m + m) (p ^ f) K) g) = projH (StatedSU (m + m) (p ^ f) K) g) :
    τ = 1 ∧ ∃ a b : K, h.bar a * b = 1 ∧
      ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        prPhi m l (a • 1) (b • 1) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hn : 3 ≤ m + m := by omega
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(m + m = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  have hK4 : 4 ≤ Nat.card K := by
    rw [h.card]
    have := h.prime.two_le
    have := h.one_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)
  have hφk : τ ^ k = 1 := fieldAut_pow_eq_one h hn hq hpow
  set A₀ := uPairA (m := m) h h2 hl hN with hA₀
  set L := (prSLHom (m := m) h h2 hl hN).range with hL
  have hQ := isQuasisimple_range_prSLHom h h2 hl hN hm hK4
  have hcomp : ∀ g ∈ L, ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K).map τ *
      (((D : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
        Matrix (Fin (m + m)) (Fin (m + m)) K) =
      ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) := fun g hg =>
    uSemilinear_eq_of_fix h (by omega) (commutator_eq_self_of_isQuasisimple hQ) hfix hg
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
  set N := prPhi m l (single (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ (1 : K))
    (-single (⟨1, by omega⟩ : Fin m) ⟨0, by omega⟩ (1 : K)) with hNdef
  have hNe : N (finSumFinEquiv (Sum.inl ⟨0, by omega⟩)) (finSumFinEquiv (Sum.inl ⟨1, by omega⟩))
      ≠ 0 := by
    rw [hNdef, prPhi_eq h2 hl, prFin_apply, fromBlocks_apply₁₁]
    simp [Matrix.smul_apply, h2]
  have hφ : τ = 1 := by
    refine eq_one_of_odd_of_fix h hk hφk (fix_of_conj_family h (D := (D : GL (Fin (m + m)) K))
      hNe fun c hc => ?_)
    have e := hcomp _ ⟨Matrix.SpecialLinearGroup.transvection h01 c, rfl⟩
    rw [coe_prSLHom_transvection h h2 hl hN h01 c, hc] at e
    have e' : prPhi m l (1 + single (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ c)
        (1 - c • single (⟨1, by omega⟩ : Fin m) ⟨0, by omega⟩ 1) = 1 + c • N := by
      rw [hNdef, ← prPhi_smul, ← prPhi_one h2 hl, ← prPhi_add, smul_neg, ← sub_eq_add_neg]
      simp only [smul_single, smul_eq_mul, mul_one]
    rwa [e'] at e
  refine ⟨hφ, ?_⟩
  subst hφ
  simp only [map_one, mul_one] at hpow hcomm
  set Dm := ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) with hDm
  set Dmi := (((D : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
    Matrix (Fin (m + m)) (Fin (m + m)) K) with hDmi
  have hDiD : Dmi * Dm = 1 := by rw [hDm, hDmi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA₀2 : uConjAut h (by omega) (A₀ * A₀) = 1 := by
    refine (uConjAut_eq_one_iff h hn _).2 ⟨Units.mk0 (l ^ 2) (pow_ne_zero 2 hl), Units.ext ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hA₀, coe_uPairA, prA_mul_self h2 hl,
      GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl
  have hodd : Odd (orderOf (uConjAut h (by omega) D)) :=
    Odd.of_dvd_nat hk (orderOf_dvd_of_pow_eq_one hpow)
  have hcD : D * A₀ = A₀ * D := uCommute_of_odd h hn hA₀2 hodd hcomm
  have hcA : Dm * prA m l = prA m l * Dm := by
    have e := congrArg (fun x : uU h (m + m) =>
      ((x : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K)) hcD
    simp only [Subgroup.coe_mul, Units.val_mul, hA₀, coe_uPairA] at e
    exact e
  obtain ⟨P, Q, hPQ⟩ := exists_prPhi_of_commute h2 hl hcA
  have hcL : ∀ G : SL(m, K), Dm * prPhi m l G (prDual h G) = prPhi m l G (prDual h G) * Dm := by
    intro G
    have e := hcomp _ ⟨G, rfl⟩
    rw [map_one_ringEquiv, coe_prSLHom] at e
    calc Dm * prPhi m l G (prDual h G) = Dm * prPhi m l G (prDual h G) * (Dmi * Dm) := by
          rw [hDiD, Matrix.mul_one]
      _ = prPhi m l G (prDual h G) * Dm := by rw [← Matrix.mul_assoc, e]
  have hPQc : ∀ i j : Fin m, i ≠ j → P * single i j 1 = single i j 1 * P ∧
      Q * single j i 1 = single j i 1 * Q := by
    intro i j hij
    have e := hcL (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [prDual_transvection h hij, map_one, one_smul, Matrix.SpecialLinearGroup.transvection_coe,
      hPQ, prPhi_mul h2 hl, prPhi_mul h2 hl] at e
    obtain ⟨e1, e2⟩ := prPhi_inj h2 hl e
    constructor
    · rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at e1
      exact add_left_cancel e1
    · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at e2
      exact sub_right_injective e2
  set a₀ : Fin m := ⟨0, by omega⟩ with ha₀
  have hP : P = Matrix.scalar (Fin m) (P a₀ a₀) :=
    eq_scalar_of_commute_single a₀ fun i j hij => (hPQc i j hij).1
  have hQ' : Q = Matrix.scalar (Fin m) (Q a₀ a₀) :=
    eq_scalar_of_commute_single a₀ fun i j hij => (hPQc j i (Ne.symm hij)).2
  have hsc : ∀ c : K, Matrix.scalar (Fin m) c = c • 1 := fun c => by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  refine ⟨P a₀ a₀, Q a₀ a₀, ?_, ?_⟩
  · have hU : (Dm.map h.bar)ᵀ * Dm = 1 := (mem_uU h).1 D.2
    rw [hPQ, prPhi_unitary_iff h h2 hl hN, hP, hQ', hsc, hsc, smul_one_map h,
      Matrix.smul_mul, Matrix.one_mul, smul_smul] at hU
    have e := congrFun (congrFun hU a₀) a₀
    simpa [Matrix.smul_apply] using e
  · rw [hPQ]
    nth_rewrite 1 [hP]
    nth_rewrite 1 [hQ']
    rw [hsc, hsc]

theorem kaPrTor_unitary (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) (a : Kˣ) :
    ((prPhi m l ((a : K) • 1) ((h.bar (a : K))⁻¹ • 1)).map h.bar)ᵀ *
      prPhi m l ((a : K) • 1) ((h.bar (a : K))⁻¹ • 1) = 1 := by
  rw [prPhi_unitary_iff h h2 hl hN, smul_one_map h, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, smul_smul, mul_inv_cancel₀ ((map_ne_zero h.bar).2 a.ne_zero), one_smul]

@[expose] noncomputable def kaPrTor (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (hN : h.norm l = -1) (a : Kˣ) : uU h (m + m) :=
  ⟨uGL h (prPhi m l ((a : K) • 1) ((h.bar (a : K))⁻¹ • 1)) (kaPrTor_unitary h h2 hl hN a),
    uGL_mem h _ _⟩

@[expose] noncomputable def kaPrTorHom (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (hN : h.norm l = -1) : Kˣ →* uU h (m + m) where
  toFun := kaPrTor h h2 hl hN
  map_one' := Subtype.ext (Units.ext (by
    change prPhi m l (((1 : Kˣ) : K) • 1) ((h.bar ((1 : Kˣ) : K))⁻¹ • 1) = 1
    simp only [Units.val_one, map_one, inv_one, one_smul]
    exact prPhi_one h2 hl))
  map_mul' a b := Subtype.ext (Units.ext (by
    change prPhi m l (((a * b : Kˣ) : K) • 1) ((h.bar ((a * b : Kˣ) : K))⁻¹ • 1) =
      prPhi m l ((a : K) • 1) ((h.bar (a : K))⁻¹ • 1) *
        prPhi m l ((b : K) • 1) ((h.bar (b : K))⁻¹ • 1)
    rw [prPhi_mul h2 hl]
    congr 1
    · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, Units.val_mul]
    · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, Units.val_mul, map_mul,
        mul_inv]))

theorem kaPr_hfix [Finite K] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m) {l : K}
    (hl : l ≠ 0) (hN : h.norm l = -1) :
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ P' : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))), IsPGroup r ↥P' →
      (∀ e ∈ P', e * uConjAut h (by omega) (uPairA (m := m) h h2 hl hN) =
        uConjAut h (by omega) (uPairA (m := m) h h2 hl hN) * e) →
      (∀ e ∈ P', ∀ x ∈ (prSLHom (m := m) h h2 hl hN).range.map
        (projH (StatedSU (m + m) (p ^ f) K)), e x = x) → IsCyclic ↥P' := by
  intro r hr hr2 P' hP' hcomm hfixP
  have : Fact p.Prime := ⟨h.prime⟩
  have hn : 3 ≤ m + m := by omega
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(m + m = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  set ρ : Kˣ →* MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)) :=
    (uConjAut h (by omega)).comp (kaPrTorHom h h2 hl hN) with hρ
  have hle : P' ≤ ρ.range := by
    intro e he
    have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hr hr2 hP' he
    obtain ⟨D, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq e
    obtain ⟨hτ, a, b, hab, hD⟩ := kaPr_form h hp2 h2 hm hl hN (D := D) (τ := τ) hodd
      (pow_orderOf_eq_one _) (hcomm _ he) (fun g hg => hfixP _ he _ ⟨g, hg, rfl⟩)
    subst hτ
    have ha0 : a ≠ 0 := fun e => by
      rw [e, map_zero, zero_mul] at hab
      exact zero_ne_one hab
    have hb : b = (h.bar a)⁻¹ := eq_inv_of_mul_eq_one_right hab
    have hDa : D = kaPrTor h h2 hl hN (Units.mk0 a ha0) :=
      Subtype.ext (Units.ext (by
        change ((D : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
          prPhi m l (((Units.mk0 a ha0 : Kˣ) : K) • 1) ((h.bar ((Units.mk0 a ha0 : Kˣ) : K))⁻¹ • 1)
        rw [hD, hb, Units.val_mk0]))
    refine ⟨Units.mk0 a ha0, ?_⟩
    rw [map_one, mul_one]
    change uConjAut h (by omega) (kaPrTor h h2 hl hN (Units.mk0 a ha0)) = _
    rw [← hDa]
  have hcycR : IsCyclic ↥ρ.range :=
    isCyclic_of_surjective ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
  exact Subgroup.isCyclic_of_le hle

end Pair

section Assembly

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m : ℕ}

theorem kaPr_all [Finite K] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m) {l : K} (hl : l ≠ 0)
    (hN : h.norm l = -1) :
    KAAll (uConjAut h (n := m + m) (by omega) (uPairA (m := m) h h2 hl hN)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hn : 3 ≤ m + m := by omega
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(m + m = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  have hnq : (m + m, p ^ f) ≠ (3, 2) := fun e => hq ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hK4 : 4 ≤ Nat.card K := by
    rw [h.card]
    have := h.prime.two_le
    have := h.one_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)
  set A₀ := uPairA (m := m) h h2 hl hN with hA₀
  set L := (prSLHom (m := m) h h2 hl hN).range with hL
  have hQ := isQuasisimple_range_prSLHom h h2 hl hN hm hK4
  have hcc := kaPr_commutator_eq h h2 hm hl hN
  have hθα : ∀ g, uConjAut h (by omega) A₀ (projH (StatedSU (m + m) (p ^ f) K) g) =
      projH (StatedSU (m + m) (p ^ f) K) (uLift h A₀ 1 g) := fun g => by
    rw [← uLift_proj h (by omega) A₀ 1 g, map_one, mul_one]
  refine ka_all_of_components_fix (ka_conj_inj_pu hK hn hnq)
    (projH (StatedSU (m + m) (p ^ f) K)) projH_surjective (uLift h A₀ 1) hθα (S := L)
    (fun g hg => mem_kaFix.1 (kaPr_range_le h h2 hl hN hg)) ?_
    (commutator_eq_self_of_isQuasisimple hQ)
    (m := 1) (fun _ => L) (fun _ => hQ) (fun _ => le_rfl) (le_iSup (fun _ : Fin 1 => L) 0)
    (fun _ x hx g hg => L.mul_mem (L.mul_mem hx hg) (L.inv_mem hx))
    (kaPr_hfix h hp2 h2 hm hl hN)
    (fun x => ka_outCentral_pu h hn hq hl (prA_mul_self h2 hl) (Or.inr hN) x)
  intro x hx g hg
  have hxα : uConjAut h (by omega) A₀ (projH (StatedSU (m + m) (p ^ f) K) x) =
      projH (StatedSU (m + m) (p ^ f) K) x := by
    rw [hθα]
    exact hx
  have hxn := ka_cover_mem_normalizer (projH (StatedSU (m + m) (p ^ f) K))
    (fun z hz g => kaPr_ker_central z hz g) (uLift h A₀ 1) hθα hxα
  have hxn' := ka_normalizer_commutator hxn
  rw [hcc] at hxn'
  exact (Subgroup.mem_normalizer_iff.1 hxn' g).1 hg

end Assembly

theorem kaU4Pair_thm : KAU4Pair := by
  intro p f K _ _ h hp2 h2 l hl hN
  exact kaPr_all h hp2 h2 (m := 2) le_rfl hl hN

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
