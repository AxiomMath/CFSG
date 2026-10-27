module

public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Assembly.LowTwoRank

theorem prod_pow_add_one_aux (q : ℕ) (hq : 2 ≤ q) (m : ℕ) :
    2 ^ m * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i + 1) + ∏ i ∈ Finset.Icc 2 (m + 1), q ^ i ≤
      2 ^ (m + 1) * ∏ i ∈ Finset.Icc 2 (m + 1), q ^ i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hA' := Finset.prod_Icc_succ_top (show 2 ≤ m + 1 + 1 by omega) (fun i => q ^ i + 1)
    have hB' := Finset.prod_Icc_succ_top (show 2 ≤ m + 1 + 1 by omega) (fun i => q ^ i)
    rw [hA', hB']
    set A := ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i + 1)
    set B := ∏ i ∈ Finset.Icc 2 (m + 1), q ^ i
    set Q := q ^ (m + 1 + 1)
    have hQ : 2 ^ (m + 2) ≤ Q := Nat.pow_le_pow_left hq _
    have e1 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have e2 : 2 ^ (m + 1 + 1) = 4 * 2 ^ m := by ring
    have e3 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
    rw [e3] at hQ
    rw [e1] at ih
    rw [e1, e2]
    have h1 := Nat.mul_le_mul_left (2 * (Q + 1)) ih
    have h2 := Nat.mul_le_mul_left B hQ
    nlinarith [h1, h2]

theorem prod_pow_add_one_le (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    ∏ i ∈ Finset.Icc 2 n, (q ^ i + 1) ≤ 2 * ∏ i ∈ Finset.Icc 2 n, q ^ i := by
  rcases n with _ | m
  · simp
  have h := prod_pow_add_one_aux q hq m
  have hB : 0 < ∏ i ∈ Finset.Icc 2 (m + 1), q ^ i :=
    Finset.prod_pos fun i _ => pow_pos (by omega) i
  have e1 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  rw [e1] at h
  refine Nat.le_of_mul_le_mul_left (c := 2 ^ m) ?_ (pow_pos (by norm_num) m)
  nlinarith [h, hB]

theorem sum_Icc_two_aux (m : ℕ) : (∑ i ∈ Finset.Icc 2 (m + 1), i) * 2 + 2 = (m + 1) * (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    nlinarith [ih]

theorem card_statedSU_le {K : Type} [Field K] [Finite K] {p e n : ℕ} [Fact p.Prime]
    (hK : Nat.card K = (p ^ e) ^ 2) (hn : 1 ≤ n) :
    Nat.card (StatedSU n (p ^ e) K) ≤ 2 * (p ^ e) ^ (n ^ 2 - 1) := by
  have he : 1 ≤ e := by
    by_contra h0
    have : e = 0 := by omega
    subst this
    have h1 := Finite.one_lt_card (α := K)
    rw [hK] at h1
    simp at h1
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p e K :=
    ⟨Fact.out, he, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq2 : 2 ≤ p ^ e := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set q := p ^ e with hqdef
  have hprod : ∏ i ∈ Finset.Icc 2 (m + 1), ((q : ℤ) ^ i - (-1) ^ i) ≤
      ((∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i + 1) : ℕ) : ℤ) := by
    push_cast
    refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
    · have h1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ q))
      rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> omega
    · rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> omega
  have hcard : (Nat.card (StatedSU (m + 1) q K) : ℤ) ≤
      (q : ℤ) ^ ((m + 1) * (m + 1 - 1) / 2) *
        ((∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i + 1) : ℕ) : ℤ) := by
    rw [hint]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  have hnat : Nat.card (StatedSU (m + 1) q K) ≤
      q ^ ((m + 1) * (m + 1 - 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i + 1) := by
    exact_mod_cast hcard
  have hA := prod_pow_add_one_le q hq2 (m + 1)
  rw [Finset.prod_pow_eq_pow_sum] at hA
  have hS := sum_Icc_two_aux m
  have hT : 2 * ((m + 1) * (m + 1 - 1) / 2) = (m + 1) * m := by
    have : (m + 1) * (m + 1 - 1) = (m + 1) * m := by simp
    rw [this]
    exact Nat.mul_div_cancel' (by
      have := Nat.even_mul_succ_self m
      rw [mul_comm] at this
      exact even_iff_two_dvd.1 this)
  have hexp : (m + 1) * (m + 1 - 1) / 2 + ∑ i ∈ Finset.Icc 2 (m + 1), i = (m + 1) ^ 2 - 1 := by
    have h2 : (m + 1) ^ 2 = (m + 1) * (m + 1) := by ring
    have h3 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have key : (m + 1) * (m + 1 - 1) / 2 + ∑ i ∈ Finset.Icc 2 (m + 1), i + 1 = (m + 1) ^ 2 := by
      nlinarith [hT, hS]
    omega
  calc Nat.card (StatedSU (m + 1) q K)
      ≤ q ^ ((m + 1) * (m + 1 - 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i + 1) := hnat
    _ ≤ q ^ ((m + 1) * (m + 1 - 1) / 2) * (2 * q ^ ∑ i ∈ Finset.Icc 2 (m + 1), i) :=
        Nat.mul_le_mul_left _ hA
    _ = 2 * q ^ ((m + 1) ^ 2 - 1) := by
        rw [← hexp, pow_add]
        ring


open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section GU

variable {K : Type} [Field K] {p e : ℕ}

@[expose] def unitGU (h : UnitaryFieldData p e K) (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {g | ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1}
  mul_mem' {g g'} hg hg' := by
    have hg : ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1 := hg
    have hg' : ((g' : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (g' : Matrix (Fin n) (Fin n) K) = 1 :=
      hg'
    have key := conjTranspose_mul_mul h (1 : Matrix (Fin n) (Fin n) K) (g : Matrix (Fin n) (Fin n) K)
      (g' : Matrix (Fin n) (Fin n) K)
    simp only [Matrix.mul_one, hg, hg'] at key
    show (((g * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((g * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Units.val_mul]
    exact key
  one_mem' := by simp
  inv_mem' {g} hg := by
    have hg1 : ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * 1 * (g : Matrix (Fin n) (Fin n) K) =
        1 := by
      rw [Matrix.mul_one]
      exact hg
    have hgg : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have key := conjTranspose_mul_mul h (1 : Matrix (Fin n) (Fin n) K) (g : Matrix (Fin n) (Fin n) K)
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hg1, hgg] at key
    simpa using key.symm

theorem mem_unitGU {h : UnitaryFieldData p e K} {n : ℕ} {g : GL (Fin n) K} :
    g ∈ unitGU h n ↔
      ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1 :=
  Iff.rfl

theorem statedSU_le_unitGU (h : UnitaryFieldData p e K) (n : ℕ) :
    StatedSU n (p ^ e) K ≤ unitGU h n := by
  intro g hg
  have hg' : g ∈ unitarySU p e K n := hg
  rw [unitarySU_eq_gramSU h n, mem_gramSU, Matrix.mul_one] at hg'
  exact hg'.1

theorem card_unitGU_le [Finite K] (h : UnitaryFieldData p e K) (n : ℕ) :
    Nat.card (unitGU h n) ≤ (p ^ e + 1) * Nat.card (StatedSU n (p ^ e) K) := by
  let f : unitGU h n →* Kˣ := (Matrix.GeneralLinearGroup.det).comp (unitGU h n).subtype
  have hker : f.ker = (StatedSU n (p ^ e) K).subgroupOf (unitGU h n) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hg : (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := g.2
    have hmem : (g : GL (Fin n) K) ∈ StatedSU n (p ^ e) K ↔
        (g : GL (Fin n) K) ∈ unitarySU p e K n := Iff.rfl
    rw [hmem, unitarySU_eq_gramSU h n, mem_gramSU]
    constructor
    · intro hd
      refine ⟨by rw [Matrix.mul_one]; exact hg, ?_⟩
      have := congrArg Units.val hd
      simpa [f, Matrix.GeneralLinearGroup.val_det_apply] using this
    · rintro ⟨-, hd⟩
      apply Units.ext
      simpa [f, Matrix.GeneralLinearGroup.val_det_apply] using hd
  have hrange : f.range ≤ rootsOfUnity (p ^ e + 1) K := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity']
    have hg : (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := g.2
    have hdet := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
    have h1 : (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar).det =
        h.bar (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) := by
      rw [RingHom.map_det]
      rfl
    rw [h1, h.bar_apply] at hdet
    have : ((f g : Kˣ) : K) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
      simp [f, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this, pow_succ]
    exact hdet
  have hcard1 : Nat.card f.ker * Nat.card f.range = Nat.card (unitGU h n) := by
    have h1 := Subgroup.card_mul_index f.ker
    rwa [Subgroup.index_ker] at h1
  have hcard2 : Nat.card f.ker = Nat.card (StatedSU n (p ^ e) K) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (statedSU_le_unitGU h n)).toEquiv
  have hcard3 : Nat.card f.range ≤ p ^ e + 1 :=
    (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity K (p ^ e + 1))
  rw [← hcard1, hcard2, mul_comm]
  exact Nat.mul_le_mul_right _ hcard3

theorem scalar_mem_unitGU (h : UnitaryFieldData p e K) {n : ℕ} (c : Kˣ)
    (hc : c ^ (p ^ e + 1) = 1) : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ unitGU h n := by
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
  have hm : ((c : K) • (1 : Matrix (Fin n) (Fin n) K)).map h.bar = h.bar c • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hcK : (c : K) ^ (p ^ e + 1) = 1 := by
    have := congrArg Units.val hc
    simpa using this
  rw [mem_unitGU, hs, hm, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, h.bar_apply, ← pow_succ, hcK, one_smul]

theorem le_card_center_unitGU [Finite K] [Fact p.Prime] (h : UnitaryFieldData p e K)
    (hK : Nat.card K = (p ^ e) ^ 2) {n : ℕ} (hn : 1 ≤ n) :
    p ^ e + 1 ≤ Nat.card ((Subgroup.center (GL (Fin n) K)).subgroupOf (unitGU h n)) := by
  have : NeZero n := ⟨by omega⟩
  have hq : 1 ≤ p ^ e := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hN : Nat.card (powMonoidHom (p ^ e + 1) : Kˣ →* Kˣ).ker = p ^ e + 1 := by
    rw [IsCyclic.card_powMonoidHom_ker]
    have hu : Nat.card Kˣ = (p ^ e) ^ 2 - 1 := by
      classical
      have := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    rw [hu]
    apply Nat.gcd_eq_right
    obtain ⟨r, hr⟩ : ∃ r, p ^ e = r + 1 := ⟨p ^ e - 1, by omega⟩
    rw [hr]
    exact ⟨r, by
      apply Nat.sub_eq_of_eq_add
      ring⟩
  let φ : (powMonoidHom (p ^ e + 1) : Kˣ →* Kˣ).ker →
      ((Subgroup.center (GL (Fin n) K)).subgroupOf (unitGU h n)) := fun c =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin n) (c : Kˣ),
      scalar_mem_unitGU h (c : Kˣ) (by simpa using MonoidHom.mem_ker.1 c.2)⟩, by
        rw [Subgroup.mem_subgroupOf, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨(c : Kˣ), rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg (fun z : ((Subgroup.center (GL (Fin n) K)).subgroupOf (unitGU h n)) =>
      ((z : unitGU h n) : GL (Fin n) K)) hab
    have h2 := congrArg (fun A : GL (Fin n) K =>
      (A : Matrix (Fin n) (Fin n) K) ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
        ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) h1
    simp [φ, Matrix.GeneralLinearGroup.scalar] at h2
    exact Subtype.ext (Units.ext h2)
  rw [← hN]
  exact Nat.card_le_card_of_injective φ hφ

theorem unitaryFieldData_of_card [Finite K] [Fact p.Prime] (hK : Nat.card K = (p ^ e) ^ 2) :
    UnitaryFieldData p e K := by
  refine ⟨Fact.out, ?_, by rw [hK, ← pow_mul, mul_comm]⟩
  by_contra h0
  have : e = 0 := by omega
  subst this
  have h1 := Finite.one_lt_card (α := K)
  rw [hK] at h1
  simp at h1

end GU

section Aut

open CFSG.ComponentClassification.RankTwoClassical

variable {K : Type} [Field K] [Finite K] {p e n : ℕ} [Fact p.Prime]

theorem card_mulAut_psu_le (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ e) ^ 2) (hn : 3 ≤ n) :
    Nat.card (MulAut (StatedProj (StatedSU n (p ^ e) K))) ≤
      2 * e * Nat.card (StatedSU n (p ^ e) K) := by
  have hU := unitaryFieldData_of_card (K := K) hK
  have hq3 : ¬(n = 3 ∧ p ^ e = 2) := by
    rintro ⟨-, h2⟩
    have hodd : Odd (p ^ e) := ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
    rw [h2] at hodd
    exact absurd hodd (by decide)
  have hrep := fun β : MulAut (StatedProj (StatedSU n (p ^ e) K)) =>
    exists_unitary_semilinear_statedProj hU hn hq3 β
  choose σ A hA hrep using hrep
  let Z : Subgroup (unitGU hU n) :=
    (Subgroup.center (GL (Fin n) K)).subgroupOf (unitGU hU n)
  let Θ : MulAut (StatedProj (StatedSU n (p ^ e) K)) → (K ≃+* K) × (unitGU hU n ⧸ Z) :=
    fun β => (σ β, QuotientGroup.mk ⟨A β, mem_unitGU.2 (hA β)⟩)
  have hΘ : Function.Injective Θ := by
    intro β β' hθ
    obtain ⟨hσ, hq⟩ := Prod.mk.inj hθ
    have hz := QuotientGroup.eq.1 hq
    have hc : (A β)⁻¹ * A β' ∈ Subgroup.center (GL (Fin n) K) := by
      have := Subgroup.mem_subgroupOf.1 hz
      simpa using this
    have hcomm := Subgroup.mem_center_iff.1 hc
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨hg, h1⟩ := hrep β g
      obtain ⟨hg', h2⟩ := hrep β' g
      rw [h1, h2]
      congr 1
      apply Subtype.ext
      show A β * glAut (σ β) (g : GL (Fin n) K) * (A β)⁻¹ =
        A β' * glAut (σ β') (g : GL (Fin n) K) * (A β')⁻¹
      rw [← hσ]
      set X := glAut (σ β) (g : GL (Fin n) K)
      set c := (A β)⁻¹ * A β' with hcdef
      have hAβ' : A β' = A β * c := by rw [hcdef]; group
      have hcX : c * X * c⁻¹ = X := mul_inv_eq_of_eq_mul (hcomm X).symm
      calc A β * X * (A β)⁻¹ = A β * (c * X * c⁻¹) * (A β)⁻¹ := by rw [hcX]
        _ = A β' * X * (A β')⁻¹ := by rw [hAβ']; group
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) (fun a b h => RingEquiv.ext (congrFun h))
  have h1 := Nat.card_le_card_of_injective Θ hΘ
  rw [Nat.card_prod] at h1
  have hAut : Nat.card (K ≃+* K) = 2 * e :=
    (card_ringAut_and_isCyclic (Fact.out : p.Prime) K (by rw [hK, ← pow_mul, mul_comm])).1
  have hZ := le_card_center_unitGU hU hK (by omega : 1 ≤ n)
  have hGU := card_unitGU_le hU n
  have hmul : Nat.card Z * Nat.card (unitGU hU n ⧸ Z) = Nat.card (unitGU hU n) :=
    Subgroup.card_mul_index Z
  have hquot : Nat.card (unitGU hU n ⧸ Z) ≤ Nat.card (StatedSU n (p ^ e) K) := by
    have hpos : 0 < p ^ e + 1 := by omega
    refine Nat.le_of_mul_le_mul_left (c := p ^ e + 1) ?_ hpos
    calc (p ^ e + 1) * Nat.card (unitGU hU n ⧸ Z)
        ≤ Nat.card Z * Nat.card (unitGU hU n ⧸ Z) := Nat.mul_le_mul_right _ hZ
      _ = Nat.card (unitGU hU n) := hmul
      _ ≤ (p ^ e + 1) * Nat.card (StatedSU n (p ^ e) K) := hGU
  calc Nat.card (MulAut (StatedProj (StatedSU n (p ^ e) K)))
      ≤ Nat.card (K ≃+* K) * Nat.card (unitGU hU n ⧸ Z) := h1
    _ ≤ 2 * e * Nat.card (StatedSU n (p ^ e) K) := by
        rw [hAut]
        exact Nat.mul_le_mul_left _ hquot

end Aut

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
