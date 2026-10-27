module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

section Count

variable (K) in
theorem card_matrix_of_upper (D : Fin r → Set K) (φ : Fin r → Fin r → K → K) :
    Nat.card {C : Matrix (Fin r) (Fin r) K //
        (∀ i, C i i ∈ D i) ∧ ∀ i j, j < i → C i j = φ i j (C j i)} =
      Nat.card K ^ r.choose 2 * ∏ i, Nat.card (D i) := by
  classical
  let e : {C : Matrix (Fin r) (Fin r) K //
      (∀ i, C i i ∈ D i) ∧ ∀ i j, j < i → C i j = φ i j (C j i)} ≃
      ({q : Fin r × Fin r // q.1 < q.2} → K) × ((i : Fin r) → D i) :=
    { toFun := fun C => (fun q => C.1 q.1.1 q.1.2, fun i => ⟨C.1 i i, C.2.1 i⟩)
      invFun := fun u => ⟨of fun i j => if hij : i < j then u.1 ⟨(i, j), hij⟩ else
          if i = j then (u.2 i).1 else
            if hji : j < i then φ i j (u.1 ⟨(j, i), hji⟩) else 0, fun i => by simp, by
          intro i j hji
          simp [hji, not_lt.mpr hji.le, hji.ne']⟩
      left_inv := fun C => by
        refine Subtype.ext (Matrix.ext fun i j => ?_)
        rcases lt_trichotomy i j with hij | rfl | hji
        · simp [hij]
        · simp
        · simp [hji, not_lt.mpr hji.le, hji.ne', C.2.2 i j hji]
      right_inv := fun u => by
        refine Prod.ext (funext fun q => ?_) (funext fun i => ?_)
        · simp [q.2]
        · simp }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_pi]
  congr 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_product_filter_lt,
    Fintype.card_fin]

theorem two_mul_choose_two (r : ℕ) : 2 * r.choose 2 = r * (r - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd]

variable (K) in
theorem card_isUnitriangular :
    Nat.card {A : Matrix (Fin r) (Fin r) K // IsUnitriangular A} = Nat.card K ^ r.choose 2 := by
  have := card_matrix_of_upper K (r := r) (fun _ => {1}) (fun _ _ _ => 0)
  simp only [Set.mem_singleton_iff, Nat.card_unique, Finset.prod_const_one, mul_one] at this
  rw [← this]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun A => ?_)
  exact ⟨fun hA => ⟨hA.2, fun i j hji => hA.1 hji⟩, fun hA => ⟨fun i j hji => hA.2 i j hji, hA.1⟩⟩

theorem card_trace_eq (h : UnitaryFieldData p f K) {m : K} (hm : h.bar m = m) :
    Nat.card {c : K // c + h.bar c = m} = p ^ f := by
  obtain ⟨c₀, hc₀⟩ := h.traceLin_surjective ⟨m, hm⟩
  have hc₀' : c₀ + h.bar c₀ = m := congrArg Subtype.val hc₀
  rw [← h.card_traceZero]
  refine Nat.card_congr
    { toFun := fun c => ⟨c.1 - c₀, (h.mem_traceZero).mpr (by
        rw [UnitaryFieldData.trace, map_sub]; linear_combination c.2 - hc₀')⟩
      invFun := fun t => ⟨t.1 + c₀, by
        have ht : t.1 + h.bar t.1 = 0 := (h.mem_traceZero).mp t.2
        rw [map_add]; linear_combination ht + hc₀'⟩
      left_inv := fun c => Subtype.ext (by simp)
      right_inv := fun t => Subtype.ext (by simp) }

theorem card_add_conjTranspose_eq (h : UnitaryFieldData p f K) {M : Matrix (Fin r) (Fin r) K}
    (hM : ∀ i j, h.bar (M j i) = M i j) :
    Nat.card {C : Matrix (Fin r) (Fin r) K // C + (C.map h.bar)ᵀ = M} = (p ^ f) ^ (r * r) := by
  have := card_matrix_of_upper K (fun i => {c | c + h.bar c = M i i})
    (fun i j c => M i j - h.bar c)
  have hfib : ∀ i, Nat.card ({c | c + h.bar c = M i i} : Set K) = p ^ f := fun i =>
    card_trace_eq h (hM i i)
  rw [Finset.prod_congr rfl fun i _ => hfib i, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, h.card_eq_sq, ← pow_mul, ← pow_add] at this
  rw [show r * r = 2 * r.choose 2 + r by rw [two_mul_choose_two]; cases r <;> simp; ring, ← this]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ?_)
  constructor
  · intro hC
    have hCij : ∀ i j, C i j + h.bar (C j i) = M i j := fun i j => by
      have := congrFun (congrFun hC i) j
      simpa using this
    exact ⟨fun i => hCij i i, fun i j _ => by linear_combination hCij i j⟩
  · rintro ⟨hd, hl⟩
    ext i j
    simp only [Matrix.add_apply, transpose_apply, map_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hl j i hij, map_sub, h.bar_bar, hM]
      ring
    · exact hd i
    · rw [hl i j hji]
      ring

theorem neg_vecMulVec_hermitian (h : UnitaryFieldData p f K) (x : Fin r → K) (i j : Fin r) :
    h.bar ((-vecMulVec x fun k => h.bar (x k)) j i) = (-vecMulVec x fun k => h.bar (x k)) i j := by
  simp only [Matrix.neg_apply, vecMulVec_apply, map_neg, map_mul, h.bar_bar]
  ring

theorem card_oddParam (h : UnitaryFieldData p f K) :
    Nat.card {q : (Fin r → K) × Matrix (Fin r) (Fin r) K //
        q.2 + (q.2.map h.bar)ᵀ = -vecMulVec q.1 fun j => h.bar (q.1 j)} =
      (p ^ f) ^ (2 * r) * (p ^ f) ^ (r * r) := by
  have := h.finite
  have := Fintype.ofFinite K
  classical
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun x (C : Matrix (Fin r) (Fin r) K) =>
    C + (C.map h.bar)ᵀ = -vecMulVec x fun j => h.bar (x j)), Nat.card_sigma,
    Finset.sum_congr rfl fun x _ => card_add_conjTranspose_eq h (neg_vecMulVec_hermitian h x),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_fun,
    h.card_eq_sq, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, ← pow_mul]

end Count

theorem card_hypUnitriangular_even (h : UnitaryFieldData p f K) :
    Nat.card (hypUnitriangular h r 0) =
      Nat.card K ^ r.choose 2 * (p ^ f) ^ (r * r) := by
  have hex : ∀ q : {A : Matrix (Fin r) (Fin r) K // IsUnitriangular A} ×
      {C : Matrix (Fin r) (Fin r) K // C + (C.map h.bar)ᵀ = 0},
      ∃ g ∈ hypUnitriangular h r 0,
        ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
          evenMat h q.1.1 q.2.1 := fun q =>
    (exists_mem_hypUnitriangular_even_iff _).mpr ⟨q.1.1, q.2.1, q.1.2, q.2.2, rfl⟩
  let Φ : {A : Matrix (Fin r) (Fin r) K // IsUnitriangular A} ×
      {C : Matrix (Fin r) (Fin r) K // C + (C.map h.bar)ᵀ = 0} → hypUnitriangular h r 0 :=
    fun q => ⟨(hex q).choose, (hex q).choose_spec.1⟩
  have hΦ : ∀ q, (((Φ q : hypSU h r 0) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) = evenMat h q.1.1 q.2.1 := fun q =>
    (hex q).choose_spec.2
  have hbij : Function.Bijective Φ := by
    refine ⟨fun q q' hqq => ?_, fun g => ?_⟩
    · have := congrArg (fun g : hypUnitriangular h r 0 => (((g : hypSU h r 0) :
        GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K)) hqq
      simp only [hΦ] at this
      obtain ⟨h1, h2⟩ := evenMat_inj q.1.2.isUnit_det this
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · obtain ⟨A, C, hA, hC, hg⟩ :=
        (exists_mem_hypUnitriangular_even_iff _).mp ⟨(g : hypSU h r 0), g.2, rfl⟩
      exact ⟨(⟨A, hA⟩, ⟨C, hC⟩), Subtype.ext (Subtype.ext (Units.ext (by rw [hΦ, hg])))⟩
  rw [← Nat.card_eq_of_bijective Φ hbij, Nat.card_prod, card_isUnitriangular,
    card_add_conjTranspose_eq h (M := 0) (by simp)]

theorem card_hypUnitriangular_odd (h : UnitaryFieldData p f K) :
    Nat.card (hypUnitriangular h r 1) =
      Nat.card K ^ r.choose 2 * ((p ^ f) ^ (2 * r) * (p ^ f) ^ (r * r)) := by
  have hex : ∀ q : {A : Matrix (Fin r) (Fin r) K // IsUnitriangular A} ×
      {q : (Fin r → K) × Matrix (Fin r) (Fin r) K //
        q.2 + (q.2.map h.bar)ᵀ = -vecMulVec q.1 fun j => h.bar (q.1 j)},
      ∃ g ∈ hypUnitriangular h r 1,
        ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
          oddDiag h q.1.1 1 * oddUni h q.2.1.1 q.2.1.2 := fun q =>
    (exists_mem_hypUnitriangular_odd_iff _).mpr ⟨q.1.1, q.2.1.2, q.2.1.1, q.1.2, q.2.2, rfl⟩
  let Φ : {A : Matrix (Fin r) (Fin r) K // IsUnitriangular A} ×
      {q : (Fin r → K) × Matrix (Fin r) (Fin r) K //
        q.2 + (q.2.map h.bar)ᵀ = -vecMulVec q.1 fun j => h.bar (q.1 j)} →
        hypUnitriangular h r 1 :=
    fun q => ⟨(hex q).choose, (hex q).choose_spec.1⟩
  have hΦ : ∀ q, (((Φ q : hypSU h r 1) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) = oddDiag h q.1.1 1 * oddUni h q.2.1.1 q.2.1.2 :=
    fun q => (hex q).choose_spec.2
  have hbij : Function.Bijective Φ := by
    refine ⟨fun q q' hqq => ?_, fun g => ?_⟩
    · have := congrArg (fun g : hypUnitriangular h r 1 => (((g : hypSU h r 1) :
        GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K)) hqq
      simp only [hΦ] at this
      obtain ⟨h1, h2, h3, -⟩ := oddProd_inj q.1.2.isUnit_det this
      exact Prod.ext (Subtype.ext h1) (Subtype.ext (Prod.ext h2 h3))
    · obtain ⟨A, C, x, hA, hC, hg⟩ :=
        (exists_mem_hypUnitriangular_odd_iff _).mp ⟨(g : hypSU h r 1), g.2, rfl⟩
      exact ⟨(⟨A, hA⟩, ⟨(x, C), hC⟩), Subtype.ext (Subtype.ext (Units.ext (by rw [hΦ, hg])))⟩
  rw [← Nat.card_eq_of_bijective Φ hbij, Nat.card_prod, card_isUnitriangular, card_oddParam h]

theorem card_hypUnitriangular (h : UnitaryFieldData p f K) (hε : ε ≤ 1) :
    Nat.card (hypUnitriangular h r ε) = (p ^ f) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) := by
  have hK : Nat.card K ^ r.choose 2 = (p ^ f) ^ (r * (r - 1)) := by
    rw [h.card_eq_sq, ← pow_mul, two_mul_choose_two]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [card_hypUnitriangular_even, hK, ← pow_add]
    congr 1
    rcases r with _ | s
    · simp
    · rw [show 2 * (s + 1) + 0 - 1 = 2 * s + 1 by omega,
        show (2 * (s + 1) + 0) * (2 * s + 1) = 2 * ((s + 1) * (2 * s + 1)) by ring,
        Nat.mul_div_cancel_left _ two_pos, Nat.add_sub_cancel]
      ring
  · rw [card_hypUnitriangular_odd, hK, ← pow_add, ← pow_add]
    congr 1
    rw [show 2 * r + 1 - 1 = 2 * r by omega,
      show (2 * r + 1) * (2 * r) = 2 * (r * (2 * r + 1)) by ring, Nat.mul_div_cancel_left _ two_pos]
    rcases r with _ | s
    · simp
    · rw [Nat.add_sub_cancel]
      ring

theorem card_hypSU (h : UnitaryFieldData p f K) (hn : 1 ≤ 2 * r + ε) :
    (Nat.card (hypSU h r ε) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 (2 * r + ε), (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) ∧
      p ^ (Nat.card (hypSU h r ε)).factorization p =
        (p ^ f) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) := by
  have hdim : Module.finrank K (HypIndex r ε → K) = 2 * r + ε := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  have := unitary_full_group_order h (hypForm_isSymm h) (hypForm_separatingLeft h) hdim hn
  rw [card_gramSU]
  exact ⟨this.2.1, this.2.2.2.2.2.2⟩

instance finite_hypSU (h : UnitaryFieldData p f K) : Finite (hypSU h r ε) := by
  have := h.finite
  infer_instance

theorem hypUnitriangular_inf_hypScalars (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) : hypUnitriangular h r ε ⊓ hypScalars h r ε = ⊥ := by
  rw [← Subgroup.card_eq_one]
  have h1 := Subgroup.card_dvd_of_le (inf_le_left (a := hypUnitriangular h r ε)
    (b := hypScalars h r ε))
  have h2 := Subgroup.card_dvd_of_le (inf_le_right (a := hypUnitriangular h r ε)
    (b := hypScalars h r ε))
  rw [card_hypUnitriangular h hε, ← pow_mul] at h1
  rw [card_hypScalars h (by omega)] at h2
  have hcop : Nat.Coprime (p ^ (f * ((2 * r + ε) * (2 * r + ε - 1) / 2)))
      (Nat.gcd (2 * r + ε) (p ^ f + 1)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr
      (not_dvd_gcd_pow_add_one h _))
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2

theorem hypProj_injective_on (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    Function.Injective ((hypProj h r ε).subgroupMap (hypUnitriangular h r ε)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro u hu
  rw [MonoidHom.mem_ker, Subtype.ext_iff, MonoidHom.subgroupMap_apply_coe, OneMemClass.coe_one,
    ← MonoidHom.mem_ker, ker_hypProj] at hu
  have : (u : hypSU h r ε) ∈ hypUnitriangular h r ε ⊓ hypScalars h r ε := ⟨u.2, hu⟩
  rw [hypUnitriangular_inf_hypScalars h hr hε, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (Subtype.ext this)

theorem card_hypPSU_mul (h : UnitaryFieldData p f K) :
    Nat.card (hypPSU h r ε) * Nat.card (hypScalars h r ε) = Nat.card (hypSU h r ε) :=
  (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem unitary_order_and_Sylow (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    Nat.card (hypUnitriangular h r ε) = (p ^ f) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) ∧
    (∃ P : Sylow p (hypSU h r ε), (P : Subgroup (hypSU h r ε)) = hypUnitriangular h r ε) ∧
    hypUnitriangular h r ε ⊓ hypScalars h r ε = ⊥ ∧
    (∃ e : hypUnitriangular h r ε ≃* hypProjUnitriangular h r ε,
      ∀ u, (e u : hypPSU h r ε) = hypProj h r ε u) ∧
    (∃ P : Sylow p (hypPSU h r ε), (P : Subgroup (hypPSU h r ε)) = hypProjUnitriangular h r ε) ∧
    (Nat.card (hypSU h r ε) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (2 * r + ε), (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) ∧
    Nat.card (hypPSU h r ε) = Nat.card (hypSU h r ε) / Nat.gcd (2 * r + ε) (p ^ f + 1) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hn : 1 ≤ 2 * r + ε := by omega
  obtain ⟨hS, hSp⟩ := card_hypSU h (r := r) (ε := ε) hn
  have hU := card_hypUnitriangular h (r := r) hε
  have hZ := card_hypScalars h (r := r) (ε := ε) hn
  have hPZ := card_hypPSU_mul h (r := r) (ε := ε)
  let e : hypUnitriangular h r ε ≃* hypProjUnitriangular h r ε :=
    MulEquiv.ofBijective ((hypProj h r ε).subgroupMap (hypUnitriangular h r ε))
      ⟨hypProj_injective_on h hr hε, MonoidHom.subgroupMap_surjective _ _⟩
  have hUbar : Nat.card (hypProjUnitriangular h r ε) = Nat.card (hypUnitriangular h r ε) :=
    (Nat.card_congr e.toEquiv).symm
  have hZp : ¬ p ∣ Nat.card (hypScalars h r ε) := by
    rw [hZ]
    exact not_dvd_gcd_pow_add_one h _
  have hfact : (Nat.card (hypPSU h r ε)).factorization p =
      (Nat.card (hypSU h r ε)).factorization p := by
    rw [← hPZ, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hZp, add_zero]
  have hcardU : Nat.card (hypUnitriangular h r ε) = p ^ (Nat.card (hypSU h r ε)).factorization p :=
    by rw [hU, hSp]
  have hcardUbar : Nat.card (hypProjUnitriangular h r ε) =
      p ^ (Nat.card (hypPSU h r ε)).factorization p := by rw [hUbar, hU, hfact, hSp]
  refine ⟨hU, ⟨Sylow.ofCard (hypUnitriangular h r ε) hcardU, rfl⟩,
    hypUnitriangular_inf_hypScalars h hr hε, ⟨e, fun u => rfl⟩,
    ⟨Sylow.ofCard (hypProjUnitriangular h r ε) hcardUbar, rfl⟩, hS, ?_⟩
  rw [← hPZ, hZ, Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_right _ (Nat.succ_pos _))]

end CFSG.ClassicalGroups.UnitaryFlag
