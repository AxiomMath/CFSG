module

public import CFSG.ClassicalInvolution.Asc77.AscSCH19
public import CFSG.ClassicalInvolution.Asc77.AscSCH07
public import CFSG.RankThree.CentralLift.ClassicalScalarCover

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.CentralLift

variable {K : Type} [Field K]

theorem torusGL_mul {r : ℕ} (a b : Fin r → Kˣ) :
    torusGL (fun i => a i * b i) = torusGL a * torusGL b := by
  apply Units.ext
  rw [Units.val_mul, coe_torusGL, coe_torusGL, coe_torusGL, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal,
    Units.val_mul, mul_inv]

theorem torusGL_injective_two {r : ℕ} {a b : Fin r → Kˣ}
    (h : torusGL a = (torusGL b : GL (Fin r ⊕ Fin r) K)) :
    a = b := by
  funext i
  apply Units.ext
  have := congrFun (congrFun (congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
    (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h) (Sum.inl i)) (Sum.inl i)
  simpa [coe_torusGL] using this

@[expose] def fixU (K : Type) [Field K] (q : ℕ) : Subgroup Kˣ := (powMonoidHom (q - 1)).ker

theorem mem_fixU {q : ℕ} {c : Kˣ} : c ∈ fixU K q ↔ c ^ (q - 1) = 1 := Iff.rfl

theorem card_fixU [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card (fixU K q) = q - 1 := by
  rw [fixU, IsCyclic.card_powMonoidHom_ker, card_units_eq, hK]
  have hq : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, h] at this
      simp at this
    · exact h
  have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [hq, Nat.one_le_pow 2 q hq]
    ring
  rw [this, Nat.gcd_mul_left_left]

theorem bar_fixU {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) {c : Kˣ} (hc : c ∈ fixU K (ℓ ^ f)) :
    h.bar (c : K) = c := by
  rw [UnitaryFieldData.bar_apply]
  have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have h1 : ((c : K)) ^ (ℓ ^ f - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, mem_fixU.1 hc, Units.val_one]
  calc (c : K) ^ ℓ ^ f = (c : K) ^ (ℓ ^ f - 1) * (c : K) := by
        rw [← pow_succ, Nat.sub_add_cancel hq]
    _ = c := by rw [h1, one_mul]

section Hyp

variable {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)

theorem torusGL_pair_mem (a b : fixU K (ℓ ^ f)) :
    torusGL ![(a : Kˣ), (b : Kˣ)] ∈ gramSU h (hypGram2 2 K) :=
  torusGL_mem_gramSU h (fun i => by
    fin_cases i
    · exact bar_fixU h a.2
    · exact bar_fixU h b.2)

@[expose] noncomputable def suTorusHom :
    fixU K (ℓ ^ f) × fixU K (ℓ ^ f) →* gramSU h (hypGram2 2 K) where
  toFun x := ⟨torusGL ![(x.1 : Kˣ), (x.2 : Kˣ)], torusGL_pair_mem h x.1 x.2⟩
  map_one' := by
    apply Subtype.ext
    change torusGL ![((1 : fixU K (ℓ ^ f)) : Kˣ), ((1 : fixU K (ℓ ^ f)) : Kˣ)] = 1
    have : (![((1 : fixU K (ℓ ^ f)) : Kˣ), ((1 : fixU K (ℓ ^ f)) : Kˣ)] : Fin 2 → Kˣ) =
        fun _ => 1 := by
      funext i
      fin_cases i <;> rfl
    rw [this, torusGL_const_one]
  map_mul' x y := by
    apply Subtype.ext
    change torusGL ![((x.1 * y.1 : fixU K (ℓ ^ f)) : Kˣ), ((x.2 * y.2 : fixU K (ℓ ^ f)) : Kˣ)] =
      torusGL ![(x.1 : Kˣ), (x.2 : Kˣ)] * torusGL ![(y.1 : Kˣ), (y.2 : Kˣ)]
    rw [← torusGL_mul]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem suTorusHom_injective : Function.Injective (suTorusHom h) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hx
  have h1 : torusGL ![(a : Kˣ), (b : Kˣ)] =
      (torusGL ![(a' : Kˣ), (b' : Kˣ)] : GL (Fin 2 ⊕ Fin 2) K) :=
    congrArg (fun g : gramSU h (hypGram2 2 K) => (g : GL (Fin 2 ⊕ Fin 2) K)) hx
  have h2 := torusGL_injective_two h1
  have e0 := congrFun h2 0
  have e1 := congrFun h2 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
  exact Prod.ext (Subtype.ext e0) (Subtype.ext e1)

@[expose] def swapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0]

theorem swap2_mul_self : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem swapMat_mul_self : swapMat * swapMat = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  rw [swapMat, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, swap2_mul_self, fromBlocks_one]

@[expose] def swapGL : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩

theorem coe_swapGL : ((swapGL : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
    swapMat := rfl

theorem swapGL_mem : (swapGL : GL (Fin 2 ⊕ Fin 2) K) ∈ gramSU h (hypGram2 2 K) := by
  have hP : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).map h.bar = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hPt : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · change (swapMat.map h.bar)ᵀ * hypGram2 2 K * swapMat = hypGram2 2 K
    rw [swapMat, hypGram2, fromBlocks_map, fromBlocks_transpose, hP, hPt, fromBlocks_multiply,
      fromBlocks_multiply]
    simp only [Matrix.map_zero _ (map_zero h.bar), Matrix.transpose_zero, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, swap2_mul_self]
  · change swapMat.det = 1
    rw [swapMat, det_fromBlocks_zero₂₁]
    simp [Matrix.det_fin_two]

theorem swapGL_conj_torus (a b : Kˣ) :
    swapGL * torusGL ![a, b] * swapGL⁻¹ = (torusGL ![b, a] : GL (Fin 2 ⊕ Fin 2) K) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swapGL, coe_torusGL, coe_torusGL, swapMat,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem factorization_su4_le_one {q : ℕ} (h3 : 3 ∣ q - 1) (hq : 2 ≤ q) :
    (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)).factorization 3 ≤
      2 * (q - 1).factorization 3 := by
  have hq3 : q % 3 = 1 := by omega
  have hqn : ¬ 3 ∣ q := by omega
  have hq1 : ¬ 3 ∣ q + 1 := by omega
  have hq2 : ¬ 3 ∣ q ^ 2 + 1 := by
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hq4 : ¬ 3 ∣ q ^ 2 - q + 1 := by
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega
  have hq1' : 1 ≤ q := by omega
  have d2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [hq1', Nat.one_le_pow 2 q hq1']
    ring
  have d3 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    zify [hq1', hqq]
    ring
  have d4 : q ^ 4 - 1 = (q - 1) * ((q + 1) * (q ^ 2 + 1)) := by
    zify [hq1', Nat.one_le_pow 4 q hq1']
    ring
  have n1 : q - 1 ≠ 0 := by omega
  have n2 : q + 1 ≠ 0 := by omega
  have n3 : q ^ 2 - q + 1 ≠ 0 := by omega
  have n4 : q ^ 2 + 1 ≠ 0 := by positivity
  have n5 : q ≠ 0 := by omega
  rw [d2, d3, d4, fac_mul (by positivity) (by positivity), fac_mul (by positivity) (by positivity),
    fac_mul (by positivity) (by positivity), fac_mul n1 n2, fac_mul n2 n3,
    fac_mul n1 (by positivity), fac_mul n2 n4, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul, fac_zero hqn, fac_zero hq1, fac_zero hq2, fac_zero hq4]
  omega

theorem exists_statedSU_equiv_gramSU {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) :
    Nonempty (StatedSU 4 (ℓ ^ f) K ≃* gramSU h (hypGram2 2 K)) := by
  have := h.finite
  obtain ⟨e⟩ := nonempty_statedSU_mulEquiv_sesq h 4
  have hsymm := gramForm_isSymm h (G := (1 : Matrix (Fin 4) (Fin 4) K))
    (by rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one])
  have hsep := gramForm_separatingLeft h (G := (1 : Matrix (Fin 4) (Fin 4) K))
    (by rw [Matrix.det_one]; exact one_ne_zero)
  obtain ⟨b, hb⟩ := exists_basis_hypGram2 h hsymm hsep (r := 2) (by rw [Module.finrank_fin_fun])
  obtain ⟨φ⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h b hb
  exact ⟨e.trans φ⟩

section Perfect

variable {E : Type*} [Group E]

theorem gramSU_hyp_perfect_ker_eq_bot_one {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)
    (h3 : 3 ∣ ℓ ^ f - 1) [Finite E] [Group.IsPerfect E] (π : E →* gramSU h (hypGram2 2 K))
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 3 π.ker) :
    π.ker = ⊥ := by
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hℓ := h.prime
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, pow_mul']
  have hq2 : 2 ≤ ℓ ^ f := by
    have hf1 := h.one_le
    have := Nat.one_lt_pow (n := f) (by omega) hℓ.one_lt
    omega
  obtain ⟨φ⟩ := exists_statedSU_equiv_gramSU h
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := fixU K (ℓ ^ f))
  have hord : orderOf t = ℓ ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht, card_fixU hK2]
  have hcz : Nat.card (Subgroup.zpowers t) = ℓ ^ f - 1 := by rw [Nat.card_zpowers, hord]
  refine ker_eq_bot_of_blocks (by norm_num) π hπ hC hCp
    ((suTorusHom h).comp (MonoidHom.inl _ _)) ((suTorusHom h).comp (MonoidHom.inr _ _))
    ((suTorusHom_injective h).comp (fun a b hab => congrArg Prod.fst hab))
    ((suTorusHom_injective h).comp (fun a b hab => congrArg Prod.snd hab)) ?_ ?_
    ⟨swapGL, swapGL_mem h⟩ ?_ ?_ t ?_
  · intro a b
    simp only [MonoidHom.comp_apply, ← map_mul]
    congr 1
    ext <;> simp
  · intro a b hab
    have h1 := suTorusHom_injective h hab
    have h2 : a = 1 := congrArg Prod.fst h1
    simp only [h2, map_one]
  · intro a
    apply Subtype.ext
    change swapGL * torusGL ![((a : fixU K (ℓ ^ f)) : Kˣ), ((1 : fixU K (ℓ ^ f)) : Kˣ)] *
      swapGL⁻¹ = torusGL ![((1 : fixU K (ℓ ^ f)) : Kˣ), ((a : fixU K (ℓ ^ f)) : Kˣ)]
    rw [swapGL_conj_torus]
  · intro a
    apply Subtype.ext
    change swapGL * torusGL ![((1 : fixU K (ℓ ^ f)) : Kˣ), ((a : fixU K (ℓ ^ f)) : Kˣ)] *
      swapGL⁻¹ = torusGL ![((a : fixU K (ℓ ^ f)) : Kˣ), ((1 : fixU K (ℓ ^ f)) : Kˣ)]
    rw [swapGL_conj_torus]
  · rw [hcz, Nat.card_congr φ.symm.toEquiv, card_statedSU_four h]
    exact factorization_su4_le_one h3 hq2

theorem statedSU_four_perfect_ker_eq_bot_one {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)
    (h3 : 3 ∣ ℓ ^ f - 1) [Finite E] [Group.IsPerfect E] (π : E →* StatedSU 4 (ℓ ^ f) K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 3 π.ker) :
    π.ker = ⊥ := by
  obtain ⟨φ⟩ := exists_statedSU_equiv_gramSU h
  have hker : (φ.toMonoidHom.comp π).ker = π.ker :=
    MonoidHom.ker_comp_of_injective _ _ φ.injective
  have := gramSU_hyp_perfect_ker_eq_bot_one h h3 (φ.toMonoidHom.comp π) (φ.surjective.comp hπ)
    (hker ▸ hC) (hker ▸ hCp)
  rwa [hker] at this

end Perfect

end Hyp

end CFSG.ClassicalInvolution.Asc77.SCH
