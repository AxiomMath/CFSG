module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASymplecticExclusion
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalDihedralLinearModel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCLinearDegree
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Matrix CFSG.Assembly.LowTwoRank

namespace UnitaryExclusion

variable {K : Type} [Field K]

theorem reindex_fromBlocks_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : Fin 2 ⊕ ι ≃ κ) {φ : K → K} (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    {B : Matrix (Fin 2) (Fin 2) K} (hB : (B.map φ)ᵀ * B = 1) :
    ((reindex e e (fromBlocks B 0 0 1)).map φ)ᵀ * reindex e e (fromBlocks B 0 0 1) = 1 := by
  rw [reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
    fromBlocks_map, Matrix.map_zero _ h0, Matrix.map_zero _ h0, Matrix.map_one _ h0 h1,
    fromBlocks_transpose, fromBlocks_multiply, hB]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    transpose_zero, transpose_one, fromBlocks_one, submatrix_one_equiv]

variable {d : ℕ}

theorem slTwoToGL_mem_statedSU (hd : 2 ≤ d) {q : ℕ} (hq : q ≠ 0)
    (B : SpecialLinearGroup (Fin 2) K)
    (hB : ((B : Matrix (Fin 2) (Fin 2) K).map (· ^ q))ᵀ * (B : Matrix (Fin 2) (Fin 2) K) = 1) :
    OutcomeLocal.slTwoToGL hd B ∈ StatedSU d q K :=
  Subgroup.subset_closure ⟨OutcomeLocal.det_slTwoToGL hd B, by
    rw [OutcomeLocal.coe_slTwoToGL]
    exact reindex_fromBlocks_unitary _ (zero_pow hq) (one_pow q) hB⟩

theorem unitary_rot {q : ℕ} (hq : Odd q) :
    ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).map (· ^ q))ᵀ * !![0, 1; -1, 0] = 1 := by
  have h0 : (0 : K) ^ q = 0 := zero_pow (by rintro rfl; simp at hq)
  have hn : (-1 : K) ^ q = -1 := hq.neg_one_pow
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, hn]

theorem unitary_neg_pair {q : ℕ} (hq : Odd q) {a b : K} (ha : a ^ q = -a) (hb : b ^ q = -b)
    (hab : a ^ 2 + b ^ 2 = -1) :
    ((!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) K).map (· ^ q))ᵀ * !![a, b; b, -a] = 1 := by
  have hna : (-a) ^ q = a := by rw [hq.neg_pow, ha, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hna] <;>
    first | ring1 | linear_combination -hab

theorem exists_neg_pair [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ a b : K, a ^ p ^ f = -a ∧ b ^ p ^ f = -b ∧ a ^ 2 + b ^ 2 = -1 := by
  obtain ⟨δ, hδ0, hδ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hδ
  set φ : K →+* K := (CFSG.LieType.BorelTits.unitaryInvolution K p f).toRingHom with hφ
  have hφc : ∀ c : K, φ c = c ^ p ^ f := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_apply K p f c
  set S : Subfield K := φ.eqLocusField (RingHom.id K) with hS
  have hmemS : ∀ c : K, c ∈ S ↔ c ^ p ^ f = c := fun c => by
    rw [← hφc]
    exact Iff.rfl
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
  have hS2 : ringChar S ≠ 2 := by
    intro h
    have h' := ringChar.Nat.cast_ringChar (R := S)
    rw [h] at h'
    apply h2
    have h3 := congrArg S.subtype h'
    rw [map_natCast, map_zero] at h3
    exact_mod_cast h3
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hδ2 : (δ ^ 2) ^ p ^ f = δ ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, hδ, neg_sq]
  have hc : -(δ ^ 2)⁻¹ ∈ S := by
    rw [hmemS, neg_pow, inv_pow, hδ2, hodd.neg_one_pow, neg_one_mul]
  obtain ⟨a', b', hab'⟩ := LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hS2 ⟨_, hc⟩
  have hab'' : (a' : K) ^ 2 + (b' : K) ^ 2 = -(δ ^ 2)⁻¹ := by
    have := congrArg (fun x : S => (x : K)) hab'
    simpa using this
  have ha' : (a' : K) ^ p ^ f = a' := (hmemS a').mp a'.2
  have hb' : (b' : K) ^ p ^ f = b' := (hmemS b').mp b'.2
  refine ⟨δ * a', δ * b', ?_, ?_, ?_⟩
  · rw [mul_pow, hδ, ha', neg_mul]
  · rw [mul_pow, hδ, hb', neg_mul]
  · calc (δ * a') ^ 2 + (δ * b') ^ 2 = δ ^ 2 * ((a' : K) ^ 2 + (b' : K) ^ 2) := by ring
      _ = δ ^ 2 * -(δ ^ 2)⁻¹ := by rw [hab'']
      _ = -1 := by rw [mul_neg, mul_inv_cancel₀ (pow_ne_zero 2 hδ0)]

end UnitaryExclusion

open UnitaryExclusion

theorem dihedral_sylow_unitary_model_exclusion {T : Type} [Group T] {d p f : ℕ}
    (hT : StatedClassicalModel T .PSU d p f) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rintro ⟨eP⟩
  obtain ⟨⟨hp, hf, hd, hd32⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
  have : Finite T := Finite.of_equiv _ eT.symm.toEquiv
  obtain ⟨hrank, hQ8⟩ :=
    SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, ⟨eP⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hchar : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK2
  have hd2 : 2 ≤ d := by omega
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    have h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, hK2⟩
    have hdeg : 2 ^ (s - 2) < d := by
      have hne : NeZero (2 ^ (s - 1)) := ⟨by positivity⟩
      have hord : orderOf (eT ((eP.symm (DihedralGroup.r 1) : P) : T)) = 2 ^ (s - 1) := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
          DihedralGroup.orderOf_r_one]
      have h1 := characteristic_two_linear_quotient_two_element_degree_bound (k := K)
        (by omega : 1 ≤ d) (by omega : 1 ≤ s - 1) (StatedSU d (2 ^ f) K)
        ((StatedScalars (Fin d) K).subgroupOf (StatedSU d (2 ^ f) K)) _ hord
      have hs2 : s - 1 - 1 = s - 2 := by omega
      rwa [hs2] at h1
    have hsd : s ≤ d := by
      have := Nat.lt_two_pow_self (n := s - 2)
      omega
    obtain ⟨r, ε, rfl, hr, hε⟩ : ∃ r ε : ℕ, d = 2 * r + ε ∧ 1 ≤ r ∧ ε ≤ 1 :=
      ⟨d / 2, d % 2, by omega, by omega, by omega⟩
    obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := r) (ε := ε) h
    let E : T ≃* CFSG.ClassicalGroups.UnitaryFlag.hypPSU h r ε :=
      eT.trans (CFSG.ClassicalGroups.UnitaryFlag.hypPSUEquivStatedProj h hR (by omega)).symm
    obtain ⟨hUcard, -, -, ⟨eU, -⟩, ⟨P', hP'⟩, -, -⟩ :=
      CFSG.ClassicalGroups.UnitaryFlag.unitary_order_and_Sylow h hr hε
    have hP'card : Nat.card P' = (2 ^ f) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) := by
      rw [hP', ← Nat.card_congr eU.toEquiv, hUcard]
    have hPcard : Nat.card (P : Subgroup T) = 2 ^ s := by
      rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card, ← pow_succ']
      congr 1
      omega
    have hcard : Nat.card (P : Subgroup T) = Nat.card P' := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, Nat.card_congr E.toEquiv]
    rw [hPcard, hP'card, ← pow_mul] at hcard
    have hsM : s = f * ((2 * r + ε) * (2 * r + ε - 1) / 2) :=
      Nat.pow_right_injective le_rfl hcard
    have hfM : (2 * r + ε) * (2 * r + ε - 1) / 2 ≤ f * ((2 * r + ε) * (2 * r + ε - 1) / 2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rcases Nat.lt_or_ge (2 * r + ε) 4 with h4 | h4
    ·
      have hD3 : 2 * r + ε = 3 := by omega
      have hM3 : (2 * r + ε) * (2 * r + ε - 1) / 2 = 3 := by rw [hD3]
      rw [hM3] at hsM
      have hf1 : f = 1 := by omega
      exact hd32 (by rw [hD3, hf1]; rfl)
    ·
      have h1 : (2 * r + ε) * 3 ≤ (2 * r + ε) * (2 * r + ε - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : (2 * r + ε) * 3 / 2 ≤ (2 * r + ε) * (2 * r + ε - 1) / 2 :=
        Nat.div_le_div_right h1
      omega
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    have hkchar : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      exact hp2
    have hqodd : Odd (p ^ f) := hpodd.pow
    have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
    obtain ⟨a, b, ha, hb, hab⟩ := exists_neg_pair hp2 hK
    obtain ⟨x, y, hxm, hym, hx2, hy2, hxy⟩ :=
      LocalAnalysis.ComponentInitial.sl2_exists_anticommuting_pair hab
    set S : Subgroup (SpecialLinearGroup (Fin 2) K) :=
      (StatedSU d (p ^ f) K).comap (OutcomeLocal.slTwoToGL hd2) with hSdef
    have hxS : x ∈ S :=
      slTwoToGL_mem_statedSU hd2 hq0 x (by rw [hxm]; exact unitary_rot hqodd)
    have hyS : y ∈ S :=
      slTwoToGL_mem_statedSU hd2 hq0 y (by rw [hym]; exact unitary_neg_pair hqodd ha hb hab)
    have hzS : (-1 : SpecialLinearGroup (Fin 2) K) ∈ S := by
      rw [← hx2]
      exact pow_mem hxS 2
    have hz : (QuotientGroup.mk' ((StatedScalars (Fin d) K).subgroupOf
        (StatedSU d (p ^ f) K))).comp (((OutcomeLocal.slTwoToGL hd2).comp S.subtype).codRestrict
          (StatedSU d (p ^ f) K) fun g => g.2) ⟨-1, hzS⟩ ≠ 1 := by
      intro h
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at h
      have h' : OutcomeLocal.slTwoToStatedProj (K := K) hd2 (-1) = 1 := by
        rw [OutcomeLocal.slTwoToStatedProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact h
      exact LocalAnalysis.ComponentInitial.sl2_neg_one_ne_one hkchar
        (OutcomeLocal.slTwoToStatedProj_injective (by omega : 3 ≤ d)
          (h'.trans (map_one _).symm))
    obtain ⟨H, ⟨eH⟩⟩ := SymplecticExclusion.exists_quaternion_of_hom _
      (x := ⟨x, hxS⟩) (y := ⟨y, hyS⟩) (z := ⟨-1, hzS⟩)
      (Subtype.ext (show (-1 : SpecialLinearGroup (Fin 2) K) ^ 2 = 1 from neg_one_sq))
      (Subtype.ext hx2) (Subtype.ext hy2) (Subtype.ext hxy) hz
    exact hQ8 ⟨H.map eT.symm.toMonoidHom,
      ⟨(H.equivMapOfInjective _ eT.symm.injective).symm.trans eH⟩⟩

end CFSG.ComponentClassification.UnbalancedGS
