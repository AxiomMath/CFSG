module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofIndep
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem exists_orderOf_eq_of_surjective {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) {n : ℕ} (h : ∃ y : H, orderOf y = n) :
    ∃ x : G, orderOf x = n := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨x₀, rfl⟩ := hf y
  have hdvd : n ∣ orderOf x₀ := hy ▸ orderOf_map_dvd f x₀
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact (orderOf_pos x₀).ne' hk
  refine ⟨x₀ ^ k, ?_⟩
  rw [orderOf_pow' _ hk0, hk, Nat.gcd_mul_left_left]
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · rw [zero_mul] at hk
      exact absurd hk (orderOf_pos x₀).ne'
    · exact h0
  exact Nat.mul_div_cancel n (Nat.pos_of_ne_zero hk0)

theorem exists_orderOf_psl2_char2 (F : Type) [Field F] [Finite F] [CharP F 2] :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, orderOf x = Nat.card F + 1 := by
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := F)
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk',
      CFSG.RankThree.PartTwo.Sec8.Item86ResProof.center_specialLinearGroup_two_eq_bot]
  exact ⟨QuotientGroup.mk A, (orderOf_injective _ hinj A).trans hA⟩

open CFSG.LieType.Chevalley in
theorem HSL_mul' {F : Type} [Field F] (s t : Fˣ) :
    (HSL (s * t) : SL2 F) = HSL s * HSL t := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      mul_inv_rev, mul_comm]

open CFSG.LieType.Chevalley in
theorem HSL_one' {F : Type} [Field F] : (HSL (1 : Fˣ) : SL2 F) = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL]

open CFSG.LieType.Chevalley in
theorem HSL_pow' {F : Type} [Field F] (t : Fˣ) (m : ℕ) : (HSL t : SL2 F) ^ m = HSL (t ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, HSL_one']
  | succ m ih => rw [pow_succ, ih, pow_succ, HSL_mul']

open CFSG.LieType.Chevalley in
theorem HSL_mem_center_iff {F : Type} [Field F] (u : Fˣ) :
    (HSL u : SL2 F) ∈ Subgroup.center (SL2 F) ↔ u ^ 2 = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, -, hrA⟩
    have h00 := congrFun (congrFun hrA 0) 0
    have h11 := congrFun (congrFun hrA 1) 1
    simp [coe_HSL] at h00 h11
    have : (u : F) = ((u⁻¹ : Fˣ) : F) := by
      rw [Units.val_inv_eq_inv_val]
      exact h00.symm.trans h11
    have hu : u = u⁻¹ := Units.ext this
    rw [pow_two]
    exact (mul_eq_one_iff_eq_inv).2 hu
  · intro h
    have hu : u = u⁻¹ := (mul_eq_one_iff_eq_inv).1 (by rw [← pow_two]; exact h)
    refine ⟨(u : F), ?_, ?_⟩
    · have : ((u ^ 2 : Fˣ) : F) = 1 := by rw [h]; rfl
      simpa [pow_two] using this
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_HSL, Matrix.scalar_apply]
      · rw [← Units.val_inv_eq_inv_val, ← hu]

theorem exists_orderOf_psl2_split (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, orderOf x = (Nat.card F - 1) / 2 := by
  classical
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units] at ht
  obtain ⟨k, hk⟩ := hodd
  have hN' : Nat.card F - 1 = 2 * k := by omega
  have hk0 : 0 < k := by
    have : 2 ≤ Nat.card F := Finite.one_lt_card
    omega
  have hdiv : (Nat.card F - 1) / 2 = k := by omega
  rw [hdiv]
  refine ⟨QuotientGroup.mk (CFSG.LieType.Chevalley.HSL t), ?_⟩
  rw [orderOf_eq_iff hk0]
  constructor
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, HSL_pow', HSL_mem_center_iff]
    rw [← pow_mul]
    have : t ^ (k * 2) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ht, hN']
      exact ⟨1, by ring⟩
    exact this
  · intro m hm hm0 h1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, HSL_pow', HSL_mem_center_iff,
      ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ht, hN'] at h1
    have : 2 * k ∣ m * 2 := h1
    have := Nat.le_of_dvd (by omega) this
    omega

theorem exists_orderOf_of_isTypeL2 {Y : Type} [Group Y] [Finite Y] {r n : ℕ}
    (h : IsTypeL2 r Y)
    (hex : ∀ (F : Type) [Field F] [Finite F], Nat.card F = r →
      ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, orderOf x = n) :
    ∃ y : Y, orderOf y = n := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  obtain ⟨x, hx⟩ := hex F hcard
  have h1 : ∃ y' : Y ⧸ Subgroup.center Y, orderOf y' = n :=
    ⟨e.symm (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F x),
      by rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hx]⟩
  exact exists_orderOf_eq_of_surjective (QuotientGroup.mk' (Subgroup.center Y))
    (QuotientGroup.mk'_surjective _) h1

theorem exists_orderOf_of_sectionL2 {S : Type} [Group S] [Finite S] (A : Subgroup S) {r n : ℕ}
    (h : IsTypeL2 r (barOf 3 A))
    (hex : ∀ (F : Type) [Field F] [Finite F], Nat.card F = r →
      ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, orderOf x = n) :
    ∃ a ∈ A, orderOf a = n := by
  obtain ⟨y, hy⟩ := exists_orderOf_of_isTypeL2 h hex
  obtain ⟨a, ha⟩ := exists_orderOf_eq_of_surjective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥A))
    (QuotientGroup.mk'_surjective _) ⟨y, hy⟩
  exact ⟨a, a.2, by rw [Subgroup.orderOf_coe]; exact ha⟩

theorem exists_order_sixtyFive_of_sectionL2 {S : Type} [Group S] [Finite S] (A : Subgroup S)
    (h : IsTypeL2 (4 ^ 3) (barOf 3 A)) : ∃ a ∈ A, orderOf a = 65 := by
  refine exists_orderOf_of_sectionL2 A h fun F _ _ hcard => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have hc : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 6)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  obtain ⟨x, hx⟩ := exists_orderOf_psl2_char2 F
  exact ⟨x, by rw [hx, hcard]; norm_num⟩

theorem exists_order_sixtyTwo_of_sectionL2 {S : Type} [Group S] [Finite S] (A : Subgroup S)
    (h : IsTypeL2 (5 ^ 3) (barOf 3 A)) : ∃ a ∈ A, orderOf a = 62 := by
  refine exists_orderOf_of_sectionL2 A h fun F _ _ hcard => ?_
  obtain ⟨x, hx⟩ := exists_orderOf_psl2_split F (by rw [hcard]; exact ⟨62, by norm_num⟩)
  exact ⟨x, by rw [hx, hcard]; norm_num⟩

end CFSG.HardMathSupport.Dickson.Sec6.I1431
