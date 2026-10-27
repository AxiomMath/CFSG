module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Tools
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.LieType.Chevalley

theorem not_isPGroup_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : ¬ IsPGroup 2 (B ⧸ pPrimeCore 2 B)) : ¬ IsPGroup 2 (A ⧸ pPrimeCore 2 A) := by
  intro hA
  exact h (isPGroup_quotient_iff_hasNormalPComplement.mpr
    (QuasiDihedralFusion.hasNormalPComplement_of_mulEquiv e
      (isPGroup_quotient_iff_hasNormalPComplement.mp hA)))

theorem not_isPGroup_of_le {G : Type*} [Group G] [Finite G] {X F : Subgroup G} (hXF : X ≤ F)
    (h : ¬ IsPGroup 2 (↥X ⧸ pPrimeCore 2 ↥X)) : ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  intro hF
  have h1 := QuasiDihedralFusion.hasNormalPComplement_subgroup
    (isPGroup_quotient_iff_hasNormalPComplement.mp hF) (X.subgroupOf F)
  exact h (isPGroup_quotient_iff_hasNormalPComplement.mpr
    (QuasiDihedralFusion.hasNormalPComplement_of_mulEquiv (subgroupOfEquivOfLe hXF) h1))

theorem not_isPGroup_of_map {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (ψ : G →* G') (hψ : Function.Injective ψ) {F : Subgroup G}
    (h : ¬ IsPGroup 2 (↥(F.map ψ) ⧸ pPrimeCore 2 ↥(F.map ψ))) :
    ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) :=
  not_isPGroup_of_mulEquiv (F.equivMapOfInjective ψ hψ) h

theorem not_isPGroup_of_perfect_ne_bot {G : Type*} [Group G] [Finite G] {F X : Subgroup G}
    (hXF : X ≤ F) (hX : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥) : ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  refine not_isPGroup_of_perfect hXF hX ?_
  by_contra hodd
  have hodd' : Odd (Nat.card X) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  exact hX1 (RankThree.GroupTheory.eq_bot_of_isPerfect_of_isSolvable
    (Subgroup.isPerfect_iff.mpr hX) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'))

theorem not_isPGroup_of_isSimpleGroup {G : Type*} [Group G] [Finite G] {F X : Subgroup G}
    (hXF : X ≤ F) [IsSimpleGroup X] (hnab : ∃ x y : X, x * y ≠ y * x) :
    ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  have htop : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer] at h
      exact hxy (mem_centralizer_iff.mp (h (mem_top x)) y (mem_top y)).symm
    · exact h
  have hperf : ⁅X, X⁆ = X := by
    have h1 : (commutator X).map X.subtype = ⁅X, X⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        range_subtype]
    rw [← h1, htop, ← MonoidHom.range_eq_map, range_subtype]
  have hX1 : X ≠ ⊥ := by
    intro h
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    have hx : (x : G) = 1 := (Subgroup.eq_bot_iff_forall X).mp h _ x.2
    have hy : (y : G) = 1 := (Subgroup.eq_bot_iff_forall X).mp h _ y.2
    exact Subtype.ext (by simp [hx, hy])
  exact not_isPGroup_of_perfect_ne_bot hXF hperf hX1

section SL2

variable {L : Type*} [Field L]

theorem uSL_mul (a b : L) : uSL a * uSL b = uSL (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem vSL_mul (a b : L) : vSL a * vSL b = vSL (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uSL_zero : uSL (0 : L) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL]

theorem vSL_zero : vSL (0 : L) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL]

theorem uSL_pow (s : L) (n : ℕ) : uSL s ^ n = uSL ((n : L) * s) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uSL_zero]
  | succ n ih =>
    rw [pow_succ, ih, uSL_mul]
    congr 1
    push_cast
    ring

theorem vSL_pow (s : L) (n : ℕ) : vSL s ^ n = vSL ((n : L) * s) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, vSL_zero]
  | succ n ih =>
    rw [pow_succ, ih, vSL_mul]
    congr 1
    push_cast
    ring

theorem uSL_one_pow_ringChar : uSL (1 : L) ^ ringChar L = 1 := by
  rw [uSL_pow, ringChar.Nat.cast_ringChar, zero_mul, uSL_zero]

theorem vSL_one_pow_ringChar : vSL (1 : L) ^ ringChar L = 1 := by
  rw [vSL_pow, ringChar.Nat.cast_ringChar, zero_mul, vSL_zero]

theorem vSL_inv (s : L) : (vSL s)⁻¹ = vSL (-s) := by
  rw [inv_eq_iff_mul_eq_one, vSL_mul, add_neg_cancel, vSL_zero]

theorem uvu_sq : (uSL (1 : L) * (vSL 1)⁻¹ * uSL 1) ^ 2 = -1 := by
  rw [pow_two, vSL_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem orderOf_uvu (hL : ringChar L ≠ 2) : orderOf (uSL (1 : L) * (vSL 1)⁻¹ * uSL 1) = 4 := by
  set w := uSL (1 : L) * (vSL 1)⁻¹ * uSL 1 with hw
  have h2 : w ^ 2 = -1 := uvu_sq
  have h4 : w ^ 2 ^ 2 = 1 := by
    rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hne : ¬ w ^ 2 ^ 1 = 1 := by
    rw [pow_one, h2]
    intro h
    have := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) L => (A : Matrix (Fin 2) (Fin 2) L) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hL this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow hne h4

theorem not_hasNormalPComplement_sl2 [Finite L] (hL : ringChar L ≠ 2) :
    ¬ HasNormalPComplement 2 (SL2 L) := by
  classical
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨n, hp, -⟩ := FiniteField.card L (ringChar L)
  have hodd : Odd (ringChar L) := hp.odd_of_ne_two hL
  set T : Set (SL2 L) := {uSL 1, vSL 1} with hT
  have hTF : T ⊆ ((⊤ : Subgroup (SL2 L)) : Set (SL2 L)) := fun _ _ => mem_top _
  have hTo : ∀ t ∈ T, Odd (orderOf t) := by
    intro t ht
    rcases ht with rfl | rfl
    · exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one uSL_one_pow_ringChar)
    · exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one vSL_one_pow_ringChar)
  have hu : uSL (1 : L) ∈ closure T := subset_closure (Set.mem_insert _ _)
  have hv : vSL (1 : L) ∈ closure T := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hw : uSL (1 : L) * (vSL 1)⁻¹ * uSL 1 ∈ closure T :=
    mul_mem (mul_mem hu (inv_mem hv)) hu
  have h2 : 2 ∣ Nat.card (closure T) := by
    have h4 := orderOf_dvd_natCard (⟨_, hw⟩ : closure T)
    rw [Subgroup.orderOf_mk, orderOf_uvu hL] at h4
    exact (show 2 ∣ 4 by norm_num).trans h4
  intro hN
  have hP := not_isPGroup_of_closure_odd hTF hTo h2
  apply hP
  exact isPGroup_quotient_iff_hasNormalPComplement.mpr
    (QuasiDihedralFusion.hasNormalPComplement_subgroup hN ⊤)

theorem not_isPGroup_of_sl2 {G : Type*} [Group G] [Finite G] {F : Subgroup G} [Finite L]
    (hL : ringChar L ≠ 2) (φ : SL2 L →* G) (hφ : Function.Injective φ) (hφF : φ.range ≤ F) :
    ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  refine not_isPGroup_of_le hφF fun hR => not_hasNormalPComplement_sl2 hL ?_
  exact QuasiDihedralFusion.hasNormalPComplement_of_mulEquiv (MonoidHom.ofInjective hφ).symm
    (isPGroup_quotient_iff_hasNormalPComplement.mp hR)

theorem not_isPGroup_of_sl2_map {G G' : Type*} [Group G] [Group G'] [Finite G] (ψ : G →* G')
    (hψ : Function.Injective ψ) {F : Subgroup G} [Finite L] (hL : ringChar L ≠ 2)
    (φ : SL2 L →* G') (hφ : Function.Injective φ) (hφF : φ.range ≤ F.map ψ) :
    ¬ IsPGroup 2 (↥F ⧸ pPrimeCore 2 ↥F) := by
  set e := F.equivMapOfInjective ψ hψ with he
  let χ : SL2 L →* F.map ψ := φ.codRestrict (F.map ψ) fun A => hφF ⟨A, rfl⟩
  let θ : SL2 L →* G := F.subtype.comp (e.symm.toMonoidHom.comp χ)
  have hθ : Function.Injective θ := by
    intro A B hAB
    apply hφ
    have h1 : e.symm (χ A) = e.symm (χ B) := Subtype.ext hAB
    have h2 : χ A = χ B := e.symm.injective h1
    exact congrArg Subtype.val h2
  refine not_isPGroup_of_sl2 hL θ hθ ?_
  rintro _ ⟨A, rfl⟩
  exact (e.symm (χ A)).2

end SL2

end CFSG.ComponentClassification.HarrisLit.L33.E1
