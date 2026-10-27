module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldPSL
public import CFSG.RankThree.PartTwo.KFacts.K71SU3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.GH74.GLS.IVK Matrix
open scoped commutatorElement

section Scalar

theorem l3bf_gl_scalar_of_map {A B : Type} [Field A] [Field B] (ι : A →+* B)
    {x : GL (Fin 3) A} {c : Bˣ} (hx : GeneralLinearGroup.map ι x = GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ r : Aˣ, x = GeneralLinearGroup.scalar (Fin 3) r ∧ ι (r : A) = c := by
  have hij : ∀ i j, ι ((x : Matrix (Fin 3) (Fin 3) A) i j) =
      (scalar (Fin 3) (c : B)) i j := fun i j => by
    have := congrArg (fun y : GL (Fin 3) B => (y : Matrix (Fin 3) (Fin 3) B) i j) hx
    simpa [GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_scalar] using this
  have hdiag : ∀ i, ι ((x : Matrix (Fin 3) (Fin 3) A) i i) = c := fun i => by
    simpa [scalar_apply, diagonal_apply_eq] using hij i i
  have hne : (x : Matrix (Fin 3) (Fin 3) A) 0 0 ≠ 0 := fun h0 => by
    have := hdiag 0
    rw [h0, map_zero] at this
    exact c.ne_zero this.symm
  refine ⟨Units.mk0 _ hne, ?_, by simpa using hdiag 0⟩
  apply Units.ext
  ext i j
  apply ι.injective
  rw [hij]
  by_cases h : i = j
  · subst h
    simp [scalar_apply, diagonal_apply_eq, hdiag]
  · simp [scalar_apply, diagonal_apply_ne _ h]

end Scalar

section PSU

variable {p f f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {σ : K ≃+* K}
  (hf : f = 3 * f₀) (h₀ : UnitaryFieldData p f₀ (fixedField σ))

@[expose] noncomputable def l3bUG : unitarySU p f₀ (fixedField σ) 3 →* unitaryPSU h 3 :=
  (unitaryProj h 3).comp (suIncl h h₀ (bar_coe_fixedField h hf h₀))

@[expose] noncomputable def l3bUT : Subgroup (unitaryPSU h 3) := (l3bUG h hf h₀).range

theorem l3bUT_le_fix : l3bUT h hf h₀ ≤ l3bFix (psuField h σ) := by
  rintro _ ⟨g', rfl⟩
  show psuField h σ (unitaryProj h 3 _) = unitaryProj h 3 _
  have hfix := (mem_range_suIncl_iff h h₀ (bar_coe_fixedField h hf h₀) _).1 ⟨g', rfl⟩
  exact (psuField_mk σ (suIncl h h₀ (bar_coe_fixedField h hf h₀) g')).trans
    (congrArg (fun x : unitarySU p f K 3 => (x : unitaryPSU h 3)) hfix)

theorem exists_scalar_of_mem_fixU {d : unitaryPSU h 3} (hd : d ∈ l3bFix (psuField h σ)) :
    ∃ A : unitarySU p f K 3, unitaryProj h 3 A = d ∧ ∃ s ∈ unitaryScalars h 3,
      suField h σ A = A * s := by
  obtain ⟨A, rfl⟩ := unitaryProj_surjective h 3 d
  refine ⟨A, rfl, A⁻¹ * suField h σ A, ?_, by group⟩
  have hd' : psuField h σ (unitaryProj h 3 A) = unitaryProj h 3 A := hd
  have h1 : unitaryProj h 3 (suField h σ A) = unitaryProj h 3 A := hd'
  have h2 : (suField h σ A)⁻¹ * A ∈ (unitaryProj h 3).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [ker_unitaryProj] at h2
  have h3 := (unitaryScalars h 3).inv_mem h2
  simpa using h3

theorem mem_l3bUT_of_fixed {A : unitarySU p f K 3} (hA : suField h σ A = A) :
    unitaryProj h 3 A ∈ l3bUT h hf h₀ := by
  obtain ⟨A₀, rfl⟩ := (mem_range_suIncl_iff h h₀ (bar_coe_fixedField h hf h₀) A).2 hA
  exact ⟨A₀, rfl⟩

theorem commutator_fix_le_l3bUT :
    ⁅l3bFix (psuField h σ), l3bFix (psuField h σ)⁆ ≤ l3bUT h hf h₀ := by
  rw [Subgroup.commutator_le]
  intro d₁ h₁ d₂ h₂
  obtain ⟨A₁, rfl, s₁, hs₁, e₁⟩ := exists_scalar_of_mem_fixU h h₁
  obtain ⟨A₂, rfl, s₂, hs₂, e₂⟩ := exists_scalar_of_mem_fixU h h₂
  rw [← map_commutatorElement]
  apply mem_l3bUT_of_fixed h hf h₀
  rw [map_commutatorElement, e₁, e₂]
  exact l3bf_commutator_central_mul (unitaryScalars_le_center h 3 hs₁)
    (unitaryScalars_le_center h 3 hs₂)

theorem cube_fix_mem_l3bUT {d : unitaryPSU h 3} (hd : d ∈ l3bFix (psuField h σ)) :
    d ^ 3 ∈ l3bUT h hf h₀ := by
  obtain ⟨A, rfl, s, hs, e⟩ := exists_scalar_of_mem_fixU h hd
  rw [← map_pow]
  apply mem_l3bUT_of_fixed h hf h₀
  have hs3 : s ^ 3 = 1 := by
    obtain ⟨c, -, hc3, hzc⟩ := hs
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one]
    rfl
  have hc : Commute A s := Subgroup.mem_center_iff.1 (unitaryScalars_le_center h 3 hs) A
  rw [map_pow, e, hc.mul_pow, hs3, mul_one]

theorem l3bUT_eq_map : l3bUT h hf h₀ = (⊤ : Subgroup (unitarySU p f₀ (fixedField σ) 3)).map
    (l3bUG h hf h₀) := by
  rw [l3bUT, ← MonoidHom.range_eq_map]

theorem ker_l3bUG : (l3bUG h hf h₀).ker = unitaryScalars h₀ 3 := by
  ext x
  have hn : 1 ≤ 3 := by norm_num
  rw [unitaryScalars_eq h₀ hn, Subgroup.mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars, MonoidHom.mem_range]
  have key : ∀ y, y ∈ unitaryScalars h 3 ↔ unitaryProj h 3 y = 1 := fun y => by
    rw [← MonoidHom.mem_ker, ker_unitaryProj]
  have e1 : x ∈ (l3bUG h hf h₀).ker ↔
      suIncl h h₀ (bar_coe_fixedField h hf h₀) x ∈ unitaryScalars h 3 :=
    Iff.trans MonoidHom.mem_ker (key _).symm
  rw [e1, unitaryScalars_eq h hn, Subgroup.mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars, MonoidHom.mem_range]
  have hcoe : ((suIncl h h₀ (bar_coe_fixedField h hf h₀) x : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.map (fixedField σ).subtype (x : GL (Fin 3) (fixedField σ)) := by
    apply GeneralLinearGroup.ext
    intro i j
    rw [coe_suIncl_apply]
    simp [GeneralLinearGroup.map_apply]
  rw [hcoe]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨r, hr, -⟩ := l3bf_gl_scalar_of_map (fixedField σ).subtype hc.symm
    exact ⟨r, hr.symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨Units.map (fixedField σ).subtype.toMonoidHom r, ?_⟩
    rw [← hr]
    apply GeneralLinearGroup.ext
    intro i j
    simp only [GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply, Units.coe_map]
    split_ifs <;> simp

variable (hq₀ : p ^ f₀ ≠ 2)

include hq₀ in
theorem l3bUT_perfect : ⁅l3bUT h hf h₀, l3bUT h hf h₀⁆ = l3bUT h hf h₀ := by
  have := h.finite
  have := h₀.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card (fixedField σ) = (p ^ f₀) ^ 2 := by
    rw [h₀.card, ← pow_mul, mul_comm]
  have hperf : commutator (unitarySU p f₀ (fixedField σ) 3) = ⊤ :=
    (Group.isPerfect_def (G := unitarySU p f₀ (fixedField σ) 3)).1
      (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl (fun h3 => hq₀ (by simpa using h3)))
  rw [l3bUT_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]

include hq₀ in
theorem commutator_fix_eq_U : ⁅l3bFix (psuField h σ), l3bFix (psuField h σ)⁆ = l3bUT h hf h₀ := by
  refine le_antisymm (commutator_fix_le_l3bUT h hf h₀) ?_
  calc l3bUT h hf h₀ = ⁅l3bUT h hf h₀, l3bUT h hf h₀⁆ := (l3bUT_perfect h hf h₀ hq₀).symm
    _ ≤ _ := Subgroup.commutator_mono (l3bUT_le_fix h hf h₀) (l3bUT_le_fix h hf h₀)

include hq₀ in
theorem l3bUT_quasisimple_data :
    IsSimpleGroup ↥(l3bUT h hf h₀) ∧ ∃ a b : ↥(l3bUT h hf h₀), a * b ≠ b * a := by
  have := h.finite
  have := h₀.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card (fixedField σ) = (p ^ f₀) ^ 2 := by
    rw [h₀.card, ← pow_mul, mul_comm]
  obtain ⟨⟨-, hsimple, a, b, hab⟩, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    hF (le_refl 3) (fun h3 => hq₀ (by simpa using h3))
  have hker : (l3bUG h hf h₀).ker = Subgroup.center (unitarySU p f₀ (fixedField σ) 3) := by
    rw [ker_l3bUG, unitaryScalars_eq h₀ (by norm_num : 1 ≤ 3)]
    exact hZ.symm
  let E : (unitarySU p f₀ (fixedField σ) 3 ⧸ Subgroup.center (unitarySU p f₀ (fixedField σ) 3)) ≃*
      ↥(l3bUT h hf h₀) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange (l3bUG h hf h₀))
  refine ⟨E.symm.isSimpleGroup, E a, E b, fun hc => hab (E.injective ?_)⟩
  rw [map_mul, map_mul]
  exact hc

theorem coe_toGL_l3bCyc (F : Type) [Field F] :
    ((SpecialLinearGroup.toGL (l3bCyc F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem l3bUCyc_mem {F : Type} [Field F] {p f₀ : ℕ} (hp : p ^ f₀ ≠ 0) :
    SpecialLinearGroup.toGL (l3bCyc F) ∈ unitarySU p f₀ F 3 := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [coe_toGL_l3bCyc]
    simp [Matrix.det_fin_three]
  · rw [coe_toGL_l3bCyc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, zero_pow hp]

theorem three_dvd_card_l3bUT : 3 ∣ Nat.card ↥(l3bUT h hf h₀) := by
  have hp : p ^ f₀ ≠ 0 := pow_ne_zero _ h.prime.ne_zero
  set c : unitarySU p f₀ (fixedField σ) 3 :=
    ⟨SpecialLinearGroup.toGL (l3bCyc (fixedField σ)), l3bUCyc_mem hp⟩ with hc
  have hne : l3bUG h hf h₀ c ≠ 1 := by
    intro h1
    have : c ∈ (l3bUG h hf h₀).ker := h1
    rw [ker_l3bUG, mem_unitaryScalars] at this
    obtain ⟨r, -, -, hr⟩ := this
    have h3 := congrArg (fun y : GL (Fin 3) (fixedField σ) =>
      (y : Matrix (Fin 3) (Fin 3) (fixedField σ)) 0 2) hr
    have h4 : ((c : GL (Fin 3) (fixedField σ)) : Matrix (Fin 3) (Fin 3) (fixedField σ)) 0 2 = 1 := by
      rw [hc]
      show ((SpecialLinearGroup.toGL (l3bCyc (fixedField σ)) : GL (Fin 3) (fixedField σ)) :
        Matrix (Fin 3) (Fin 3) (fixedField σ)) 0 2 = 1
      rw [coe_toGL_l3bCyc]
      rfl
    simp only [h4, GeneralLinearGroup.coe_scalar, scalar_apply] at h3
    simp at h3
  have hpow : l3bUG h hf h₀ c ^ 3 = 1 := by
    rw [← map_pow]
    have : c ^ 3 = 1 := by
      apply Subtype.ext
      show (SpecialLinearGroup.toGL (l3bCyc (fixedField σ))) ^ 3 = 1
      rw [← map_pow, l3bCyc_pow_three, map_one]
    rw [this, map_one]
  have hx : l3bUG h hf h₀ c ∈ l3bUT h hf h₀ := ⟨_, rfl⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (⟨_, hx⟩ : ↥(l3bUT h hf h₀)) = 3 :=
    orderOf_eq_prime (Subtype.ext hpow) (fun h1 => hne (congrArg Subtype.val h1))
  have := orderOf_dvd_natCard (⟨_, hx⟩ : ↥(l3bUT h hf h₀))
  rwa [ho] at this

include hf h₀ hq₀ in
theorem l3bf_fixData_psu : L3BFixData (psuField h σ) := by
  have hq := l3bUT_quasisimple_data h hf h₀ hq₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [commutator_fix_eq_U h hf h₀ hq₀]; exact hq.1
  · rw [commutator_fix_eq_U h hf h₀ hq₀]; exact hq.2
  · rw [commutator_fix_eq_U h hf h₀ hq₀]; exact three_dvd_card_l3bUT h hf h₀
  · intro d hd
    rw [commutator_fix_eq_U h hf h₀ hq₀]
    exact cube_fix_mem_l3bUT h hf h₀ hd

@[expose] noncomputable def l3bUTEquiv :
    unitaryPSU h₀ 3 ≃* ↥(l3bUT h hf h₀) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_l3bUG h hf h₀).symm).trans
    (QuotientGroup.quotientKerEquivRange (l3bUG h hf h₀))

theorem l3bUT_solvable (hq : p ^ f₀ = 2) : Group.IsSolvable ↥(l3bUT h hf h₀) := by
  have := h.finite
  have := h₀.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card (fixedField σ) = (p ^ f₀) ^ 2 := by
    rw [h₀.card, ← pow_mul, mul_comm]
  have hcard : Nat.card ↥(l3bUT h hf h₀) = 2 ^ 3 * 3 ^ 2 := by
    rw [← Nat.card_congr (l3bUTEquiv h hf h₀).toEquiv,
      Nat.card_congr (unitaryPSUEquiv h₀ (n := 3) (by norm_num)).toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU h₀.prime h₀.one_le hF
        (by norm_num), hq]
    decide
  have := Fintype.ofFinite ↥(l3bUT h hf h₀)
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

include hf h₀ in
theorem l3bUfix_solvable (hq : p ^ f₀ = 2) : Group.IsSolvable ↥(l3bFix (psuField h σ)) :=
  l3bf_solvable_of_commutator_le (l3bUT_solvable h hf h₀ hq) (commutator_fix_le_l3bUT h hf h₀)

end PSU

end CFSG.HardMathSupport.Solomon.Coordinator
