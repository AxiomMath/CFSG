module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

namespace TwA5Big

section Certs


variable {n q : ℕ} {F : Type} [Field F] [Finite F]

theorem pow_six_ne_one {ζu : Fˣ} (hζo : orderOf ζu = q) (hq6 : ¬ q ∣ 6) :
    (ζu : F) ^ 6 ≠ 1 := by
  intro h6
  have h6u : ζu ^ 6 = 1 := by
    apply Units.ext
    simpa using h6
  have hdvd : q ∣ 6 := by
    rw [← hζo]
    exact orderOf_dvd_iff_pow_eq_one.2 h6u
  exact hq6 hdvd

theorem map_le_normalizer_map_unitaryProj (h : UnitaryFieldData 2 n F)
    {A J : Subgroup (unitarySU 2 n F 6)}
    (hAJ : A ≤ Subgroup.normalizer (J : Set (unitarySU 2 n F 6))) :
    A.map (unitaryProj h 6) ≤
      Subgroup.normalizer ((J.map (unitaryProj h 6) : Subgroup (unitaryPSU h 6)) : Set _) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    have h1 : a * b * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hAJ ha) b).1 hb
    exact ⟨a * b * a⁻¹, h1, by simp only [map_mul, map_inv]⟩
  · rintro ⟨b, hb, hbeq⟩
    have h1 : a⁻¹ * b * a ∈ J :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hAJ ha)) b).1 hb
    refine ⟨a⁻¹ * b * a, h1, ?_⟩
    rw [map_mul, map_mul, map_inv, hbeq]
    group

theorem twA5Torus_le_normalizer_lineRadical (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) :
    twA5Torus h hζ ≤
      Subgroup.normalizer (unitaryLineRadical h : Set (unitarySU 2 n F 6)) := by
  intro A hA
  obtain ⟨c, rfl⟩ := hA
  exact diagSU_mem_normalizer_unitaryLineRadical h
    (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ (c i).2)
    (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ (c i).2)
    (by simp [twA5Vec])

theorem twA5B_le_normalizer_lineRadical (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) :
    twA5B h hζ ≤ Subgroup.normalizer
      (((unitaryLineRadical h).map (unitaryProj h 6) : Subgroup (unitaryPSU h 6)) : Set _) := by
  rw [twA5B, MonoidHom.range_comp]
  exact map_le_normalizer_map_unitaryProj h (twA5Torus_le_normalizer_lineRadical h hζ)

theorem exists_pow_eq_of_mem_zpowers {ζu : Fˣ} (hζo : orderOf ζu = q) {k : ℕ} (hq : q.Prime)
    (hk : ¬ q ∣ k) {b : Fˣ} (hb : b ∈ Subgroup.zpowers ζu) :
    ∃ c ∈ Subgroup.zpowers ζu, c ^ k = b := by
  have hinj : Function.Injective (fun x : Subgroup.zpowers ζu => x ^ k) := by
    intro x y hxy
    have hxy' : x ^ k = y ^ k := hxy
    have h1 : (x * y⁻¹) ^ k = 1 := by
      rw [mul_pow, hxy', inv_pow, mul_inv_cancel]
    have h2 : orderOf (x * y⁻¹) ∣ k := orderOf_dvd_iff_pow_eq_one.2 h1
    have h3 : orderOf (x * y⁻¹) ∣ q := by
      have h := orderOf_dvd_natCard (x * y⁻¹)
      rwa [Nat.card_zpowers, hζo] at h
    have hcop : Nat.Coprime k q :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hk)
    have h4 : orderOf (x * y⁻¹) = 1 := by
      have h5 : orderOf (x * y⁻¹) ∣ Nat.gcd k q := Nat.dvd_gcd h2 h3
      exact Nat.dvd_one.mp (hcop ▸ h5)
    have h6 : x * y⁻¹ = 1 := orderOf_eq_one_iff.1 h4
    exact mul_inv_eq_one.1 h6
  obtain ⟨c, hc⟩ := Finite.surjective_of_injective hinj ⟨b, hb⟩
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem coe_diagFiveLast_pow (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (m : ℕ) :
    ((((diagFiveLast h (ζu : F) hζ) ^ m : unitarySU 2 n F 6) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) = diagonal (diagFiveLastEntries ((ζu : F) ^ m)) := by
  have hζm : h.norm (((ζu ^ m : Fˣ) : F)) = 1 := by
    have h1 : (Units.map h.normHom) (ζu ^ m) = 1 := by
      rw [map_pow,
        show (Units.map h.normHom) ζu = 1 from
          (MonoidHom.mem_ker).2 ((h.mem_ker_normUnits).2 hζ), one_pow]
    exact (h.mem_ker_normUnits).1 ((MonoidHom.mem_ker).1 h1)
  rw [← diagFiveLast_pow h hζ m hζm, coe_diagFiveLast, Units.val_pow_eq_pow_val]

theorem twA5B_le_sup (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1)
    (hζo : orderOf ζu = q) (hq : q.Prime) (hq5 : ¬ q ∣ 5) :
    twA5B h hζ ≤ blockSU h suFiveIndex ⊔
      Subgroup.zpowers (unitaryProj h 6 (diagFiveLast h (ζu : F) hζ)) := by
  rintro x ⟨c, rfl⟩
  set A : unitarySU 2 n F 6 := twA5TorusHom h hζ c with hA
  change unitaryProj h 6 A ∈ blockSU h suFiveIndex ⊔
    Subgroup.zpowers (unitaryProj h 6 (diagFiveLast h (ζu : F) hζ))
  have h5ne : twA5Vec (fun i => ((c i : Fˣ) : F)) 5 ≠ 0 := by
    rw [twA5Vec_five]
    exact inv_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (Units.ne_zero ((c 0 : Fˣ)))) (Units.ne_zero ((c 1 : Fˣ))))
      (Units.ne_zero ((c 2 : Fˣ)))) (Units.ne_zero ((c 3 : Fˣ))))
  set b5 : Fˣ := Units.mk0 (twA5Vec (fun i => ((c i : Fˣ) : F)) 5) h5ne with hb5
  have hb5val : (b5 : F) = twA5Vec (fun i => ((c i : Fˣ) : F)) 5 := rfl
  have hb5val' : (b5 : F) =
      (((c 0 : Fˣ) : F) ^ 2 * ((c 1 : Fˣ) : F) * ((c 2 : Fˣ) : F) * ((c 3 : Fˣ) : F))⁻¹ := by
    rw [hb5val, twA5Vec_five]
  have hb5mem : b5 ∈ Subgroup.zpowers ζu := by
    have h1 : b5 = ((c 0 : Fˣ) ^ 2 * (c 1 : Fˣ) * (c 2 : Fˣ) * (c 3 : Fˣ))⁻¹ := by
      apply Units.ext
      rw [hb5val, twA5Vec_five]
      push_cast
      rfl
    rw [h1]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ (c 0).2 2) (c 1).2) (c 2).2) (c 3).2)
  obtain ⟨κ, hκmem, hκ5⟩ := exists_pow_eq_of_mem_zpowers hζo hq hq5 hb5mem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hκmem
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ζu ^ m = κ := by
    refine ⟨(j % (q : ℤ)).toNat, ?_⟩
    have hq1 : (ζu : Fˣ) ^ (q : ℤ) = 1 := by
      rw [zpow_natCast, ← hζo, pow_orderOf_eq_one]
    rw [← hj, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg j (by
        have := hq.ne_zero
        omega : (q : ℤ) ≠ 0))]
    exact (zpow_eq_zpow_emod j hq1).symm
  have hκ : ((ζu : F) ^ m) = (κ : F) := by rw [← hm]; push_cast; rfl
  have hmem : A * (diagFiveLast h (ζu : F) hζ) ^ m ∈ unitaryBlock h suFiveIndex := by
    have hAmat : (((A : GL (Fin 6) F)) : Matrix (Fin 6) (Fin 6) F) =
        diagonal (twA5Vec fun i => ((c i : Fˣ) : F)) := coe_twA5Diag h hζ c
    have hprod : ((((A * (diagFiveLast h (ζu : F) hζ) ^ m : unitarySU 2 n F 6) : GL (Fin 6) F)) :
        Matrix (Fin 6) (Fin 6) F) = diagonal (fun i =>
          twA5Vec (fun i => ((c i : Fˣ) : F)) i * diagFiveLastEntries ((ζu : F) ^ m) i) := by
      rw [Subgroup.coe_mul, Units.val_mul, hAmat, coe_diagFiveLast_pow h hζ m,
        diagonal_mul_diagonal]
    intro i j hij
    show (((A * (diagFiveLast h (ζu : F) hζ) ^ m : unitarySU 2 n F 6) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) i j = (1 : Matrix (Fin 6) (Fin 6) F) i j
    rw [hprod]
    by_cases hidx : i = j
    · subst hidx
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      have hi5 : i = 5 := by
        by_contra h
        have hmem : i ∈ suFiveIndex := by simp [suFiveIndex, h]
        rcases hij with h1 | h1
        · exact h1 hmem
        · exact h1 hmem
      subst hi5
      simp only [twA5Vec_five, diagFiveLastEntries, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      have hκ5F : ((ζu : F) ^ m) ^ 5 = (b5 : F) := by
        rw [hκ, show (κ : F) ^ 5 = ((κ ^ 5 : Fˣ) : F) by push_cast; rfl, hκ5]
      rw [hκ5F, ← hb5val']
      exact mul_inv_cancel₀ (by rw [hb5val']; exact Units.ne_zero b5)
    · rw [Matrix.diagonal_apply_ne _ hidx, Matrix.one_apply_ne hidx]
  have hdecomp : unitaryProj h 6 A = unitaryProj h 6 (A * (diagFiveLast h (ζu : F) hζ) ^ m) *
      (unitaryProj h 6 (diagFiveLast h (ζu : F) hζ) ^ m)⁻¹ := by
    rw [map_mul, map_pow]
    group
  rw [hdecomp]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (unitaryProj_mem_blockSU h hmem)) ?_
  exact Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m))


theorem unitaryRadMatrix_zero_apply_zero (h : UnitaryFieldData 2 n F) (y : F) :
    unitaryRadMatrix h 0 y 0 0 = 1 + y := by
  simp [unitaryRadMatrix, suLineVec, suRadVec, Matrix.add_apply, Matrix.vecMulVec_apply]

theorem unitaryRadMatrix_zero_apply_two (h : UnitaryFieldData 2 n F) (y : F) :
    unitaryRadMatrix h 0 y 2 2 = 1 := by
  simp [unitaryRadMatrix, suLineVec, suRadVec, Matrix.add_apply, Matrix.vecMulVec_apply]

theorem unitaryLineRadical_map_ne_bot (h : UnitaryFieldData 2 n F) :
    (unitaryLineRadical h).map (unitaryProj h 6) ≠ ⊥ := by
  haveI : CharP F 2 := h.charP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hytrace : (c + h.bar c) + h.bar (c + h.bar c) = 0 := by
    rw [map_add, h.bar_bar]
    rw [show c + h.bar c + (h.bar c + c) = (c + c) + (h.bar c + h.bar c) by ring]
    rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  have hyne : c + h.bar c ≠ 0 := by
    intro h0
    refine hc ?_
    have hneg : -h.bar c = h.bar c := by
      rw [neg_eq_iff_add_eq_zero]
      exact CharTwo.add_self_eq_zero _
    rw [← hneg, neg_eq_iff_add_eq_zero, add_comm]
    exact h0
  intro hbot
  have hmem : unitaryRadElem h 0 (c + h.bar c) (by rw [suRadCocycle_zero]; exact hytrace) ∈
      unitaryLineRadical h := ⟨0, _, _, rfl⟩
  have hmem' : unitaryProj h 6 (unitaryRadElem h 0 (c + h.bar c)
      (by rw [suRadCocycle_zero]; exact hytrace)) ∈
      (unitaryLineRadical h).map (unitaryProj h 6) := ⟨_, hmem, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem'
  have h1 : unitaryRadElem h 0 (c + h.bar c)
      (by rw [suRadCocycle_zero]; exact hytrace) ∈ unitaryScalars h 6 := by
    rw [← ker_unitaryProj h 6, MonoidHom.mem_ker]
    exact hmem'
  obtain ⟨lam, -, -, hsc⟩ := mem_unitaryScalars.1 h1
  have h00 := congrFun (congrFun (congrArg (fun x : GL (Fin 6) F =>
    ((x : Matrix (Fin 6) (Fin 6) F))) hsc) 0) 0
  have h22 := congrFun (congrFun (congrArg (fun x : GL (Fin 6) F =>
    ((x : Matrix (Fin 6) (Fin 6) F))) hsc) 2) 2
  rw [coe_unitaryRadElem, unitaryRadMatrix_zero_apply_zero] at h00
  rw [coe_unitaryRadElem, unitaryRadMatrix_zero_apply_two] at h22
  have h00' : 1 + (c + h.bar c) = lam := by simpa [Matrix.scalar_apply] using h00
  have h22' : (1 : F) = lam := by simpa [Matrix.scalar_apply] using h22
  refine hyne ?_
  have h1 : (1 : F) + (c + h.bar c) = 1 + 0 := by rw [h00', h22', add_zero]
  exact add_left_cancel h1

theorem twA5_commutator_mem (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) (hq6 : ¬ q ∣ 6) :
    ∀ g ∈ Subgroup.centralizer
        ({unitaryProj h 6 (diagFiveLast h (ζu : F) hζ)} : Set (unitaryPSU h 6)),
      ∀ k ∈ Subgroup.centralizer
        ({unitaryProj h 6 (diagFiveLast h (ζu : F) hζ)} : Set (unitaryPSU h 6)),
        g * k * g⁻¹ * k⁻¹ ∈ blockSU h suFiveIndex := by
  intro g hg k hk
  rw [centralizer_unitaryProj_diagFiveLast h hζ (pow_six_ne_one hζo hq6)] at hg hk
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.1 hk
  have hAB : A * B * A⁻¹ * B⁻¹ ∈ unitaryBlock h suFiveIndex :=
    commutator_unitaryBlockDiag_le_unitaryBlock h compl_suFiveIndex
      (Subgroup.commutator_mem_commutator hA hB)
  rw [show unitaryProj h 6 A * unitaryProj h 6 B * (unitaryProj h 6 A)⁻¹ *
      (unitaryProj h 6 B)⁻¹ = unitaryProj h 6 (A * B * A⁻¹ * B⁻¹) by
    simp only [map_mul, map_inv]]
  exact unitaryProj_mem_blockSU h hAB

theorem evenRank_unitaryPSU_six (h : UnitaryFieldData 2 n F) (hn : 4 ≤ n)
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ 2 ^ n + 1) (hq6 : ¬ q ∣ 6) (hq2 : q ≠ 2) :
    evenRank (unitaryPSU h 6) = 4 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨ζu, hζ, hζo⟩ := exists_twA5_zeta h hq hqdvd
  have heq := evenRank_unitaryPSU_six_le h hn
  refine le_antisymm heq ?_
  set S : Subgroup (unitaryPSU h 6) := (unitaryLineRadical h).map (unitaryProj h 6) with hS
  have hS2 : IsPGroup 2 S := by
    rw [hS]
    exact IsPGroup.map (unitaryLineRadical_isPGroup h) (unitaryProj h 6)
  have hSne : S ≠ ⊥ := by
    rw [hS]
    exact unitaryLineRadical_map_ne_bot h
  have hBS : twA5B h hζ ≤ Subgroup.normalizer (S : Set (unitaryPSU h 6)) := by
    rw [hS]
    exact twA5B_le_normalizer_lineRadical h hζ
  have hloc : IsTwoLocal (Subgroup.normalizer (S : Set (unitaryPSU h 6))) :=
    ⟨S, hSne, hS2, rfl⟩
  have hbdd : BddAbove {k | ∃ (p : ℕ) (H : Subgroup (unitaryPSU h 6)),
      p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card (unitaryPSU h 6), ?_⟩
    rintro k ⟨p, H, hp, -, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
    have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card (unitaryPSU h 6) :=
      hE ▸ Subgroup.card_le_card_group E
    omega
  have hge : 4 ≤ CFSG.Open.pRank q (Subgroup.normalizer (S : Set (unitaryPSU h 6))) :=
    CFSG.SectionRank.le_pRank hq.one_lt hBS (twA5B_isElemAbelian h hζ hζo)
      (card_twA5B h hζ hζo hq hq6)
  have hmem : CFSG.Open.pRank q (Subgroup.normalizer (S : Set (unitaryPSU h 6))) ∈
      {k | ∃ (p : ℕ) (H : Subgroup (unitaryPSU h 6)),
        p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧ CFSG.Open.pRank p H = k} :=
    ⟨q, _, hq, hq2, hloc, rfl⟩
  exact le_trans hge (le_csSup hbdd hmem)

theorem twA5B0Param_mul_last {ζu : Fˣ} (c c' : Fin 3 → Subgroup.zpowers ζu) :
    ((c 0 * c' 0) ^ 2 * (c 1 * c' 1) * (c 2 * c' 2))⁻¹ =
      (c 0 ^ 2 * c 1 * c 2)⁻¹ * (c' 0 ^ 2 * c' 1 * c' 2)⁻¹ := by
  have h : (c 0 * c' 0) ^ 2 * (c 1 * c' 1) * (c 2 * c' 2) =
      (c 0 ^ 2 * c 1 * c 2) * (c' 0 ^ 2 * c' 1 * c' 2) := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [h, mul_inv]


@[expose] noncomputable def twA5B0Param {ζu : Fˣ} :
    (Fin 3 → Subgroup.zpowers ζu) →* (Fin 4 → Subgroup.zpowers ζu) where
  toFun c := ![c 0, c 1, c 2, (c 0 ^ 2 * c 1 * c 2)⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' c c' := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact twA5B0Param_mul_last c c'

@[simp] theorem twA5B0Param_apply_zero {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5B0Param c 0 = c 0 := rfl

@[simp] theorem twA5B0Param_apply_one {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5B0Param c 1 = c 1 := rfl

@[simp] theorem twA5B0Param_apply_two {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5B0Param c 2 = c 2 := rfl

@[simp] theorem twA5B0Param_apply_three {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5B0Param c 3 = (c 0 ^ 2 * c 1 * c 2)⁻¹ := rfl

theorem twA5B0Param_last {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5Vec (fun i => ((twA5B0Param c i : Fˣ) : F)) 5 = 1 := by
  rw [twA5Vec_five]
  simp only [twA5B0Param_apply_zero, twA5B0Param_apply_one, twA5B0Param_apply_two,
    twA5B0Param_apply_three]
  push_cast
  rw [show ∀ (a b cc : F), a ≠ 0 → b ≠ 0 → cc ≠ 0 →
      (a ^ 2 * b * cc * (a ^ 2 * b * cc)⁻¹)⁻¹ = 1 from fun a b cc ha hb hc => by
    rw [mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hb) hc), inv_one]]
  exacts [Units.ne_zero _, Units.ne_zero _, Units.ne_zero _]

@[expose] noncomputable def twA5B0 (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) : Subgroup (unitaryPSU h 6) :=
  ((unitaryProj h 6).comp ((twA5TorusHom h hζ).comp twA5B0Param)).range

theorem twA5B0_le (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1) :
    twA5B0 h hζ ≤ twA5B h hζ := by
  rintro x ⟨c, rfl⟩
  exact ⟨twA5B0Param c, rfl⟩

theorem twA5B0_le_blockSU (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) :
    twA5B0 h hζ ≤ blockSU h suFiveIndex := by
  rintro x ⟨c, rfl⟩
  apply unitaryProj_mem_blockSU
  show twA5TorusHom h hζ (twA5B0Param c) ∈ unitaryBlock h suFiveIndex
  refine diagSU_mem_unitaryBlock h (twA5Vec fun i => ((twA5B0Param c i : Fˣ) : F))
    (twA5Vec_norm h fun i => norm_eq_one_of_mem_zpowers h hζ (twA5B0Param c i).2)
    (twA5Vec_prod h fun i => norm_eq_one_of_mem_zpowers h hζ (twA5B0Param c i).2) ?_
  intro i hi
  have hi5 : i = 5 := by
    by_contra h
    exact hi (by simp [suFiveIndex, h])
  subst hi5
  exact twA5B0Param_last c

theorem twA5B0_hom_injective (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) (hq : q.Prime) (hq6 : ¬ q ∣ 6) :
    Function.Injective ((unitaryProj h 6).comp ((twA5TorusHom h hζ).comp twA5B0Param)) := by
  intro c c' hcc
  have h1 : (twA5TorusHom h hζ) (twA5B0Param c) = (twA5TorusHom h hζ) (twA5B0Param c') :=
    unitaryProj_injective_on_twA5Torus h hζ hζo hq hq6 _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ hcc
  have h2 : twA5B0Param c = twA5B0Param c' := twA5TorusHom_injective h hζ h1
  have h0 : c 0 = c' 0 := by simpa using congrFun h2 0
  have h1' : c 1 = c' 1 := by simpa using congrFun h2 1
  have h2' : c 2 = c' 2 := by simpa using congrFun h2 2
  funext i
  fin_cases i <;> assumption

theorem card_twA5B0 (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1)
    (hζo : orderOf ζu = q) (hq : q.Prime) (hq6 : ¬ q ∣ 6) :
    Nat.card (twA5B0 h hζ) = q ^ 3 := by
  have hdom : Nat.card (Fin 3 → Subgroup.zpowers ζu) = q ^ 3 := by
    rw [Nat.card_pi]
    simp [Nat.card_zpowers, hζo]
  rw [twA5B0, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (twA5B0_hom_injective h hζ hζo hq hq6), Subgroup.card_top, hdom]

theorem twA5B0_isElemAbelian (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) :
    IsElemAbelian q (twA5B0 h hζ) := by
  constructor
  · refine ⟨⟨fun A B => ?_⟩⟩
    obtain ⟨a, ha⟩ := A.2
    obtain ⟨b, hb⟩ := B.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm a b]
  · intro A hA
    obtain ⟨a, ha⟩ := hA
    rw [← ha, ← map_pow]
    have h1 : a ^ q = 1 := by
      funext i
      apply Subtype.ext
      apply Units.ext
      have h2 : ((a i : Fˣ)) ^ q = 1 := by
        have h3 : orderOf ((a i : Fˣ)) ∣ Nat.card ↥(Subgroup.zpowers ζu) := by
          have h := orderOf_dvd_natCard (⟨(a i : Fˣ), (a i).2⟩ : Subgroup.zpowers ζu)
          rwa [Subgroup.orderOf_mk] at h
        rw [Nat.card_zpowers, hζo] at h3
        exact orderOf_dvd_iff_pow_eq_one.1 h3
      exact congrArg (fun u : Fˣ => (u : F)) h2
    rw [h1, map_one]

theorem twA5B_inf_blockSU_pRank (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) (hq : q.Prime) (hq6 : ¬ q ∣ 6)
    (he : evenRank (unitaryPSU h 6) = 4) :
    evenRank (unitaryPSU h 6) ≤ CFSG.Open.pRank q (twA5B h hζ ⊓ blockSU h suFiveIndex) + 2 := by
  have hle : twA5B0 h hζ ≤ twA5B h hζ ⊓ blockSU h suFiveIndex :=
    le_inf (twA5B0_le h hζ) (twA5B0_le_blockSU h hζ)
  have hp := CFSG.SectionRank.le_pRank hq.one_lt hle (twA5B0_isElemAbelian h hζ hζo)
    (card_twA5B0 h hζ hζo hq hq6)
  rw [he]
  omega

end Certs

end TwA5Big

end CFSG.LocalAnalysis.GLTheoremA.Y10F
