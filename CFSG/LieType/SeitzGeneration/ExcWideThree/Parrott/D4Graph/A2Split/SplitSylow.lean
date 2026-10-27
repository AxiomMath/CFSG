module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.SplitY
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.SylowAbstract

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree

section Fixed

variable {K : Type} [Field K]

theorem fin_D4_cases : ∀ r : Fin Tag.D4.rank, r = ⟨0, by decide⟩ ∨ r = ⟨1, by decide⟩ ∨
    r = ⟨2, by decide⟩ ∨ r = ⟨3, by decide⟩ := by decide

theorem tupAct_apply_four (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)
    (c : Fin Tag.D4.rank → Kˣ) (r : Fin Tag.D4.rank) :
    tupAct M c r = c ⟨0, by decide⟩ ^ M r ⟨0, by decide⟩ * c ⟨1, by decide⟩ ^ M r ⟨1, by decide⟩ *
      c ⟨2, by decide⟩ ^ M r ⟨2, by decide⟩ * c ⟨3, by decide⟩ ^ M r ⟨3, by decide⟩ :=
  Fin.prod_univ_four _

theorem tuple_eq_one {c : Fin Tag.D4.rank → Kˣ} (h0 : c ⟨0, by decide⟩ = 1)
    (h1 : c ⟨1, by decide⟩ = 1) (h2 : c ⟨2, by decide⟩ = 1) (h3 : c ⟨3, by decide⟩ = 1) :
    c = 1 := by
  funext r
  rcases fin_D4_cases r with rfl | rfl | rfl | rfl <;> assumption

@[expose] def fixedCoord (k : ℕ) : Fin Tag.D4.rank :=
  if k = 0 then ⟨2, by decide⟩ else ⟨1, by decide⟩

theorem fixed_eq_one {k j : ℕ} (hk : k < 3) (hj : j = 1 ∨ j = 2) {c : Fin Tag.D4.rank → Kˣ}
    (h : tupAct (weylG2M ^ (4 * k) * permM ^ j) c = c) (h0 : c ⟨0, by decide⟩ = 1)
    (h1 : c (fixedCoord k) = 1) : c = 1 := by
  have row : ∀ r, c r = _ := fun r => (congrFun h r).symm.trans (tupAct_apply_four _ c r)
  interval_cases k <;> rcases hj with rfl | rfl <;> simp only [fixedCoord] at h1 <;>
    simp only [if_true, show (1 : ℕ) ≠ 0 from one_ne_zero, show (2 : ℕ) ≠ 0 from two_ne_zero,
      if_false] at h1
  ·
    have e1 := row ⟨1, by decide⟩
    have e0 := row ⟨0, by decide⟩
    have m1 : (weylG2M ^ (4 * 0) * permM ^ 1) ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 0) * permM ^ 1) ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 1) ⟨1, by decide⟩ ⟨2, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 1) ⟨1, by decide⟩ ⟨3, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 1) ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 1) ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 1) ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 1) ⟨0, by decide⟩ ⟨3, by decide⟩ = 1 := by decide
    obtain ⟨a, b, c', d, a', b', c'', d'⟩ := m1
    rw [a, b, c', d, h0] at e1
    rw [a', b', c'', d', h0] at e0
    simp only [zpow_one, zpow_zero, one_mul, mul_one] at e1 e0
    exact tuple_eq_one h0 e1 h1 e0.symm
  ·
    have e0 := row ⟨0, by decide⟩
    have e3 := row ⟨3, by decide⟩
    have m1 : (weylG2M ^ (4 * 0) * permM ^ 2) ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 2) ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 0) * permM ^ 2) ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 2) ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 2) ⟨3, by decide⟩ ⟨0, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 0) * permM ^ 2) ⟨3, by decide⟩ ⟨1, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 2) ⟨3, by decide⟩ ⟨2, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 0) * permM ^ 2) ⟨3, by decide⟩ ⟨3, by decide⟩ = 0 := by decide
    obtain ⟨a, b, c', d, a', b', c'', d'⟩ := m1
    rw [a, b, c', d, h0] at e0
    rw [a', b', c'', d', h0] at e3
    simp only [zpow_one, zpow_zero, one_mul, mul_one] at e0 e3
    exact tuple_eq_one h0 e0.symm h1 e3
  ·
    have e0 := row ⟨0, by decide⟩
    have e2 := row ⟨2, by decide⟩
    have m1 : (weylG2M ^ (4 * 1) * permM ^ 1) ⟨0, by decide⟩ ⟨0, by decide⟩ = -1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 1) ⟨0, by decide⟩ ⟨1, by decide⟩ = -1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 1) ⟨0, by decide⟩ ⟨2, by decide⟩ = -1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 1) ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 1) * permM ^ 1) ⟨2, by decide⟩ ⟨0, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 1) ⟨2, by decide⟩ ⟨1, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 1) ⟨2, by decide⟩ ⟨2, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 1) ⟨2, by decide⟩ ⟨3, by decide⟩ = 1 := by decide
    obtain ⟨a, b, c', d, a', b', c'', d'⟩ := m1
    rw [a, b, c', d, h0, h1] at e0
    rw [a', b', c'', d', h0, h1] at e2
    simp only [zpow_one, zpow_zero, one_mul, mul_one, zpow_neg, inv_one] at e0 e2
    have h2 : c ⟨2, by decide⟩ = 1 := inv_eq_one.1 e0.symm
    rw [h2, one_mul] at e2
    exact tuple_eq_one h0 h1 h2 e2.symm
  ·
    have e1 := row ⟨1, by decide⟩
    have e2 := row ⟨2, by decide⟩
    have m1 : (weylG2M ^ (4 * 1) * permM ^ 2) ⟨1, by decide⟩ ⟨0, by decide⟩ = -1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 2) ⟨1, by decide⟩ ⟨1, by decide⟩ = -1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 2) ⟨1, by decide⟩ ⟨2, by decide⟩ = -1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 2) ⟨1, by decide⟩ ⟨3, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 1) * permM ^ 2) ⟨2, by decide⟩ ⟨0, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 2) ⟨2, by decide⟩ ⟨1, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 2) ⟨2, by decide⟩ ⟨2, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 1) * permM ^ 2) ⟨2, by decide⟩ ⟨3, by decide⟩ = 1 := by decide
    obtain ⟨a, b, c', d, a', b', c'', d'⟩ := m1
    rw [a, b, c', d, h0, h1] at e1
    rw [a', b', c'', d', h0, h1] at e2
    simp only [zpow_one, zpow_zero, one_mul, mul_one, zpow_neg, inv_one] at e1 e2
    have h2 : c ⟨2, by decide⟩ = 1 := inv_eq_one.1 e1.symm
    rw [h2, one_mul] at e2
    exact tuple_eq_one h0 h1 h2 e2.symm
  ·
    have e1 := row ⟨1, by decide⟩
    have e0 := row ⟨0, by decide⟩
    have m1 : (weylG2M ^ (4 * 2) * permM ^ 1) ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 2) * permM ^ 1) ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 2) * permM ^ 1) ⟨1, by decide⟩ ⟨2, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 2) * permM ^ 1) ⟨1, by decide⟩ ⟨3, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 2) * permM ^ 1) ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 2) * permM ^ 1) ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 2) * permM ^ 1) ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 2) * permM ^ 1) ⟨0, by decide⟩ ⟨3, by decide⟩ = 1 := by decide
    obtain ⟨a, b, c', d, a', b', c'', d'⟩ := m1
    rw [a, b, c', d, h0, h1] at e1
    rw [a', b', c'', d', h0, h1] at e0
    simp only [zpow_one, zpow_zero, one_mul, mul_one] at e1 e0
    have h2 : c ⟨2, by decide⟩ = 1 := e1.symm
    rw [h2, one_mul] at e0
    exact tuple_eq_one h0 h1 h2 e0.symm
  ·
    have e0 := row ⟨0, by decide⟩
    have e1 := row ⟨1, by decide⟩
    have m1 : (weylG2M ^ (4 * 2) * permM ^ 2) ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 2) * permM ^ 2) ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 2) * permM ^ 2) ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 2) * permM ^ 2) ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 2) * permM ^ 2) ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 2) * permM ^ 2) ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 ∧
        (weylG2M ^ (4 * 2) * permM ^ 2) ⟨1, by decide⟩ ⟨2, by decide⟩ = 1 ∧
        (weylG2M ^ (4 * 2) * permM ^ 2) ⟨1, by decide⟩ ⟨3, by decide⟩ = 1 := by decide
    obtain ⟨a, b, c', d, a', b', c'', d'⟩ := m1
    rw [a, b, c', d, h0, h1] at e0
    rw [a', b', c'', d', h0, h1] at e1
    simp only [zpow_one, zpow_zero, one_mul, mul_one] at e0 e1
    have h2 : c ⟨2, by decide⟩ = 1 := e0.symm
    rw [h2, one_mul] at e1
    exact tuple_eq_one h0 h1 h2 e1.symm

end Fixed

section D4


variable {K : Type} [Field K] [Finite K]

theorem conj_injective_adj :
    Function.Injective (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hZ : Subgroup.center ↥(adjointGroup Tag.D4 K) = ⊥ := center_adjointGroup_eq_bot
  have hgc : g ∈ Subgroup.center ↥(adjointGroup Tag.D4 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => φ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = g * (g⁻¹ * y * g) := by group
      _ = g * y := by
        have h3 : g⁻¹ * y * g = y := by
          calc g⁻¹ * y * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [this]
            _ = y := by group
        rw [h3]
  rw [hZ] at hgc
  exact hgc

open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple in
theorem gammaP_HSL_not_inner {ω : Kˣ} (hω : orderOf ω = 3) (hK3 : 3 ≤ Nat.card K) :
    gammaP K (HSL ω) ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)).range := by
  rintro ⟨g, hg⟩
  set h := sl2At K ⟨2, by decide⟩ (HSL ω)
  set g' := h⁻¹ * g
  have hγ : d4Graph K 1 = MulAut.conj g' := by
    rw [map_mul, map_inv, hg, gammaP, ← mul_assoc, inv_mul_cancel, one_mul]
  have hfix : d4Graph K 1 g' = g' := by
    apply conj_injective_adj
    have e : MulAut.conj (d4Graph K 1 g') = d4Graph K 1 * MulAut.conj g' * (d4Graph K 1)⁻¹ := by
      ext y
      simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [e, ← hγ, mul_inv_cancel_right]
  have hcen : (⟨g', mem_fixSubgroup.2 hfix⟩ : ↥(fixSubgroup (d4Graph K 1))) ∈
      Subgroup.center ↥(fixSubgroup (d4Graph K 1)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨yv, hyv⟩ := y
    have hy : d4Graph K 1 yv = yv := mem_fixSubgroup.1 hyv
    rw [hγ, MulAut.conj_apply] at hy
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    calc yv * g' = g' * yv * g'⁻¹ * g' := by rw [hy]
      _ = g' * yv := by group
  set Φ := fixSubgroupEquivG2 K hK3
  have hΦ : Φ ⟨g', mem_fixSubgroup.2 hfix⟩ ∈ Subgroup.center ↥(adjointGroup Tag.G2 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := Φ.surjective z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hcen) w]
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hΦ
  have hg1 : g' = 1 := congrArg Subtype.val (Φ.injective (hΦ.trans (map_one Φ).symm))
  rw [hg1, map_one] at hγ
  have hmove := d4Graph_one_torusSub (coe_torusElement (K := K) ⟨0, by decide⟩ ω)
  rw [hγ, MulAut.one_apply, coe_torusElement, tupAct_zpow] at hmove
  have h0 := congrFun (rootDiagUnit_injective_D4 hmove) ⟨0, by decide⟩
  have hmod := (zpow_eq_zpow_iff_modEq).1 h0
  rw [hω] at hmod
  have hfact : Tag.D4.cartan ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 ∧
      permM.mulVec (fun j => Tag.D4.cartan ⟨0, by decide⟩ j) ⟨0, by decide⟩ = 0 := by decide
  rw [hfact.1, hfact.2] at hmod
  exact absurd (Int.ModEq.dvd hmod) (by decide)

variable {ω : Kˣ} (hω3 : ω ^ 3 = 1)

theorem yP_pow_conj_mem (μ : Subgroup Kˣ) (k : ℕ) {g : ↥(adjointGroup Tag.D4 K)}
    (hg : g ∈ torusSub μ) : yP hω3 ^ k * g * (yP hω3 ^ k)⁻¹ ∈ torusSub μ := by
  obtain ⟨a, ha, hga⟩ := hg
  exact ⟨_, tupAct_mem μ _ ha, yP_pow_conj_diag hω3 k hga⟩

theorem yP_mem_normalizer (μ : Subgroup Kˣ) :
    yP hω3 ∈ Subgroup.normalizer (torusSub (K := K) μ : Set ↥(adjointGroup Tag.D4 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    simpa using yP_pow_conj_mem hω3 μ 1 hg
  · intro hg
    have h2 := yP_pow_conj_mem hω3 μ 2 hg
    have h3 := yP_pow_three (K := K) hω3
    have e : yP hω3 ^ 2 * (yP hω3 * g * (yP hω3)⁻¹) * (yP hω3 ^ 2)⁻¹ = g := by
      have : yP hω3 ^ 2 * (yP hω3 * g * (yP hω3)⁻¹) * (yP hω3 ^ 2)⁻¹ =
          yP hω3 ^ 3 * g * (yP hω3 ^ 3)⁻¹ := by group
      rw [this, h3, one_mul, inv_one, mul_one]
    rwa [e] at h2

theorem yP_zpow_eq (k : ℤ) : yP hω3 ^ k = yP hω3 ^ (k % 3).toNat := by
  have h3 := yP_pow_three (K := K) hω3
  have hk : k = (k % 3) + 3 * (k / 3) := by have := Int.mul_ediv_add_emod k 3; omega
  have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  conv_lhs => rw [hk]
  rw [zpow_add, zpow_mul, zpow_ofNat, h3, one_zpow, mul_one]

theorem torusSub_inf_zpowers_yP (hω : orderOf ω = 3) (μ : Subgroup Kˣ) :
    torusSub (K := K) μ ⊓ Subgroup.zpowers (yP hω3) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, -, hxa⟩, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [Subgroup.mem_bot, yP_zpow_eq]
  rw [yP_zpow_eq] at hxa
  have hlt : (k % 3).toNat < 3 := by
    have := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
    omega
  rcases (by omega : (k % 3).toNat = 0 ∨ (k % 3).toNat = 1 ∨ (k % 3).toNat = 2) with h | h | h
  · rw [h, pow_zero]
  · exact (yP_pow_not_diag hω3 hω (Or.inl h) hxa).elim
  · exact (yP_pow_not_diag hω3 hω (Or.inr h) hxa).elim

theorem orderOf_yP (hω : orderOf ω = 3) : orderOf (yP (K := K) hω3) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (yP_pow_three hω3) fun h1 => ?_
  have h1' : yP (K := K) hω3 ^ 1 = 1 := by rw [pow_one, h1]
  exact yP_pow_not_diag hω3 hω (Or.inl rfl) (a := 1) (by rw [h1', Subgroup.coe_one,
    rootDiagUnit_one])

@[expose] noncomputable def S1 (μ : Subgroup Kˣ) : Subgroup ↥(adjointGroup Tag.D4 K) :=
  torusSub μ ⊔ Subgroup.zpowers (yP hω3)

theorem card_S1 (hω : orderOf ω = 3) (μ : Subgroup Kˣ) :
    Nat.card (S1 (K := K) hω3 μ) = Nat.card (torusSub (K := K) μ) * 3 := by
  rw [S1, card_sup_of_le_normalizer ((Subgroup.zpowers_le).2 (yP_mem_normalizer hω3 μ))
    (torusSub_inf_zpowers_yP hω3 hω μ), Nat.card_zpowers, orderOf_yP hω3 hω]

theorem gammaP_HSL_pow_diag (ω : Kˣ) (j : ℕ) {g : ↥(adjointGroup Tag.D4 K)}
    {a : Fin Tag.D4.rank → Kˣ} (hga : (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a) :
    (((gammaP K (HSL ω) ^ j) g : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (tupAct (permM ^ j) a) := by
  induction j generalizing g a with
  | zero =>
    rw [pow_zero, MulAut.one_apply, hga, pow_zero, tupAct_one]
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, gammaP_HSL_diag ω (ih hga), tupAct_tupAct, ← pow_succ']

theorem gammaP_HSL_mem_S1 (μ : Subgroup Kˣ) {x : ↥(adjointGroup Tag.D4 K)}
    (hx : x ∈ S1 hω3 μ) : gammaP K (HSL ω) x ∈ S1 hω3 μ := by
  obtain ⟨t, ht, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup ((Subgroup.zpowers_le).2 (yP_mem_normalizer hω3 μ)) hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [map_mul, map_zpow, gammaP_HSL_yP]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  obtain ⟨a, ha, hta⟩ := ht
  exact ⟨_, tupAct_mem μ _ ha, gammaP_HSL_diag ω hta⟩

theorem beta_diag (μ : Subgroup Kˣ) {s : ↥(adjointGroup Tag.D4 K)} (hs : s ∈ S1 hω3 μ)
    (j : ℕ) : ∃ k < 3, ∀ (g : ↥(adjointGroup Tag.D4 K)) (a : Fin Tag.D4.rank → Kˣ),
      (g : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a →
      (((MulAut.conj s * gammaP K (HSL ω) ^ j) g : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        rootDiagUnit Tag.D4 (tupAct (weylG2M ^ (4 * k) * permM ^ j) a) := by
  obtain ⟨t, ht, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup ((Subgroup.zpowers_le).2 (yP_mem_normalizer hω3 μ)) hs
  obtain ⟨k0, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  obtain ⟨c, -, htc⟩ := ht
  refine ⟨(k0 % 3).toNat, by have := Int.emod_lt_of_pos k0 (by norm_num : (0 : ℤ) < 3); omega,
    fun g a hga => ?_⟩
  have h1 := gammaP_HSL_pow_diag ω j hga
  have h2 := yP_pow_conj_diag hω3 (k0 % 3).toNat h1
  rw [MulAut.mul_apply, MulAut.conj_apply, yP_zpow_eq, mul_inv_rev,
    show t * yP hω3 ^ (k0 % 3).toNat * (gammaP K (HSL ω) ^ j) g *
        ((yP hω3 ^ (k0 % 3).toNat)⁻¹ * t⁻¹) =
      t * (yP hω3 ^ (k0 % 3).toNat * (gammaP K (HSL ω) ^ j) g *
        (yP hω3 ^ (k0 % 3).toNat)⁻¹) * t⁻¹ by group,
    commute_of_diag htc h2, mul_inv_cancel_right, h2, tupAct_tupAct]

theorem card_fixed_le (μ : Subgroup Kˣ) {s : ↥(adjointGroup Tag.D4 K)} (hs : s ∈ S1 hω3 μ)
    {j : ℕ} (hj : 0 < j) (hj3 : j < 3) {F : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hF : F ≤ torusSub μ) (hfix : ∀ x ∈ F, (MulAut.conj s * gammaP K (HSL ω) ^ j) x = x) :
    Nat.card F ≤ Nat.card μ ^ 2 := by
  classical
  obtain ⟨k, hk, hact⟩ := beta_diag hω3 μ hs j
  have hj12 : j = 1 ∨ j = 2 := by omega
  have hmem : ∀ x : F, ∃ a : Fin Tag.D4.rank → Kˣ, (∀ i, a i ∈ μ) ∧
      ((x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 a :=
    fun x => hF x.2
  choose a ha hxa using hmem
  have hfixa : ∀ x : F, tupAct (weylG2M ^ (4 * k) * permM ^ j) (a x) = a x := by
    intro x
    have h := hact x (a x) (hxa x)
    rw [hfix x x.2, hxa x] at h
    exact (rootDiagUnit_injective_D4 h).symm
  let ψ : F → μ × μ := fun x => (⟨a x ⟨0, by decide⟩, ha x _⟩, ⟨a x (fixedCoord k), ha x _⟩)
  have hψ : Function.Injective ψ := by
    intro x x' hxx
    have h0 : a x ⟨0, by decide⟩ = a x' ⟨0, by decide⟩ := congrArg (fun p => (p.1 : Kˣ)) hxx
    have h1 : a x (fixedCoord k) = a x' (fixedCoord k) := congrArg (fun p => (p.2 : Kˣ)) hxx
    have hc : tupAct (weylG2M ^ (4 * k) * permM ^ j) (a x * (a x')⁻¹) = a x * (a x')⁻¹ := by
      rw [tupAct_mul, tupAct_inv, hfixa, hfixa]
    have hc1 := fixed_eq_one hk hj12 hc (by rw [Pi.mul_apply, Pi.inv_apply, h0, mul_inv_cancel])
      (by rw [Pi.mul_apply, Pi.inv_apply, h1, mul_inv_cancel])
    have heq : a x = a x' := by
      have := congrArg (· * a x') hc1
      simpa using this
    apply Subtype.ext
    apply Subtype.ext
    rw [hxa, hxa, heq]
  calc Nat.card F ≤ Nat.card (μ × μ) := Nat.card_le_card_of_injective ψ hψ
    _ = Nat.card μ ^ 2 := by rw [Nat.card_prod, sq]

@[expose] noncomputable def T3fix (μ : Subgroup Kˣ) : Subgroup ↥(adjointGroup Tag.D4 K) :=
  torusSub μ ⊓ fixedSubgroup (gammaP K (HSL ω))

theorem card_T3fix_ge (μ : Subgroup Kˣ) (hμ : ∀ u ∈ μ, ∃ b : Kˣ, u = b ^ 2) :
    Nat.card μ ^ 2 ≤ Nat.card (T3fix (ω := ω) (K := K) μ) := by
  classical
  let tup : μ × μ → Fin Tag.D4.rank → Kˣ := fun p j =>
    if j = ⟨2, by decide⟩ then (p.2 : Kˣ) else (p.1 : Kˣ)
  have htup : ∀ p j, tup p j ∈ μ := fun p j => by
    simp only [tup]
    split_ifs
    · exact p.2.2
    · exact p.1.2
  have hρ : ∀ j : Fin Tag.D4.rank, rhoP.symm j = ⟨2, by decide⟩ ↔ j = ⟨2, by decide⟩ := by
    decide
  have hrho : ∀ p, tupAct permM (tup p) = tup p := by
    intro p
    rw [tupAct_permM]
    funext j
    simp only [tup]
    by_cases hj : j = ⟨2, by decide⟩
    · rw [if_pos ((hρ j).2 hj), if_pos hj]
    · rw [if_neg (fun h => hj ((hρ j).1 h)), if_neg hj]
  let f : μ × μ → T3fix (ω := ω) (K := K) μ := fun p =>
    ⟨⟨rootDiagUnit Tag.D4 (tup p), rootDiagUnit_mem_of_sq (fun j => hμ _ (htup p j))⟩,
      ⟨⟨tup p, htup p, rfl⟩, Subtype.ext (by
        rw [gammaP_HSL_diag ω rfl, hrho p])⟩⟩
  have hf : Function.Injective f := by
    intro p p' hpp
    have h := rootDiagUnit_injective_D4 (congrArg (fun z : T3fix (ω := ω) (K := K) μ =>
      ((z : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)) hpp)
    have h0 := congrFun h ⟨0, by decide⟩
    have h2 := congrFun h ⟨2, by decide⟩
    simp only [tup, show (⟨0, by decide⟩ : Fin Tag.D4.rank) ≠ ⟨2, by decide⟩ by decide, if_false,
      if_true] at h0 h2
    exact Prod.ext (Subtype.ext h0) (Subtype.ext h2)
  calc Nat.card μ ^ 2 = Nat.card (μ × μ) := by rw [Nat.card_prod, sq]
    _ ≤ Nat.card (T3fix (ω := ω) (K := K) μ) := Nat.card_le_card_of_injective f hf

theorem yP_mem_normalizer_T3fix (μ : Subgroup Kˣ) :
    yP hω3 ∈ Subgroup.normalizer (T3fix (ω := ω) (K := K) μ : Set ↥(adjointGroup Tag.D4 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hN := Subgroup.mem_normalizer_iff.1 (yP_mem_normalizer hω3 μ) g
  have hfixy : gammaP K (HSL ω) (yP hω3) = yP hω3 := gammaP_HSL_yP hω3
  constructor
  · rintro ⟨hgT, hgα⟩
    refine ⟨hN.1 hgT, ?_⟩
    show gammaP K (HSL ω) _ = _
    rw [map_mul, map_mul, map_inv, hfixy, show gammaP K (HSL ω) g = g from hgα]
  · rintro ⟨hgT, hgα⟩
    refine ⟨hN.2 hgT, ?_⟩
    have h : gammaP K (HSL ω) (yP hω3 * g * (yP hω3)⁻¹) = yP hω3 * g * (yP hω3)⁻¹ := hgα
    rw [map_mul, map_mul, map_inv, hfixy] at h
    show gammaP K (HSL ω) g = g
    have := congrArg (fun z => (yP hω3)⁻¹ * z * yP hω3) h
    simpa [mul_assoc] using this

@[expose] noncomputable def Q0 (μ : Subgroup Kˣ) : Subgroup ↥(adjointGroup Tag.D4 K) :=
  T3fix (ω := ω) μ ⊔ Subgroup.zpowers (yP hω3)

theorem card_Q0 (hω : orderOf ω = 3) (μ : Subgroup Kˣ) :
    Nat.card (Q0 (K := K) hω3 μ) = Nat.card (T3fix (ω := ω) (K := K) μ) * 3 := by
  rw [Q0, card_sup_of_le_normalizer ((Subgroup.zpowers_le).2 (yP_mem_normalizer_T3fix hω3 μ)),
    Nat.card_zpowers, orderOf_yP hω3 hω]
  rw [eq_bot_iff]
  exact le_trans (inf_le_inf_right _ inf_le_left)
    (le_of_eq (torusSub_inf_zpowers_yP hω3 hω μ))

theorem Q0_le_fixed (μ : Subgroup Kˣ) :
    Q0 (K := K) hω3 μ ≤ fixedSubgroup (gammaP K (HSL ω)) :=
  sup_le inf_le_right ((Subgroup.zpowers_le).2 (gammaP_HSL_yP hω3))

theorem Q0_le_centralizer (μ : Subgroup Kˣ) (l : Kˣ) :
    Q0 (K := K) hω3 μ ≤ Subgroup.centralizer
      ({torusElement Tag.D4 K ⟨0, by decide⟩ l * torusElement Tag.D4 K ⟨1, by decide⟩ l⁻¹} :
        Set ↥(adjointGroup Tag.D4 K)) := by
  refine sup_le ?_ ((Subgroup.zpowers_le).2 ?_)
  · rintro x ⟨⟨a, -, hxa⟩, -⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_diag hxa (coe_dTorus l)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact yP_commute_dTorus hω3 l

end D4

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
