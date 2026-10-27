module

public import CFSG.GH74.GLS.IVK.L2.TorusMatrices
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.SteinbergBSCharTwoSLTwoOdd

public section

namespace CFSG.GroupTheory

open Matrix Subgroup CFSG.GH74.GLS.IVK.L2Torus
open scoped commutatorElement

variable {F : Type*} [Field F]

theorem unipotent_inv (t : F) :
    (CFSG.SL2MinimalFaithful.unipotent t)⁻¹ = CFSG.SL2MinimalFaithful.unipotent (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← CFSG.SL2MinimalFaithful.unipotent_add, add_neg_cancel,
    CFSG.SL2MinimalFaithful.unipotent_zero]

theorem dg_mul_unipotent (a : F) (ha : a ≠ 0) (t : F) :
    dg a a⁻¹ (mul_inv_cancel₀ ha) * CFSG.SL2MinimalFaithful.unipotent t =
      CFSG.SL2MinimalFaithful.unipotent (a * a * t) * dg a a⁻¹ (mul_inv_cancel₀ ha) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg, sl2, CFSG.SL2MinimalFaithful.coe_unipotent,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

private theorem unipotent_range_facts [Finite F] [CharP F 2] :
    IsPGroup 2 (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range ∧
      (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range ≠ ⊥ ∧
      ∀ s ∈ (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range, s * s = 1 := by
  have hcard : Nat.card (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range =
      Nat.card F := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.SL2MinimalFaithful.unipotentHom_injective (F := F))).toEquiv]
    exact Nat.card_congr Multiplicative.toAdd
  have hp : IsPGroup 2 (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range := by
    letI : Fintype F := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    exact IsPGroup.of_card (n := n) (by rw [hcard, Nat.card_eq_fintype_card, hn])
  have hsq : ∀ s ∈ (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range, s * s = 1 := by
    intro s hs
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hs
    change CFSG.SL2MinimalFaithful.unipotent t.toAdd *
      CFSG.SL2MinimalFaithful.unipotent t.toAdd = 1
    rw [← CFSG.SL2MinimalFaithful.unipotent_add, CharTwo.add_self_eq_zero,
      CFSG.SL2MinimalFaithful.unipotent_zero]
  have hne : (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range ≠ ⊥ := by
    intro hbot
    have hmem : CFSG.SL2MinimalFaithful.unipotent 1 ∈
        (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range :=
      MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [hbot] at hmem
    have h1 : CFSG.SL2MinimalFaithful.unipotent (1 : F) = 1 := Subgroup.mem_bot.mp hmem
    exact one_ne_zero (CFSG.SL2MinimalFaithful.unipotent_injective
      (by simpa [← CFSG.SL2MinimalFaithful.unipotent_zero] using h1))
  exact ⟨hp, hne, hsq⟩

private theorem conj_unipotent_mem_range {a : F} (ha0 : a ≠ 0) (t : F) :
    dg a a⁻¹ (mul_inv_cancel₀ ha0) * CFSG.SL2MinimalFaithful.unipotent t *
        (dg a a⁻¹ (mul_inv_cancel₀ ha0))⁻¹ ∈
      (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range := by
  refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (a * a * t), ?_⟩
  symm
  calc dg a a⁻¹ (mul_inv_cancel₀ ha0) * CFSG.SL2MinimalFaithful.unipotent t *
        (dg a a⁻¹ (mul_inv_cancel₀ ha0))⁻¹
      = (CFSG.SL2MinimalFaithful.unipotent (a * a * t) *
          dg a a⁻¹ (mul_inv_cancel₀ ha0)) *
          (dg a a⁻¹ (mul_inv_cancel₀ ha0))⁻¹ := by rw [dg_mul_unipotent a ha0 t]
    _ = CFSG.SL2MinimalFaithful.unipotent (a * a * t) := by group
    _ = CFSG.SL2MinimalFaithful.unipotentHom (Multiplicative.ofAdd (a * a * t)) := rfl

private theorem dg_mem_normalizer_unipotent_range {a : F} (ha0 : a ≠ 0) :
    dg a a⁻¹ (mul_inv_cancel₀ ha0) ∈
      Subgroup.normalizer ((CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range :
        Set (SL2m F)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro s ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
    exact conj_unipotent_mem_range ha0 t.toAdd
  · intro s hs
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hs
    refine ⟨CFSG.SL2MinimalFaithful.unipotent
      ((a * a)⁻¹ * t.toAdd), MonoidHom.mem_range.mpr
      ⟨Multiplicative.ofAdd ((a * a)⁻¹ * t.toAdd), rfl⟩, ?_⟩
    change dg a a⁻¹ (mul_inv_cancel₀ ha0) *
        CFSG.SL2MinimalFaithful.unipotent ((a * a)⁻¹ * t.toAdd) *
        (dg a a⁻¹ (mul_inv_cancel₀ ha0))⁻¹ =
        CFSG.SL2MinimalFaithful.unipotent t.toAdd
    rw [dg_mul_unipotent a ha0 ((a * a)⁻¹ * t.toAdd)]
    rw [mul_assoc, mul_inv_cancel, mul_one]
    congr 1
    field_simp [ha0]

private theorem exists_commutator_dg_unipotent [CharP F 2] {a : F} (ha0 : a ≠ 0)
    (haa : a * a ≠ 1) :
    ∃ s ∈ (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range,
      ⁅dg a a⁻¹ (mul_inv_cancel₀ ha0), s⁆ ≠ 1 := by
  let t : F := (a * a + 1)⁻¹
  have hden : a * a + 1 ≠ 0 := by
    intro h0
    have hsq : a * a = 1 := by
      have hneg := eq_neg_of_add_eq_zero_left h0
      rwa [CharTwo.neg_eq] at hneg
    exact haa hsq
  refine ⟨CFSG.SL2MinimalFaithful.unipotent t, MonoidHom.mem_range.mpr
    ⟨Multiplicative.ofAdd t, rfl⟩, ?_⟩
  have hcomm : ⁅dg a a⁻¹ (mul_inv_cancel₀ ha0),
      CFSG.SL2MinimalFaithful.unipotent t⁆ =
      CFSG.SL2MinimalFaithful.unipotent (a * a * t + -t) := by
    rw [commutatorElement_def]
    calc dg a a⁻¹ (mul_inv_cancel₀ ha0) * CFSG.SL2MinimalFaithful.unipotent t *
          (dg a a⁻¹ (mul_inv_cancel₀ ha0))⁻¹ *
          (CFSG.SL2MinimalFaithful.unipotent t)⁻¹
        = (CFSG.SL2MinimalFaithful.unipotent (a * a * t) *
            dg a a⁻¹ (mul_inv_cancel₀ ha0)) *
            (dg a a⁻¹ (mul_inv_cancel₀ ha0))⁻¹ *
            (CFSG.SL2MinimalFaithful.unipotent t)⁻¹ := by
          rw [dg_mul_unipotent a ha0 t]
      _ = CFSG.SL2MinimalFaithful.unipotent (a * a * t) *
            (CFSG.SL2MinimalFaithful.unipotent t)⁻¹ := by group
      _ = CFSG.SL2MinimalFaithful.unipotent (a * a * t) *
            CFSG.SL2MinimalFaithful.unipotent (-t) := by rw [unipotent_inv]
      _ = CFSG.SL2MinimalFaithful.unipotent (a * a * t + -t) := by
            rw [← CFSG.SL2MinimalFaithful.unipotent_add]
  rw [hcomm]
  have hexp : a * a * t + -t = 1 := by
    dsimp [t]
    rw [CharTwo.neg_eq]
    have hc := mul_inv_cancel₀ hden
    calc a * a * (a * a + 1)⁻¹ + (a * a + 1)⁻¹
        = (a * a + 1) * (a * a + 1)⁻¹ := by ring
      _ = 1 := hc
  rw [hexp]
  exact fun h => one_ne_zero (CFSG.SL2MinimalFaithful.unipotent_injective
    (by simpa [← CFSG.SL2MinimalFaithful.unipotent_zero] using h))

theorem exists_conj_mem_diagSub_of_odd_order_dvd_card_sub_one [Finite F] [CharP F 2]
    {y : SL2m F} (hodd : Odd (orderOf y)) (hdvd : orderOf y ∣ Nat.card F - 1)
    (hy1 : y ≠ 1) : ∃ P : SL2m F, P⁻¹ * y * P ∈ diagSub F := by
  letI : Fintype F := Fintype.ofFinite F
  have hpow : y ^ (Nat.card F - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hqnat : y ^ Nat.card F = y := by
    have hpos : 0 < Nat.card F := Nat.card_pos
    rw [show Nat.card F = Nat.card F - 1 + 1 by omega, pow_succ, hpow, one_mul]
  have hq : y ^ Fintype.card F = y := by
    rwa [Nat.card_eq_fintype_card] at hqnat
  have hmat : ((y : SL2m F) : Matrix (Fin 2) (Fin 2) F) ^ Fintype.card F = y.1 := by
    have := congrArg Subtype.val hq
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  obtain ⟨a, ha⟩ := exists_det_sub_eq_zero F y.1 hmat
  have htr := trace_eq_of_det_sub_eq_zero ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hdet0 : y.1.det = 0 := by simpa using ha
    exact zero_ne_one (hdet0.symm.trans y.2)
  have haa : a * a ≠ 1 := by
    intro hsq
    have htr0 : y.1 0 0 + y.1 1 1 = 0 := by
      rw [hsq] at htr
      rw [show (1 : F) + 1 = 0 from CharTwo.add_self_eq_zero 1] at htr
      exact (mul_eq_zero.mp htr).resolve_left ha0
    have hsqy : y ^ 2 = 1 := by
      rw [pow_two]
      exact CFSG.LocalAnalysis.SteinbergBS.sq_eq_one_of_trace_eq_zero y (by
        rwa [Matrix.trace_fin_two])
    have hdvd2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hsqy
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact hy1 (orderOf_eq_one_iff.mp h)
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hne : a ≠ a⁻¹ := by
    intro h
    exact haa (by simpa [← h] using mul_inv_cancel₀ ha0)
  have htr' : y.1 0 0 + y.1 1 1 = a + a⁻¹ := by
    refine mul_left_cancel₀ ha0 ?_
    rw [htr]
    field_simp
  exact exists_conj_mem_diagSub_of_eigenvalue (mul_inv_cancel₀ ha0) hne htr'

private theorem exists_conj_dg_form [Finite F] [CharP F 2] {y : SL2m F}
    (hodd : Odd (orderOf y)) (hdvd : orderOf y ∣ Nat.card F - 1) (hy1 : y ≠ 1) :
    ∃ (P d : SL2m F) (a : F) (ha0 : a ≠ 0),
      d = P⁻¹ * y * P ∧ d ∈ diagSub F ∧
        d = dg a a⁻¹ (mul_inv_cancel₀ ha0) ∧ a * a ≠ 1 := by
  obtain ⟨P, hP⟩ := exists_conj_mem_diagSub_of_odd_order_dvd_card_sub_one hodd hdvd hy1
  set d : SL2m F := P⁻¹ * y * P with hd
  have ha0 : d.1 0 0 ≠ 0 := by
    intro h0
    have hdet := sl2_det d
    rw [h0, (mem_diagSub.mp hP).1, (mem_diagSub.mp hP).2] at hdet
    simpa using hdet
  have hmul : d.1 0 0 * d.1 1 1 = 1 := by
    have hdet := sl2_det d
    rw [(mem_diagSub.mp hP).1, (mem_diagSub.mp hP).2] at hdet
    simpa using hdet
  have hd_eq : d = dg (d.1 0 0) (d.1 0 0)⁻¹ (mul_inv_cancel₀ ha0) := by
    apply Subtype.ext
    have h11 : d.1 1 1 = (d.1 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hmul
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dg, sl2, h11, (mem_diagSub.mp hP).1, (mem_diagSub.mp hP).2]
  have hd_ne_one : d ≠ 1 := by
    intro hd1
    apply hy1
    calc y = P * d * P⁻¹ := by rw [hd]; group
      _ = 1 := by rw [hd1, mul_one, mul_inv_cancel]
  have haa : d.1 0 0 * d.1 0 0 ≠ 1 := by
    intro hsq
    have ha1 : d.1 0 0 = 1 := by
      have h2 : (d.1 0 0 + 1) ^ 2 = 0 := by
        have h2z : (2 : F) = 0 := CharP.cast_eq_zero F 2
        linear_combination hsq + d.1 0 0 * h2z + h2z
      have h3 := pow_eq_zero_iff two_ne_zero |>.mp h2
      linear_combination h3 - CharP.cast_eq_zero F 2
    apply hd_ne_one
    have h11 : d.1 1 1 = 1 := by simpa [ha1] using hmul
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha1, h11, (mem_diagSub.mp hP).1, (mem_diagSub.mp hP).2]
  exact ⟨P, d, d.1 0 0, ha0, hd, hP, hd_eq, haa⟩

theorem exists_twoSubgroup_normalizer_commutator_eq [Finite F] [CharP F 2] {y : SL2m F}
    (hodd : Odd (orderOf y)) (hdvd : orderOf y ∣ Nat.card F - 1) (hy1 : y ≠ 1) :
    ∃ S : Subgroup (SL2m F),
      IsPGroup 2 S ∧ S ≠ ⊥ ∧ (∀ s ∈ S, s * s = 1) ∧
        y ∈ Subgroup.normalizer (S : Set (SL2m F)) ∧
        ∃ s ∈ S, ⁅y, s⁆ ≠ 1 := by
  obtain ⟨P, d, a, ha0, hd, hP, hd_eq, haa⟩ := exists_conj_dg_form hodd hdvd hy1
  obtain ⟨hS0p, hS0ne, hS0sq⟩ := unipotent_range_facts (F := F)
  have hdS0 : d ∈ Subgroup.normalizer
      ((CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range : Set (SL2m F)) := by
    rw [hd_eq]
    exact dg_mem_normalizer_unipotent_range ha0
  obtain ⟨s, hs, hne⟩ := exists_commutator_dg_unipotent ha0 haa
  refine ⟨(CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range.map
    (MulAut.conj P).toMonoidHom, hS0p.map _, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hS0ne ((Subgroup.map_eq_bot_iff_of_injective
      (H := (CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range)
      (f := (MulAut.conj P).toMonoidHom) (MulAut.conj P).injective).mp hbot)
  · rintro _ ⟨s, hs, rfl⟩
    simpa using hS0sq s hs
  · rw [show y = P * d * P⁻¹ by rw [hd]; group]
    change P * d * P⁻¹ ∈ Subgroup.normalizer
      (((CFSG.SL2MinimalFaithful.unipotentHom (F := F)).range.map
        (MulAut.conj P).toMonoidHom : Subgroup (SL2m F)) : Set (SL2m F))
    rw [← Subgroup.map_equiv_normalizer_eq _ (MulAut.conj P)]
    exact Subgroup.mem_map_of_mem _ hdS0
  · refine ⟨P * s * P⁻¹, Subgroup.mem_map_of_mem _ hs, ?_⟩
    rw [show y = P * d * P⁻¹ by rw [hd]; group]
    change ⁅(MulAut.conj P).toMonoidHom d, (MulAut.conj P).toMonoidHom s⁆ ≠ 1
    rw [hd_eq, ← map_commutatorElement]
    intro h
    exact hne ((MulAut.conj P).injective (by simpa using h))

end CFSG.GroupTheory

end
