module

public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.RootSL2

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley
open scoped MatrixGroups Pointwise

variable {K : Type} [Field K]

theorem coe_conj_lower (w : SL(2, K)) (t : K) :
    ((w * sl2Lower K t * w⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![1 + t * (w : Matrix (Fin 2) (Fin 2) K) 0 1 * (w : Matrix (Fin 2) (Fin 2) K) 1 1,
         -(t * (w : Matrix (Fin 2) (Fin 2) K) 0 1 ^ 2);
         t * (w : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2,
         1 - t * (w : Matrix (Fin 2) (Fin 2) K) 0 1 * (w : Matrix (Fin 2) (Fin 2) K) 1 1] := by
  have hdet := w.det_coe
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two] <;> first | ring1 | linear_combination hdet

theorem conj_lower_of_d_eq_zero (w : SL(2, K)) (hd : (w : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)
    (t : K) :
    w * sl2Lower K t * w⁻¹ = sl2Upper K (-(t * (w : Matrix (Fin 2) (Fin 2) K) 0 1 ^ 2)) := by
  apply Subtype.ext
  rw [coe_conj_lower, hd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem conj_lower_of_d_ne_zero (w : SL(2, K)) (hd : (w : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0)
    (t : K) :
    w * sl2Lower K t * w⁻¹ =
      sl2Upper K ((w : Matrix (Fin 2) (Fin 2) K) 0 1 / (w : Matrix (Fin 2) (Fin 2) K) 1 1) *
        sl2Lower K (t * (w : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2) *
        (sl2Upper K ((w : Matrix (Fin 2) (Fin 2) K) 0 1 / (w : Matrix (Fin 2) (Fin 2) K) 1 1))⁻¹ := by
  apply Subtype.ext
  rw [coe_conj_lower, ← sl2Upper_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring


theorem exists_conj_of_card {L : Type*} [Group L] [Finite L] {J S S' : Subgroup L}
    {p q m n : ℕ} [Fact p.Prime]
    (hq : q = p ^ n) (hJ : Nat.card J = q * m) (hm : ¬ p ∣ m)
    (hS : S ≤ J) (hS' : S' ≤ J) (hc : Nat.card S = q) (hc' : Nat.card S' = q) :
    ∃ w ∈ J, S.map (MulAut.conj w).toMonoidHom = S' := by
  have key : ∀ T : Subgroup L, T ≤ J → Nat.card T = q →
      ∃ P : Sylow p J, (P : Subgroup J) = T.subgroupOf J := by
    intro T hT hTc
    have hcard : Nat.card (T.subgroupOf J) = q := (card_subgroupOf_of_le hT).trans hTc
    have hp : IsPGroup p (T.subgroupOf J) := IsPGroup.of_card (n := n) (hcard.trans hq)
    have hidx : ¬ p ∣ (T.subgroupOf J).index := by
      have h := Subgroup.card_mul_index (T.subgroupOf J)
      rw [hcard, hJ] at h
      have hqpos : 0 < q := by rw [hq]; exact pow_pos (Fact.out : p.Prime).pos n
      have := Nat.eq_of_mul_eq_mul_left hqpos h
      rwa [this]
    exact ⟨hp.toSylow hidx, IsPGroup.toSylow_coe hp hidx⟩
  obtain ⟨P, hP⟩ := key S hS hc
  obtain ⟨P', hP'⟩ := key S' hS' hc'
  obtain ⟨c, hcP⟩ := MulAction.exists_smul_eq J P P'
  refine ⟨c, c.2, ?_⟩
  have h1 : ((c • P : Sylow p J) : Subgroup J) =
      (P : Subgroup J).map (MulAut.conj c).toMonoidHom := coe_smul_sylow_eq_map c P
  rw [hcP, hP', hP, map_conj_subgroupOf hS c] at h1
  have hle : S.map (MulAut.conj (c : L)).toMonoidHom ≤ J := by
    rintro _ ⟨s, hs, rfl⟩
    exact mul_mem (mul_mem c.2 (hS hs)) (inv_mem c.2)
  have h2 := Subgroup.subgroupOf_inj.1 h1.symm
  rwa [inf_of_le_left hle, inf_of_le_left hS'] at h2


section Card

variable [Finite K]

theorem card_sl2 : Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have := Fintype.ofFinite K
  have h := Matrix.card_SL_field (𝔽 := K) 2
  rw [Fin.prod_univ_two, ← Nat.card_eq_fintype_card] at h
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one] at h
  rw [h]
  have hq : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 := ⟨Nat.card K - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  rw [hr]
  have e1 : (r + 1) ^ 2 - 1 = r ^ 2 + 2 * r := by
    have : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
    omega
  have e2 : (r + 1) ^ 2 - (r + 1) = r ^ 2 + r := by
    have : (r + 1) ^ 2 = (r ^ 2 + r) + (r + 1) := by ring
    omega
  rw [e1, e2, Nat.add_sub_cancel]
  refine Nat.div_eq_of_eq_mul_left (by omega) ?_
  ring

theorem exists_pow_card : ∃ n : ℕ, Nat.card K = ringChar K ^ n := by
  have := Fintype.ofFinite K
  have hp : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

end Card


section Rank

variable [Finite K] {L : Type} [Group L] {ρ : SL(2, K) →* L}
  (hker : ∀ g : SL(2, K), ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
    (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K))

include hker in
theorem card_sl2RootX : Nat.card (sl2RootX ρ) = Nat.card K :=
  Nat.card_range_of_injective (sl2Upper_injective hker)

include hker in
theorem card_sl2RootY : Nat.card (sl2RootY ρ) = Nat.card K :=
  Nat.card_range_of_injective (sl2Lower_injective hker)

theorem sl2RootX_le_range : sl2RootX ρ ≤ ρ.range := by
  rintro _ ⟨c, rfl⟩
  exact ⟨sl2Upper K c, rfl⟩

theorem sl2RootY_le_range : sl2RootY ρ ≤ ρ.range := by
  rintro _ ⟨c, rfl⟩
  exact ⟨sl2Lower K c, rfl⟩

include hker in
theorem exists_card_range : ∃ m : ℕ, Nat.card ρ.range = Nat.card K * m ∧ ¬ ringChar K ∣ m := by
  have h1 := card_sl2RootX hker
  have h2 : Nat.card K ∣ Nat.card ρ.range := h1 ▸ Subgroup.card_dvd_of_le sl2RootX_le_range
  obtain ⟨m, hm⟩ := h2
  refine ⟨m, hm, fun hpm => ?_⟩
  have h3 : Nat.card ρ.range ∣ Nat.card SL(2, K) := Subgroup.card_range_dvd ρ
  rw [card_sl2, hm] at h3
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have h4 : m ∣ Nat.card K ^ 2 - 1 := Nat.dvd_of_mul_dvd_mul_left hqpos h3
  have hp : (ringChar K).Prime := CharP.char_is_prime K _
  obtain ⟨n, hn⟩ := exists_pow_card (K := K)
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := K)
    rw [pow_zero] at hn
    omega
  have hpq : ringChar K ∣ Nat.card K := by
    rw [hn]
    exact dvd_pow_self _ hn0
  have h5 : ringChar K ∣ Nat.card K ^ 2 - 1 := hpm.trans h4
  have h6 : ringChar K ∣ Nat.card K ^ 2 := Dvd.dvd.pow hpq two_ne_zero
  have h7 := Nat.dvd_sub h6 h5
  have h8 : Nat.card K ^ 2 - (Nat.card K ^ 2 - 1) = 1 := by
    have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hqpos
    omega
  rw [h8] at h7
  exact hp.one_lt.ne' (Nat.dvd_one.1 h7)

include hker in
theorem exists_conj_of_card_range [Finite L] {S S' : Subgroup L} (hS : S ≤ ρ.range)
    (hS' : S' ≤ ρ.range) (hc : Nat.card S = Nat.card K) (hc' : Nat.card S' = Nat.card K) :
    ∃ w ∈ ρ.range, S.map (MulAut.conj w).toMonoidHom = S' := by
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨m, hm, hpm⟩ := exists_card_range hker
  obtain ⟨n, hn⟩ := exists_pow_card (K := K)
  exact exists_conj_of_card hn hm hpm hS hS' hc hc'

include hker in
theorem exists_conj_upper {w : L} (hw : w ∈ ρ.range)
    (h : sl2RootX ρ ⊓ (sl2RootY ρ).map (MulAut.conj w).toMonoidHom = ⊥) :
    ∃ u ∈ sl2RootX ρ, (sl2RootY ρ).map (MulAut.conj w).toMonoidHom =
      (sl2RootY ρ).map (MulAut.conj u).toMonoidHom := by
  obtain ⟨ŵ, rfl⟩ := hw
  by_cases hd : (ŵ : Matrix (Fin 2) (Fin 2) K) 1 1 = 0
  · exfalso
    have hmemY : ρ (ŵ * sl2Lower K 1 * ŵ⁻¹) ∈
        (sl2RootY ρ).map (MulAut.conj (ρ ŵ)).toMonoidHom :=
      ⟨ρ (sl2Lower K 1), ⟨1, rfl⟩, by simp [MulAut.conj_apply, map_mul, map_inv]⟩
    have hmemX : ρ (ŵ * sl2Lower K 1 * ŵ⁻¹) ∈ sl2RootX ρ := by
      rw [conj_lower_of_d_eq_zero ŵ hd]
      exact ⟨_, rfl⟩
    have h1 : ρ (ŵ * sl2Lower K 1 * ŵ⁻¹) ∈
        sl2RootX ρ ⊓ (sl2RootY ρ).map (MulAut.conj (ρ ŵ)).toMonoidHom := ⟨hmemX, hmemY⟩
    rw [h, Subgroup.mem_bot, map_mul, map_mul, map_inv, mul_inv_eq_one, mul_eq_left] at h1
    have h2 : (1 : K) = 0 :=
      sl2Lower_injective hker (show ρ (sl2Lower K 1) = ρ (sl2Lower K 0) by
        rw [sl2Lower_zero, map_one]; exact h1)
    exact one_ne_zero h2
  · refine ⟨ρ (sl2Upper K ((ŵ : Matrix (Fin 2) (Fin 2) K) 0 1 / (ŵ : Matrix (Fin 2) (Fin 2) K) 1 1)),
      ⟨_, rfl⟩, ?_⟩
    have hd2 : (ŵ : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2 ≠ 0 := pow_ne_zero 2 hd
    ext y
    constructor
    · rintro ⟨y0, ⟨t, rfl⟩, rfl⟩
      refine ⟨ρ (sl2Lower K (t * (ŵ : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2)), ⟨_, rfl⟩, ?_⟩
      have h := congrArg ρ (conj_lower_of_d_ne_zero ŵ hd t)
      simp only [map_mul, map_inv] at h
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact h.symm
    · rintro ⟨y0, ⟨t, rfl⟩, rfl⟩
      refine ⟨ρ (sl2Lower K (t / (ŵ : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2)), ⟨_, rfl⟩, ?_⟩
      have h := congrArg ρ (conj_lower_of_d_ne_zero ŵ hd (t / (ŵ : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2))
      rw [div_mul_cancel₀ t hd2] at h
      simp only [map_mul, map_inv] at h
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact h

include hker in
theorem sl2RootX_inf_sl2RootY : sl2RootX ρ ⊓ sl2RootY ρ = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨⟨c, hcx⟩, ⟨d, hdy⟩⟩ := hx
  simp only at hcx hdy
  rw [Subgroup.mem_bot]
  have h1 : ρ (sl2Upper K c * sl2Lower K (-d)) = 1 := by
    rw [map_mul, sl2Lower_neg, map_inv, hcx, hdy, mul_inv_cancel]
  obtain ⟨l, -, hl⟩ := hker _ h1
  have h2 := congrFun (congrFun hl 0) 1
  simp at h2
  rw [← hcx, h2, sl2Upper_zero, map_one]

include hker in
theorem exists_pairAut_adjust [Finite L] {η : MulAut L}
    (hη : ρ.range.map η.toMonoidHom = ρ.range) :
    ∃ v ∈ ρ.range, MulAut.conj v * η ∈ pairAutSubgroup (sl2RootX ρ) (sl2RootY ρ) := by
  have hXη : (sl2RootX ρ).map η.toMonoidHom ≤ ρ.range := by
    rw [← hη]
    exact Subgroup.map_mono sl2RootX_le_range
  have hcardη : ∀ S : Subgroup L, Nat.card (S.map η.toMonoidHom) = Nat.card S := fun S =>
    Subgroup.card_map_of_injective η.injective
  obtain ⟨c, hc, hcX⟩ := exists_conj_of_card_range hker sl2RootX_le_range hXη
    (card_sl2RootX hker) ((hcardη _).trans (card_sl2RootX hker))
  set η₁ : MulAut L := MulAut.conj c⁻¹ * η with hη₁
  have hJη₁ : ρ.range.map η₁.toMonoidHom = ρ.range := by
    rw [hη₁, map_mulAut_mul, hη, map_conj_self (inv_mem hc)]
  have hXη₁ : (sl2RootX ρ).map η₁.toMonoidHom = sl2RootX ρ := by
    rw [hη₁, map_mulAut_mul, ← hcX, ← map_mulAut_mul, ← map_mul, inv_mul_cancel, map_one,
      map_mulAut_one]
  have hYη₁ : (sl2RootY ρ).map η₁.toMonoidHom ≤ ρ.range := by
    rw [← hJη₁]
    exact Subgroup.map_mono sl2RootY_le_range
  have hcard₁ : Nat.card ((sl2RootY ρ).map η₁.toMonoidHom) = Nat.card K := by
    exact Subgroup.card_map_of_injective η₁.injective |>.trans (card_sl2RootY hker)
  obtain ⟨w, hw, hwY⟩ := exists_conj_of_card_range hker sl2RootY_le_range hYη₁
    (card_sl2RootY hker) hcard₁
  have hinf : sl2RootX ρ ⊓ (sl2RootY ρ).map (MulAut.conj w).toMonoidHom = ⊥ := by
    rw [hwY]
    conv_lhs => rw [← hXη₁]
    rw [← Subgroup.map_inf_eq _ _ _ η₁.injective, sl2RootX_inf_sl2RootY hker, Subgroup.map_bot]
  obtain ⟨u, hu, huY⟩ := exists_conj_upper hker hw hinf
  have hβ : MulAut.conj (c * u)⁻¹ * η = MulAut.conj u⁻¹ * η₁ := by
    rw [hη₁, ← mul_assoc, ← map_mul, mul_inv_rev]
  have hYu : (sl2RootY ρ).map η₁.toMonoidHom = (sl2RootY ρ).map (MulAut.conj u).toMonoidHom := by
    rw [← hwY, huY]
  refine ⟨(c * u)⁻¹, inv_mem (mul_mem hc (sl2RootX_le_range hu)), ?_, ?_⟩
  · show (sl2RootX ρ).map (MulAut.conj (c * u)⁻¹ * η).toMonoidHom = sl2RootX ρ
    rw [hβ, map_mulAut_mul, hXη₁, map_conj_self (inv_mem hu)]
  · show (sl2RootY ρ).map (MulAut.conj (c * u)⁻¹ * η).toMonoidHom = sl2RootY ρ
    rw [hβ, map_mulAut_mul, hYu, ← map_mulAut_mul, ← map_mul, inv_mul_cancel, map_one,
      map_mulAut_one]

end Rank


theorem coe_conj_upper_mul (w : SL(2, K)) (c m : K) :
    ((w * sl2Upper K c * w⁻¹ * sl2Upper K (-m) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![1 - c * (w : Matrix (Fin 2) (Fin 2) K) 0 0 * (w : Matrix (Fin 2) (Fin 2) K) 1 0,
         -m * (1 - c * (w : Matrix (Fin 2) (Fin 2) K) 0 0 * (w : Matrix (Fin 2) (Fin 2) K) 1 0) +
           c * (w : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2;
         -(c * (w : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2),
         m * c * (w : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 + 1 +
           c * (w : Matrix (Fin 2) (Fin 2) K) 0 0 * (w : Matrix (Fin 2) (Fin 2) K) 1 0] := by
  have hdet := w.det_coe
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two] <;> first | ring1 | linear_combination hdet | linear_combination (-m) * hdet | linear_combination m * hdet


section Square

variable [Finite K] {L : Type} [Group L] {ρ : SL(2, K) →* L}
  (hker : ∀ g : SL(2, K), ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
    (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K))

theorem entry_conj_upper_mul (w : SL(2, K)) (c m : K) :
    (((w * sl2Upper K c * w⁻¹ * sl2Upper K (-m) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      -(c * (w : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2)) ∧
    (((w * sl2Upper K c * w⁻¹ * sl2Upper K (-m) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      1 - c * (w : Matrix (Fin 2) (Fin 2) K) 0 0 * (w : Matrix (Fin 2) (Fin 2) K) 1 0) ∧
    (((w * sl2Upper K c * w⁻¹ * sl2Upper K (-m) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      -m * (1 - c * (w : Matrix (Fin 2) (Fin 2) K) 0 0 * (w : Matrix (Fin 2) (Fin 2) K) 1 0) +
           c * (w : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2) := by
  rw [coe_conj_upper_mul]
  exact ⟨rfl, rfl, rfl⟩

include hker in
theorem exists_sq_of_conj_upper {e : L} (he : e ∈ ρ.range) {μ : K → K}
    (h : ∀ c, e * ρ (sl2Upper K c) * e⁻¹ = ρ (sl2Upper K (μ c))) :
    ∃ p : Kˣ, ∀ c, μ c = (p : K) ^ 2 * c := by
  obtain ⟨w, rfl⟩ := he
  have key : ∀ c : K, ∃ l : Kˣ, l ^ 2 = 1 ∧
      ((w * sl2Upper K c * w⁻¹ * sl2Upper K (-μ c) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        (l : K) • (1 : Matrix (Fin 2) (Fin 2) K) := fun c => by
    refine hker _ ?_
    have hc := h c
    simp only [map_mul, map_inv, sl2Upper_neg]
    rw [hc, mul_inv_cancel]
  obtain ⟨l1, -, hl1⟩ := key 1
  have h10 := congrFun (congrFun hl1 1) 0
  rw [(entry_conj_upper_mul w 1 (μ 1)).1] at h10
  have hr : (w : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have : (w : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 = 0 := by
      have h' : -(1 * (w : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2) = 0 := by
        rw [h10]; simp
      linear_combination -h'
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have hdet := w.det_coe
  rw [Matrix.det_fin_two, hr] at hdet
  have ha : (w : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  obtain ⟨a, ha'⟩ : ∃ a : Kˣ, (a : K) = (w : Matrix (Fin 2) (Fin 2) K) 0 0 :=
    ⟨Units.mk0 _ ha, rfl⟩
  refine ⟨a, fun c => ?_⟩
  obtain ⟨l, -, hl⟩ := key c
  have h00 := congrFun (congrFun hl 0) 0
  have h01 := congrFun (congrFun hl 0) 1
  have e00 : ((l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 = l := by simp
  have e01 : ((l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) 0 1 = 0 := by simp
  rw [(entry_conj_upper_mul w c (μ c)).2.1, hr, e00] at h00
  rw [(entry_conj_upper_mul w c (μ c)).2.2, hr, e01] at h01
  rw [ha']
  linear_combination (-1 : K) * h01 + (μ c) * h00 - (μ c) * h00

end Square


theorem sl2Diag_mul_lower' (t : Kˣ) (c : K) :
    sl2Diag K t * sl2Lower K c = sl2Lower K (((t⁻¹ : Kˣ) : K) ^ 2 * c) * sl2Diag K t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp

section Diag

variable {L : Type} [Group L] {ρ : SL(2, K) →* L}

theorem eq_conj_diag {α : MulAut L} {r : Kˣ}
    (hx : ∀ c, α (ρ (sl2Upper K c)) = ρ (sl2Upper K ((r : K) ^ 2 * c)))
    (hy : ∀ c, α (ρ (sl2Lower K c)) = ρ (sl2Lower K (((r⁻¹ : Kˣ) : K) ^ 2 * c))) :
    ∀ y ∈ ρ.range, α y = ρ (sl2Diag K r) * y * (ρ (sl2Diag K r))⁻¹ := by
  have h : (α : L →* L).comp ρ = (MulAut.conj (ρ (sl2Diag K r))).toMonoidHom.comp ρ := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change α (ρ (sl2Upper K c)) = ρ (sl2Diag K r) * ρ (sl2Upper K c) * (ρ (sl2Diag K r))⁻¹
      rw [hx, ← map_mul, sl2Diag_mul_upper, map_mul, mul_inv_cancel_right]
    · change α (ρ (sl2Lower K c)) = ρ (sl2Diag K r) * ρ (sl2Lower K c) * (ρ (sl2Diag K r))⁻¹
      rw [hy, ← map_mul, sl2Diag_mul_lower', map_mul, mul_inv_cancel_right]
  rintro _ ⟨g, rfl⟩
  exact DFunLike.congr_fun h g

end Diag

end CFSG.HardMathSupport.Dickson.Sec6.I1431.RootSL2
