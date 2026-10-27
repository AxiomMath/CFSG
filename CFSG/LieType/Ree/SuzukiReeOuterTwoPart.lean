module

public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.Walter.Ree.Model.PSL2
public import CFSG.LieType.Chevalley.GraphTwistedOuterTwoPart

public noncomputable section

namespace CFSG.LieType.Ree.SuzukiReeOuterTwoPart

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree.ReeTag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Walter.Ree.Model
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

theorem suzuki_case
    {T : Type} [Group T] {p f : ℕ} (h : SuzukiModel T p f) :
    ordProj[2] (Nat.card (Outer T)) = 1 ∧ ordProj[2] (Nat.card T) = (p ^ f) ^ 2 := by
  have ho := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} T p f h).1.2.2
  refine ⟨ordProj_two_of_odd ho, ?_⟩
  obtain ⟨rfl, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, suzuki_order hK]
  set q := 2 ^ (2 * a + 1) with hq
  have hq2 : 2 ≤ q := Nat.le_self_pow (by omega) 2
  have hev : Even q := by rw [hq]; exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have h1 : Odd (q - 1) := by
    obtain ⟨r, hr⟩ := hev
    exact ⟨r - 1, by omega⟩
  have h2 : Odd (q ^ 2 + 1) := (hev.pow_of_ne_zero (n := 2) two_ne_zero).add_one
  have hq0 : q ^ 2 ≠ 0 := by positivity
  rw [Nat.ordProj_mul 2 (Nat.mul_ne_zero hq0 (by omega)) (by omega),
    Nat.ordProj_mul 2 hq0 (by omega), ordProj_two_of_odd h1, ordProj_two_of_odd h2, mul_one,
    mul_one, hq, ← pow_mul, Nat.ordProj_self_pow Nat.prime_two]

theorem large_Ree_case
    {T : Type} [Group T] {p f : ℕ} (h : ReeTitsModel T .twistedF4 p f) :
    ordProj[2] (Nat.card (Outer T)) = 1 ∧ 8 ≤ p ^ f ∧ p ^ f ≤ ordProj[2] (Nat.card T) := by
  obtain ⟨rfl, hf3, hodd, -, hcardO, -, hiso⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions T p f h
  refine ⟨by rw [hcardO]; exact ordProj_two_of_odd hodd, ?_, ?_⟩
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  obtain ⟨-, a, hfa, K, _, _, hK, hw⟩ := h
  have : CharP K F4.prime := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  obtain ⟨⟨E⟩, -⟩ := hiso a K hfa hK hw
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hU : Nat.card (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩) = (2 ^ f) ^ 2 := by
    have h1 := Nat.card_congr (large_Ree_B2_fixed_coordinates a K hK').1.equiv
    rw [Nat.card_univ, Nat.card_prod, hK] at h1
    rw [sq]
    exact h1.symm
  have hdvd : 2 ^ (2 * f) ∣ Nat.card T := by
    rw [Nat.card_congr E.toEquiv, pow_mul', ← hU]
    exact Subgroup.card_dvd_of_le
      (inf_le_right : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≤ F4.reeGamma K a)
  have : Finite (F4.reeGamma K a) := by
    have := finite_modGL (τ := F4.tag) (K := K)
    infer_instance
  have hT0 : Nat.card T ≠ 0 := by
    rw [Nat.card_congr E.toEquiv]
    exact Nat.card_pos.ne'
  calc 2 ^ f ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ ordProj[2] (Nat.card T) := pow_le_ordProj_two hT0 hdvd

theorem small_Ree_case
    {T : Type} [Group T] {p f : ℕ} (h : ReeTitsModel T .twistedG2 p f) :
    ordProj[2] (Nat.card (Outer T)) = 1 ∧
      ordProj[2] ((p ^ f) ^ 2 - 1) / 2 ≤ ordProj[2] (Nat.card T) ∧
      4 ≤ ordProj[2] ((p ^ f) ^ 2 - 1) / 2 := by
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T p f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K G2.prime := finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  obtain ⟨-, -, -, -, hoddO, -⟩ := small_Ree_outer_three_kernel_field_complement a' ha K hK'
  have hO : Nat.card (Outer T) = Nat.card (Outer (G2.reeGamma K a')) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence E).toEquiv
  have hfodd : Odd f := ⟨a', hfa⟩
  have h8 := eight_mul_ordProj_two_le Nat.prime_three (by norm_num) (by omega : 1 ≤ f)
  rw [ordProj_two_of_odd hfodd, mul_one] at h8
  refine ⟨by rw [hO]; exact ordProj_two_of_odd hoddO, ?_, by omega⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
  obtain ⟨ψ, hψmem, -, -, -, hψ1, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a' K hK' w₀ hw₀
  have hψle : ψ.range ≤ G2.reeGamma K a' := by
    rintro _ ⟨g, rfl⟩
    exact (inf_le_left : smallReeInvCentralizer a' K ≤ G2.reeGamma K a') (hψmem g)
  have hne : (1 : SL2 K) ≠ -1 := by
    intro h1
    have h2 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.one_apply_eq, Matrix.neg_apply] at h2
    have h3 : ((2 : ℕ) : K) = 0 := by
      push_cast
      linear_combination h2
    rw [CharP.cast_eq_zero_iff K 3] at h3
    omega
  have hker : Nat.card ψ.ker = 2 := by
    have hset : (ψ.ker : Set (SL2 K)) = {1, -1} := Set.ext fun g => by
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hψ1 g
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hne]
  have hSL : Nat.card (SL2 K) = 3 ^ f * ((3 ^ f) ^ 2 - 1) := by
    rw [LinearFlag.card_SL_eq (n := 2) (by norm_num), hK]
    simp
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = Nat.card (SL2 K) := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hq0 : 3 ^ f ≠ 0 := by positivity
  have hq1 : (3 ^ f) ^ 2 - 1 ≠ 0 := by
    have : 3 ≤ 3 ^ f := Nat.le_self_pow (by omega) 3
    have : 9 ≤ (3 ^ f) ^ 2 := by nlinarith
    omega
  have hr0 : Nat.card ψ.range ≠ 0 := fun h0 => by
    rw [h0, mul_zero, hSL] at hmul
    exact Nat.mul_ne_zero hq0 hq1 hmul.symm
  have hqodd : Odd (3 ^ f) := Odd.pow (by decide)
  have h2part : 2 * ordProj[2] (Nat.card ψ.range) = ordProj[2] ((3 ^ f) ^ 2 - 1) := by
    have e1 : 2 * Nat.card ψ.range = Nat.card (SL2 K) := by rw [← hmul, hker]
    rw [← ordProj_two_two_mul hr0, e1, hSL, Nat.ordProj_mul 2 hq0 hq1,
      ordProj_two_of_odd hqodd, one_mul]
  have : Finite (G2.reeGamma K a') := by
    have := finite_modGL (τ := G2.tag) (K := K)
    infer_instance
  have hT : Nat.card T = Nat.card (G2.reeGamma K a') := Nat.card_congr E.toEquiv
  have hΓ0 : Nat.card (G2.reeGamma K a') ≠ 0 := Nat.card_pos.ne'
  have hdvd := Nat.ordProj_dvd_ordProj_of_dvd hΓ0 (Subgroup.card_dvd_of_le hψle) 2
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (by positivity)) hdvd
  rw [hT, ← h2part, Nat.mul_div_cancel_left _ two_pos]
  exact hle


theorem _root_.CFSG.LieType.Ree.suzuki_ree_model_outer_two_part_bound
    (T : Type) [Group T]
    (p f : ℕ) :
    (SuzukiModel T p f →
      ordProj[2] (Nat.card (Outer T)) = 1 ∧ ordProj[2] (Nat.card T) = (p ^ f) ^ 2 ∧
      4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T)) ∧
    (ReeTitsModel T .twistedF4 p f →
      ordProj[2] (Nat.card (Outer T)) = 1 ∧ p ^ f ≤ ordProj[2] (Nat.card T) ∧ 8 ≤ p ^ f ∧
      4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T)) ∧
    (ReeTitsModel T .twistedG2 p f →
      ordProj[2] (Nat.card (Outer T)) = 1 ∧
      ordProj[2] ((p ^ f) ^ 2 - 1) / 2 ≤ ordProj[2] (Nat.card T) ∧
      4 ≤ ordProj[2] ((p ^ f) ^ 2 - 1) / 2 ∧ 4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨ho, ha⟩ := suzuki_case h
    obtain ⟨hp, b, hb, -, -, -, hf, -⟩ := h
    have h4 : 4 ≤ (p ^ f) ^ 2 := by
      rw [hp, hf]
      calc 4 = (2 ^ 1) ^ 2 := by norm_num
        _ ≤ (2 ^ (2 * b + 1)) ^ 2 :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) 2
    exact ⟨ho, ha, ha ▸ h4, by omega⟩
  · obtain ⟨ho, h8, hq⟩ := large_Ree_case h
    exact ⟨ho, hq, h8, by omega, by omega⟩
  · obtain ⟨ho, hq, h4⟩ := small_Ree_case h
    exact ⟨ho, hq, h4, by omega, by omega⟩

end CFSG.LieType.Ree.SuzukiReeOuterTwoPart
