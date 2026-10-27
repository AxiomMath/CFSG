module

public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.GroupTheory.GL52.Simple
public import Mathlib.Tactic.NormNum.Prime

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

@[expose] def s31M : M5 :=
  !![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]

@[expose] def phi31M : M5 :=
  !![1, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 0, 1, 1; 0, 0, 1, 0, 0]

set_option maxRecDepth 100000 in
theorem syl31_facts : s31M ^ 31 = 1 ∧ s31M * s31M ^ 30 = 1 ∧ s31M ≠ 1 ∧ phi31M ^ 5 = 1 ∧
    phi31M * phi31M ^ 4 = 1 ∧ phi31M ≠ 1 ∧ s31M ^ 5 + s31M ^ 2 + 1 = 0 ∧
    (∀ j : Fin 5, phi31M ^ (j : ℕ) * s31M = s31M ^ (2 ^ (j : ℕ)) * phi31M ^ (j : ℕ)) ∧
    (∀ j : Fin 5, (j : ℕ) ≠ 0 → phi31M ^ (j : ℕ) * s31M ≠ s31M * phi31M ^ (j : ℕ)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem syl31_minpoly : ∀ k : Fin 31, (s31M ^ (k : ℕ)) ^ 5 + (s31M ^ (k : ℕ)) ^ 2 + 1 = 0 →
    (k : ℕ) = 1 ∨ (k : ℕ) = 2 ∨ (k : ℕ) = 4 ∨ (k : ℕ) = 8 ∨ (k : ℕ) = 16 := by
  decide +kernel

theorem syl31_mulVec_single :
    s31M *ᵥ Pi.single 0 1 = Pi.single 1 1 ∧ s31M *ᵥ Pi.single 1 1 = Pi.single 2 1 ∧
      s31M *ᵥ Pi.single 2 1 = Pi.single 3 1 ∧ s31M *ᵥ Pi.single 3 1 = Pi.single 4 1 := by
  decide +kernel

@[expose] def s31 : G52 :=
  mk5 s31M (s31M ^ 30) syl31_facts.2.1

@[expose] def phi31 : G52 :=
  mk5 phi31M (phi31M ^ 4) syl31_facts.2.2.2.2.1

theorem orderOf_s31 : orderOf s31 = 31 := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h => syl31_facts.2.2.1 ?_
  · rw [Units.val_pow_eq_pow_val, s31, coe_mk5, Units.val_one]
    exact syl31_facts.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [s31] using this

theorem orderOf_phi31 : orderOf phi31 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h => syl31_facts.2.2.2.2.2.1 ?_
  · rw [Units.val_pow_eq_pow_val, phi31, coe_mk5, Units.val_one]
    exact syl31_facts.2.2.2.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [phi31] using this

theorem syl31_eq_of_commute {A B : M5} (hA : A * s31M = s31M * A) (hB : B * s31M = s31M * B)
    (h : A *ᵥ Pi.single 0 1 = B *ᵥ Pi.single 0 1) : A = B := by
  obtain ⟨h1, h2, h3, h4⟩ := syl31_mulVec_single
  have e1 : A *ᵥ Pi.single 1 1 = B *ᵥ Pi.single 1 1 := by
    rw [← h1, mulVec_comm hA, mulVec_comm hB, h]
  have e2 : A *ᵥ Pi.single 2 1 = B *ᵥ Pi.single 2 1 := by
    rw [← h2, mulVec_comm hA, mulVec_comm hB, e1]
  have e3 : A *ᵥ Pi.single 3 1 = B *ᵥ Pi.single 3 1 := by
    rw [← h3, mulVec_comm hA, mulVec_comm hB, e2]
  have e4 : A *ᵥ Pi.single 4 1 = B *ᵥ Pi.single 4 1 := by
    rw [← h4, mulVec_comm hA, mulVec_comm hB, e3]
  refine ext_cols fun j => ?_
  fin_cases j
  exacts [h, e1, e2, e3, e4]

theorem syl31_matrix_commute {g : G52} (hg : g ∈ Subgroup.centralizer {s31}) :
    (g : M5) * s31M = s31M * (g : M5) := by
  have := congrArg (fun x : G52 => (x : M5)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [s31] using this

theorem syl31_card_nonzero : Nat.card {v : V5 // v ≠ 0} = 31 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem syl31_card_centralizer_le : Nat.card (Subgroup.centralizer {s31}) ≤ 31 := by
  have he : (Pi.single 0 1 : V5) ≠ 0 := by decide
  let f : Subgroup.centralizer {s31} → {v : V5 // v ≠ 0} := fun g =>
    ⟨((g : G52) : M5) *ᵥ Pi.single 0 1, fun h => he (eq_zero_of_mulVec_eq_zero _ h)⟩
  have hf : Function.Injective f := by
    intro g h hgh
    have e : ((g : G52) : M5) *ᵥ Pi.single 0 1 = ((h : G52) : M5) *ᵥ Pi.single 0 1 :=
      congrArg Subtype.val hgh
    exact Subtype.ext (Units.ext (syl31_eq_of_commute (syl31_matrix_commute g.2)
      (syl31_matrix_commute h.2) e))
  calc Nat.card (Subgroup.centralizer {s31}) ≤ Nat.card {v : V5 // v ≠ 0} :=
        Nat.card_le_card_of_injective f hf
    _ = 31 := syl31_card_nonzero

theorem syl31_centralizer_eq : Subgroup.centralizer {s31} = Subgroup.zpowers s31 := by
  have hle : Subgroup.zpowers s31 ≤ Subgroup.centralizer {s31} := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, orderOf_s31]
  exact syl31_card_centralizer_le

theorem syl31_card_zpowers : Nat.card (Subgroup.zpowers s31) = 31 := by
  rw [Nat.card_zpowers, orderOf_s31]

theorem syl31_card_zpowers_phi : Nat.card (Subgroup.zpowers phi31) = 5 := by
  rw [Nat.card_zpowers, orderOf_phi31]

theorem syl31_phi_pow_mul (j : ℕ) (hj : j < 5) :
    phi31 ^ j * s31 = s31 ^ (2 ^ j) * phi31 ^ j := by
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, phi31, s31, coe_mk5]
  exact syl31_facts.2.2.2.2.2.2.2.1 ⟨j, hj⟩

theorem syl31_phi_mem_normalizer :
    phi31 ∈ Subgroup.normalizer (Subgroup.zpowers s31 : Set G52) := by
  have h := syl31_phi_pow_mul 1 (by norm_num)
  simp only [pow_one] at h
  have e : phi31 * s31 * phi31⁻¹ = s31 ^ 2 := by rw [h, mul_inv_cancel_right]
  exact mem_normalizer_zpowers_of_conj_mem (e ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers s31) 2)

theorem syl31_cover {g : G52} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers s31 : Set G52)) :
    ∃ j < 5, (phi31 ^ j)⁻¹ * g ∈ Subgroup.zpowers s31 := by
  classical
  have hmem : g * s31 * g⁻¹ ∈ Subgroup.zpowers s31 :=
    (Subgroup.mem_normalizer_iff.1 hg s31).1 (Subgroup.mem_zpowers s31)
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_s31] at hmem
  obtain ⟨k, hk, hgk⟩ := Finset.mem_image.1 hmem
  rw [Finset.mem_range] at hk
  have hroot : (s31M ^ k) ^ 5 + (s31M ^ k) ^ 2 + 1 = 0 := by
    have e : (s31M ^ k : M5) = (g : M5) * s31M * ((g⁻¹ : G52) : M5) := by
      have := congrArg (fun x : G52 => (x : M5)) hgk
      simpa [s31] using this
    have hgg : ((g⁻¹ : G52) : M5) * (g : M5) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hpow : ∀ n : ℕ, ((g : M5) * s31M * ((g⁻¹ : G52) : M5)) ^ n =
        (g : M5) * s31M ^ n * ((g⁻¹ : G52) : M5) := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      | succ n ih =>
        rw [pow_succ, ih, pow_succ]
        calc (g : M5) * s31M ^ n * ((g⁻¹ : G52) : M5) * ((g : M5) * s31M * ((g⁻¹ : G52) : M5))
            = (g : M5) * s31M ^ n * (((g⁻¹ : G52) : M5) * (g : M5)) * s31M *
                ((g⁻¹ : G52) : M5) := by noncomm_ring
          _ = _ := by rw [hgg, mul_one, mul_assoc (g : M5)]
    have hone' : (g : M5) * ((g⁻¹ : G52) : M5) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have key : (g : M5) * (s31M ^ 5 + s31M ^ 2 + 1) * ((g⁻¹ : G52) : M5) = 0 := by
      rw [syl31_facts.2.2.2.2.2.2.1, mul_zero, zero_mul]
    rw [e, hpow, hpow, ← key, mul_add, mul_add, add_mul, add_mul, mul_one, hone']
  have hk' := syl31_minpoly ⟨k, hk⟩ hroot
  obtain ⟨j, hj, hkj⟩ : ∃ j < 5, k = 2 ^ j := by
    simp only at hk'
    rcases hk' with h | h | h | h | h
    · exact ⟨0, by norm_num, by rw [h]; rfl⟩
    · exact ⟨1, by norm_num, by rw [h]; rfl⟩
    · exact ⟨2, by norm_num, by rw [h]; rfl⟩
    · exact ⟨3, by norm_num, by rw [h]; rfl⟩
    · exact ⟨4, by norm_num, by rw [h]; rfl⟩
  refine ⟨j, hj, ?_⟩
  rw [← syl31_centralizer_eq, Subgroup.mem_centralizer_singleton_iff]
  have hgs : g * s31 = s31 ^ (2 ^ j) * g := by
    rw [← hkj, hgk, inv_mul_cancel_right]
  have hφ := syl31_phi_pow_mul j hj
  calc (phi31 ^ j)⁻¹ * g * s31 = (phi31 ^ j)⁻¹ * (s31 ^ (2 ^ j) * g) := by rw [mul_assoc, hgs]
    _ = (phi31 ^ j)⁻¹ * (phi31 ^ j * s31 * (phi31 ^ j)⁻¹ * g) := by
        rw [hφ, mul_inv_cancel_right]
    _ = s31 * ((phi31 ^ j)⁻¹ * g) := by group

theorem syl31_disj (j : ℕ) (hj : j < 5) (h : phi31 ^ j ∈ Subgroup.zpowers s31) : j = 0 := by
  by_contra hj0
  rw [← syl31_centralizer_eq, Subgroup.mem_centralizer_singleton_iff] at h
  apply syl31_facts.2.2.2.2.2.2.2.2 ⟨j, hj⟩ hj0
  have := congrArg (fun x : G52 => (x : M5)) h
  simpa [phi31, s31, Units.val_pow_eq_pow_val] using this

theorem syl31_card_normalizer :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers s31 : Set G52)) = 155 := by
  rw [card_eq_mul_of_cosets Subgroup.le_normalizer syl31_phi_mem_normalizer
    (fun g hg => syl31_cover hg) syl31_disj, syl31_card_zpowers]

theorem syl31_frobenius_data :
    Subgroup.zpowers s31 ≤ Subgroup.normalizer (Subgroup.zpowers s31 : Set G52) ∧
    Subgroup.zpowers phi31 ≤ Subgroup.normalizer (Subgroup.zpowers s31 : Set G52) ∧
    Subgroup.zpowers s31 ⊓ Subgroup.zpowers phi31 = ⊥ ∧
    Subgroup.zpowers s31 ⊔ Subgroup.zpowers phi31 =
      Subgroup.normalizer (Subgroup.zpowers s31 : Set G52) ∧
    (∀ r ∈ Subgroup.zpowers phi31, r ≠ 1 → ∀ k ∈ Subgroup.zpowers s31, k ≠ 1 →
      r * k * r⁻¹ ≠ k) ∧
    Subgroup.zpowers s31 ≠ ⊥ ∧ Subgroup.zpowers phi31 ≠ ⊥ := by
  have hRN : Subgroup.zpowers phi31 ≤ Subgroup.normalizer (Subgroup.zpowers s31 : Set G52) :=
    (Subgroup.zpowers_le).2 syl31_phi_mem_normalizer
  have hinf : Subgroup.zpowers s31 ⊓ Subgroup.zpowers phi31 = ⊥ := by
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [syl31_card_zpowers, syl31_card_zpowers_phi]
    norm_num
  refine ⟨Subgroup.le_normalizer, hRN, hinf, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.eq_of_le_of_card_ge (sup_le Subgroup.le_normalizer hRN) ?_
    rw [syl31_card_normalizer]
    have h31 : 31 ∣ Nat.card (Subgroup.zpowers s31 ⊔ Subgroup.zpowers phi31 : Subgroup G52) := by
      rw [← syl31_card_zpowers]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h5 : 5 ∣ Nat.card (Subgroup.zpowers s31 ⊔ Subgroup.zpowers phi31 : Subgroup G52) := by
      have := Subgroup.card_dvd_of_le
        (le_sup_right : Subgroup.zpowers phi31 ≤ Subgroup.zpowers s31 ⊔ Subgroup.zpowers phi31)
      rwa [syl31_card_zpowers_phi] at this
    have h155 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 31 5) h31 h5
    exact Nat.le_of_dvd Nat.card_pos h155
  · intro r hr hr1 k hk hk1 hfix
    have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    have hgen : (⟨s31, Subgroup.mem_zpowers s31⟩ : Subgroup.zpowers s31) ∈
        Subgroup.zpowers (⟨k, hk⟩ : Subgroup.zpowers s31) :=
      mem_zpowers_of_prime_card syl31_card_zpowers (fun h => hk1 (congrArg Subtype.val h))
    obtain ⟨m, hm⟩ := hgen
    have hm' : k ^ m = s31 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hcomm : r * s31 = s31 * r := by
      have e : r * k = k * r := by
        calc r * k = r * k * r⁻¹ * r := by group
          _ = k * r := by rw [hfix]
      rw [← hm']
      exact (Commute.zpow_right e m).eq
    have hrC : r ∈ Subgroup.zpowers s31 := by
      rw [← syl31_centralizer_eq, Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have : r ∈ Subgroup.zpowers s31 ⊓ Subgroup.zpowers phi31 := Subgroup.mem_inf.2 ⟨hrC, hr⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hr1 this
  · rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    have := orderOf_s31
    rw [h, orderOf_one] at this
    norm_num at this
  · rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    have := orderOf_phi31
    rw [h, orderOf_one] at this
    norm_num at this

theorem syl31_card_sylow (P : Sylow 31 G52) : Nat.card P = 31 := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  exact card_sylow_of_card_eq_prime_mul (m := 322560) (by rw [card_G52]; norm_num) (by norm_num) P

theorem syl31_structure (P : Sylow 31 G52) :
    Nat.card (Subgroup.normalizer (P : Set G52)) = 155 ∧
    IsFrobeniusSubgroup (Subgroup.normalizer (P : Set G52)) := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card syl31_card_zpowers syl31_card_sylow
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow Q P
  rw [hQ] at hc
  have hP : ((P : Set G52)) = ((P : Subgroup G52) : Set G52) := rfl
  rw [hP, hc, normalizer_map_conj]
  obtain ⟨hKY, hRY, hinf, hsup, hfpf, hK, hR⟩ := syl31_frobenius_data
  refine ⟨?_, isFrobeniusSubgroup_map_conj c hKY hRY le_rfl hinf hsup hfpf hK hR⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, syl31_card_normalizer]

end CFSG.GroupTheory.GL52
