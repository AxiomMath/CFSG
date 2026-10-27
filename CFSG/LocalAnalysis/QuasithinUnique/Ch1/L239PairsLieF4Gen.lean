module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Rel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Center
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Core

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

section Abstract

theorem mem_of_prod3 {G : Type*} [Group G] {N : Subgroup G} {a b c : G} (h : a * b * c ∈ N)
    (hb : b ∈ N) (hc : c ∈ N) : a ∈ N := by
  have := N.mul_mem (N.mul_mem h (N.inv_mem hc)) (N.inv_mem hb)
  rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this

theorem mem_of_conj {G : Type*} [Group G] {N : Subgroup G} {x n y : G} (h : ⁅x, n⁆ ∈ N)
    (hy : y ∈ N) (hxy : n * x * n⁻¹ = y) : x ∈ N := by
  have e : x = ⁅x, n⁆ * y := by
    rw [commutatorElement_def, ← hxy]
    group
  rw [e]
  exact N.mul_mem h hy

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

@[expose] def HighFam
    (m : ℕ) (K : Type) [Field K] (N : Subgroup (ModGL F4.tag K)) : Prop :=
  (∀ c : K, fam m K 4 c ∈ N) ∧ (∀ c : K, fam m K 6 c ∈ N) ∧ (∀ c : K, fam m K 8 c ∈ N) ∧
    (∀ c : K, fam m K 9 c ∈ N) ∧ (∀ c : K, fam m K 10 c ∈ N) ∧ (∀ c : K, fam m K 11 c ∈ N)

omit [CharP K F4.prime] [Finite K] in
theorem sylowV_zero_zero
    : sylowV m K 0 0 0 0 0 0 0 0 0 0 0 0 = 1 := by
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', mul_one]

omit [CharP K F4.prime] [Finite K] in
theorem fam_zero
    {n : ℕ} (hn : n ≤ 11) : fam m K n (0 : K) = 1 := by
  match n, hn with
  | 0, _ => rw [fam_0_eq]; exact sylowV_zero_zero
  | 1, _ => rw [fam_1_eq]; exact sylowV_zero_zero
  | 2, _ => rw [fam_2_eq]; exact sylowV_zero_zero
  | 3, _ => rw [fam_3_eq]; exact sylowV_zero_zero
  | 4, _ => rw [fam_4_eq]; exact sylowV_zero_zero
  | 5, _ => rw [fam_5_eq]; exact sylowV_zero_zero
  | 6, _ => rw [fam_6_eq]; exact sylowV_zero_zero
  | 7, _ => rw [fam_7_eq]; exact sylowV_zero_zero
  | 8, _ => rw [fam_8_eq]; exact sylowV_zero_zero
  | 9, _ => rw [fam_9_eq]; exact sylowV_zero_zero
  | 10, _ => rw [fam_10_eq]; exact sylowV_zero_zero
  | 11, _ => rw [fam_11_eq]; exact sylowV_zero_zero

omit [Finite K] in
theorem tail_mem
    {N : Subgroup (ModGL F4.tag K)} (hh : HighFam m K N) (e g i j k l : K) :
    sylowV m K 0 0 0 0 e 0 g 0 i j k l ∈ N := by
  have hs := sylowV_zero_split (m := m) (K := K) 0 0 0 e 0 g 0 i j k l
  have z1 : fam m K 1 (0 : K) = 1 := fam_zero (by norm_num)
  have z2 : fam m K 2 (0 : K) = 1 := fam_zero (by norm_num)
  have z3 : fam m K 3 (0 : K) = 1 := fam_zero (by norm_num)
  have z5 : fam m K 5 (0 : K) = 1 := fam_zero (by norm_num)
  have z7 : fam m K 7 (0 : K) = 1 := fam_zero (by norm_num)
  rw [z1, z2, z3, z5, z7] at hs
  simp only [one_mul, mul_one] at hs
  rw [hs]
  exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (hh.1 e) (hh.2.1 g)) (hh.2.2.1 i))
    (hh.2.2.2.1 j)) (hh.2.2.2.2.1 k)) (hh.2.2.2.2.2 l)

theorem T2_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {N : Subgroup (ModGL F4.tag K)}
    (hh : HighFam m K N) (hc : ∀ s t : K, ⁅fam m K 2 s, fam m K 0 t⁆ ∈ N) (s t : K) :
    fam m K 5 (s * t) * fam m K 7 (s * largeReeSigma m t) ∈ N := by
  obtain ⟨e, g, i, j, k, l, h⟩ := rel_T2 hK s t
  have h1 := hc s t
  rw [h] at h1
  have := N.mul_mem h1 (N.inv_mem (tail_mem hh e g i j k l))
  rwa [mul_inv_cancel_right] at this

theorem T1_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {N : Subgroup (ModGL F4.tag K)}
    (hh : HighFam m K N) (hc : ∀ s t : K, ⁅fam m K 1 s, fam m K 0 t⁆ ∈ N) (s t : K) :
    fam m K 3 (s * t) * fam m K 7 (s * largeReeSigma m s * largeReeSigma m t) ∈ N := by
  obtain ⟨e, g, i, j, k, l, h⟩ := rel_T1 hK s t
  have h1 := hc s t
  rw [h] at h1
  have := N.mul_mem h1 (N.inv_mem (tail_mem hh e g i j k l))
  rwa [mul_inv_cancel_right] at this

omit [CharP K F4.prime] in
theorem exists_sigma_ne
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    (ha : 1 ≤ m) : ∃ t : K, largeReeSigma m t ≠ t := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨u, hu⟩ := CFSG.LieType.BorelTits.exists_units_sq_ne_one hK4
  refine ⟨(u : K), fun h => hu ?_⟩
  have h2 := largeReeSigma_sigma hK (u : K)
  rw [h, h] at h2
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have : (u : K) * ((u : K) - 1) = 0 := by linear_combination -h2
  rcases mul_eq_zero.1 this with h0 | h1
  · exact absurd h0 hu0
  · rw [sub_eq_zero.1 h1]
    norm_num

omit [CharP K F4.prime] in
theorem exists_sigma_ne_one
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (ha : 1 ≤ m) : ∃ s : K, s ≠ 0 ∧ largeReeSigma m s + 1 ≠ 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨u, hu⟩ := CFSG.LieType.BorelTits.exists_units_sq_ne_one hK4
  refine ⟨(u : K), u.ne_zero, fun h => hu ?_⟩
  have h1 : largeReeSigma m (u : K) = 1 := by
    have := eq_of_add_eq_zero_two h
    rw [this]
  have h2 := largeReeSigma_sigma hK (u : K)
  rw [h1, largeReeSigma_one] at h2
  exact h2.symm

omit [CharP K F4.prime] in
theorem exists_sigma_eq (hK : Nat.card K = 2 ^ (2 * m + 1)) (w : K) :
    ∃ t : K, largeReeSigma m t = w := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma (m := m) hK
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective σ.injective w
  exact ⟨t, by rw [← hσ]; exact ht⟩

theorem fam8_commute
    (ha : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K m) (c : K) : u * fam m K 8 c = fam m K 8 c * u := by
  have e : fam m K 8 c = centralZ K m c := sylowH_zero_eq_centralZ c
  rw [e]
  exact commute_centralZ ha hK hu c

theorem hh_mem_chain0
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (ha : 1 ≤ m)
    {N : Subgroup (ModGL F4.tag K)} (hHi : ∀ c : K, fam m K 8 c ∈ N)
    (hT2 : ∀ s t : K, fam m K 5 (s * t) * fam m K 7 (s * largeReeSigma m t) ∈ N)
    (hW : ∀ x : K, fam m K 5 x * (fam m K 7 x)⁻¹ ∈ N) (z : K) : fam m K 7 z ∈ N := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have key : ∀ s t : K, fam m K 7 (s * t + s * largeReeSigma m t) ∈ N := by
    intro s t
    have h1 : fam m K 7 (s * t) * fam m K 7 (s * largeReeSigma m t) ∈ N := by
      have := N.mul_mem (N.inv_mem (hW (s * t))) (hT2 s t)
      have e : (fam m K 5 (s * t) * (fam m K 7 (s * t))⁻¹)⁻¹ *
          (fam m K 5 (s * t) * fam m K 7 (s * largeReeSigma m t)) =
          fam m K 7 (s * t) * fam m K 7 (s * largeReeSigma m t) := by group
      rwa [e] at this
    have h2 := rel_addH hK (s * t) (s * largeReeSigma m t)
    have h3 : fam m K 7 (s * t + s * largeReeSigma m t) =
        (fam m K 7 (s * t) * fam m K 7 (s * largeReeSigma m t)) *
          (fam m K 8 (s * largeReeSigma m t * largeReeSigma m (s * t)))⁻¹ := by
      rw [h2]
      group
    rw [h3]
    exact N.mul_mem h1 (N.inv_mem (hHi _))
  obtain ⟨t₀, ht₀⟩ := exists_sigma_ne hK ha
  have hne : t₀ + largeReeSigma m t₀ ≠ 0 := fun h => ht₀ (eq_of_add_eq_zero_two h).symm
  have := key (z / (t₀ + largeReeSigma m t₀)) t₀
  rwa [← mul_add, div_mul_cancel₀ _ hne] at this

theorem hh_mem_chain1
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (ha : 1 ≤ m)
    {N : Subgroup (ModGL F4.tag K)} (hHi : ∀ c : K, fam m K 8 c ∈ N)
    (hT1 : ∀ s t : K, fam m K 3 (s * t) * fam m K 7 (s * largeReeSigma m s * largeReeSigma m t) ∈ N)
    (hT2 : ∀ s t : K, fam m K 5 (s * t) * fam m K 7 (s * largeReeSigma m t) ∈ N)
    (hW : ∀ x : K, fam m K 3 x * (fam m K 5 x)⁻¹ ∈ N) (z : K) : fam m K 7 z ∈ N := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have key : ∀ s t : K, fam m K 7 (s * largeReeSigma m s * largeReeSigma m t +
      s * largeReeSigma m t) ∈ N := by
    intro s t
    set a := s * largeReeSigma m s * largeReeSigma m t with ha'
    set b := s * largeReeSigma m t with hb'
    have h1 : (fam m K 7 a)⁻¹ * fam m K 7 b ∈ N := by
      have := N.mul_mem (N.mul_mem (N.inv_mem (hT1 s t)) (hW (s * t))) (hT2 s t)
      have e : (fam m K 3 (s * t) * fam m K 7 a)⁻¹ * (fam m K 3 (s * t) * (fam m K 5 (s * t))⁻¹) *
          (fam m K 5 (s * t) * fam m K 7 b) = (fam m K 7 a)⁻¹ * fam m K 7 b := by group
      rwa [e] at this
    have haa := rel_addH hK a a
    rw [CharTwo.add_self_eq_zero] at haa
    have h7 : fam m K 7 (0 : K) = 1 := fam_zero (by norm_num)
    rw [h7, one_mul] at haa
    have hinv : (fam m K 7 a)⁻¹ = fam m K 7 a * (fam m K 8 (a * largeReeSigma m a))⁻¹ :=
      inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, haa, mul_inv_cancel])
    have hcom : (fam m K 8 (a * largeReeSigma m a))⁻¹ * fam m K 7 b =
        fam m K 7 b * (fam m K 8 (a * largeReeSigma m a))⁻¹ :=
      (Commute.inv_left (fam8_commute ha hK (fam_mem_U hK (by norm_num) b) _).symm).eq
    have hab : fam m K 7 a * fam m K 7 b ∈ N := by
      have e : fam m K 7 a * fam m K 7 b = ((fam m K 7 a)⁻¹ * fam m K 7 b) *
          fam m K 8 (a * largeReeSigma m a) := by
        calc fam m K 7 a * fam m K 7 b
            = fam m K 7 a * ((fam m K 8 (a * largeReeSigma m a))⁻¹ * fam m K 7 b) *
              fam m K 8 (a * largeReeSigma m a) := by
              rw [hcom]; group
          _ = ((fam m K 7 a)⁻¹ * fam m K 7 b) * fam m K 8 (a * largeReeSigma m a) := by
              rw [hinv]; group
      rw [e]
      exact N.mul_mem h1 (hHi _)
    have h2 := rel_addH hK a b
    have h3 : fam m K 7 (a + b) = (fam m K 7 a * fam m K 7 b) *
        (fam m K 8 (b * largeReeSigma m a))⁻¹ := by
      rw [h2]
      group
    rw [h3]
    exact N.mul_mem hab (N.inv_mem (hHi _))
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_sigma_ne_one hK ha
  have hc₀ : s₀ * (largeReeSigma m s₀ + 1) ≠ 0 := mul_ne_zero hs₀ hs₀'
  obtain ⟨t, ht⟩ := exists_sigma_eq hK (z / (s₀ * (largeReeSigma m s₀ + 1)))
  have := key s₀ t
  rw [ht] at this
  have e : s₀ * largeReeSigma m s₀ * (z / (s₀ * (largeReeSigma m s₀ + 1))) +
      s₀ * (z / (s₀ * (largeReeSigma m s₀ + 1))) = z := by
    field_simp
  rwa [e] at this

end Abstract

section Main

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

theorem commutator_perfectCore_le {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (Q : Set G)) : ⁅Q, perfectCore P⁆ ≤ Q := by
  refine Subgroup.commutator_le.2 fun q hq g hg => ?_
  have h1 : g * q⁻¹ * g⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.1 (hPN (perfectCore_le P hg)) q⁻¹).1 (Q.inv_mem hq)
  have : ⁅q, g⁆ = q * (g * q⁻¹ * g⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact Q.mul_mem hq h1

theorem V0_le_of_fams
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {N : Subgroup (ModGL F4.tag K)}
    (h : ∀ n, 1 ≤ n → n ≤ 11 → ∀ c : K, fam m K n c ∈ N) :
    F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ≤ N := by
  intro v hv
  have hvU : v ∈ F4.reeFixedPosUnipotent K m := reeFixedOrbitComplementUnipotent_le _ hv
  obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hvU
  have hx0 : x 0 = 0 := eq_zero_of_sylowV_mem_complement hK hv
  have e : sylowVec m K x = sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
      (x 10) (x 11) := by
    simp only [sylowVec, hx0]
  rw [e, sylowV_zero_split]
  exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem
    (N.mul_mem (N.mul_mem (N.mul_mem (h 1 (by norm_num) (by norm_num) _)
    (h 2 (by norm_num) (by norm_num) _)) (h 3 (by norm_num) (by norm_num) _))
    (h 4 (by norm_num) (by norm_num) _)) (h 5 (by norm_num) (by norm_num) _))
    (h 6 (by norm_num) (by norm_num) _)) (h 7 (by norm_num) (by norm_num) _))
    (h 8 (by norm_num) (by norm_num) _)) (h 9 (by norm_num) (by norm_num) _))
    (h 10 (by norm_num) (by norm_num) _)) (h 11 (by norm_num) (by norm_num) _)

theorem V1_le_of_fams
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {N : Subgroup (ModGL F4.tag K)}
    (h : ∀ n, (n = 0 ∨ 3 ≤ n) → n ≤ 11 → ∀ c : K, fam m K n c ∈ N) :
    F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ ≤ N := by
  intro v hv
  have hvU : v ∈ F4.reeFixedPosUnipotent K m := reeFixedOrbitComplementUnipotent_le _ hv
  obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hvU
  have hx12 : x 1 = 0 ∧ x 2 = 0 := by
    refine coord_one_two_eq hK hv ?_
    rw [sylowB_zero_zero, one_mul]
  have e : sylowVec m K x = sylowV m K (x 0) 0 0 (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
      (x 10) (x 11) := by
    simp only [sylowVec, hx12.1, hx12.2]
  rw [e, sylowV_one_split]
  exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem
    (N.mul_mem (N.mul_mem (h 0 (Or.inl rfl) (by norm_num) _)
    (h 3 (Or.inr (by norm_num)) (by norm_num) _)) (h 4 (Or.inr (by norm_num)) (by norm_num) _))
    (h 5 (Or.inr (by norm_num)) (by norm_num) _)) (h 6 (Or.inr (by norm_num)) (by norm_num) _))
    (h 7 (Or.inr (by norm_num)) (by norm_num) _)) (h 8 (Or.inr (by norm_num)) (by norm_num) _))
    (h 9 (Or.inr (by norm_num)) (by norm_num) _)) (h 10 (Or.inr (by norm_num)) (by norm_num) _))
    (h 11 (Or.inr (by norm_num)) (by norm_num) _)

theorem generation_zero
    (ha : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ≤
      ⁅F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩,
        perfectCore (F4.reeLocalParabolic K m ⟨0, by decide⟩)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  set V := F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ with hV
  set P := F4.reeLocalParabolic K m ⟨0, by decide⟩ with hP
  set E := ⁅V, perfectCore P⁆ with hE
  have hVP : V ≤ P := rad_le_parabolic _
  have hPN : P ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K)) := parabolic_le_normalizer_rad _
  have hV2 := isPGroup_rad ha hK ⟨0, by decide⟩
  have hEV : E ≤ V := commutator_perfectCore_le hPN
  set N := E ⊔ ⁅V, V⁆ with hN
  have hcomm : ∀ v ∈ V, ∀ g ∈ perfectCore P, ⁅v, g⁆ ∈ N := fun v hv g hg =>
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv hg)
  have hVV : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ N := fun v hv w hw =>
    Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hv hw)
  have := (isSimpleGroup_rankOneGroupOne ha hK).1
  obtain ⟨⟨h0eq, hn0, -⟩, -⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hMP := (levi_hom ha hK ⟨0, by decide⟩ (M := rankOneGroupOne K m) h0eq
    (isSimpleGroup_rankOneGroupOne ha hK).2).2
  have hA : ∀ s : K, fam m K 0 s ∈ perfectCore P := fun s => hMP (h0eq ▸
    reeFixedOrbitUnipotent_le_reeLocalBlock _ (sylowA_mem_U1 hK s))
  have hn : weylOne K ∈ perfectCore P := hMP (h0eq ▸ hn0)
  have fV : ∀ n, 1 ≤ n → n ≤ 11 → ∀ c : K, fam m K n c ∈ V := fun n h1 h2 c =>
    fam_mem_V0 hK h1 h2 c
  have hHi : ∀ c : K, fam m K 8 c ∈ N := fun c => by
    have := hVV _ (fV 3 (by norm_num) (by norm_num) c) _ (fV 11 (by norm_num) (by norm_num) 1)
    rwa [show ⁅fam m K 3 c, fam m K 11 1⁆ = fam m K 8 (c * 1) from rel_C3 hK c 1, mul_one] at this
  have hFg : ∀ c : K, fam m K 6 c ∈ N := fun c => by
    have := hVV _ (fV 1 (by norm_num) (by norm_num) c) _ (fV 11 (by norm_num) (by norm_num) 1)
    rwa [show ⁅fam m K 1 c, fam m K 11 1⁆ = fam m K 6 (c * 1) from rel_C2 hK c 1, mul_one] at this
  have hJ : ∀ c : K, fam m K 9 c ∈ N := fun c => by
    have := hVV _ (fV 1 (by norm_num) (by norm_num) c) _ (fV 5 (by norm_num) (by norm_num) 1)
    rwa [show ⁅fam m K 1 c, fam m K 5 1⁆ = fam m K 9 (c * 1) from rel_C1 hK c 1, mul_one] at this
  have hKK : ∀ c : K, fam m K 10 c ∈ N := fun c => by
    have h1 := hVV _ (fV 1 (by norm_num) (by norm_num) c) _ (fV 4 (by norm_num) (by norm_num) 1)
    rw [rel_C4 hK c 1] at h1
    have h2 := mem_of_prod3 h1 (hFg _) (hHi _)
    rwa [mul_one] at h2
  have hL : ∀ c : K, fam m K 11 c ∈ N := fun c => by
    have h1 := hVV _ (fV 2 (by norm_num) (by norm_num) c) _ (fV 4 (by norm_num) (by norm_num) 1)
    rw [rel_C5 hK c 1] at h1
    have h2 := mem_of_prod3 h1 (hFg _) (hHi _)
    rwa [mul_one] at h2
  have hDe : ∀ c : K, fam m K 4 c ∈ N := fun c => by
    have h1 := N.inv_mem (hcomm _ (fV 7 (by norm_num) (by norm_num) 1) _ (hA c))
    rwa [commutatorElement_inv, rel_C6 hK c 1, mul_one] at h1
  have hBc : ∀ c : K, fam m K 2 c ∈ N := fun c =>
    mem_of_conj (hcomm _ (fV 2 (by norm_num) (by norm_num) c) _ hn) (hDe c) (weylOne_fam_2 c)
  have hh : HighFam m K N := ⟨hDe, hFg, hHi, hJ, hKK, hL⟩
  have hT2 := T2_mem hK hh fun s t => hcomm _ (fV 2 (by norm_num) (by norm_num) s) _ (hA t)
  have hW : ∀ x : K, fam m K 5 x * (fam m K 7 x)⁻¹ ∈ N := fun x => by
    have e : ⁅fam m K 5 x, weylOne K⁆ = fam m K 5 x * (fam m K 7 x)⁻¹ := by
      rw [commutatorElement_def, ← weylOne_fam_5 x]
      group
    rw [← e]
    exact hcomm _ (fV 5 (by norm_num) (by norm_num) x) _ hn
  have hH := hh_mem_chain0 hK ha hHi hT2 hW
  have hF : ∀ c : K, fam m K 5 c ∈ N := fun c => by
    have h1 := N.mul_mem (hT2 c 1) (N.inv_mem (hH (c * largeReeSigma m 1)))
    rwa [mul_inv_cancel_right, mul_one] at h1
  have hT1 := T1_mem hK hh fun s t => hcomm _ (fV 1 (by norm_num) (by norm_num) s) _ (hA t)
  have hD : ∀ c : K, fam m K 3 c ∈ N := fun c => by
    have h1 := N.mul_mem (hT1 c 1) (N.inv_mem (hH (c * largeReeSigma m c * largeReeSigma m 1)))
    rwa [mul_inv_cancel_right, mul_one] at h1
  have hB : ∀ c : K, fam m K 1 c ∈ N := fun c =>
    mem_of_conj (hcomm _ (fV 1 (by norm_num) (by norm_num) c) _ hn) (hD c) (weylOne_fam_1 c)
  have hall : ∀ n, 1 ≤ n → n ≤ 11 → ∀ c : K, fam m K n c ∈ N := by
    intro n h1 h2 c
    match n, h1, h2 with
    | 1, _, _ => exact hB c
    | 2, _, _ => exact hBc c
    | 3, _, _ => exact hD c
    | 4, _, _ => exact hDe c
    | 5, _, _ => exact hF c
    | 6, _, _ => exact hFg c
    | 7, _, _ => exact hH c
    | 8, _, _ => exact hHi c
    | 9, _, _ => exact hJ c
    | 10, _, _ => exact hKK c
    | 11, _, _ => exact hL c
  have hsup : E ⊔ ⁅V, V⁆ = V :=
    le_antisymm (sup_le hEV (commutator_self_le V)) (V0_le_of_fams hK hall)
  exact (eq_of_sup_commutator_eq (p := 2) hV2 hEV hsup).ge

theorem generation_one
    (ha : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ ≤
      ⁅F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩,
        perfectCore (F4.reeLocalParabolic K m ⟨1, by decide⟩)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  set V := F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ with hV
  set P := F4.reeLocalParabolic K m ⟨1, by decide⟩ with hP
  set E := ⁅V, perfectCore P⁆ with hE
  have hVP : V ≤ P := rad_le_parabolic _
  have hPN : P ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K)) := parabolic_le_normalizer_rad _
  have hV2 := isPGroup_rad ha hK ⟨1, by decide⟩
  have hEV : E ≤ V := commutator_perfectCore_le hPN
  set N := E ⊔ ⁅V, V⁆ with hN
  have hcomm : ∀ v ∈ V, ∀ g ∈ perfectCore P, ⁅v, g⁆ ∈ N := fun v hv g hg =>
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv hg)
  have hcomm' : ∀ g ∈ perfectCore P, ∀ v ∈ V, ⁅g, v⁆ ∈ N := fun g hg v hv => by
    rw [← commutatorElement_inv]
    exact N.inv_mem (hcomm v hv g hg)
  have hVV : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ N := fun v hv w hw =>
    Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hv hw)
  have := (isSimpleGroup_rankOneGroupTwo ha hK).1
  obtain ⟨-, ⟨h1eq, hn1, -⟩⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hMP := (levi_hom ha hK ⟨1, by decide⟩ (M := rankOneGroupTwo K m) h1eq
    (isSimpleGroup_rankOneGroupTwo ha hK).2).2
  have hB1 : ∀ s : K, fam m K 1 s ∈ perfectCore P := fun s => hMP (h1eq ▸
    reeFixedOrbitUnipotent_le_reeLocalBlock _ (sylowB_mem_U2 hK s 0))
  have hB2 : ∀ s : K, fam m K 2 s ∈ perfectCore P := fun s => hMP (h1eq ▸
    reeFixedOrbitUnipotent_le_reeLocalBlock _ (sylowB_mem_U2 hK 0 s))
  have hn : weylTwo K ∈ perfectCore P := hMP (h1eq ▸ hn1)
  have fV : ∀ n, (n = 0 ∨ 3 ≤ n) → n ≤ 11 → ∀ c : K, fam m K n c ∈ V := fun n h1 h2 c =>
    fam_mem_V1 hK h1 h2 c
  have hHi : ∀ c : K, fam m K 8 c ∈ N := fun c => by
    have := hVV _ (fV 3 (Or.inr (by norm_num)) (by norm_num) c) _
      (fV 11 (Or.inr (by norm_num)) (by norm_num) 1)
    rwa [show ⁅fam m K 3 c, fam m K 11 1⁆ = fam m K 8 (c * 1) from rel_C3 hK c 1, mul_one] at this
  have hFg : ∀ c : K, fam m K 6 c ∈ N := fun c => by
    have := hcomm' _ (hB1 c) _ (fV 11 (Or.inr (by norm_num)) (by norm_num) 1)
    rwa [show ⁅fam m K 1 c, fam m K 11 1⁆ = fam m K 6 (c * 1) from rel_C2 hK c 1, mul_one] at this
  have hJ : ∀ c : K, fam m K 9 c ∈ N := fun c => by
    have := hcomm' _ (hB1 c) _ (fV 5 (Or.inr (by norm_num)) (by norm_num) 1)
    rwa [show ⁅fam m K 1 c, fam m K 5 1⁆ = fam m K 9 (c * 1) from rel_C1 hK c 1, mul_one] at this
  have hA : ∀ c : K, fam m K 0 c ∈ N := fun c =>
    mem_of_conj (hcomm _ (fV 0 (Or.inl rfl) (by norm_num) c) _ hn) (hJ c) (weylTwo_fam_0 c)
  have hDe : ∀ c : K, fam m K 4 c ∈ N := fun c =>
    mem_of_conj (hcomm _ (fV 4 (Or.inr (by norm_num)) (by norm_num) c) _ hn) (hFg c)
      (weylTwo_fam_4 c)
  have hKK : ∀ c : K, fam m K 10 c ∈ N := fun c => by
    have h1 := hcomm' _ (hB1 c) _ (fV 4 (Or.inr (by norm_num)) (by norm_num) 1)
    rw [rel_C4 hK c 1] at h1
    have h2 := mem_of_prod3 h1 (hFg _) (hHi _)
    rwa [mul_one] at h2
  have hL : ∀ c : K, fam m K 11 c ∈ N := fun c => by
    have hinv : (weylTwo K)⁻¹ ∈ perfectCore P := (perfectCore P).inv_mem hn
    refine mem_of_conj (n := (weylTwo K)⁻¹) (y := fam m K 10 c)
      (hcomm _ (fV 11 (Or.inr (by norm_num)) (by norm_num) c) _ hinv) (hKK c) ?_
    have := weylTwo_fam_10 (m := m) (K := K) c
    calc (weylTwo K)⁻¹ * fam m K 11 c * ((weylTwo K)⁻¹)⁻¹
        = (weylTwo K)⁻¹ * (weylTwo K * fam m K 10 c * (weylTwo K)⁻¹) * weylTwo K := by
          rw [this]; simp
      _ = fam m K 10 c := by group
  have hh : HighFam m K N := ⟨hDe, hFg, hHi, hJ, hKK, hL⟩
  have hT2 := T2_mem hK hh fun s t => hcomm' _ (hB2 s) _ (fV 0 (Or.inl rfl) (by norm_num) t)
  have hT1 := T1_mem hK hh fun s t => hcomm' _ (hB1 s) _ (fV 0 (Or.inl rfl) (by norm_num) t)
  have hW : ∀ x : K, fam m K 3 x * (fam m K 5 x)⁻¹ ∈ N := fun x => by
    have e : ⁅fam m K 3 x, weylTwo K⁆ = fam m K 3 x * (fam m K 5 x)⁻¹ := by
      rw [commutatorElement_def, ← weylTwo_fam_3 x]
      group
    rw [← e]
    exact hcomm _ (fV 3 (Or.inr (by norm_num)) (by norm_num) x) _ hn
  have hH := hh_mem_chain1 hK ha hHi hT1 hT2 hW
  have hF : ∀ c : K, fam m K 5 c ∈ N := fun c => by
    have h1 := N.mul_mem (hT2 c 1) (N.inv_mem (hH (c * largeReeSigma m 1)))
    rwa [mul_inv_cancel_right, mul_one] at h1
  have hD : ∀ c : K, fam m K 3 c ∈ N := fun c => by
    have h1 := N.mul_mem (hT1 c 1) (N.inv_mem (hH (c * largeReeSigma m c * largeReeSigma m 1)))
    rwa [mul_inv_cancel_right, mul_one] at h1
  have hall : ∀ n, (n = 0 ∨ 3 ≤ n) → n ≤ 11 → ∀ c : K, fam m K n c ∈ N := by
    intro n h1 h2 c
    match n, h1, h2 with
    | 0, _, _ => exact hA c
    | 3, _, _ => exact hD c
    | 4, _, _ => exact hDe c
    | 5, _, _ => exact hF c
    | 6, _, _ => exact hFg c
    | 7, _, _ => exact hH c
    | 8, _, _ => exact hHi c
    | 9, _, _ => exact hJ c
    | 10, _, _ => exact hKK c
    | 11, _, _ => exact hL c
  have hsup : E ⊔ ⁅V, V⁆ = V :=
    le_antisymm (sup_le hEV (commutator_self_le V)) (V1_le_of_fams hK hall)
  exact (eq_of_sup_commutator_eq (p := 2) hV2 hEV hsup).ge

theorem center_zero
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ⊓
        Subgroup.centralizer
          (F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ : Set (ModGL F4.tag K)) ≤
      ⁅F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩,
        F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩⁆ := by
  intro x hx
  obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxU : x ∈ F4.reeFixedPosUnipotent K m := reeFixedOrbitComplementUnipotent_le _ hxV
  obtain ⟨y, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hxU
  have hy0 : y 0 = 0 := eq_zero_of_sylowV_mem_complement hK hxV
  have e : sylowVec m K y = sylowV m K 0 (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9)
      (y 10) (y 11) := by
    simp only [sylowVec, hy0]
  have hcomm : ∀ n ∈ testsV0, sylowV m K 0 (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9)
      (y 10) (y 11) * fam m K n 1 = fam m K n 1 * sylowV m K 0 (y 1) (y 2) (y 3) (y 4) (y 5)
        (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) := by
    intro n hn
    have hn' : 1 ≤ n ∧ n ≤ 11 := by
      simp only [testsV0, List.mem_cons, List.not_mem_nil, or_false] at hn
      omega
    have hnV := fam_mem_V0 hK hn'.1 hn'.2 (1 : K)
    have := Subgroup.mem_centralizer_iff.1 hxC _ hnV
    rw [e] at this
    exact this.symm
  obtain ⟨hb, hc, hd, he, hf, hh, hj, hk, hl⟩ := center_V0_forced (m := m) (y 1) (y 2) (y 3)
    (y 4) (y 5) (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) hcomm
  have e2 : sylowVec m K y = fam m K 6 (y 6) * fam m K 8 (y 8) := by
    rw [e, hb, hc, hd, he, hf, hh, hj, hk, hl, sylowV_zero_split]
    simp only [fam_zero (m := m) (K := K) (n := 1) (by norm_num),
      fam_zero (m := m) (K := K) (n := 2) (by norm_num),
      fam_zero (m := m) (K := K) (n := 3) (by norm_num),
      fam_zero (m := m) (K := K) (n := 4) (by norm_num),
      fam_zero (m := m) (K := K) (n := 5) (by norm_num),
      fam_zero (m := m) (K := K) (n := 7) (by norm_num),
      fam_zero (m := m) (K := K) (n := 9) (by norm_num),
      fam_zero (m := m) (K := K) (n := 10) (by norm_num),
      fam_zero (m := m) (K := K) (n := 11) (by norm_num), one_mul, mul_one]
  rw [e2]
  have hF : fam m K 6 (y 6) ∈ ⁅F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩,
      F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩⁆ := by
    have := Subgroup.commutator_mem_commutator
      (fam_mem_V0 hK (by norm_num : 1 ≤ 1) (by norm_num) (y 6))
      (fam_mem_V0 hK (by norm_num : 1 ≤ 11) (by norm_num) (1 : K))
    rwa [show ⁅fam m K 1 (y 6), fam m K 11 1⁆ = fam m K 6 (y 6 * 1) from rel_C2 hK _ 1,
      mul_one] at this
  have hH : fam m K 8 (y 8) ∈ ⁅F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩,
      F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩⁆ := by
    have := Subgroup.commutator_mem_commutator
      (fam_mem_V0 hK (by norm_num : 1 ≤ 3) (by norm_num) (y 8))
      (fam_mem_V0 hK (by norm_num : 1 ≤ 11) (by norm_num) (1 : K))
    rwa [show ⁅fam m K 3 (y 8), fam m K 11 1⁆ = fam m K 8 (y 8 * 1) from rel_C3 hK _ 1,
      mul_one] at this
  exact Subgroup.mul_mem _ hF hH

theorem center_one
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ ⊓
        Subgroup.centralizer
          (F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ : Set (ModGL F4.tag K)) ≤
      ⁅F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩,
        F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩⁆ := by
  intro x hx
  obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxU : x ∈ F4.reeFixedPosUnipotent K m := reeFixedOrbitComplementUnipotent_le _ hxV
  obtain ⟨y, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hxU
  have hx12 : y 1 = 0 ∧ y 2 = 0 := by
    refine coord_one_two_eq hK hxV ?_
    rw [sylowB_zero_zero, one_mul]
  have e : sylowVec m K y = sylowV m K (y 0) 0 0 (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9)
      (y 10) (y 11) := by
    simp only [sylowVec, hx12.1, hx12.2]
  have hcomm : ∀ n ∈ testsV1, sylowV m K (y 0) 0 0 (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9)
      (y 10) (y 11) * fam m K n 1 = fam m K n 1 * sylowV m K (y 0) 0 0 (y 3) (y 4) (y 5)
        (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) := by
    intro n hn
    have hn' : (n = 0 ∨ 3 ≤ n) ∧ n ≤ 11 := by
      simp only [testsV1, List.mem_cons, List.not_mem_nil, or_false] at hn
      omega
    have hnV := fam_mem_V1 hK hn'.1 hn'.2 (1 : K)
    have := Subgroup.mem_centralizer_iff.1 hxC _ hnV
    rw [e] at this
    exact this.symm
  obtain ⟨ha0, hd, he, hf, hg, hh, hj, hk, hl⟩ := center_V1_forced (m := m) (y 0) (y 3) (y 4)
    (y 5) (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) hcomm
  have e2 : sylowVec m K y = fam m K 8 (y 8) := by
    rw [e, ha0, hd, he, hf, hg, hh, hj, hk, hl, sylowV_one_split]
    simp only [fam_zero (m := m) (K := K) (n := 0) (by norm_num),
      fam_zero (m := m) (K := K) (n := 3) (by norm_num),
      fam_zero (m := m) (K := K) (n := 4) (by norm_num),
      fam_zero (m := m) (K := K) (n := 5) (by norm_num),
      fam_zero (m := m) (K := K) (n := 6) (by norm_num),
      fam_zero (m := m) (K := K) (n := 7) (by norm_num),
      fam_zero (m := m) (K := K) (n := 9) (by norm_num),
      fam_zero (m := m) (K := K) (n := 10) (by norm_num),
      fam_zero (m := m) (K := K) (n := 11) (by norm_num), one_mul, mul_one]
  rw [e2]
  have := Subgroup.commutator_mem_commutator
    (fam_mem_V1 hK (Or.inr (by norm_num : 3 ≤ 3)) (by norm_num) (y 8))
    (fam_mem_V1 hK (Or.inr (by norm_num : 3 ≤ 11)) (by norm_num) (1 : K))
  rwa [show ⁅fam m K 3 (y 8), fam m K 11 1⁆ = fam m K 8 (y 8 * 1) from rel_C3 hK _ 1,
    mul_one] at this

end Main

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4
