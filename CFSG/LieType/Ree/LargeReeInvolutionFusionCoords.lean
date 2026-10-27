module

public import CFSG.LieType.Ree.LargeReeInvolutionFusionWord
public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizer

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open ReeTag
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i torusPair
  torusPair_apply torusPair_conj_pinnedX torusWeight torusWeight_apply torusExp0 torusExp1)

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem exists_conj_eq_mul {G : Type*} [Group G] {U N : Subgroup G}
    (hUN : U ≤ Subgroup.normalizer (N : Set G)) {a₁ a₂ n₁ n₂ : G} (ha₁ : a₁ ∈ U) (ha₂ : a₂ ∈ U)
    (hn₁ : n₁ ∈ N) (hn₂ : n₂ ∈ N) (hc : a₁ * a₂ = a₂ * a₁) :
    ∃ n ∈ N, (a₁ * n₁) * (a₂ * n₂) * (a₁ * n₁)⁻¹ = a₂ * n := by
  have hconj : ∀ g ∈ U, ∀ x ∈ N, g * x * g⁻¹ ∈ N := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (hUN hg) x).1 hx
  have h1 : a₂⁻¹ * n₁ * a₂ ∈ N := by
    have := hconj _ (inv_mem ha₂) _ hn₁
    rwa [inv_inv] at this
  refine ⟨a₁ * ((a₂⁻¹ * n₁ * a₂) * (n₂ * n₁⁻¹)) * a₁⁻¹,
    hconj _ ha₁ _ (mul_mem h1 (mul_mem hn₂ (inv_mem hn₁))), ?_⟩
  have hc' : a₂⁻¹ * a₁ = a₁ * a₂⁻¹ := by
    calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * a₂) * a₂⁻¹ := by group
      _ = a₂⁻¹ * (a₂ * a₁) * a₂⁻¹ := by rw [hc]
      _ = a₁ * a₂⁻¹ := by group
  calc (a₁ * n₁) * (a₂ * n₂) * (a₁ * n₁)⁻¹ = a₂ * (a₂⁻¹ * a₁) * n₁ * a₂ * n₂ * n₁⁻¹ * a₁⁻¹ := by
        group
    _ = a₂ * (a₁ * a₂⁻¹) * n₁ * a₂ * n₂ * n₁⁻¹ * a₁⁻¹ := by rw [hc']
    _ = a₂ * (a₁ * ((a₂⁻¹ * n₁ * a₂) * (n₂ * n₁⁻¹)) * a₁⁻¹) := by group

omit [Finite K] [CharP K F4.prime] in
theorem sylowA_zero
    : sylowA m K (0 : K) = 1 := by
  rw [sylowA, largeReeSigma_zero, sylowX, sylowX, pinnedX_zero, pinnedX_zero, one_mul]

omit [Finite K] [CharP K F4.prime] in
theorem sylowB_zero_zero
    : sylowB m K (0 : K) 0 = 1 := by
  simp [sylowB, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem sylowVec_eq_sylowA_mul
    (x : Fin 12 → K) :
    sylowVec m K x = sylowA m K (x 0) *
      sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) := by
  simp only [sylowVec, sylowV, sylowA_zero, one_mul, mul_assoc]

omit [Finite K] [CharP K F4.prime] in
theorem sylowV_eq_sylowA
    (s : K) : sylowV m K s 0 0 0 0 0 0 0 0 0 0 0 = sylowA m K s := by
  simp [sylowV, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

theorem sylowA_mem_U1
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : K) :
    sylowA m K s ∈ F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩ := by
  have h := sylowV_mem hK s 0 0 0 0 0 0 0 0 0 0 0
  rw [sylowV_eq_sylowA] at h
  exact Subgroup.mem_inf.2 ⟨sylowA_mem_rootSpan s, (Subgroup.mem_inf.1 h).2⟩

theorem sylowA_mul
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    sylowA m K s * sylowA m K t = sylowA m K (s + t) := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma hK
  have hc := sylowX_commute_of_commFactors (K := K) (i := 24) (j := 33) (by norm_num)
    (by norm_num) (by norm_num) (by decide) t (largeReeSigma m s)
  rw [sylowA, sylowA, sylowA, ← hσ, ← hσ, ← hσ, map_add]
  simp only [sylowX, pinnedX_add]
  rw [sylowX, sylowX, ← hσ] at hc
  calc pinnedX F4.tag K (orbitCertRoot F4.tag 24) s *
        pinnedX F4.tag K (orbitCertRoot F4.tag 33) (σ s) *
          (pinnedX F4.tag K (orbitCertRoot F4.tag 24) t *
            pinnedX F4.tag K (orbitCertRoot F4.tag 33) (σ t)) =
      pinnedX F4.tag K (orbitCertRoot F4.tag 24) s *
        (pinnedX F4.tag K (orbitCertRoot F4.tag 33) (σ s) *
          pinnedX F4.tag K (orbitCertRoot F4.tag 24) t) *
            pinnedX F4.tag K (orbitCertRoot F4.tag 33) (σ t) := by group
    _ = pinnedX F4.tag K (orbitCertRoot F4.tag 24) s *
        (pinnedX F4.tag K (orbitCertRoot F4.tag 24) t *
          pinnedX F4.tag K (orbitCertRoot F4.tag 33) (σ s)) *
            pinnedX F4.tag K (orbitCertRoot F4.tag 33) (σ t) := by rw [hc.eq]
    _ = _ := by group

omit [Finite K] [CharP K F4.prime] in
theorem sylowA_injective
    {s t : K} (h : sylowA m K s = sylowA m K t) : s = t := by
  rw [sylowA, sylowA, sylowX, sylowX, sylowX, sylowX] at h
  exact (pinnedX_mul_pinnedX_inj (Or.inl ⟨sylowRoot_pos (r := 24) (by norm_num) (by norm_num),
    sylowRoot_pos (r := 33) (by norm_num) (by norm_num)⟩) (by decide) h).1

theorem coord_zero_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : Fin 12 → K} {s : K}
    {w : ModGL F4.tag K} (hw : w ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩)
    (h : sylowVec m K x = sylowA m K s * w) : x 0 = s := by
  have hw₀ := sylowV_zero_mem_complement hK (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    (x 9) (x 10) (x 11)
  rw [sylowVec_eq_sylowA_mul] at h
  have hV : (sylowA m K s)⁻¹ * sylowA m K (x 0) ∈
      F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ := by
    have e : (sylowA m K s)⁻¹ * sylowA m K (x 0) =
        w * (sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
          (x 11))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hw (inv_mem hw₀)
  have hU : (sylowA m K s)⁻¹ * sylowA m K (x 0) ∈ F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩ :=
    mul_mem (inv_mem (sylowA_mem_U1 hK s)) (sylowA_mem_U1 hK (x 0))
  have h1 := Subgroup.mem_inf.2 ⟨hV, hU⟩
  rw [reeFixedOrbitComplementUnipotent_inf_reeFixedOrbitUnipotent, Subgroup.mem_bot,
    inv_mul_eq_one] at h1
  exact (sylowA_injective h1).symm

theorem coord_zero_conj
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K m) {x y : Fin 12 → K}
    (h : u * sylowVec m K x * u⁻¹ = sylowVec m K y) : y 0 = x 0 := by
  obtain ⟨z, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
  have hA : ∀ s : K, sylowA m K s ∈ F4.reeFixedPosUnipotent K m := fun s =>
    reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK s)
  obtain ⟨n, hn, hn'⟩ := exists_conj_eq_mul (reeFixedPosUnipotent_le_normalizer ⟨0, by decide⟩)
    (hA (z 0)) (hA (x 0))
    (sylowV_zero_mem_complement hK (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8) (z 9) (z 10)
      (z 11))
    (sylowV_zero_mem_complement hK (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
      (x 11))
    (by rw [sylowA_mul hK, sylowA_mul hK, add_comm])
  rw [← sylowVec_eq_sylowA_mul, ← sylowVec_eq_sylowA_mul, h] at hn'
  exact coord_zero_eq hK hn hn'

omit [Finite K] [CharP K F4.prime] in
theorem sylowB_eq_largeReeCoord
    (b c : K) : sylowB m K b c = largeReeCoord m K b c := by
  have h : LargeReeCover.stdFourRoot 0 = orbitCertRoot F4.tag 25 ∧
      LargeReeCover.stdFourRoot 1 = orbitCertRoot F4.tag 27 ∧
      LargeReeCover.stdFourRoot 2 = orbitCertRoot F4.tag 28 ∧
      LargeReeCover.stdFourRoot 3 = orbitCertRoot F4.tag 30 := by
    decide +kernel
  rw [← stdFourG_eq_largeReeCoord, stdFourG, sylowB, sylowX, sylowX, sylowX, sylowX, h.1, h.2.1,
    h.2.2.1, h.2.2.2]

theorem sylowB_mem_U2
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (b c : K) :
    sylowB m K b c ∈ F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ := by
  rw [sylowB_eq_largeReeCoord]
  exact largeReeCoord_mem hK b c

theorem sylowB_injective
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {b c b' c' : K}
    (h : sylowB m K b c = sylowB m K b' c') : b = b' ∧ c = c' := by
  rw [sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord] at h
  have := (bijOn_largeReeCoord hK).2.1 (Set.mem_univ (b, c)) (Set.mem_univ (b', c')) h
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem sylowB_zero_commute
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (c b' c' : K) :
    sylowB m K 0 c * sylowB m K b' c' = sylowB m K b' c' * sylowB m K 0 c := by
  have h1 := largeReeCoord_mul hK 0 c b' c'
  have h2 := largeReeCoord_mul hK b' c' 0 c
  rw [largeReeSigma_zero, zero_mul, add_zero, zero_add] at h1
  rw [mul_zero, add_zero, add_zero] at h2
  rw [sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord]
  exact h1.trans ((congrArg (largeReeCoord m K b') (add_comm c c')).trans h2.symm)

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem complement_one_check : ∀ r ∈ ([24, 26, 29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
    42, 43, 44, 45, 46, 47] : List ℕ), (24 ≤ r ∧ r ≤ 47) ∧
      ∃ i, F4.fixedOrbitIndex i ≠ ⟨1, by decide⟩ ∧ orbitCertRoot F4.tag r i ≠ 0 := by
  decide +kernel

omit [Finite K] [CharP K F4.prime] in
theorem sylowX_mem_complement_one
    {r : ℕ} (hr : r ∈ ([24, 26, 29, 31, 32, 33, 34, 35, 36, 37, 38,
    39, 40, 41, 42, 43, 44, 45, 46, 47] : List ℕ)) (c : K) :
    sylowX K r c ∈ rootSpan F4.tag K (F4.fixedOrbitComplementRoots ⟨1, by decide⟩) := by
  obtain ⟨⟨h1, h2⟩, hex⟩ := complement_one_check r hr
  exact pinnedX_mem_rootSpan (mem_fixedOrbitComplementRoots_iff.2
    ⟨(sylowRoot_pos h1 h2).1, (sylowRoot_pos h1 h2).2, hex⟩) c

omit [Finite K] [CharP K F4.prime] in
theorem sylowA_mem_rootSpan_one
    (s : K) :
    sylowA m K s ∈ rootSpan F4.tag K (F4.fixedOrbitComplementRoots ⟨1, by decide⟩) :=
  mul_mem (sylowX_mem_complement_one (by decide) _) (sylowX_mem_complement_one (by decide) _)

omit [Finite K] [CharP K F4.prime] in
theorem sylowV_rest_mem_rootSpan_one
    (d e f g h i j k l : K) :
    sylowV m K 0 0 0 d e f g h i j k l ∈
      rootSpan F4.tag K (F4.fixedOrbitComplementRoots ⟨1, by decide⟩) := by
  have H : ∀ r ∈ ([24, 26, 29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
      47] : List ℕ), ∀ c : K, sylowX K r c ∈
        rootSpan F4.tag K (F4.fixedOrbitComplementRoots ⟨1, by decide⟩) :=
    fun r hr c => sylowX_mem_complement_one hr c
  rw [sylowV, sylowA_zero, sylowB_zero_zero, one_mul, one_mul]
  simp only [sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_
  · exact mul_mem (mul_mem (mul_mem (H 26 (by decide) _) (H 34 (by decide) _))
      (H 36 (by decide) _)) (H 39 (by decide) _)
  · exact mul_mem (mul_mem (mul_mem (H 29 (by decide) _) (H 37 (by decide) _))
      (H 43 (by decide) _)) (H 46 (by decide) _)
  · exact mul_mem (mul_mem (mul_mem (H 35 (by decide) _) (H 32 (by decide) _))
      (H 44 (by decide) _)) (H 47 (by decide) _)
  · exact mul_mem (H 31 (by decide) _) (H 40 (by decide) _)
  · exact mul_mem (H 38 (by decide) _) (H 42 (by decide) _)
  · exact mul_mem (H 41 (by decide) _) (H 45 (by decide) _)

theorem exists_sylowVec_eq_sylowB_mul
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (x : Fin 12 → K) :
    ∃ n ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩,
      sylowVec m K x = sylowB m K (x 1) (x 2) * n := by
  set R := sylowV m K 0 0 0 (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) with hR
  have hRV : R ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    Subgroup.mem_inf.2 ⟨sylowV_rest_mem_rootSpan_one _ _ _ _ _ _ _ _ _,
      (Subgroup.mem_inf.1 (sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _)).2⟩
  have hAV : sylowA m K (x 0) ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    Subgroup.mem_inf.2 ⟨sylowA_mem_rootSpan_one _,
      (Subgroup.mem_inf.1 (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK (x 0)))).2⟩
  have hBU : sylowB m K (x 1) (x 2) ∈ F4.reeFixedPosUnipotent K m :=
    reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK _ _)
  have hconj : (sylowB m K (x 1) (x 2))⁻¹ * sylowA m K (x 0) * sylowB m K (x 1) (x 2) ∈
      F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
    have := (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer ⟨1, by decide⟩
      (inv_mem hBU)) _).1 hAV
    rwa [inv_inv] at this
  refine ⟨(sylowB m K (x 1) (x 2))⁻¹ * sylowA m K (x 0) * sylowB m K (x 1) (x 2) * R,
    mul_mem hconj hRV, ?_⟩
  have e : sylowVec m K x = sylowA m K (x 0) * sylowB m K (x 1) (x 2) * R := by
    simp only [hR, sylowVec, sylowV, sylowA_zero, sylowB_zero_zero, one_mul, mul_assoc]
  rw [e]
  group

theorem coord_one_two_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : Fin 12 → K} {b c : K}
    {n : ModGL F4.tag K} (hn : n ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩)
    (h : sylowVec m K x = sylowB m K b c * n) : x 1 = b ∧ x 2 = c := by
  obtain ⟨n₀, hn₀, h₀⟩ := exists_sylowVec_eq_sylowB_mul hK x
  have hV : (sylowB m K b c)⁻¹ * sylowB m K (x 1) (x 2) ∈
      F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
    have e : (sylowB m K b c)⁻¹ * sylowB m K (x 1) (x 2) = n * n₀⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, h₀, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hn (inv_mem hn₀)
  have hU : (sylowB m K b c)⁻¹ * sylowB m K (x 1) (x 2) ∈
      F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ :=
    mul_mem (inv_mem (sylowB_mem_U2 hK b c)) (sylowB_mem_U2 hK _ _)
  have h1 := Subgroup.mem_inf.2 ⟨hV, hU⟩
  rw [reeFixedOrbitComplementUnipotent_inf_reeFixedOrbitUnipotent, Subgroup.mem_bot,
    inv_mul_eq_one] at h1
  obtain ⟨hb, hc⟩ := sylowB_injective hK h1
  exact ⟨hb.symm, hc.symm⟩

theorem coord_one_two_conj
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K m) {x y : Fin 12 → K} (hx : x 1 = 0)
    (h : u * sylowVec m K x * u⁻¹ = sylowVec m K y) : y 1 = 0 ∧ y 2 = x 2 := by
  obtain ⟨z, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
  obtain ⟨nz, hnz, hz⟩ := exists_sylowVec_eq_sylowB_mul hK z
  obtain ⟨nx, hnx, hxe⟩ := exists_sylowVec_eq_sylowB_mul hK x
  rw [hx] at hxe
  have hB : ∀ b c : K, sylowB m K b c ∈ F4.reeFixedPosUnipotent K m := fun b c =>
    reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK b c)
  obtain ⟨n, hn, hn'⟩ := exists_conj_eq_mul (reeFixedPosUnipotent_le_normalizer ⟨1, by decide⟩)
    (hB (z 1) (z 2)) (hB 0 (x 2)) hnz hnx (sylowB_zero_commute hK _ _ _).symm
  rw [← hz, ← hxe, h] at hn'
  exact coord_one_two_eq hK hn hn'

omit [CharP K F4.prime] in
theorem units_pow_card_sub_one (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) :
    u ^ (2 ^ (2 * m + 1) - 1) = 1 := by
  classical
  have := Fintype.ofFinite K
  have hq : u ^ (Fintype.card Kˣ) = 1 := pow_card_eq_one
  rwa [Fintype.card_units, ← Nat.card_eq_fintype_card, hK] at hq

omit [CharP K F4.prime] in
theorem units_zpow_congr (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) {e e' : ℤ} (k : ℤ)
    (h : e = e' + k * (2 ^ (2 * m + 1) - 1)) : u ^ e = u ^ e' := by
  have h1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have hq : u ^ ((2 : ℤ) ^ (2 * m + 1) - 1) = 1 := by
    have := units_pow_card_sub_one hK u
    rw [← zpow_natCast, Nat.cast_sub h1] at this
    simpa using this
  rw [h, zpow_add, mul_comm k, zpow_mul, hq, one_zpow, mul_one]

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem cartanPair_A_B : (F4.cartanPair (f4i 0) (orbitCertRoot F4.tag 24) = 0 ∧
      F4.cartanPair (f4i 1) (orbitCertRoot F4.tag 24) = 0 ∧
      F4.cartanPair (f4i 2) (orbitCertRoot F4.tag 24) = -1 ∧
      F4.cartanPair (f4i 3) (orbitCertRoot F4.tag 24) = 2) ∧
    (F4.cartanPair (f4i 0) (orbitCertRoot F4.tag 33) = 2 ∧
      F4.cartanPair (f4i 1) (orbitCertRoot F4.tag 33) = -1 ∧
      F4.cartanPair (f4i 2) (orbitCertRoot F4.tag 33) = 0 ∧
      F4.cartanPair (f4i 3) (orbitCertRoot F4.tag 33) = 0) ∧
    (F4.cartanPair (f4i 0) (orbitCertRoot F4.tag 28) = -1 ∧
      F4.cartanPair (f4i 1) (orbitCertRoot F4.tag 28) = 1 ∧
      F4.cartanPair (f4i 2) (orbitCertRoot F4.tag 28) = 0 ∧
      F4.cartanPair (f4i 3) (orbitCertRoot F4.tag 28) = -1) ∧
    (F4.cartanPair (f4i 0) (orbitCertRoot F4.tag 30) = -1 ∧
      F4.cartanPair (f4i 1) (orbitCertRoot F4.tag 30) = 0 ∧
      F4.cartanPair (f4i 2) (orbitCertRoot F4.tag 30) = 2 ∧
      F4.cartanPair (f4i 3) (orbitCertRoot F4.tag 30) = -2) ∧
    (F4.cartanPair (f4i 1) (orbitCertRoot F4.tag 45) = -1 ∧
      F4.cartanPair (f4i 2) (orbitCertRoot F4.tag 45) = 2) := by
  decide +kernel

omit [Finite K] [CharP K F4.prime] in
theorem torusWeight_left_A (s : Kˣ) :
    ((torusWeight m (orbitCertRoot F4.tag 24) (s, 1) : Kˣ) : K) = largeReeSigma m (s : K) ∧
      ((torusWeight m (orbitCertRoot F4.tag 33) (s, 1) : Kˣ) : K) = (s : K) ^ 2 := by
  obtain ⟨⟨h0, -, -, h3⟩, ⟨h0', -, -, h3'⟩, -⟩ := cartanPair_A_B
  refine ⟨?_, ?_⟩ <;> rw [torusWeight_apply, one_zpow, mul_one] <;> simp only [torusExp0]
  · rw [h0, h3, zero_add, largeReeSigma, show (2 : ℤ) * 2 ^ m = ((2 * 2 ^ m : ℕ) : ℤ) by
      push_cast; ring, zpow_natCast, Units.val_pow_eq_pow_val]
  · rw [h0', h3', zero_mul, add_zero, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
      Units.val_pow_eq_pow_val]

omit [CharP K F4.prime] in
theorem torusOne_conj_sylowA
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : Kˣ) (a : K) :
    pairedTorusHom m (f4i 0) (f4i 3) s * sylowA m K a * (pairedTorusHom m (f4i 0) (f4i 3) s)⁻¹ =
      sylowA m K (largeReeSigma m (s : K) * a) := by
  obtain ⟨h24, h33⟩ := torusWeight_left_A (m := m) s
  rw [← rankOneTorusPair_left, sylowA, sylowA, sylowX, sylowX, sylowX, sylowX, weyl_conj_mul,
    torusPair_conj_pinnedX m (s, 1) (sylowRoot_pos (r := 24) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX m (s, 1) (sylowRoot_pos (r := 33) (by norm_num) (by norm_num)).1,
    h24, h33, largeReeSigma_mul, largeReeSigma_sigma hK]

omit [CharP K F4.prime] in
theorem torusOne_conj_sylowH
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : Kˣ) (i : K) :
    pairedTorusHom m (f4i 0) (f4i 3) s * sylowH m K 0 i * (pairedTorusHom m (f4i 0) (f4i 3) s)⁻¹ =
      sylowH m K 0 ((s : K) ^ 2 ^ m * i) := by
  rw [sylowH_zero_eq_centralZ, sylowH_zero_eq_centralZ, ← rankOneTorusPair_left,
    torusPair_conj_centralZ hK]

omit [CharP K F4.prime] in
theorem torusTwo_conj_sylowH
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) (i : K) :
    pairedTorusHom m (f4i 1) (f4i 2) u * sylowH m K 0 i * (pairedTorusHom m (f4i 1) (f4i 2) u)⁻¹ =
      sylowH m K 0 i := by
  rw [sylowH_zero_eq_centralZ, ← rankOneTorusPair_right, torusPair_conj_centralZ hK,
    Units.val_one, one_pow, one_mul]

omit [Finite K] [CharP K F4.prime] in
theorem torusTwo_conj_sylowB
    (u : Kˣ) (c : K) :
    pairedTorusHom m (f4i 1) (f4i 2) u * sylowB m K 0 c * (pairedTorusHom m (f4i 1) (f4i 2) u)⁻¹ =
      sylowB m K 0 ((u : K) * c) := by
  obtain ⟨-, -, ⟨-, h1, h2, -⟩, ⟨-, h1', h2', -⟩, -⟩ := cartanPair_A_B
  have w28 : ((torusWeight m (orbitCertRoot F4.tag 28) (1, u) : Kˣ) : K) = u := by
    rw [torusWeight_apply, one_zpow, one_mul]
    simp only [torusExp1]
    rw [h1, h2, zero_mul, add_zero, zpow_one]
  have w30 : ((torusWeight m (orbitCertRoot F4.tag 30) (1, u) : Kˣ) : K) =
      largeReeSigma m (u : K) := by
    rw [torusWeight_apply, one_zpow, one_mul]
    simp only [torusExp1]
    rw [h1', h2', zero_add, largeReeSigma, show (2 : ℤ) * 2 ^ m = ((2 * 2 ^ m : ℕ) : ℤ) by
      push_cast; ring, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [← rankOneTorusPair_right, sylowB_zero_left, sylowB_zero_left, sylowX, sylowX, sylowX,
    sylowX, weyl_conj_mul,
    torusPair_conj_pinnedX m (1, u) (sylowRoot_pos (r := 28) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX m (1, u) (sylowRoot_pos (r := 30) (by norm_num) (by norm_num)).1,
    w28, w30, largeReeSigma_mul]

omit [CharP K F4.prime] in
theorem torusOne_conj_sylowB
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : Kˣ) (c : K) :
    pairedTorusHom m (f4i 0) (f4i 3) s * sylowB m K 0 c * (pairedTorusHom m (f4i 0) (f4i 3) s)⁻¹ =
      sylowB m K 0 (((s ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) * c) := by
  obtain ⟨-, -, ⟨h0, -, -, h3⟩, ⟨h0', -, -, h3'⟩, -⟩ := cartanPair_A_B
  have w28 : torusWeight m (orbitCertRoot F4.tag 28) (s, 1) = s ^ ((-1 : ℤ) - 2 ^ m) := by
    rw [torusWeight_apply, one_zpow, mul_one]
    simp only [torusExp0]
    rw [h0, h3]
    ring_nf
  have w30 : ((torusWeight m (orbitCertRoot F4.tag 30) (s, 1) : Kˣ) : K) =
      largeReeSigma m (((s ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K)) := by
    rw [torusWeight_apply, one_zpow, mul_one, largeReeSigma, ← Units.val_pow_eq_pow_val,
      ← zpow_natCast, ← zpow_mul]
    simp only [torusExp0]
    rw [h0', h3']
    congr 1
    refine units_zpow_congr hK s 1 ?_
    push_cast
    rw [show ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 by ring]
    ring
  rw [← rankOneTorusPair_left, sylowB_zero_left, sylowB_zero_left, sylowX, sylowX, sylowX,
    sylowX, weyl_conj_mul,
    torusPair_conj_pinnedX m (s, 1) (sylowRoot_pos (r := 28) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX m (s, 1) (sylowRoot_pos (r := 30) (by norm_num) (by norm_num)).1,
    w28, w30, largeReeSigma_mul]

omit [CharP K F4.prime] in
theorem torusTwo_conj_sylowL
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) (l : K) :
    pairedTorusHom m (f4i 1) (f4i 2) u * sylowL m K l * (pairedTorusHom m (f4i 1) (f4i 2) u)⁻¹ =
      sylowL m K (((u ^ ((1 : ℤ) - 2 ^ m) : Kˣ) : K) * l) := by
  obtain ⟨-, -, -, -, ⟨h1, h2⟩⟩ := cartanPair_A_B
  have w45 : ((torusWeight m (orbitCertRoot F4.tag 45) (1, u) : Kˣ) : K) =
      largeReeSigma m (((u ^ ((1 : ℤ) - 2 ^ m) : Kˣ) : K)) := by
    rw [torusWeight_apply, one_zpow, one_mul, largeReeSigma, ← Units.val_pow_eq_pow_val,
      ← zpow_natCast, ← zpow_mul]
    simp only [torusExp1]
    rw [h1, h2]
    congr 1
    refine units_zpow_congr hK u 1 ?_
    push_cast
    rw [show ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 by ring]
    ring
  rw [← rankOneTorusPair_right, sylowL, sylowL, sylowX, sylowX, sylowX, sylowX, weyl_conj_mul,
    torusPair_conj_pinnedX m (1, u) (sylowRoot_pos (r := 41) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX m (1, u) (sylowRoot_pos (r := 45) (by norm_num) (by norm_num)).1,
    torusWeight_right_41, w45, largeReeSigma_mul]

theorem torusOne_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : Kˣ) :
    pairedTorusHom m (f4i 0) (f4i 3) s ∈ F4.reeFixedTorus K m :=
  rankOneTorusOne_le hK ⟨s, rfl⟩

theorem torusTwo_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) :
    pairedTorusHom m (f4i 1) (f4i 2) u ∈ F4.reeFixedTorus K m :=
  rankOneTorusTwo_le hK ⟨u, rfl⟩

theorem exists_torus_conj_sylowA
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {a a' : K} (ha : a ≠ 0)
    (ha' : a' ≠ 0) : ∃ h ∈ F4.reeFixedTorus K m, h * sylowA m K a * h⁻¹ = sylowA m K a' := by
  set r : Kˣ := Units.mk0 ((a' / a) ^ 2 ^ m) (pow_ne_zero _ (div_ne_zero ha' ha))
  refine ⟨_, torusOne_mem hK r, ?_⟩
  rw [torusOne_conj_sylowA hK, Units.val_mk0, largeReeSigma_pow hK, div_mul_cancel₀ _ ha]

theorem exists_torus_conj_sylowH
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {i i' : K} (hi : i ≠ 0)
    (hi' : i' ≠ 0) :
    ∃ h ∈ F4.reeFixedTorus K m, h * sylowH m K 0 i * h⁻¹ = sylowH m K 0 i' := by
  set r : Kˣ := Units.mk0 (largeReeSigma m (i' / i))
    ((largeReeSigma_eq_zero_iff _).not.2 (div_ne_zero hi' hi))
  refine ⟨_, torusOne_mem hK r, ?_⟩
  rw [torusOne_conj_sylowH hK, Units.val_mk0, largeReeSigma_pow_two_pow hK, div_mul_cancel₀ _ hi]

omit [CharP K F4.prime] in
theorem zpow_one_sub_surj (hK : Nat.card K = 2 ^ (2 * m + 1)) (r : Kˣ) :
    (r ^ ((2 : ℤ) * 2 ^ m + 2)) ^ ((1 : ℤ) - 2 ^ m) = r := by
  rw [← zpow_mul]
  conv_rhs => rw [← zpow_one r]
  refine units_zpow_congr hK r (-1) ?_
  rw [show ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 by ring]
  ring

theorem exists_torus_conj_sylowL
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {l l' : K} (hl : l ≠ 0)
    (hl' : l' ≠ 0) : ∃ h ∈ F4.reeFixedTorus K m, h * sylowL m K l * h⁻¹ = sylowL m K l' := by
  set r : Kˣ := Units.mk0 (l' / l) (div_ne_zero hl' hl)
  refine ⟨_, torusTwo_mem hK (r ^ ((2 : ℤ) * 2 ^ m + 2)), ?_⟩
  rw [torusTwo_conj_sylowL hK, zpow_one_sub_surj hK, Units.val_mk0, div_mul_cancel₀ _ hl]

theorem exists_torus_conj_sylowB_mul_sylowH
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {c i c' i' : K}
    (hc : c ≠ 0) (hi : i ≠ 0) (hc' : c' ≠ 0) (hi' : i' ≠ 0) :
    ∃ h ∈ F4.reeFixedTorus K m,
      h * (sylowB m K 0 c * sylowH m K 0 i) * h⁻¹ = sylowB m K 0 c' * sylowH m K 0 i' := by
  set s : Kˣ := Units.mk0 (largeReeSigma m (i' / i))
    ((largeReeSigma_eq_zero_iff _).not.2 (div_ne_zero hi' hi))
  have hc1 : ((s ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) * c ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) hc
  set u : Kˣ := Units.mk0 (c' / (((s ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) * c)) (div_ne_zero hc' hc1)
  refine ⟨pairedTorusHom m (f4i 1) (f4i 2) u * pairedTorusHom m (f4i 0) (f4i 3) s,
    mul_mem (torusTwo_mem hK u) (torusOne_mem hK s), ?_⟩
  have e : ∀ T₁ T₂ X Y : ModGL F4.tag K, T₂ * T₁ * (X * Y) * (T₂ * T₁)⁻¹ =
      (T₂ * (T₁ * X * T₁⁻¹) * T₂⁻¹) * (T₂ * (T₁ * Y * T₁⁻¹) * T₂⁻¹) := fun _ _ _ _ => by group
  rw [e, torusOne_conj_sylowB hK, torusOne_conj_sylowH hK, torusTwo_conj_sylowB,
    torusTwo_conj_sylowH hK, Units.val_mk0, Units.val_mk0, div_mul_cancel₀ _ hc1,
    largeReeSigma_pow_two_pow hK, div_mul_cancel₀ _ hi]

end CFSG.LieType.Ree.LargeReeInvolution
