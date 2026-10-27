module

public import CFSG.LieType.Ree.LargeReeInvolutionFusionStrata

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open ReeTag
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom f4i)

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

section Transports

omit [Finite K]

theorem weylOne_conj_sylowD
    (e : K) :
    weylOne K * sylowD m K 0 e * (weylOne K)⁻¹ = sylowB m K 0 e := by
  rw [sylowD_zero_left, sylowB_zero_left,
    weylOne_conj_pair (r₁ := 36) (r₁' := 28) (r₂ := 39) (r₂' := 30) (by decide) (by decide)]

theorem weylOne_conj_sylowF
    (g : K) :
    weylOne K * sylowF m K 0 g * (weylOne K)⁻¹ = sylowH m K 0 g := by
  rw [sylowF_zero_left, sylowH_zero_left,
    weylOne_conj_pair (r₁ := 43) (r₁' := 44) (r₂ := 46) (r₂' := 47) (by decide) (by decide)]

theorem weylOne_conj_sylowH
    (i : K) :
    weylOne K * sylowH m K 0 i * (weylOne K)⁻¹ = sylowF m K 0 i := by
  rw [sylowF_zero_left, sylowH_zero_left,
    weylOne_conj_pair (r₁ := 44) (r₁' := 43) (r₂ := 47) (r₂' := 46) (by decide) (by decide)]

theorem weylOne_conj_sylowK
    (k : K) :
    weylOne K * sylowK m K k * (weylOne K)⁻¹ = sylowJ m K k := by
  rw [sylowK, sylowJ,
    weylOne_conj_pair (r₁ := 38) (r₁' := 31) (r₂ := 42) (r₂' := 40) (by decide) (by decide)]

theorem weylOne_conj_sylowL
    (l : K) :
    weylOne K * sylowL m K l * (weylOne K)⁻¹ = sylowL m K l := by
  rw [sylowL, weylOne_conj_pair (r₁ := 41) (r₁' := 41) (r₂ := 45) (r₂' := 45) (by decide)
    (by decide)]

theorem weylOne_conj_sylowJ
    (j : K) :
    weylOne K * sylowJ m K j * (weylOne K)⁻¹ = sylowK m K j := by
  rw [sylowK, sylowJ,
    weylOne_conj_pair (r₁ := 31) (r₁' := 38) (r₂ := 40) (r₂' := 42) (by decide) (by decide)]

theorem weylOne_conj_sylowB
    (c : K) :
    weylOne K * sylowB m K 0 c * (weylOne K)⁻¹ = sylowD m K 0 c := by
  rw [sylowD_zero_left, sylowB_zero_left,
    weylOne_conj_pair (r₁ := 28) (r₁' := 36) (r₂ := 30) (r₂' := 39) (by decide) (by decide)]

theorem weylTwo_conj_sylowF
    (g : K) :
    weylTwo K * sylowF m K 0 g * (weylTwo K)⁻¹ = sylowD m K 0 g := by
  rw [sylowF_zero_left, sylowD_zero_left,
    weylTwo_conj_pair (r₁ := 43) (r₁' := 36) (r₂ := 46) (r₂' := 39) (by decide) (by decide)]

theorem weylTwo_conj_sylowH
    (i : K) :
    weylTwo K * sylowH m K 0 i * (weylTwo K)⁻¹ = sylowH m K 0 i := by
  rw [sylowH_zero_left, weylTwo_conj_pair (r₁ := 44) (r₁' := 44) (r₂ := 47) (r₂' := 47)
    (by decide) (by decide)]

theorem weylTwo_conj_sylowJ
    (j : K) :
    weylTwo K * sylowJ m K j * (weylTwo K)⁻¹ = sylowA m K j := by
  rw [sylowJ, sylowA,
    weylTwo_conj_pair (r₁ := 31) (r₁' := 24) (r₂ := 40) (r₂' := 33) (by decide) (by decide)]

theorem weylTwo_conj_sylowK
    (k : K) :
    weylTwo K * sylowK m K k * (weylTwo K)⁻¹ = sylowL m K k := by
  rw [sylowK, sylowL,
    weylTwo_conj_pair (r₁ := 38) (r₁' := 41) (r₂ := 42) (r₂' := 45) (by decide) (by decide)]

theorem weylTwo_conj_sylowL
    (l : K) :
    weylTwo K * sylowL m K l * (weylTwo K)⁻¹ = sylowK m K l := by
  rw [sylowK, sylowL,
    weylTwo_conj_pair (r₁ := 41) (r₁' := 38) (r₂ := 45) (r₂' := 42) (by decide) (by decide)]

theorem weylTwo_conj_sylowD
    (e : K) :
    weylTwo K * sylowD m K 0 e * (weylTwo K)⁻¹ = sylowF m K 0 e := by
  rw [sylowF_zero_left, sylowD_zero_left,
    weylTwo_conj_pair (r₁ := 36) (r₁' := 43) (r₂ := 39) (r₂' := 46) (by decide) (by decide)]

theorem weylTwo_conj_sylowA
    (a : K) :
    weylTwo K * sylowA m K a * (weylTwo K)⁻¹ = sylowJ m K a := by
  rw [sylowJ, sylowA,
    weylTwo_conj_pair (r₁ := 24) (r₁' := 31) (r₂ := 33) (r₂' := 40) (by decide) (by decide)]

theorem weyl_conj_sylowA_one :
    (weylTwo K * weylOne K * weylTwo K) * sylowA m K 1 * (weylTwo K * weylOne K * weylTwo K)⁻¹ =
      sylowL m K 1 := by
  calc (weylTwo K * weylOne K * weylTwo K) * sylowA m K 1 *
        (weylTwo K * weylOne K * weylTwo K)⁻¹ =
      weylTwo K * (weylOne K * (weylTwo K * sylowA m K 1 * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
        (weylTwo K)⁻¹ := by group
    _ = sylowL m K 1 := by
      rw [weylTwo_conj_sylowA, weylOne_conj_sylowJ, weylTwo_conj_sylowK]

theorem weyl_conj_sylowB_zero
    (c : K) :
    (weylOne K * weylTwo K * weylOne K) * sylowB m K 0 c * (weylOne K * weylTwo K * weylOne K)⁻¹ =
      sylowH m K 0 c := by
  calc (weylOne K * weylTwo K * weylOne K) * sylowB m K 0 c *
        (weylOne K * weylTwo K * weylOne K)⁻¹ =
      weylOne K * (weylTwo K * (weylOne K * sylowB m K 0 c * (weylOne K)⁻¹) * (weylTwo K)⁻¹) *
        (weylOne K)⁻¹ := by group
    _ = sylowH m K 0 c := by
      rw [weylOne_conj_sylowB, weylTwo_conj_sylowD, weylOne_conj_sylowF]

end Transports

theorem weylOne_mem :
    weylOne K ∈ F4.reeGamma K m :=
  rankOne_canonicalRep_one_mem_reeGamma

theorem weylTwo_mem :
    weylTwo K ∈ F4.reeGamma K m :=
  rankOne_canonicalRep_two_mem_reeGamma

theorem reeFixedPosUnipotent_le_reeGamma' :
    F4.reeFixedPosUnipotent K m ≤ F4.reeGamma K m :=
  fun _ hu => (Subgroup.mem_inf.1 hu).2

theorem reeFixedTorus_le_reeGamma' :
    F4.reeFixedTorus K m ≤ F4.reeGamma K m :=
  fun _ hh => (Subgroup.mem_inf.1 hh).2

omit [Finite K] [CharP K F4.prime] in
theorem sylowV_blocks
    (e g i j k l : K) :
    sylowV m K 0 0 0 0 e 0 g 0 i j k l =
      sylowD m K 0 e * sylowF m K 0 g * sylowH m K 0 i * sylowJ m K j * sylowK m K k *
        sylowL m K l := by
  rw [sylowV, sylowA_zero, sylowB_zero_zero, one_mul, one_mul]

omit [Finite K] [CharP K F4.prime] in
theorem sylowJ_zero
    : sylowJ m K (0 : K) = 1 := by
  simp [sylowJ, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem sylowK_zero
    : sylowK m K (0 : K) = 1 := by
  simp [sylowK, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem sylowF_zero_zero
    : sylowF m K 0 (0 : K) = 1 := by
  simp [sylowF, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem sylowD_zero_zero
    : sylowD m K 0 (0 : K) = 1 := by
  simp [sylowD, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem blocks_eq_sylowV
    (c e g i j k l : K) :
    sylowB m K 0 c = sylowV m K 0 0 c 0 0 0 0 0 0 0 0 0 ∧
    sylowD m K 0 e = sylowV m K 0 0 0 0 e 0 0 0 0 0 0 0 ∧
    sylowF m K 0 g = sylowV m K 0 0 0 0 0 0 g 0 0 0 0 0 ∧
    sylowH m K 0 i = sylowV m K 0 0 0 0 0 0 0 0 i 0 0 0 ∧
    sylowJ m K j = sylowV m K 0 0 0 0 0 0 0 0 0 j 0 0 ∧
    sylowK m K k = sylowV m K 0 0 0 0 0 0 0 0 0 0 k 0 ∧
    sylowL m K l = sylowV m K 0 0 0 0 0 0 0 0 0 0 0 l := by
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowJ_zero, sylowK_zero, one_mul, mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [sylowH, sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem blocks_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (c e g i j k l : K) :
    sylowB m K 0 c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
    (sylowD m K 0 e ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowD m K 0 e ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) ∧
    (sylowF m K 0 g ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowF m K 0 g ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) ∧
    (sylowH m K 0 i ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowH m K 0 i ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) ∧
    (sylowJ m K j ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowJ m K j ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) ∧
    (sylowK m K k ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowK m K k ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) ∧
    (sylowL m K l ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowL m K l ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩) := by
  obtain ⟨hB, hD, hF, hH, hJ, hKk, hL⟩ := blocks_eq_sylowV (m := m) c e g i j k l
  have h2 : ∀ d e f g h i j k l : K, sylowV m K 0 0 0 d e f g h i j k l ∈
      F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := fun d e f g h i j k l =>
    Subgroup.mem_inf.2 ⟨sylowV_rest_mem_rootSpan_one _ _ _ _ _ _ _ _ _,
      (Subgroup.mem_inf.1 (sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _)).2⟩
  rw [hB, hD, hF, hH, hJ, hKk, hL]
  exact ⟨sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _,
    ⟨sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _, h2 _ _ _ _ _ _ _ _ _⟩,
    ⟨sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _, h2 _ _ _ _ _ _ _ _ _⟩,
    ⟨sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _, h2 _ _ _ _ _ _ _ _ _⟩,
    ⟨sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _, h2 _ _ _ _ _ _ _ _ _⟩,
    ⟨sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _, h2 _ _ _ _ _ _ _ _ _⟩,
    ⟨sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _, h2 _ _ _ _ _ _ _ _ _⟩⟩

theorem sylowA_mem_complement_one
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : K) :
    sylowA m K s ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
  Subgroup.mem_inf.2 ⟨sylowA_mem_rootSpan_one _,
    (Subgroup.mem_inf.1 (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK s))).2⟩

theorem complement_le_U
    (j : Fin F4.fixedOrbitCount) {w : ModGL F4.tag K}
    (hw : w ∈ F4.reeFixedOrbitComplementUnipotent K m j) : w ∈ F4.reeFixedPosUnipotent K m :=
  reeFixedOrbitComplementUnipotent_le j hw

theorem conj_tOne_of_coord_zero_ne
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : Fin 12 → K}
    (hsq : sylowVec m K x ^ 2 = 1) (hx : x 0 ≠ 0) :
    ∃ g ∈ F4.reeGamma K m, g * sylowVec m K x * g⁻¹ = sylowL m K 1 := by
  set s : Kˣ := Units.mk0 ((x 0)⁻¹ ^ 2 ^ m) (pow_ne_zero _ (inv_ne_zero hx)) with hs
  have hσs : largeReeSigma m (s : K) = (x 0)⁻¹ := by rw [hs, Units.val_mk0, largeReeSigma_pow hK]
  set T := pairedTorusHom m (f4i 0) (f4i 3) s with hT
  have hTmem := torusOne_mem (m := m) hK s
  obtain ⟨y, -, hy⟩ := (bijOn_sylowVec hK).2.2 (torus_conj_mem hTmem
    ((bijOn_sylowVec hK).1 (Set.mem_univ x)))
  have hw := sylowV_zero_mem_complement hK (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
    (x 10) (x 11)
  have hw' : T * sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
      (x 11) * T⁻¹ ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ :=
    (Subgroup.mem_normalizer_iff.1 (reeFixedTorus_le_normalizer_complement _ hTmem) _).1 hw
  have e : sylowVec m K y = sylowA m K (largeReeSigma m (s : K) * x 0) *
      (T * sylowV m K 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) *
        T⁻¹) := by
    rw [hy, sylowVec_eq_sylowA_mul x, hT, ← torusOne_conj_sylowA hK]
    group
  have hy0 := coord_zero_eq hK hw' e
  rw [hσs, inv_mul_cancel₀ hx] at hy0
  have hyS : sylowVec m K y ∈ sylowVec m K '' {x | x 0 = 1 ∧ sylowVec m K x ^ 2 = 1} :=
    ⟨y, ⟨hy0, by rw [hy]; exact conj_sq_eq_one hsq⟩, rfl⟩
  rw [← uClass_sylowA_one_eq hK] at hyS
  obtain ⟨u, hu, hu'⟩ := hyS
  refine ⟨(weylTwo K * weylOne K * weylTwo K) * u⁻¹ * T,
    mul_mem (mul_mem (mul_mem (mul_mem weylTwo_mem weylOne_mem) weylTwo_mem)
      (inv_mem (reeFixedPosUnipotent_le_reeGamma' hu))) (reeFixedTorus_le_reeGamma' hTmem), ?_⟩
  have hA : u⁻¹ * (T * sylowVec m K x * T⁻¹) * u = sylowA m K 1 := by
    rw [← hy, ← hu']
    group
  calc (weylTwo K * weylOne K * weylTwo K) * u⁻¹ * T * sylowVec m K x *
        ((weylTwo K * weylOne K * weylTwo K) * u⁻¹ * T)⁻¹ =
      (weylTwo K * weylOne K * weylTwo K) * (u⁻¹ * (T * sylowVec m K x * T⁻¹) * u) *
        (weylTwo K * weylOne K * weylTwo K)⁻¹ := by group
    _ = sylowL m K 1 := by rw [hA, weyl_conj_sylowA_one]

theorem conj_of_coord_two_ne
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {x : Fin 12 → K} (hsq : sylowVec m K x ^ 2 = 1) (hx0 : x 0 = 0) (hx2 : x 2 ≠ 0) :
    (∃ g ∈ F4.reeGamma K m, g * sylowVec m K x * g⁻¹ = sylowH m K 0 1) ∨
      ∃ g ∈ F4.reeGamma K m, g * sylowVec m K x * g⁻¹ = sylowL m K 1 := by
  have hmem : sylowVec m K x ∈ sylowVec m K '' {y | y 0 = 0 ∧ y 2 = x 2 ∧ sylowVec m K y ^ 2 = 1} :=
    ⟨x, ⟨hx0, rfl, hsq⟩, rfl⟩
  rw [(stratumZero_eq hm hK hx2).1, Set.mem_iUnion] at hmem
  obtain ⟨i, u, hu, hu'⟩ := hmem
  have huΓ := reeFixedPosUnipotent_le_reeGamma' hu
  have hv : u⁻¹ * sylowVec m K x * u = sylowB m K 0 (x 2) * sylowH m K 0 i := by
    rw [← hu']
    group
  by_cases hi : i = 0
  ·
    left
    have hz0 : sylowH m K 0 (0 : K) = 1 := by
      rw [sylowH_zero_left, sylowX, sylowX, largeReeSigma_zero, pinnedX_zero, pinnedX_zero,
        mul_one]
    rw [hi, hz0, mul_one] at hv
    obtain ⟨h, hh, hh'⟩ := exists_torus_conj_sylowH hK hx2 one_ne_zero
    refine ⟨h * (weylOne K * weylTwo K * weylOne K) * u⁻¹,
      mul_mem (mul_mem (reeFixedTorus_le_reeGamma' hh)
        (mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem)) (inv_mem huΓ), ?_⟩
    calc h * (weylOne K * weylTwo K * weylOne K) * u⁻¹ * sylowVec m K x *
          (h * (weylOne K * weylTwo K * weylOne K) * u⁻¹)⁻¹ =
        h * ((weylOne K * weylTwo K * weylOne K) * (u⁻¹ * sylowVec m K x * u) *
          (weylOne K * weylTwo K * weylOne K)⁻¹) * h⁻¹ := by group
      _ = sylowH m K 0 1 := by rw [hv, weyl_conj_sylowB_zero, hh']
  ·
    right
    obtain ⟨h, hh, hh'⟩ := exists_torus_conj_sylowB_mul_sylowH hK hx2 hi one_ne_zero one_ne_zero
    have hBU : sylowB m K 1 0 ∈ F4.reeGamma K m :=
      reeFixedPosUnipotent_le_reeGamma' (reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK 1 0))
    have hAU : sylowA m K 1 ∈ F4.reeGamma K m :=
      reeFixedPosUnipotent_le_reeGamma' (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK 1))
    refine ⟨(sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h * u⁻¹,
      mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hBU weylTwo_mem) hBU) hAU) weylOne_mem)
        (reeFixedTorus_le_reeGamma' hh)) (inv_mem huΓ), ?_⟩
    calc (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h * u⁻¹ *
          sylowVec m K x *
            ((sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) * h *
              u⁻¹)⁻¹ =
        (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) *
          (h * (u⁻¹ * sylowVec m K x * u) * h⁻¹) *
            (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K)⁻¹ := by
          group
      _ = sylowL m K 1 := by rw [hv, hh', fusion_word]

theorem conj_tOne_of_eq_sylowA_mul
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {E : ModGL F4.tag K}
    (hE : E ∈ F4.reeFixedPosUnipotent K m) (hsq : E ^ 2 = 1) {s : K} (hs : s ≠ 0)
    {w : ModGL F4.tag K} (hw : w ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩)
    (h : E = sylowA m K s * w) : ∃ g ∈ F4.reeGamma K m, g * E * g⁻¹ = sylowL m K 1 := by
  obtain ⟨y, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hE
  have hy0 := coord_zero_eq hK hw h
  exact conj_tOne_of_coord_zero_ne hK hsq (hy0 ▸ hs)

theorem conj_of_eq_sylowB_mul
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {E : ModGL F4.tag K} (hE : E ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩)
    (hsq : E ^ 2 = 1) {c : K} (hc : c ≠ 0) {n : ModGL F4.tag K}
    (hn : n ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩)
    (h : E = sylowB m K 0 c * n) :
    (∃ g ∈ F4.reeGamma K m, g * E * g⁻¹ = sylowH m K 0 1) ∨
      ∃ g ∈ F4.reeGamma K m, g * E * g⁻¹ = sylowL m K 1 := by
  obtain ⟨y, -, rfl⟩ := (bijOn_sylowVec hK).2.2 (complement_le_U _ hE)
  have hy0 := coord_zero_eq hK hE (by rw [sylowA_zero, one_mul])
  have hy2 := (coord_one_two_eq hK hn h).2
  exact conj_of_coord_two_ne hm hK hsq hy0 (hy2 ▸ hc)

theorem conj_or_comp
    {v E w : ModGL F4.tag K} (hw : w ∈ F4.reeGamma K m) (hE : w * v * w⁻¹ = E)
    (h : (∃ g ∈ F4.reeGamma K m, g * E * g⁻¹ = sylowH m K 0 1) ∨
      ∃ g ∈ F4.reeGamma K m, g * E * g⁻¹ = sylowL m K 1) :
    (∃ g ∈ F4.reeGamma K m, g * v * g⁻¹ = sylowH m K 0 1) ∨
      ∃ g ∈ F4.reeGamma K m, g * v * g⁻¹ = sylowL m K 1 := by
  have key : ∀ g : ModGL F4.tag K, g * w * v * (g * w)⁻¹ = g * E * g⁻¹ := fun g => by
    rw [← hE]
    group
  rcases h with ⟨g, hg, hgE⟩ | ⟨g, hg, hgE⟩
  · exact Or.inl ⟨g * w, mul_mem hg hw, (key g).trans hgE⟩
  · exact Or.inr ⟨g * w, mul_mem hg hw, (key g).trans hgE⟩

theorem conj_mem_U
    {v w E : ModGL F4.tag K} (hv : v ∈ F4.reeGamma K m) (hw : w ∈ F4.reeGamma K m)
    (hE : w * v * w⁻¹ = E) (hEU : E ∈ posUnipotent F4.tag K) : E ∈ F4.reeFixedPosUnipotent K m :=
  Subgroup.mem_inf.2 ⟨hEU, hE ▸ mul_mem (mul_mem hw hv) (inv_mem hw)⟩

theorem conj_of_coord_zero_two_eq
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {x : Fin 12 → K} (hsq : sylowVec m K x ^ 2 = 1) (hx0 : x 0 = 0) (hx2 : x 2 = 0)
    (hne : sylowVec m K x ≠ 1) :
    (∃ g ∈ F4.reeGamma K m, g * sylowVec m K x * g⁻¹ = sylowH m K 0 1) ∨
      ∃ g ∈ F4.reeGamma K m, g * sylowVec m K x * g⁻¹ = sylowL m K 1 := by
  have hsq' : sylowV m K 0 (x 1) 0 (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) ^ 2 =
      1 := by
    have h := hsq
    simp only [sylowVec, hx0, hx2] at h
    exact h
  obtain ⟨h1, h3, h5, h7, hej⟩ := (sylowV_zero_zero_sq_eq_one_iff _ _ _ _ _ _ _ _ _ _).1 hsq'
  have hv : sylowVec m K x = sylowV m K 0 0 0 0 (x 4) 0 (x 6) 0 (x 8) (x 9) (x 10) (x 11) := by
    simp only [sylowVec, hx0, h1, hx2, h3, h5, h7]
  have hvΓ : sylowVec m K x ∈ F4.reeGamma K m :=
    reeFixedPosUnipotent_le_reeGamma' ((bijOn_sylowVec hK).1 (Set.mem_univ x))
  rw [sylowV_blocks] at hv
  set e := x 4
  set g := x 6
  set i := x 8
  set j := x 9
  set k := x 10
  set l := x 11
  have hU : ∀ {E : ModGL F4.tag K}, E ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ →
      E ∈ posUnipotent F4.tag K := fun hE => (Subgroup.mem_inf.1 (complement_le_U _ hE)).1
  obtain ⟨-, ⟨hD1, -⟩, ⟨hF1, hF2⟩, ⟨hH1, hH2⟩, ⟨hJ1, hJ2⟩, ⟨hK1, hK2⟩, ⟨hL1, hL2⟩⟩ :=
    blocks_mem (m := m) hK 0 0 0 0 0 0 0
  have hB : ∀ c, sylowB m K 0 c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ :=
    fun c => (blocks_mem (m := m) hK c 0 0 0 0 0 0).1
  have hD : ∀ c, sylowD m K 0 c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowD m K 0 c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    fun c => (blocks_mem (m := m) hK 0 c 0 0 0 0 0).2.1
  have hF : ∀ c, sylowF m K 0 c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowF m K 0 c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    fun c => (blocks_mem (m := m) hK 0 0 c 0 0 0 0).2.2.1
  have hH : ∀ c, sylowH m K 0 c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowH m K 0 c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    fun c => (blocks_mem (m := m) hK 0 0 0 c 0 0 0).2.2.2.1
  have hJ : ∀ c, sylowJ m K c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowJ m K c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    fun c => (blocks_mem (m := m) hK 0 0 0 0 c 0 0).2.2.2.2.1
  have hKb : ∀ c, sylowK m K c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowK m K c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    fun c => (blocks_mem (m := m) hK 0 0 0 0 0 c 0).2.2.2.2.2.1
  have hLb : ∀ c, sylowL m K c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ ∧
      sylowL m K c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
    fun c => (blocks_mem (m := m) hK 0 0 0 0 0 0 c).2.2.2.2.2.2
  clear hD1 hF1 hF2 hH1 hH2 hJ1 hJ2 hK1 hK2 hL1 hL2
  have hAV2 := sylowA_mem_complement_one (m := m) hK
  have hn1 := weylOne_mem (K := K) (m := m)
  have hn2 := weylTwo_mem (K := K) (m := m)
  by_cases he : e = 0
  · rw [he, sylowD_zero_zero, one_mul] at hv
    by_cases hj : j = 0
    · rw [hj, sylowJ_zero, mul_one] at hv
      by_cases hk : k = 0
      · rw [hk, sylowK_zero, mul_one] at hv
        by_cases hg : g = 0
        · rw [hg, sylowF_zero_zero, one_mul] at hv
          by_cases hl : l = 0
          ·
            rw [hl, show sylowL m K (0 : K) = 1 by
              rw [sylowL, largeReeSigma_zero, sylowX, sylowX, pinnedX_zero, pinnedX_zero,
                mul_one], mul_one] at hv
            have hi : i ≠ 0 := by
              rintro hi
              apply hne
              rw [hv, hi, sylowH_zero_left, sylowX, sylowX, largeReeSigma_zero, pinnedX_zero,
                pinnedX_zero, mul_one]
            obtain ⟨h, hh, hh'⟩ := exists_torus_conj_sylowH hK hi one_ne_zero
            exact Or.inl ⟨h, reeFixedTorus_le_reeGamma' hh, by rw [hv, hh']⟩
          ·
            set w := weylTwo K * weylOne K * weylTwo K with hw
            have hE : w * sylowVec m K x * w⁻¹ = sylowD m K 0 i * sylowA m K l := by
              rw [hv, hw]
              calc weylTwo K * weylOne K * weylTwo K * (sylowH m K 0 i * sylowL m K l) *
                    (weylTwo K * weylOne K * weylTwo K)⁻¹ =
                  weylTwo K * (weylOne K * (weylTwo K * sylowH m K 0 i * (weylTwo K)⁻¹) *
                    (weylOne K)⁻¹) * (weylTwo K)⁻¹ *
                  (weylTwo K * (weylOne K * (weylTwo K * sylowL m K l * (weylTwo K)⁻¹) *
                    (weylOne K)⁻¹) * (weylTwo K)⁻¹) := by group
                _ = _ := by
                  rw [weylTwo_conj_sylowH, weylOne_conj_sylowH, weylTwo_conj_sylowF,
                    weylTwo_conj_sylowL, weylOne_conj_sylowK, weylTwo_conj_sylowJ]
            have hwΓ : w ∈ F4.reeGamma K m := mul_mem (mul_mem hn2 hn1) hn2
            have hEU := conj_mem_U hvΓ hwΓ hE (mul_mem (hU (hD i).1)
              (Subgroup.mem_inf.1 (complement_le_U _ (hAV2 l))).1)
            refine conj_or_comp hwΓ hE (Or.inr ?_)
            refine conj_tOne_of_eq_sylowA_mul hK hEU (by rw [← hE]; exact conj_sq_eq_one hsq) hl
              (w := (sylowA m K l)⁻¹ * sylowD m K 0 i * sylowA m K l) ?_ (by group)
            have := (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer
              ⟨0, by decide⟩ (inv_mem (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK l)))) _).1
                (hD i).1
            rwa [inv_inv] at this
        ·
          set w := weylOne K * weylTwo K with hw
          have hE : w * sylowVec m K x * w⁻¹ =
              sylowB m K 0 g * (sylowF m K 0 i * sylowJ m K l) := by
            rw [hv, hw]
            calc weylOne K * weylTwo K * (sylowF m K 0 g * sylowH m K 0 i * sylowL m K l) *
                  (weylOne K * weylTwo K)⁻¹ =
                (weylOne K * (weylTwo K * sylowF m K 0 g * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
                  ((weylOne K * (weylTwo K * sylowH m K 0 i * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
                    (weylOne K * (weylTwo K * sylowL m K l * (weylTwo K)⁻¹) *
                      (weylOne K)⁻¹)) := by group
              _ = _ := by
                rw [weylTwo_conj_sylowF, weylOne_conj_sylowD, weylTwo_conj_sylowH,
                  weylOne_conj_sylowH, weylTwo_conj_sylowL, weylOne_conj_sylowK]
          have hwΓ : w ∈ F4.reeGamma K m := mul_mem hn1 hn2
          have hEV : sylowB m K 0 g * (sylowF m K 0 i * sylowJ m K l) ∈
              F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ :=
            mul_mem (hB g) (mul_mem (hF i).1 (hJ l).1)
          refine conj_or_comp hwΓ hE ?_
          exact conj_of_eq_sylowB_mul hm hK hEV (by rw [← hE]; exact conj_sq_eq_one hsq) hg
            (mul_mem (hF i).2 (hJ l).2) rfl
      ·
        set w := weylTwo K * weylOne K with hw
        have hE : w * sylowVec m K x * w⁻¹ =
            sylowH m K 0 g * sylowD m K 0 i * sylowA m K k * sylowK m K l := by
          rw [hv, hw]
          calc weylTwo K * weylOne K *
                (sylowF m K 0 g * sylowH m K 0 i * sylowK m K k * sylowL m K l) *
                  (weylTwo K * weylOne K)⁻¹ =
              (weylTwo K * (weylOne K * sylowF m K 0 g * (weylOne K)⁻¹) * (weylTwo K)⁻¹) *
                (weylTwo K * (weylOne K * sylowH m K 0 i * (weylOne K)⁻¹) * (weylTwo K)⁻¹) *
                  (weylTwo K * (weylOne K * sylowK m K k * (weylOne K)⁻¹) * (weylTwo K)⁻¹) *
                    (weylTwo K * (weylOne K * sylowL m K l * (weylOne K)⁻¹) *
                      (weylTwo K)⁻¹) := by group
            _ = _ := by
              rw [weylOne_conj_sylowF, weylTwo_conj_sylowH, weylOne_conj_sylowH,
                weylTwo_conj_sylowF, weylOne_conj_sylowK, weylTwo_conj_sylowJ,
                weylOne_conj_sylowL, weylTwo_conj_sylowL]
        have hwΓ : w ∈ F4.reeGamma K m := mul_mem hn2 hn1
        have hP : sylowH m K 0 g * sylowD m K 0 i ∈
            F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ :=
          mul_mem (hH g).1 (hD i).1
        have hEU := conj_mem_U hvΓ hwΓ hE (mul_mem (mul_mem (hU hP)
          (Subgroup.mem_inf.1 (complement_le_U _ (hAV2 k))).1) (hU (hKb l).1))
        refine conj_or_comp hwΓ hE (Or.inr ?_)
        refine conj_tOne_of_eq_sylowA_mul hK hEU (by rw [← hE]; exact conj_sq_eq_one hsq) hk
          (w := (sylowA m K k)⁻¹ * (sylowH m K 0 g * sylowD m K 0 i) * sylowA m K k *
            sylowK m K l) (mul_mem ?_ (hKb l).1) (by group)
        have := (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer
          ⟨0, by decide⟩ (inv_mem (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK k)))) _).1 hP
        rwa [inv_inv] at this
    ·
      have hE : weylTwo K * sylowVec m K x * (weylTwo K)⁻¹ =
          sylowD m K 0 g * sylowH m K 0 i * sylowA m K j * sylowL m K k * sylowK m K l := by
        rw [hv, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul, weylTwo_conj_sylowF,
          weylTwo_conj_sylowH, weylTwo_conj_sylowJ, weylTwo_conj_sylowK, weylTwo_conj_sylowL]
      have hP : sylowD m K 0 g * sylowH m K 0 i ∈
          F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ :=
        mul_mem (hD g).1 (hH i).1
      have hEU := conj_mem_U hvΓ hn2 hE (mul_mem (mul_mem (mul_mem (hU hP)
        (Subgroup.mem_inf.1 (complement_le_U _ (hAV2 j))).1) (hU (hLb k).1)) (hU (hKb l).1))
      refine conj_or_comp hn2 hE (Or.inr ?_)
      refine conj_tOne_of_eq_sylowA_mul hK hEU (by rw [← hE]; exact conj_sq_eq_one hsq) hj
        (w := (sylowA m K j)⁻¹ * (sylowD m K 0 g * sylowH m K 0 i) * sylowA m K j *
          (sylowL m K k * sylowK m K l)) (mul_mem ?_ (mul_mem (hLb k).1 (hKb l).1)) (by group)
      have := (Subgroup.mem_normalizer_iff.1 (reeFixedPosUnipotent_le_normalizer
        ⟨0, by decide⟩ (inv_mem (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK j)))) _).1 hP
      rwa [inv_inv] at this
  ·
    have hj : j = 0 := by
      rcases mul_eq_zero.1 hej with h | h
      · exact absurd h he
      · exact h
    rw [hj, sylowJ_zero, mul_one] at hv
    have hE : weylOne K * sylowVec m K x * (weylOne K)⁻¹ =
        sylowB m K 0 e * (sylowH m K 0 g * sylowF m K 0 i * sylowJ m K k * sylowL m K l) := by
      rw [hv, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul, weyl_conj_mul, weylOne_conj_sylowD,
        weylOne_conj_sylowF, weylOne_conj_sylowH, weylOne_conj_sylowK, weylOne_conj_sylowL]
      group
    have hN : sylowH m K 0 g * sylowF m K 0 i * sylowJ m K k * sylowL m K l ∈
        F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
      mul_mem (mul_mem (mul_mem (hH g).2 (hF i).2) (hJ k).2) (hLb l).2
    have hEV : sylowB m K 0 e * (sylowH m K 0 g * sylowF m K 0 i * sylowJ m K k *
        sylowL m K l) ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ :=
      mul_mem (hB e) (mul_mem (mul_mem (mul_mem (hH g).1 (hF i).1) (hJ k).1) (hLb l).1)
    refine conj_or_comp hn1 hE ?_
    exact conj_of_eq_sylowB_mul hm hK hEV (by rw [← hE]; exact conj_sq_eq_one hsq) he hN rfl

theorem exists_conj_mem_reeFixedPosUnipotent
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {g : ModGL F4.tag K} (hg : g ∈ F4.reeGamma K m) (hsq : g ^ 2 = 1) :
    ∃ y ∈ F4.reeGamma K m, y * g * y⁻¹ ∈ F4.reeFixedPosUnipotent K m := by
  have := finite_modGL (τ := F4.tag) (K := K)
  obtain ⟨S, hS⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center m hm K hK).1
  have hg2 : (⟨g, hg⟩ : F4.reeGamma K m) ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨g, hg⟩ : F4.reeGamma K m)) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (F4.reeGamma K m) P S
  have hgP : (⟨g, hg⟩ : F4.reeGamma K m) ∈ P := hP (Subgroup.mem_zpowers _)
  have hmem : y * ⟨g, hg⟩ * y⁻¹ ∈ ((y • P : Sylow 2 (F4.reeGamma K m)) :
      Set (F4.reeGamma K m)) := by
    rw [Sylow.coe_smul]
    exact ⟨⟨g, hg⟩, hgP, rfl⟩
  rw [hy] at hmem
  have hmem' : y * ⟨g, hg⟩ * y⁻¹ ∈ (S : Subgroup (F4.reeGamma K m)) := hmem
  rw [hS, Subgroup.mem_subgroupOf] at hmem'
  exact ⟨y, y.2, hmem'⟩

theorem involution_conj_zOne_or_tOne
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {g : ModGL F4.tag K} (hg : g ∈ F4.reeGamma K m) (hsq : g ^ 2 = 1) (hne : g ≠ 1) :
    (∃ x ∈ F4.reeGamma K m, x * g * x⁻¹ = sylowH m K 0 1) ∨
      ∃ x ∈ F4.reeGamma K m, x * g * x⁻¹ = sylowL m K 1 := by
  obtain ⟨y, hy, hyU⟩ := exists_conj_mem_reeFixedPosUnipotent hm hK hg hsq
  obtain ⟨x, -, hx⟩ := (bijOn_sylowVec hK).2.2 hyU
  have hxsq : sylowVec m K x ^ 2 = 1 := by rw [hx]; exact conj_sq_eq_one hsq
  have hxne : sylowVec m K x ≠ 1 := by
    rw [hx]
    intro h
    apply hne
    calc g = y⁻¹ * (y * g * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  refine conj_or_comp hy hx.symm ?_
  by_cases h0 : x 0 = 0
  · by_cases h2 : x 2 = 0
    · exact conj_of_coord_zero_two_eq hm hK hxsq h0 h2 hxne
    · exact conj_of_coord_two_ne hm hK hxsq h0 h2
  · exact Or.inr (conj_tOne_of_coord_zero_ne hK hxsq h0)

theorem large_Ree_every_involution_fuses
    (m : ℕ) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (∀ g ∈ F4.reeGamma K m, g ^ 2 = 1 → g ≠ 1 →
      (∃ x ∈ F4.reeGamma K m, x * g * x⁻¹ = sylowH m K 0 1) ∨
        ∃ x ∈ F4.reeGamma K m, x * g * x⁻¹ = sylowL m K 1) ∧
    (∀ c : K, c ≠ 0 →
      sylowVec m K '' {x | x 0 = 0 ∧ x 2 = c ∧ sylowVec m K x ^ 2 = 1} =
          ⋃ i : K, {y | ∃ u ∈ F4.reeFixedPosUnipotent K m,
            u * (sylowB m K 0 c * sylowH m K 0 i) * u⁻¹ = y} ∧
        (∀ i j : K, i ≠ j → Disjoint
          {y | ∃ u ∈ F4.reeFixedPosUnipotent K m, u * (sylowB m K 0 c * sylowH m K 0 i) * u⁻¹ = y}
          {y | ∃ u ∈ F4.reeFixedPosUnipotent K m,
            u * (sylowB m K 0 c * sylowH m K 0 j) * u⁻¹ = y}) ∧
        ∀ i : K, {y | ∃ u ∈ F4.reeFixedPosUnipotent K m,
          u * (sylowB m K 0 c * sylowH m K 0 i) * u⁻¹ = y}.ncard = (2 ^ (2 * m + 1)) ^ 4) ∧
    (∀ a a' : K, a ≠ 0 → a' ≠ 0 →
      ∃ h ∈ F4.reeFixedTorus K m, h * sylowA m K a * h⁻¹ = sylowA m K a') ∧
    (∀ i i' : K, i ≠ 0 → i' ≠ 0 →
      ∃ h ∈ F4.reeFixedTorus K m, h * sylowH m K 0 i * h⁻¹ = sylowH m K 0 i') ∧
    (∀ l l' : K, l ≠ 0 → l' ≠ 0 →
      ∃ h ∈ F4.reeFixedTorus K m, h * sylowL m K l * h⁻¹ = sylowL m K l') ∧
    (∀ c i c' i' : K, c ≠ 0 → i ≠ 0 → c' ≠ 0 → i' ≠ 0 → ∃ h ∈ F4.reeFixedTorus K m,
      h * (sylowB m K 0 c * sylowH m K 0 i) * h⁻¹ = sylowB m K 0 c' * sylowH m K 0 i') ∧
    (sylowB m K 1 0 * canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) *
          sylowB m K 1 0 * sylowA m K 1 *
            canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩)) *
        (sylowB m K 0 1 * sylowH m K 0 1) *
          (sylowB m K 1 0 *
            canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) *
              sylowB m K 1 0 * sylowA m K 1 *
                canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ =
      sylowL m K 1 :=
  ⟨fun _ hg hsq hne => involution_conj_zOne_or_tOne hm hK hg hsq hne,
    fun _ hc => stratumZero_eq hm hK hc,
    fun _ _ ha ha' => exists_torus_conj_sylowA hK ha ha',
    fun _ _ hi hi' => exists_torus_conj_sylowH hK hi hi',
    fun _ _ hl hl' => exists_torus_conj_sylowL hK hl hl',
    fun _ _ _ _ hc hi hc' hi' => exists_torus_conj_sylowB_mul_sylowH hK hc hi hc' hi',
    fusion_word⟩

end CFSG.LieType.Ree.LargeReeInvolution
