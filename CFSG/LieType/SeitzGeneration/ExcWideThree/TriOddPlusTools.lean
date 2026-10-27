module

public import CFSG.GroupTheory.IndexThreeCosets
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.NormaliseShort
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.NormalizerSubfieldSL2
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.MaxLNoT
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBPhi3
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddJ
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTau
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools

open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
open CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartOne.CTP
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
open scoped commutatorElement MatrixGroups

theorem d43Par_nsmul_eq_zero {K : Type} [Field K] {ℓ : ℕ} [CharP K ℓ] {σ : K →+* K}
    (i : Fin 6) (c : CFSG.Timmesfeld.RankTwo.d43Par σ i) : (ℓ : ℕ) • c = 0 := by
  revert c
  fin_cases i <;> intro c <;>
    simp only [CFSG.Timmesfeld.RankTwo.d43Par] at c ⊢ <;>
    (first
      | change (ℓ : ℕ) • (c : K) = 0
      | change (ℓ : ℕ) • (c : ↥(fixedField σ)) = 0) <;>
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

section DPow


theorem d4X_pow_eq_one {K : Type} [Field K] {ℓ : ℕ} [CharP K ℓ] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) (i : Fin 6)
    (c : CFSG.Timmesfeld.RankTwo.d43Par σ i) : (d4X hσ i c) ^ ℓ = 1 := by
  let φ : CFSG.Timmesfeld.RankTwo.d43Par σ i →+ Additive (twistedGroup σ) :=
    AddMonoidHom.mk' (fun c => Additive.ofMul (d4X hσ i c))
      fun a b => congrArg Additive.ofMul (d4X_add hσ i a b)
  have hzero : d4X hσ i (0 : CFSG.Timmesfeld.RankTwo.d43Par σ i) = 1 := by
    have := map_zero φ
    simpa [φ] using this
  have hpow : ∀ n : ℕ, (d4X hσ i c) ^ n = d4X hσ i ((n : ℕ) • c) := by
    intro n
    induction n with
    | zero => rw [pow_zero, zero_nsmul, hzero]
    | succ n ih => rw [pow_succ, ih, ← d4X_add, succ_nsmul]
  have hℓc : (ℓ : ℕ) • c = 0 := d43Par_nsmul_eq_zero i c
  rw [hpow, hℓc, hzero]

end DPow

section ConjPow


theorem conj_root_pow_eq_one {K : Type} [Field K] {ℓ : ℕ} [CharP K ℓ] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) {m : twistedGroup σ} {k k' : ℤ}
    (hc : conjBy m (hexGroup (twistedX σ) k) = hexGroup (twistedX σ) k')
    (hk : ∀ y ∈ hexGroup (twistedX σ) k, y ^ ℓ = 1) :
    ∀ y ∈ hexGroup (twistedX σ) k', y ^ ℓ = 1 := by
  intro y hy
  have hc' : conjBy m⁻¹ (hexGroup (twistedX σ) k') = hexGroup (twistedX σ) k := by
    have h := congrArg (conjBy m⁻¹) hc
    rw [← conjBy_mul, mul_inv_cancel, conjBy_one] at h
    exact h.symm
  have hmem : m * y * m⁻¹ ∈ hexGroup (twistedX σ) k := by
    rw [← hc']
    exact ⟨y, hy, by change m⁻¹⁻¹ * y * (m⁻¹⁻¹)⁻¹ = m * y * m⁻¹; rw [inv_inv]⟩
  have hp := hk _ hmem
  have e : (m * y * m⁻¹) ^ ℓ = m * y ^ ℓ * m⁻¹ := by
    simpa [MulAut.conj_apply] using map_pow (MulAut.conj m) y ℓ
  have h1 : m * y ^ ℓ * m⁻¹ = 1 := by rw [← e, hp]
  calc y ^ ℓ = m⁻¹ * (m * y ^ ℓ * m⁻¹) * m := by group
    _ = 1 := by rw [h1]; group

end ConjPow

section Core


theorem longSub_commutator_eq {K : Type} [Field K] [Finite K] (σ : K →+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    ⁅longSub 6 (hexGroup (twistedX σ)), longSub 6 (hexGroup (twistedX σ))⁆ =
      longSub 6 (hexGroup (twistedX σ)) := by
  have h : Group.IsPerfect ↥(longSub 6 (hexGroup (twistedX σ))) :=
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_longSub_quasisimple (σ := σ) hσ).1
  exact Subgroup.isPerfect_iff.mp h

theorem d4X_pow_eq_one_neg {K : Type} [Field K] {ℓ : ℕ} [CharP K ℓ] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) (k : ℤ) (hk : IsRoot 6 k) (hkneg : k < 0) :
    ∀ y ∈ hexGroup (twistedX σ) k, y ^ ℓ = 1 := by
  classical
  have R := d4RGD2 σ hσ
  have hpos1 : ∀ y ∈ hexGroup (twistedX σ) 1, y ^ ℓ = 1 := by
    intro y hy
    obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff hσ 0 y).1 (by simpa using hy)
    exact d4X_pow_eq_one hσ 0 c
  have hpos6 : ∀ y ∈ hexGroup (twistedX σ) 6, y ^ ℓ = 1 := by
    intro y hy
    obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff hσ 5 y).1 (by simpa using hy)
    exact d4X_pow_eq_one hσ 5 c
  have hm1 : ∀ y ∈ hexGroup (twistedX σ) (-1), y ^ ℓ = 1 :=
    conj_root_pow_eq_one hσ R.act₁.1 hpos1
  have hneg6 : ∀ y ∈ hexGroup (twistedX σ) (-6), y ^ ℓ = 1 :=
    conj_root_pow_eq_one hσ R.act₂.1 hpos6
  have hneg2 : ∀ y ∈ hexGroup (twistedX σ) (-2), y ^ ℓ = 1 := by
    refine conj_root_pow_eq_one (m := (nHat σ (1 : Fin 2))⁻¹) hσ ?_ hneg6
    have h := (R.act₁.2.2 6 (by norm_num) (by norm_num)).2
    simpa using h
  have hneg4 : ∀ y ∈ hexGroup (twistedX σ) (-4), y ^ ℓ = 1 := by
    refine conj_root_pow_eq_one (m := (nHat σ (0 : Fin 2))⁻¹) hσ ?_ hneg2
    have h := (R.act₂.2.2 2 (by norm_num) (by norm_num)).2
    simpa using h
  have hneg5 : ∀ y ∈ hexGroup (twistedX σ) (-5), y ^ ℓ = 1 := by
    refine conj_root_pow_eq_one (m := (nHat σ (0 : Fin 2))⁻¹) hσ ?_ hm1
    have h := (R.act₂.2.2 1 (by norm_num) (by norm_num)).2
    simpa using h
  have hneg3 : ∀ y ∈ hexGroup (twistedX σ) (-3), y ^ ℓ = 1 := by
    refine conj_root_pow_eq_one (m := (nHat σ (1 : Fin 2))⁻¹) hσ ?_ hneg5
    have h := (R.act₁.2.2 5 (by norm_num) (by norm_num)).2
    simpa using h
  intro y hy
  have hk0 := hk.1
  have hk6 := hk.2
  have hcases : k = -1 ∨ k = -2 ∨ k = -3 ∨ k = -4 ∨ k = -5 ∨ k = -6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hm1 _ hy, hneg2 _ hy, hneg3 _ hy, hneg4 _ hy, hneg5 _ hy, hneg6 _ hy]

theorem pow_eq_one_of_mem_root {K : Type} [Field K] {ℓ : ℕ} [CharP K ℓ] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    ∀ k, IsRoot 6 k → ∀ y ∈ hexGroup (twistedX σ) k, y ^ ℓ = 1 := by
  intro k hk y hy
  by_cases hneg : k < 0
  · exact d4X_pow_eq_one_neg hσ k hk hneg y hy
  · have hkpos : 0 < k := by have := hk.1; omega
    have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
      have := hk.2; omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff hσ 0 y).1 (by simpa using hy)
      exact d4X_pow_eq_one hσ 0 c
    · obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff hσ 1 y).1 (by simpa using hy)
      exact d4X_pow_eq_one hσ 1 c
    · obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff hσ 2 y).1 (by simpa using hy)
      exact d4X_pow_eq_one hσ 2 c
    · obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff hσ 3 y).1 (by simpa using hy)
      exact d4X_pow_eq_one hσ 3 c
    · obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff hσ 4 y).1 (by simpa using hy)
      exact d4X_pow_eq_one hσ 4 c
    · obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff hσ 5 y).1 (by simpa using hy)
      exact d4X_pow_eq_one hσ 5 c

theorem longSub_le_of_forall_mem {K : Type} [Field K] [Finite K] {ℓ : ℕ} [CharP K ℓ]
    {σ : K ≃+* K} (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (t : Kˣ) (ht : (t : K) * σ t * σ (σ t) = 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hH : ∀ y : twistedGroup σ.toRingHom, y ^ ℓ = 1 →
      y * slShort σ.toRingHom hσ3 (HSL t) =
        slShort σ.toRingHom hσ3 (HSL t) * y → y ∈ H) :
    longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H := by
  intro x hx
  rw [longSub] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, hk2, hyk⟩ := hy
    have hyL : y ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) :=
      Subgroup.subset_closure ⟨k, hk, hk2, hyk⟩
    have hcomm : y * slShort σ.toRingHom hσ3 (HSL t) =
        slShort σ.toRingHom hσ3 (HSL t) * y :=
      Subgroup.mem_centralizer_singleton_iff.1
        (longSub_le_centralizer_slShort_HSL hσ3 t ht hyL)
    exact hH y (pow_eq_one_of_mem_root hσ3 k hk y hyk) hcomm
  | one => exact H.one_mem
  | mul a b _ _ ha hb => exact H.mul_mem ha hb
  | inv a _ ha => exact H.inv_mem ha

theorem conj_eq_or_eq_inv_of_mem_normalizer {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (s : (fixedField σ.toRingHom)ˣ) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (t : Kˣ) (ht : t = Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s)
    (n : twistedGroup σ.toRingHom)
    (hn : n ∈ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom))) :
    n * slShort σ.toRingHom hσ3 (HSL t) * n⁻¹ =
        slShort σ.toRingHom hσ3 (HSL t) ∨
      n * slShort σ.toRingHom hσ3 (HSL t) * n⁻¹ =
        (slShort σ.toRingHom hσ3 (HSL t))⁻¹ := by
  classical
  set v := slShort σ.toRingHom hσ3 (HSL t) with hv
  have htK : (t : K) = ((s : fixedField σ.toRingHom) : K) := by rw [ht]; rfl
  have htσ : σ.toRingHom (t : K) = t := by
    rw [htK]
    exact (s : fixedField σ.toRingHom).2
  have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, hs3, map_one]
  have hnorm : (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1 := by
    rw [htσ, htσ]
    have := congrArg Units.val ht3
    simpa [pow_succ, mul_assoc] using this
  have hvL : v ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) := by
    rw [hv, ht]
    exact slShort_HSL_fixed_mem_longSub hσ3 s
  have hv1 : v ≠ 1 := by
    rw [hv]
    intro h
    have h1 : HSL t = 1 :=
      slShort_injective hσ3 (h.trans (map_one (slShort σ.toRingHom hσ3)).symm)
    have h2 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => (M 0 0 : K)) h1
    have ht1 : (t : K) = 1 := by simpa [HSL] using h2
    have hs1' : s = 1 := by
      apply Units.ext
      apply Subtype.ext
      rw [← htK]
      simpa using ht1
    exact hs1 hs1'
  have hvc : ∀ l ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)), v * l = l * v := by
    intro l hl
    have := longSub_le_centralizer_slShort_HSL hσ3 t hnorm hl
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  have hv3 : v ^ 3 = 1 := by
    rw [hv, ← map_pow, CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_pow, ht3,
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_one', map_one]
  rw [Subgroup.mem_normalizer_iff] at hn
  have hzL : n * v * n⁻¹ ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) := (hn v).1 hvL
  have hzc : ∀ l ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)),
      (n * v * n⁻¹) * l = l * (n * v * n⁻¹) := by
    intro l hl
    have hl' : n⁻¹ * l * n ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) :=
      (hn (n⁻¹ * l * n)).2 (by rwa [show n * (n⁻¹ * l * n) * n⁻¹ = l by group])
    have hcomm := hvc _ hl'
    calc (n * v * n⁻¹) * l = n * (v * (n⁻¹ * l * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * l * n) * v) * n⁻¹ := by rw [hcomm]
      _ = l * (n * v * n⁻¹) := by group
  have hz := mem_zpowers_of_central_longSub hσ3 hvL hvc hv1 hzL hzc
  have hz1 : n * v * n⁻¹ ≠ 1 := by
    intro h1
    apply hv1
    calc v = n⁻¹ * (n * v * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  exact CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
    (orderOf_eq_prime hv3 hv1) hz hz1

theorem not_mem_normalizer_of_not_commute {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (s : (fixedField σ.toRingHom)ˣ) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (t : Kˣ) (ht : t = Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s)
    {ℓ m : ℕ} (hℓ : Odd ℓ) (u : twistedGroup σ.toRingHom)
    (hu : u ^ (ℓ ^ m) = 1)
    (hnc : u * slShort σ.toRingHom hσ3 (HSL t) ≠
      slShort σ.toRingHom hσ3 (HSL t) * u) :
    u ∉ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)) := by
  intro huN
  have hℓm : Odd (ℓ ^ m) := Odd.pow hℓ
  have hodd : Odd (orderOf u) := hℓm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hu)
  rcases conj_eq_or_eq_inv_of_mem_normalizer σ hσ3 s hs3 hs1 t ht u huN with h | h
  · apply hnc
    calc u * slShort σ.toRingHom hσ3 (HSL t) =
        (u * slShort σ.toRingHom hσ3 (HSL t) * u⁻¹) * u := by group
      _ = slShort σ.toRingHom hσ3 (HSL t) * u := by rw [h]
  · have h2 : u ^ 2 * slShort σ.toRingHom hσ3 (HSL t) * (u ^ 2)⁻¹ =
        slShort σ.toRingHom hσ3 (HSL t) := by
      simp only [pow_two, mul_inv_rev]
      calc u * u * slShort σ.toRingHom hσ3 (HSL t) * (u⁻¹ * u⁻¹) =
          u * (u * slShort σ.toRingHom hσ3 (HSL t) * u⁻¹) * u⁻¹ := by group
        _ = u * (slShort σ.toRingHom hσ3 (HSL t))⁻¹ * u⁻¹ := by rw [h]
        _ = (u * slShort σ.toRingHom hσ3 (HSL t) * u⁻¹)⁻¹ := by group
        _ = slShort σ.toRingHom hσ3 (HSL t) := by rw [h]; group
    have hmem : u ∈ Subgroup.zpowers (u ^ 2) :=
      mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr hodd)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hc : Commute (u ^ 2) (slShort σ.toRingHom hσ3 (HSL t)) := by
      show u ^ 2 * slShort σ.toRingHom hσ3 (HSL t) =
        slShort σ.toRingHom hσ3 (HSL t) * u ^ 2
      calc u ^ 2 * slShort σ.toRingHom hσ3 (HSL t) =
          (u ^ 2 * slShort σ.toRingHom hσ3 (HSL t) * (u ^ 2)⁻¹) * u ^ 2 := by group
        _ = slShort σ.toRingHom hσ3 (HSL t) * u ^ 2 := by rw [h2]
    have hcomm : u * slShort σ.toRingHom hσ3 (HSL t) =
        slShort σ.toRingHom hσ3 (HSL t) * u := by
      rw [← hk]
      exact (hc.zpow_left k).eq
    exact hnc hcomm

theorem exists_conj_short_mem {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hL : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (u : twistedGroup σ.toRingHom) (hu : u ∈ H)
    (huN : u ∉ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)))
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1) :
    ∃ n ∈ Subgroup.normalizer
        (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)),
      longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H.map (MulAut.conj n).toMonoidHom ∧
        (d4X hσ3 2 (1 : K) ∈ H.map (MulAut.conj n).toMonoidHom ∨
          d4X hσ3 4 (1 : K) ∈ H.map (MulAut.conj n).toMonoidHom) := by
  obtain ⟨m, hm, hs⟩ := shortUpToNL_of_not_normalizes hσ3 ha H hL hu huN
  obtain ⟨t, htW, hx⟩ := exists_torus_conj_short_one hσ3 hs
  have htN : t ∈ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)) :=
    hHat_le_normalizer_longSub hσ3 htW
  have hLmap : (longSub 6 (hexGroup (twistedX σ.toRingHom))).map
      (MulAut.conj t).toMonoidHom = longSub 6 (hexGroup (twistedX σ.toRingHom)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 htN
  have hmap : H.map (MulAut.conj (t * m)).toMonoidHom =
      (H.map (MulAut.conj m).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  have hLm : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤
      H.map (MulAut.conj m).toMonoidHom := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.1 hm]
    exact Subgroup.map_mono hL
  refine ⟨t * m, (Subgroup.normalizer _).mul_mem htN hm, ?_, ?_⟩
  · rw [hmap, ← hLmap]
    exact Subgroup.map_mono hLm
  · rw [hmap]
    exact hx

end Core

section QOnly


theorem fixedSub_conj_transfer {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    {m : twistedGroup σ.toRingHom} (hm : m ∈ FixedSub σ) {k k' : ℤ}
    (hc : conjBy m (hexGroup (twistedX σ.toRingHom) k') = hexGroup (twistedX σ.toRingHom) k)
    (hk : hexGroup (twistedX σ.toRingHom) k ≤ FixedSub σ) :
    hexGroup (twistedX σ.toRingHom) k' ≤ FixedSub σ := by
  intro x hx
  have hmem : m⁻¹ * x * m ∈ hexGroup (twistedX σ.toRingHom) k := by
    rw [← hc]
    exact ⟨x, hx, by change m⁻¹ * x * (m⁻¹)⁻¹ = m⁻¹ * x * m; rw [inv_inv]⟩
  have hfix := hk hmem
  have e : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
  rw [e]
  exact (FixedSub σ).mul_mem ((FixedSub σ).mul_mem hm hfix) ((FixedSub σ).inv_mem hm)

theorem root_six_le_fixedSub {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) :
    hexGroup (twistedX σ.toRingHom) 6 ≤ FixedSub σ := by
  intro x hx
  have hxr : x ∈ rankOne (twistedRootGroup σ.toRingHom) (ng 0) := by
    rw [rankOne]
    exact Subgroup.mem_sup_left (by rw [← hexPos_six]; exact hx)
  obtain ⟨A, hA⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.rankOne_long_le_range_slLong σ.toRingHom hσ3 hxr
  rw [← hA]
  exact slLong_mem_FixedSub σ hσ3 A

theorem root_neg_six_le_fixedSub {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) :
    hexGroup (twistedX σ.toRingHom) (-6) ≤ FixedSub σ := by
  intro x hx
  have hxr : x ∈ rankOne (twistedRootGroup σ.toRingHom) (ng 0) := by
    rw [rankOne]
    exact Subgroup.mem_sup_right (by rw [← hexPos_neg_six]; exact hx)
  obtain ⟨A, hA⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.rankOne_long_le_range_slLong σ.toRingHom hσ3 hxr
  rw [← hA]
  exact slLong_mem_FixedSub σ hσ3 A

end QOnly

section Fixed


theorem longSub_le_fixedSub {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) :
    longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ FixedSub σ := by
  have R := d4RGD2 σ.toRingHom hσ3
  have hr1 : nHat σ.toRingHom (1 : Fin 2) ∈ FixedSub σ := by
    rw [show (1 : Fin 2) = ng 1 from rfl]
    exact nHat_one_mem_FixedSub σ hσ3
  have hr2 : nHat σ.toRingHom (0 : Fin 2) ∈ FixedSub σ := by
    rw [show (0 : Fin 2) = ng 0 from rfl]
    exact nHat_zero_mem_FixedSub σ hσ3
  have hr1' : (nHat σ.toRingHom (1 : Fin 2))⁻¹ ∈ FixedSub σ := (FixedSub σ).inv_mem hr1
  have hr2' : (nHat σ.toRingHom (0 : Fin 2))⁻¹ ∈ FixedSub σ := (FixedSub σ).inv_mem hr2
  have h6 := root_six_le_fixedSub σ hσ3
  have hm6 := root_neg_six_le_fixedSub σ hσ3
  have h2 : hexGroup (twistedX σ.toRingHom) 2 ≤ FixedSub σ := by
    refine fixedSub_conj_transfer σ hσ3 hr1' ?_ h6
    have h := (R.act₁.2.2 2 (by norm_num) (by norm_num)).1
    simpa using h
  have h4 : hexGroup (twistedX σ.toRingHom) 4 ≤ FixedSub σ := by
    refine fixedSub_conj_transfer σ hσ3 hr2' ?_ h2
    have h := (R.act₂.2.2 4 (by norm_num) (by norm_num)).1
    simpa using h
  have hcneg2 : conjBy (nHat σ.toRingHom (1 : Fin 2))
      (hexGroup (twistedX σ.toRingHom) (-2)) = hexGroup (twistedX σ.toRingHom) (-6) := by
    have h := (R.act₁.2.2 6 (by norm_num) (by norm_num)).2
    have h' : conjBy (nHat σ.toRingHom (1 : Fin 2))⁻¹
        (hexGroup (twistedX σ.toRingHom) (-6)) = hexGroup (twistedX σ.toRingHom) (-2) := by
      simpa using h
    have hh := congrArg (conjBy (nHat σ.toRingHom (1 : Fin 2))) h'
    rw [← conjBy_mul, inv_mul_cancel, conjBy_one] at hh
    exact hh.symm
  have hm2 : hexGroup (twistedX σ.toRingHom) (-2) ≤ FixedSub σ :=
    fixedSub_conj_transfer σ hσ3 hr1 hcneg2 hm6
  have hm4 : hexGroup (twistedX σ.toRingHom) (-4) ≤ FixedSub σ := by
    refine fixedSub_conj_transfer σ hσ3 hr2' ?_ hm2
    have h := (R.act₂.2.2 4 (by norm_num) (by norm_num)).2
    simpa using h
  rw [longSub]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨k, hk, hk2, hx⟩
  have hk0 := hk.1
  have hk6 := hk.2
  have hcases : k = 2 ∨ k = 4 ∨ k = 6 ∨ k = -2 ∨ k = -4 ∨ k = -6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h2 hx, h4 hx, h6 hx, hm2 hx, hm4 hx, hm6 hx]

theorem map_longSub_eq_of_fix {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) (t : Kˣ)
    (ht : (t : K) * σ t * σ (σ t) = 1) (ht2 : (t : K) ^ 2 ≠ 1)
    (β : MulAut (twistedGroup σ.toRingHom))
    (hβ : β (slShort σ.toRingHom hσ3 (HSL t)) = slShort σ.toRingHom hσ3 (HSL t)) :
    (longSub 6 (hexGroup (twistedX σ.toRingHom))).map β.toMonoidHom =
      longSub 6 (hexGroup (twistedX σ.toRingHom)) := by
  classical
  set L := longSub 6 (hexGroup (twistedX σ.toRingHom)) with hL
  set v := slShort σ.toRingHom hσ3 (HSL t) with hv
  have hβv : β v = v := hβ
  have hcen : Subgroup.center (twistedGroup σ.toRingHom) = ⊥ :=
    center_twistedGroup_eq_bot σ hK2 hq hK hσq
  have hperf : ⁅L.map β.toMonoidHom, L.map β.toMonoidHom⁆ = L.map β.toMonoidHom := by
    rw [← Subgroup.map_commutator, longSub_commutator_eq σ.toRingHom hσ3]
  have hPz : L.map β.toMonoidHom ≤ Subgroup.centralizer {v} := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hc := congrArg β (Subgroup.mem_centralizer_singleton_iff.1
      (longSub_le_centralizer_slShort_HSL hσ3 t ht hy))
    rw [map_mul, map_mul, ← hv, hβv] at hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc
  have hPL : L.map β.toMonoidHom ≤ L :=
    perfect_le_longSub_of_le_centralizer hσ3 hcen t ht ht2 hperf hPz
  have hcard : Nat.card ↥(L.map β.toMonoidHom) = Nat.card ↥L :=
    Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective
  exact Subgroup.eq_of_le_of_card_ge hPL (by rw [hcard])

end Fixed

section QPlus


theorem eq_top_of_fixedSub_le_of_slShort_mem {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (hK2 : ringChar K ≠ 2) (h3 : Module.finrank (fixedField σ.toRingHom) K = 3)
    (hF5 : 5 ≤ Nat.card (fixedField σ.toRingHom))
    (N : Subgroup (twistedGroup σ.toRingHom)) (hFN : FixedSub σ ≤ N)
    (j : Matrix.SpecialLinearGroup (Fin 2) K)
    (hj : j ∉ CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.sl2Range
      (fixedField σ.toRingHom) K)
    (hsl : slShort σ.toRingHom hσ3 j ∈ N) : N = ⊤ := by
  classical
  set F := fixedField σ.toRingHom with hF
  have hbase : CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.sl2Range F K ≤
      N.comap (slShort σ.toRingHom hσ3) := by
    rintro M ⟨M', rfl⟩
    show slShort σ.toRingHom hσ3
      (Matrix.SpecialLinearGroup.map (algebraMap F K) M') ∈ N
    apply hFN
    have hfix : Matrix.SpecialLinearGroup.map σ.toRingHom
        (Matrix.SpecialLinearGroup.map (algebraMap F K) M') =
        Matrix.SpecialLinearGroup.map (algebraMap F K) M' := by
      refine Subtype.ext ?_
      ext i j
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply]
      exact (M' i j).2
    exact slShort_mem_FixedSub σ hσ3 _ hfix
  have hjmem : j ∈ N.comap (slShort σ.toRingHom hσ3) := hsl
  have htop := CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.sl2_range_maximal
    h3 hK2 hF5 (N.comap (slShort σ.toRingHom hσ3)) hbase hjmem hj
  have hrange : (slShort σ.toRingHom hσ3).range ≤ N := by
    rintro x ⟨A, rfl⟩
    have : A ∈ N.comap (slShort σ.toRingHom hσ3) := htop ▸ Subgroup.mem_top A
    exact this
  rw [eq_top_iff, ← triOdd_fixedSub_sup_slShort σ hσ3]
  exact sup_le hFN hrange

theorem tauAut_eqRoot_eq_iff {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) (w : twistedGroup σ.toRingHom) :
    tauAut σ (triOddEqRoot σ hK2 hq hK hσq w) =
      triOddEqRoot σ hK2 hq hK hσq w ↔ w ∈ FixedSub σ := by
  classical
  set ε := triOddEqRoot σ hK2 hq hK hσq with hε
  have hfix := triOdd_fixedSubgroup_tau_eq_map σ hσ3 hK2 hq hK hσq
  have hmem : (tauAut σ (ε w) = ε w) ↔ ε w ∈ fixedSubgroup (tauAut σ) := Iff.rfl
  rw [hmem, hfix, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzw⟩
    rwa [ε.injective hzw] at hz
  · intro hw
    exact ⟨w, hw, rfl⟩

end QPlus

theorem exists_conj_not_mem_sl2Range {K : Type} [Field K] (σ : K ≃+* K)
    (h3 : Module.finrank (fixedField σ.toRingHom) K = 3)
    (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (hg : Matrix.SpecialLinearGroup.map σ.toRingHom g ≠ g) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom),
      g * Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) M * g⁻¹ ∉
        CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.sl2Range
          (fixedField σ.toRingHom) K := by
  classical
  by_contra h
  push Not at h
  have hnorm : ∀ x : Matrix (Fin 2) (Fin 2) (fixedField σ.toRingHom), x.det = 1 →
      ∃ y : Matrix (Fin 2) (Fin 2) (fixedField σ.toRingHom), y.det = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) K) * x.map (algebraMap (fixedField σ.toRingHom) K) =
          y.map (algebraMap (fixedField σ.toRingHom) K) *
            (g : Matrix (Fin 2) (Fin 2) K) := by
    intro x hx
    set M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom) := ⟨x, hx⟩ with hM
    obtain ⟨y, hy⟩ := h M
    refine ⟨y.1, y.2, ?_⟩
    have hcoe : (Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) y :
        Matrix (Fin 2) (Fin 2) K) =
        (g * Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) M * g⁻¹ :
          Matrix.SpecialLinearGroup (Fin 2) K) :=
      congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) K =>
        (z : Matrix (Fin 2) (Fin 2) K)) hy
    have hginv : (g : Matrix (Fin 2) (Fin 2) K).adjugate =
        (g : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
      rw [Matrix.inv_def, g.2]
      simp
    have h1 : (g : Matrix (Fin 2) (Fin 2) K) * x.map (algebraMap (fixedField σ.toRingHom) K) *
        (g : Matrix (Fin 2) (Fin 2) K)⁻¹ =
        y.1.map (algebraMap (fixedField σ.toRingHom) K) := by
      have hcoe' := hcoe.symm
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        hginv, hM, Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply] at hcoe'
      exact hcoe'
    have h2SL : g * Matrix.SpecialLinearGroup.map
        (algebraMap (fixedField σ.toRingHom) K) M =
        Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) y * g :=
      mul_inv_eq_iff_eq_mul.mp hy.symm
    have h2 : (g : Matrix (Fin 2) (Fin 2) K) * x.map (algebraMap (fixedField σ.toRingHom) K) =
        y.1.map (algebraMap (fixedField σ.toRingHom) K) * (g : Matrix (Fin 2) (Fin 2) K) := by
      have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) K =>
        (z : Matrix (Fin 2) (Fin 2) K)) h2SL
      ext i j
      have hij := congrFun (congrFun h i) j
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hij
      rw [Matrix.SpecialLinearGroup.map_apply_coe,
        Matrix.SpecialLinearGroup.map_apply_coe] at hij
      simp only [RingHom.mapMatrix_apply] at hij
      simpa [Matrix.map_apply, Matrix.mul_apply, hM] using hij
    exact h2
  obtain ⟨y, hy, hgy⟩ := CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.mem_SL2_of_normalizes_SL2
    h3 (g : Matrix (Fin 2) (Fin 2) K) g.2 hnorm
  apply hg
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, hgy]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (y i j).2

section Full


theorem tauAut_eqRoot_slShort {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    tauAut σ (triOddEqRoot σ hK2 hq hK hσq
      (slShort σ.toRingHom hσ3 M)) =
      triOddEqRoot σ hK2 hq hK hσq
        (slShort σ.toRingHom hσ3 (Matrix.SpecialLinearGroup.map σ.toRingHom M)) := by
  apply Subtype.ext
  rw [coe_tauAut]
  rw [triOddEqRoot_coe]
  rw [triOddEqRoot_coe]
  exact CFSG.ClassicalInvolution.Disconnected.AschTight.S19F.slShort_entrywise
    (σ := σ.toRingHom) hσ3 σ (fun c => rfl) M

end Full

end CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools
