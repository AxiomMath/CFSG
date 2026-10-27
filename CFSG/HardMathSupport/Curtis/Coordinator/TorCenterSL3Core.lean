module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Aut
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Order
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterAbelian
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Mono

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix CFSG.AGLEmbedding.LinearThreeKit CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K]

theorem pow_c_eq_one [Finite K] {m t₀ : ℕ} (ht : Nat.card K - 1 = 3 ^ m * t₀) (ht0 : ¬ 3 ∣ t₀)
    {x : K} (hx0 : x ≠ 0) {k : ℕ} (hx : x ^ 3 ^ k = 1) : x ^ 3 ^ m = 1 := by
  let u : Kˣ := Units.mk0 x hx0
  have hu : u ^ 3 ^ k = 1 := Units.ext (by simpa [u] using hx)
  have h1 : orderOf u ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ 3 ^ m * t₀ := by
    rw [← ht, ← Nat.card_units]
    exact orderOf_dvd_natCard u
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have hcop : Nat.Coprime (3 ^ j) t₀ :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ht0)
  rw [hord] at h2
  have h3 : 3 ^ j ∣ 3 ^ m := hcop.dvd_of_dvd_mul_right h2
  have : orderOf u ∣ 3 ^ m := by rw [hord]; exact h3
  have h := orderOf_dvd_iff_pow_eq_one.mp this
  simpa [u] using congrArg Units.val h

theorem map_diagSub_eq [Finite K] {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {m t₀ : ℕ}
    (hm : 2 ≤ m) (ht : Nat.card K - 1 = 3 ^ m * t₀) (ht0 : ¬ 3 ∣ t₀)
    {s : SpecialLinearGroup (Fin 3) K} {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b)
    (hb0 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = b 0)
    (hb1 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = ω • b 1)
    (hb2 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = ω ^ 2 • b 2)
    {R : Subgroup (SpecialLinearGroup (Fin 3) K)} (hR : IsPGroup 3 R)
    (hTR : diagSub b (3 ^ m) (pow_pos (by norm_num) m) ≤ R)
    {β : MulAut (SpecialLinearGroup (Fin 3) K)} (hβR : R.map β.toMonoidHom = R) :
    (diagSub b (3 ^ m) (pow_pos (by norm_num) m)).map β.toMonoidHom =
      diagSub b (3 ^ m) (pow_pos (by norm_num) m) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set hc : 0 < 3 ^ m := pow_pos (by norm_num) m with hcdef
  set T := diagSub b (3 ^ m) hc with hT
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd (K := K) (d := 3 ^ m)
    (by rw [ht]; exact Dvd.intro _ rfl)
  have hTcard : (3 ^ m) ^ 2 ≤ Nat.card T := card_diagSub_ge hb hζ
  have hRcard : Nat.card R ≤ 3 ^ (2 * m + 1) :=
    card_le_of_isPGroup_sl_three ht ht0 (by omega) hR
  have hTcR : Nat.card (T.subgroupOf R) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv
  have hmul := Subgroup.card_mul_index (T.subgroupOf R)
  rw [hTcR] at hmul
  obtain ⟨j, hj⟩ := hR.exists_card_eq
  have hidxdvd : (T.subgroupOf R).index ∣ 3 ^ j := by
    rw [← hj]; exact Subgroup.index_dvd_card _
  obtain ⟨i, hi, hidx⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hidxdvd
  have hidxle : (T.subgroupOf R).index ≤ 3 := by
    have h1 : Nat.card T * (T.subgroupOf R).index ≤ 3 ^ (2 * m + 1) := by
      rw [hmul]; exact hRcard
    have h2 : 3 * (3 ^ m) ^ 2 = 3 ^ (2 * m + 1) := by ring
    by_contra hgt
    push Not at hgt
    nlinarith
  have hcases : (T.subgroupOf R).index = 1 ∨ (T.subgroupOf R).index = 3 := by
    rw [hidx] at hidxle ⊢
    have hi1 : i ≤ 1 := by
      by_contra h2
      push Not at h2
      have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) h2
      omega
    interval_cases i <;> simp
  rcases hcases with h1 | h3
  ·
    have hTR' : R ≤ T := by
      have : T.subgroupOf R = ⊤ := Subgroup.index_eq_one.mp h1
      intro r hr
      have : (⟨r, hr⟩ : R) ∈ T.subgroupOf R := by rw [this]; exact Subgroup.mem_top _
      exact this
    have : T = R := le_antisymm hTR hTR'
    rw [this]; exact hβR
  · have hjpos : j ≠ 0 := by
      rintro rfl
      have h' : (T.subgroupOf R).index ∣ 3 ^ 0 := hidxdvd
      rw [h3] at h'
      simp at h'
    have hmin : (Nat.card ↥R).minFac = 3 := by
      rw [hj]; exact Nat.Prime.pow_minFac Nat.prime_three hjpos
    have hnorm : (T.subgroupOf R).Normal :=
      Subgroup.normal_of_index_eq_minFac_card (by rw [h3, hmin])
    have hTβR : T.map β.toMonoidHom ≤ R := by rw [← hβR]; exact Subgroup.map_mono hTR
    have hAcard : Nat.card ((T.map β.toMonoidHom).subgroupOf R) = Nat.card T := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTβR).toEquiv,
        Subgroup.card_map_of_injective β.injective]
    have hAidx : ((T.map β.toMonoidHom).subgroupOf R).index = 3 := by
      have h1 := Subgroup.card_mul_index ((T.map β.toMonoidHom).subgroupOf R)
      rw [hAcard] at h1
      have h' := hmul
      rw [h3] at h'
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h'.symm)
    have hAc : ∀ a ∈ (T.map β.toMonoidHom).subgroupOf R, ∀ a' ∈ (T.map β.toMonoidHom).subgroupOf R,
        a * a' = a' * a := by
      intro a ha a' ha'
      obtain ⟨ta, hta, hta'⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha)
      obtain ⟨tb, htb, htb'⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha')
      refine Subtype.ext ?_
      change (a : SpecialLinearGroup (Fin 3) K) * a' = a' * a
      rw [← hta', ← htb']
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, diagSub_comm hb hta htb]
    have hsT : s ∈ T := by
      refine ⟨![1, ω, ω ^ 2], ?_, forall_fin_three ?_ ?_ ?_⟩
      · have hcube : ∀ x : K, x ^ 3 = 1 → x ^ 3 ^ m = 1 := fun x hx => by
          obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rw [hm', pow_succ', pow_mul, hx, one_pow]
        refine forall_fin_three ?_ ?_ ?_
        · exact one_pow _
        · exact hcube ω hω3
        · exact hcube (ω ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow])
      · show _ = (1 : K) • b 0
        rw [one_smul]; exact hb0
      · exact hb1
      · exact hb2
    have hsR : s ∈ R := hTR hsT
    have hZ : ∀ r : ↥R, r ∉ T.subgroupOf R → ∀ d ∈ T.subgroupOf R, r * d = d * r →
        d ∈ (scalars 3 K).subgroupOf R := by
      intro r hr d hd hcomm
      have hrT : (r : SpecialLinearGroup (Fin 3) K) ∉ T := fun h =>
        hr (Subgroup.mem_subgroupOf.mpr h)
      have hdT : (d : SpecialLinearGroup (Fin 3) K) ∈ T := Subgroup.mem_subgroupOf.mp hd
      have hrs : (r : SpecialLinearGroup (Fin 3) K) * s * (r : SpecialLinearGroup (Fin 3) K)⁻¹ ∈
          T := by
        have := hnorm.conj_mem ⟨s, hsR⟩ (Subgroup.mem_subgroupOf.mpr hsT) r
        exact Subgroup.mem_subgroupOf.mp this
      obtain ⟨k, hk⟩ := hR r
      have hk' : (r : SpecialLinearGroup (Fin 3) K) ^ 3 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      have hrdiag : ¬ ∃ x : Fin 3 → K, ∀ i,
          ((r : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = x i • b i := by
        rintro ⟨x, hx⟩
        apply hrT
        have hxk : ∀ i, x i ^ 3 ^ k = 1 := fun i => by
          have h1 := pow_mulVec_of_mulVec_eq_smul (hx i) (3 ^ k)
          rw [← Matrix.SpecialLinearGroup.coe_pow, hk', Matrix.SpecialLinearGroup.coe_one,
            Matrix.one_mulVec] at h1
          have h2 := smul_left_injective K (hb.ne_zero i) (show (1 : K) • b i = (x i ^ 3 ^ k) • b i
            by rw [one_smul]; exact h1)
          exact h2.symm
        refine ⟨x, fun i => ?_, hx⟩
        refine pow_c_eq_one ht ht0 (fun h0 => ?_) (hxk i)
        have := hxk i
        rw [h0, zero_pow (pow_pos (by norm_num) k).ne'] at this
        exact zero_ne_one this
      exact mem_scalars_of_commute_monomial hω1 hω3 hb hb0 hb1 hb2 hrs ⟨k, hk'⟩ hrdiag hdT
        (congrArg Subtype.val hcomm)
    have hZcard : Nat.card ((scalars 3 K).subgroupOf R) ≤ 3 := by
      calc Nat.card ((scalars 3 K).subgroupOf R)
          = Nat.card (((scalars 3 K).subgroupOf R).map R.subtype) :=
            (Subgroup.card_map_of_injective R.subtype_injective).symm
        _ ≤ Nat.card (scalars 3 K) :=
            Subgroup.card_le_of_le (by rintro _ ⟨z, hz, rfl⟩; exact hz)
        _ ≤ 3 := card_scalars_le_three
    have hcardT : 3 * Nat.card ((scalars 3 K).subgroupOf R) < Nat.card (T.subgroupOf R) := by
      rw [hTcR]
      have h9 : 9 ≤ 3 ^ m := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      nlinarith
    have hAT := eq_of_abelian_index_three (T := T.subgroupOf R)
      (A := (T.map β.toMonoidHom).subgroupOf R) (Z₀ := (scalars 3 K).subgroupOf R) h3 hAidx hAc
      hZ hcardT
    have hinf := Subgroup.subgroupOf_inj.mp hAT
    rw [inf_eq_left.mpr hTβR, inf_eq_left.mpr hTR] at hinf
    exact hinf

theorem pow_three_eq_one_of_regular {ω : K} (hω3 : ω ^ 3 = 1) {s : SpecialLinearGroup (Fin 3) K}
    {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b)
    (hb0 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = b 0)
    (hb1 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = ω • b 1)
    (hb2 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = ω ^ 2 • b 2) : s ^ 3 = 1 := by
  refine Subtype.ext ?_
  show (s : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1
  refine eq_of_mulVec_eq hb (forall_fin_three ?_ ?_ ?_)
  · show ((s : Matrix (Fin 3) (Fin 3) K) ^ 3) *ᵥ b 0 = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0
    have hb0' : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = (1 : K) • b 0 := by
      rw [one_smul]; exact hb0
    rw [pow_mulVec_of_mulVec_eq_smul hb0', one_pow, one_smul, Matrix.one_mulVec]
  · show ((s : Matrix (Fin 3) (Fin 3) K) ^ 3) *ᵥ b 1 = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1
    rw [pow_mulVec_of_mulVec_eq_smul hb1, hω3, one_smul, Matrix.one_mulVec]
  · show ((s : Matrix (Fin 3) (Fin 3) K) ^ 3) *ᵥ b 2 = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2
    rw [pow_mulVec_of_mulVec_eq_smul hb2, ← pow_mul, mul_comm, pow_mul, hω3, one_pow, one_smul,
      Matrix.one_mulVec]

theorem aut_apply_eq_scalar_smul_of_three_group [Finite K] {ω : K} (hω1 : ω ≠ 1)
    (hω3 : ω ^ 3 = 1) {m t₀ : ℕ} (hm : 2 ≤ m) (ht : Nat.card K - 1 = 3 ^ m * t₀)
    (ht0 : ¬ 3 ∣ t₀) {s : SpecialLinearGroup (Fin 3) K} {b : Fin 3 → Fin 3 → K}
    (hb : LinearIndependent K b) (hb0 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = b 0)
    (hb1 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = ω • b 1)
    (hb2 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = ω ^ 2 • b 2) (hs : s ∉ scalars 3 K)
    {R : Subgroup (SpecialLinearGroup (Fin 3) K)} (hR : IsPGroup 3 R)
    (hTR : diagSub b (3 ^ m) (pow_pos (by norm_num) m) ≤ R)
    {β : MulAut (SpecialLinearGroup (Fin 3) K)} {k : ℕ} (hβ : β ^ 3 ^ k = 1)
    (hβR : R.map β.toMonoidHom = R) :
    ∃ c : K, c ^ 3 = 1 ∧ ((β s : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (s : Matrix (Fin 3) (Fin 3) K) := by
  have hTβ := map_diagSub_eq hω1 hω3 hm ht ht0 hb hb0 hb1 hb2 hR hTR hβR
  have hsT : s ∈ diagSub b (3 ^ m) (pow_pos (by norm_num) m) := by
    refine ⟨![1, ω, ω ^ 2], ?_, forall_fin_three ?_ ?_ ?_⟩
    · have hcube : ∀ x : K, x ^ 3 = 1 → x ^ 3 ^ m = 1 := fun x hx => by
        obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [hm', pow_succ', pow_mul, hx, one_pow]
      refine forall_fin_three ?_ ?_ ?_
      · exact one_pow _
      · exact hcube ω hω3
      · exact hcube (ω ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow])
    · show _ = (1 : K) • b 0
      rw [one_smul]; exact hb0
    · exact hb1
    · exact hb2
  have hβsT : β s ∈ diagSub b (3 ^ m) (pow_pos (by norm_num) m) := by
    rw [← hTβ]; exact ⟨s, hsT, rfl⟩
  obtain ⟨y, -, hy⟩ := hβsT
  have hss := pow_three_eq_one_of_regular hω3 hb hb0 hb1 hb2
  have hy3 : ∀ i, y i ^ 3 = 1 := fun i => by
    have h1 : (β s) ^ 3 = 1 := by rw [← map_pow, hss, map_one]
    have h2 := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) h1
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec] at h2
    rw [pow_mulVec_of_mulVec_eq_smul (hy i) 3] at h2
    exact (smul_left_injective K (hb.ne_zero i) (h2.trans (one_smul K _).symm))
  exact aut_apply_eq_scalar_smul hω1 hω3 hb hb0 hb1 hb2 hs hβ hy3 hy

end CFSG.HardMathSupport.Curtis.Coordinator
