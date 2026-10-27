module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Sub

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.DFour
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem d3_exists_involution_pow {M : Type*} [Group M] {x : M} (hx : ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hx1 : x ≠ 1) : ∃ m : ℕ, (x ^ m) ^ 2 = 1 ∧ x ^ m ≠ 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hx = j + 1 := by
    have h0 : Nat.find hx ≠ 0 := by
      intro h
      have := Nat.find_spec hx
      rw [h] at this
      exact hx1 (by simpa using this)
    exact ⟨Nat.find hx - 1, by omega⟩
  refine ⟨2 ^ j, ?_, ?_⟩
  · have := Nat.find_spec hx
    rw [hj, pow_succ, pow_mul] at this
    exact this
  · intro h
    have := Nat.find_min hx (m := j) (by omega)
    exact this h

theorem d3_false_of_involution {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 3 ^ n)
    {E : Subgroup (MulAut (D4Model K))} (hE : IsElemAbelian 3 E) (hEQ : ¬ E ≤ D4Img K)
    (hcard : 3 ^ (4 * n) ≤ Nat.card E) {z : MulAut (D4Model K)}
    (hzE : ∀ e ∈ E, e * z = z * e)
    (hbound : ∀ b ∈ E, b ∉ D4Img K → ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A →
      (∀ a ∈ A, b a = a) → (∀ a ∈ A, z a = a) → Nat.card A ≤ 3 ^ (2 * n)) : False := by
  have hf : 1 ≤ n := one_le_of_card_field hK
  obtain ⟨-, -, hcen⟩ := d4Facts2 Nat.prime_three (by norm_num) hf hK
  have hinj := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_injective_of_center_eq_bot hcen
  obtain ⟨b, hbE, hbQ⟩ := Set.not_subset.mp hEQ
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set A : Subgroup (D4Model K) := E.comap (MulAut.conj : D4Model K →* MulAut (D4Model K)) with hA
  have hAel : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun a b' => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      apply hinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcommE _ a.2 _ b'.2
    · apply hinj
      rw [map_pow, map_one]
      exact hE.2 _ ha
  have hAfix : ∀ a ∈ A, b a = a := fun a ha =>
    fixed_of_commute_conj hcen (hcommE _ hbE _ ha)
  have hAz : ∀ a ∈ A, z a = a := fun a ha =>
    fixed_of_commute_conj hcen (hzE _ ha).symm
  have hAcard : Nat.card A = Nat.card (E ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) := by
    have hmap : A.map (MulAut.conj : D4Model K →* MulAut (D4Model K)) = E ⊓ Inn (D4Model K) := by
      rw [hA, Subgroup.map_comap_eq, inf_comm]
      rfl
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hA2 : Nat.card A ≤ 3 ^ (2 * n) := hbound b hbE hbQ A hAel hAfix hAz
  obtain ⟨h9, h3⟩ := d3_card_le_nine_inner hK E hE
  rw [← hAcard] at h9 h3
  by_cases h3n : 3 ∣ n
  · have hn3 : 3 ≤ n := Nat.le_of_dvd (by omega) h3n
    have h1 : 3 ^ (4 * n) ≤ 3 ^ (2 * n + 2) :=
      hcard.trans (h9.trans (by rw [pow_add]; nlinarith))
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
    omega
  · have h1 : 3 ^ (4 * n) ≤ 3 ^ (2 * n + 1) :=
      hcard.trans ((h3 h3n).trans (by rw [pow_succ]; nlinarith))
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
    omega

theorem d3TwoLocalTriality_of (hI : D3InnerInvolution) (hF : D3FieldInvolution)
    (hP : D3FixedPointFree) : D3TwoLocalTriality := by
  intro K _ _ n hK E hE hEQ hcard T hT hT2 hnorm
  by_cases hC : ∃ x ∈ T, x ≠ 1 ∧ ∀ e ∈ E, e * x = x * e
  · obtain ⟨x, hxT, hx1, hxE⟩ := hC
    obtain ⟨k, hk⟩ := hT2 ⟨x, hxT⟩
    have hx2 : ∃ k : ℕ, x ^ (2 ^ k) = 1 := ⟨k, by simpa using congrArg Subtype.val hk⟩
    obtain ⟨m, hm2, hm1⟩ := d3_exists_involution_pow hx2 hx1
    have hzE : ∀ e ∈ E, e * x ^ m = x ^ m * e := fun e he => (Commute.pow_right (hxE e he) m).eq
    by_cases hzI : x ^ m ∈ Inn (D4Model K)
    · exact d3_false_of_involution hK hE hEQ hcard hzE fun b hb hbQ A hA hAb hAz =>
        hI K n hK b (hE.2 b hb) hbQ (x ^ m) hm2 hm1 hzI (hzE b hb).symm A hA hAb hAz
    · exact d3_false_of_involution hK hE hEQ hcard hzE fun b hb hbQ A hA hAb hAz =>
        hF K n hK b (hE.2 b hb) hbQ (x ^ m) hm2 hzI (hzE b hb).symm A hA hAb hAz
  · push Not at hC
    refine hP K n hK E hE hEQ hcard T hT hT2 hnorm (fun x hx hcx => ?_)
    by_contra h
    obtain ⟨e, he, hne⟩ := hC x hx h
    exact hne (hcx e he)

end CFSG.LocalAnalysis.GLTheoremA
