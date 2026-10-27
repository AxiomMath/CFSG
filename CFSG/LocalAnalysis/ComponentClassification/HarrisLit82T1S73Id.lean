module

public import CFSG.LieType.Steinberg.CentralExt.SpinSevenThree
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem spinSeven_three_exists_section {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {E : Type*} [Group E] {π : E →* spinGroup (quadOdd 3 K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : spinGroup (quadOdd 3 K) →* E, ∀ g, π (σ g) = g := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have h2K : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Group.IsPerfect (spinGroup (quadOdd 3 K)) := isPerfect_spinGroup_quadOdd h2K le_rfl
  obtain ⟨D, hD⟩ : ∃ D : Subgroup E, D = commutator E := ⟨_, rfl⟩
  have hdecomp : ∀ e : E, ∃ d ∈ D, e * d⁻¹ ∈ π.ker := by
    intro e
    have hmem : π e ∈ D.map π := by
      rw [hD, _root_.commutator_def, map_commutator, map_top_of_surjective π hπ,
        ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
      exact mem_top _
    obtain ⟨d, hd, hde⟩ := hmem
    exact ⟨d, hd, by rw [MonoidHom.mem_ker, map_mul, map_inv, hde, mul_inv_cancel]⟩
  have hDperf : ⁅D, D⁆ = D := by
    refine le_antisymm (commutator_le.mpr fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hle : commutator E ≤ ⁅D, D⁆ := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      obtain ⟨d₁, hd₁, h₁⟩ := hdecomp a
      obtain ⟨d₂, hd₂, h₂⟩ := hdecomp b
      have e := LieType.Steinberg.commutatorElement_mul_mul_of_mem_center (hcen h₁) (hcen h₂)
        d₁ d₂
      rw [inv_mul_cancel_right, inv_mul_cancel_right] at e
      rw [e]
      exact commutator_mem_commutator hd₁ hd₂
    rwa [← hD] at hle
  have : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr hDperf
  set πD : D →* spinGroup (quadOdd 3 K) := π.comp D.subtype with hπD
  have hπDs : Function.Surjective πD := by
    intro g
    obtain ⟨e, rfl⟩ := hπ g
    obtain ⟨d, hd, h⟩ := hdecomp e
    refine ⟨⟨d, hd⟩, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h
    exact h.symm
  have hcenD : πD.ker ≤ center D := by
    intro x hx
    have hx' : (x : E) ∈ π.ker := hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hcen hx') (y : E))
  obtain ⟨c, hc3, hle⟩ :=
    LieType.Steinberg.CentralExt.SpinOddClosed.spinSeven_three_ker_le_zpowers hK hπDs hcenD
  have hker : πD.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hle hx)
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
    obtain ⟨n, hn⟩ := h2 ⟨(x : E), hx⟩
    have hn' : x ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have h := congrArg Subtype.val hn
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hx3)
      (orderOf_dvd_of_pow_eq_one hn'))
  have hinj : Function.Injective πD := (MonoidHom.ker_eq_bot_iff πD).mp hker
  set eD := MulEquiv.ofBijective πD ⟨hinj, hπDs⟩ with heD
  refine ⟨D.subtype.comp eD.symm.toMonoidHom, fun g => ?_⟩
  show πD (eD.symm g) = g
  exact eD.apply_symm_apply g

theorem nonempty_mulEquiv_spinSeven_three {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (h3 : p ^ f = 3) (hY : IsCoverOf .POmegaOdd 3 p f 2 Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 3 ∧
      Nonempty (Y ≃* spinGroup (quadOdd 3 K)) := by
  obtain ⟨hq, hZ, hm⟩ := hY
  rcases hm with ⟨-, ⟨hp, -, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hK3 : Nat.card K = 3 := hK.trans h3
  have hodd : Odd (Nat.card K) := by rw [hK3]; decide
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Finite (spinGroup (quadOdd 3 K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Group.IsPerfect Y := hq.1
  obtain ⟨hβs, -, -⟩ := spinToStatedProj_quadOdd h2 hn
  set β := spinToStatedProj (quadOdd 3 K) (range_spinMatrix_quadOdd h2 hn) with hβ
  set η : Y →* StatedProj (StatedOmega (StatedQuadOdd 3 K)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : IsPGroup 2 (center Y) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect
    (fun E _ _ π hπ hcen h2E => spinSeven_three_exists_section hK3 hπ hcen h2E)
    hβs hηs (hηker ▸ le_rfl) (hηker ▸ hZ2)
  have hβcard : Nat.card β.ker = 2 :=
    LieType.Steinberg.CentralExt.SpinOddClosed.card_ker_spinToStatedProj_quadOdd h2 hn
  have hαβ : α.ker ≤ β.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    rw [← hα, hA, map_one]
  have hne : α.ker ≠ β.ker := by
    intro h1
    have hbot : center Y = ⊥ := by
      rw [← hηker, hker, ← h1, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [hbot, Subgroup.card_bot] at hZ
    exact absurd hZ (by norm_num)
  have hdvd : Nat.card α.ker ∣ Nat.card β.ker := Subgroup.card_dvd_of_le hαβ
  have h1 : Nat.card α.ker = 1 := by
    rw [hβcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hαβ (by rw [h, hβcard])) hne
  have hinj : Function.Injective α :=
    (MonoidHom.ker_eq_bot_iff α).1 (Subgroup.eq_bot_of_card_eq _ h1)
  exact ⟨K, inferInstance, inferInstance, hK3,
    ⟨(MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm⟩⟩

end CFSG.ComponentClassification.HarrisLit.T1
