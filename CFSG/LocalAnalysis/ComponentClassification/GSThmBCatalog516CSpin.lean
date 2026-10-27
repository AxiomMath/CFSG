module

public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCenter
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

section Center

variable {K : Type} [Field K] [Finite K] {b c : K}

theorem finite_spinMinus (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Finite (spinGroup (quadMinus 4 K b c)) :=
  LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (n := 4) hirr)

theorem gcd_four_pow_four_add_one {q : ℕ} (hq : q % 2 = 1) : Nat.gcd 4 (q ^ 4 + 1) = 2 := by
  have h4 : q ^ 4 % 4 = 1 := by
    rw [Nat.pow_mod]
    rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h | h <;> rw [h]
  rw [Nat.gcd_rec, show (q ^ 4 + 1) % 4 = 2 by omega]
  rfl

theorem card_center_spinMinus (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) :
    Nat.card (center (spinGroup (quadMinus 4 K b c))) = 2 := by
  obtain ⟨-, h1, h2⟩ := spinToStatedProj_quadMinus (n := 4) (le_refl 4) hirr
  have hc := (LieType.Steinberg.CentralExt.SpinMinusClosed.card_scalarSpinM hirr (n := 4)
    (le_refl 4) hK).1
  have hodd : (p ^ e) % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  rw [← h2, h1]
  exact hc.trans (gcd_four_pow_four_add_one hodd)

end Center

theorem exists_equiv_spinMinus {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hZ : Nat.card (center Y) = 2) {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e)
    (φ : Y ⧸ center Y ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) :
    ∃ ψ : Y ≃* spinGroup (quadMinus 4 K b c), ∀ y : Y,
      φ (QuotientGroup.mk y) = spinToStatedProj (quadMinus 4 K b c)
        (range_spinMatrix_quadMinus (le_refl 4) hirr) (ψ y) := by
  have := finite_spinMinus hirr
  have hk : ringChar K ≠ 2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hK
  obtain ⟨hβs, -, hβZ⟩ := spinToStatedProj_quadMinus (n := 4) (le_refl 4) hirr
  set β := spinToStatedProj (quadMinus 4 K b c) (range_spinMatrix_quadMinus (le_refl 4) hirr)
    with hβ
  set η : Y →* StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : IsPGroup 2 (center Y) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* spinGroup (quadMinus 4 K b c)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ σ : spinGroup (quadMinus 4 K b c) →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker h2
    obtain ⟨σ, hσ, -⟩ :=
      LieType.Steinberg.spinMinus_central_two_extension_splitting (le_refl 4) hk hirr hπ hker h2
    exact ⟨σ, hσ⟩
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβs hηs
    (hηker ▸ le_rfl) (hηker ▸ hZ2)
  have hβcard : Nat.card β.ker = 2 := by
    rw [hβZ]
    exact card_center_spinMinus hirr hp hp2 hK
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
  refine ⟨(MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm, fun y => ?_⟩
  have hy : α ((MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm y) = y :=
    MulEquiv.ofBijective_apply_symm_apply α ⟨hinj, hαs⟩
  have h3 := hα ((MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm y)
  rw [hy] at h3
  exact h3

section Pair

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def pairElt (u v : V) (h : Q u * Q v = 1) : spinGroup Q :=
  ⟨ι Q u * ι Q v, ι_mul_ι_mem_spinGroup Q h⟩

theorem coe_pairElt (u v : V) (h : Q u * Q v = 1) :
    (pairElt u v h : CliffordAlgebra Q) = ι Q u * ι Q v := rfl

theorem spinAction_pairElt {u v : V} (h : Q u * Q v = 1) :
    spinAction Q (pairElt u v h) = reflect Q u * reflect Q v := by
  have hu : Q u ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hv : Q v ≠ 0 := right_ne_zero_of_mul_eq_one h
  refine LinearEquiv.ext fun w => ?_
  rw [spinAction_apply_eq_iff', coe_pairElt]
  have hl : ∀ a ∈ [u, v], Q a ≠ 0 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    exacts [hu, hv]
  have h1 := prod_map_ι_mul_ι hl w
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.length_cons, List.length_nil] at h1
  rw [h1, show (0 + 1 + 1 : ℕ) = 2 by rfl, neg_one_sq, one_smul]

theorem coe_pairElt_mul_self {u v : V} (h : Q u * Q v = 1) (huv : polar Q u v = 0) :
    ((pairElt u v h * pairElt u v h : spinGroup Q) : CliffordAlgebra Q) = -1 := by
  rw [Submonoid.coe_mul, coe_pairElt]
  have hvu : ι Q v * ι Q u = -(ι Q u * ι Q v) := by
    rw [ι_mul_ι_comm v u, polar_comm, huv, map_zero, zero_sub]
  calc ι Q u * ι Q v * (ι Q u * ι Q v) = ι Q u * (ι Q v * ι Q u) * ι Q v := by
        simp only [mul_assoc]
    _ = -((ι Q u * ι Q u) * (ι Q v * ι Q v)) := by
        rw [hvu]
        simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by
        rw [ι_sq_scalar, ι_sq_scalar, ← map_mul, h, map_one]

theorem pairElt_mul_self {u v : V} (h : Q u * Q v = 1) (huv : polar Q u v = 0) (hQ : Q ≠ 0) :
    pairElt u v h * pairElt u v h = spinGroup.negOne Q hQ := by
  apply Subtype.ext
  rw [coe_pairElt_mul_self h huv, spinGroup.coe_negOne]

end Pair

end CFSG.ComponentClassification.GSThmB.Cent516
