module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltPermIm
public import CFSG.LieType.Steinberg.CentralExt.POmegaOddMultiplier

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank

theorem nonempty_mulEquiv_spinOdd {Y : Type} [Group Y] [Finite Y] {n p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hY : IsCoverOf .POmegaOdd n p f 2 Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧ 3 ≤ n ∧ p.Prime ∧ p ≠ 2 ∧
      Nonempty (Y ≃* spinGroup (quadOdd n K)) := by
  obtain ⟨hq, hZ, hm⟩ := hY
  rcases hm with ⟨-, ⟨hp, -, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  have : Finite (spinGroup (quadOdd n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Group.IsPerfect Y := hq.1
  obtain ⟨hβs, -, -⟩ := spinToStatedProj_quadOdd h2 hn
  set β := spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn) with hβ
  set η : Y →* StatedProj (StatedOmega (StatedQuadOdd n K)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : IsPGroup 2 (center Y) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect
    (fun E _ _ π hπ hcen _ =>
      LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_exists_section_of_central h2 hn h5K
        hπ hcen)
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
  exact ⟨K, inferInstance, inferInstance, hK, hn, hp, hp2,
    ⟨(MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm⟩⟩

section Transport

variable {A B : Type} [Group A] [Group B] (e : A ≃* B)

theorem map_centralizer_singleton_mulEquiv (t : A) :
    (centralizer ({t} : Set A)).map e.toMonoidHom = centralizer {e t} := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem mem_center_mulEquiv_iff (x : A) : e x ∈ center B ↔ x ∈ center A := by
  rw [mem_center_iff, mem_center_iff]
  constructor
  · intro h g
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)
  · intro h g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, h g]

theorem map_center_map_mulEquiv (J : Subgroup A) :
    (center ↥(J.map e.toMonoidHom)).map (J.map e.toMonoidHom).subtype =
      ((center ↥J).map J.subtype).map e.toMonoidHom := by
  set eJ := J.equivMapOfInjective e.toMonoidHom e.injective with heJ
  rw [← map_center_eq eJ, map_map, map_map]
  exact congrArg (fun φ : ↥J →* B => (center ↥J).map φ) (MonoidHom.ext fun _ => rfl)

@[expose] def Lemma412Concl (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ z : X, orderOf z = 2 ∧ center X = zpowers z ∧
    ∃ (t : X) (J₁ J₂ : Subgroup X), orderOf t = 2 ∧ t ∉ center X ∧
      IsTwoComponentIn J₁ (centralizer {t}) ∧ IsTwoComponentIn J₂ (centralizer {t}) ∧
      IsSLTwoOver q ↥J₁ ∧ IsSLTwoOver q ↥J₂ ∧
      (center ↥J₁).map J₁.subtype = zpowers t ∧ (center ↥J₂).map J₂.subtype = zpowers (t * z)

theorem isSLTwoOver_map_mulEquiv {q : ℕ} {J : Subgroup A} (h : IsSLTwoOver q ↥J) :
    IsSLTwoOver q ↥(J.map e.toMonoidHom) := by
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨(J.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eF⟩⟩

include e in
theorem Lemma412Concl.map {q : ℕ} (h : Lemma412Concl q A) : Lemma412Concl q B := by
  obtain ⟨z, hz2, hZ, t, J₁, J₂, ht2, htZ, hJ₁, hJ₂, hs₁, hs₂, hc₁, hc₂⟩ := h
  refine ⟨e z, by rw [MulEquiv.orderOf_eq, hz2], ?_, e t, J₁.map e.toMonoidHom,
    J₂.map e.toMonoidHom, by rw [MulEquiv.orderOf_eq, ht2],
    fun h => htZ ((mem_center_mulEquiv_iff e t).mp h), ?_, ?_,
    isSLTwoOver_map_mulEquiv e hs₁, isSLTwoOver_map_mulEquiv e hs₂, ?_, ?_⟩
  · rw [← map_center_eq e, hZ]
    exact MonoidHom.map_zpowers _ z
  · rw [← map_centralizer_singleton_mulEquiv e t]
    exact L35.isTwoComponentIn_map_of_injective _ e.injective hJ₁
  · rw [← map_centralizer_singleton_mulEquiv e t]
    exact L35.isTwoComponentIn_map_of_injective _ e.injective hJ₂
  · rw [map_center_map_mulEquiv, hc₁, MonoidHom.map_zpowers]
    rfl
  · rw [map_center_map_mulEquiv, hc₂, MonoidHom.map_zpowers, map_mul]
    rfl

end Transport

theorem lemma412_of_isCoverOf {X : Type} [Group X] [Finite X] {n p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hX : IsCoverOf .POmegaOdd n p f 2 X) : Lemma412Concl (p ^ f) X := by
  obtain ⟨K, _, _, hK, hn, hp, hp2, ⟨e⟩⟩ := nonempty_mulEquiv_spinOdd h5 hX
  exact Lemma412Concl.map e.symm (spinOdd_lemma412 hp hp2 hK h5 hn)

end CFSG.ComponentClassification.HarrisLit.T1
