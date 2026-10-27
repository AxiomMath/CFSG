module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldE67Odd
public import CFSG.RankThree.PartOne.S11c.Sec66Exc

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem three_dvd_ordE6 {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ ordE6 q := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h => hq (h ▸ dvd_zero 3)
  have h2 : 3 ∣ q ^ 2 - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow,
      Nat.cast_one, sub_eq_zero]
    have h0 : ((q : ℕ) : ZMod 3) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q 3).1 h)
    generalize ((q : ℕ) : ZMod 3) = z at h0 ⊢
    revert z
    decide
  have h6 : 3 ∣ q ^ 6 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 3
    rw [one_pow, ← pow_mul] at h
    exact h2.trans h
  have hnum : 9 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1) := by
    have h9 : (9 : ℕ) = 3 * 3 := by norm_num
    rw [h9]
    exact Nat.mul_dvd_mul (Dvd.dvd.mul_right (Dvd.dvd.mul_left h6 _) _) h2
  have hg : Nat.gcd 3 (q - 1) = 1 ∨ Nat.gcd 3 (q - 1) = 3 :=
    (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three) _ (Nat.gcd_dvd_left 3 (q - 1))
  unfold ordE6
  obtain ⟨m, hm⟩ := hnum
  rw [hm]
  rcases hg with h | h
  · rw [h, Nat.div_one]
    exact Dvd.intro (3 * m) (by ring)
  · rw [h, show 9 * m = 3 * (3 * m) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.intro m rfl

@[expose] noncomputable def e6Inndiag
    (K : Type) [Field K] : Subgroup (MulAut (adjointGroup Tag.E6 K)) :=
  innerAut (adjointGroup Tag.E6 K) ⊔ (rootDiagAutHom Tag.E6 K).range

theorem innerAut_le_e6Inndiag
    (K : Type) [Field K] : innerAut (adjointGroup Tag.E6 K) ≤ e6Inndiag K :=
  le_sup_left

section Descent


theorem exists_conj_entrywise_of_not_mem_e6Inndiag {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) {x : MulAut (adjointGroup Tag.E6 K)} (hxp : x ^ p = 1)
    (hxo : x ∉ e6Inndiag K) :
    ∃ σ : K ≃+* K, orderOf σ = p ∧ p ∣ f ∧ ∃ ψ : MulAut (adjointGroup Tag.E6 K),
      ψ * x * ψ⁻¹ = entrywiseAdjointAut Tag.E6 σ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨d, T, r, j, ψ, hd, -, -, -, hTj, hxβ, hψ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag .E6 (Or.inl rfl)
      hf K hK hp hp2 x hxp fun g a hxdiag => hxo (by
        rw [hxdiag]
        exact mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨a, rfl⟩))
  refine ⟨T ^ j, hTj, ⟨d, hd⟩, ψ, ?_⟩
  rw [← hxβ, ← conj_pow, hψ, ← entrywiseAdjointAut_pow]

theorem not_coprime_three_card_adjointE6_fixSubfield {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) :
    ¬ Nat.Coprime 3 (Nat.card (adjointGroup Tag.E6 (fixSubfield σ))) := by
  have : Finite (fixSubfield σ) := Subtype.finite
  rw [← Nat.Prime.dvd_iff_not_coprime Nat.prime_three,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
  refine three_dvd_ordE6 fun h3 => ?_
  rw [(SteinbergBT.card_fixSubfield hℓ hf hK σ).2] at h3
  exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h3)).symm

end Descent

section Core


theorem fieldCoreAt_E6_of_not_mem_e6Inndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {x : MulAut (adjointGroup Tag.E6 K)}
    (hx3 : x ^ 3 = 1) (hxo : x ∉ e6Inndiag K) : FieldCoreAt 3 x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hdvd : ∀ σ : K ≃+* K, ¬ Nat.Coprime 3 (Nat.card (adjointGroup Tag.E6 (fixSubfield σ))) :=
    not_coprime_three_card_adjointE6_fixSubfield hℓ hℓ3 hf hK
  obtain ⟨σ, hσp, hpf, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ hf K hK
    Nat.prime_three (by norm_num) hx3 hxo
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    obtain ⟨f', hff'⟩ := hpf
    have hf'1 : 1 ≤ f' := by
      rcases Nat.eq_zero_or_pos f' with h0 | h0
      · rw [h0, mul_zero] at hff'
        omega
      · exact h0
    obtain ⟨σ₀, hσ₀, hzp⟩ :=
      CFSG.RankThree.PartOne.Sec66T.exists_canonical_generator hf hK hσp (by norm_num) hff'
    have hσ₀ord : orderOf σ₀ = 3 := by
      rw [← Nat.card_zpowers, ← hzp, Nat.card_zpowers, hσp]
    have hK' : Nat.card K = 2 ^ (f' * 3) := by rw [hK, hff', mul_comm]
    obtain ⟨-, -, -, hJC, hsimple, hnc, -, hNδ, hnormal, hcent, -⟩ :=
      even_E6_canonical_field_derived_subgroup_and_pointwise_centralizer hf'1 (by norm_num) K hK'
        σ₀ hσ₀
    have hcore := fieldCoreAt_entrywise_of_data hσ₀ord hJC hsimple hnc hNδ hnormal hcent
      (hdvd σ₀)
    have hz : Subgroup.zpowers (entrywiseAdjointAut Tag.E6 σ) =
        Subgroup.zpowers (entrywiseAdjointAut Tag.E6 σ₀) := by
      have h1 := MonoidHom.map_zpowers (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) σ
      have h2 := MonoidHom.map_zpowers (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) σ₀
      rw [hzp] at h1
      exact h1.symm.trans h2
    exact fieldCoreAt_of_conj (FieldCoreAt.of_zpowers_eq hz.symm hcore) ψ hψ
  · have : CharP (AlgebraicClosure K) ℓ :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
    obtain ⟨-, -, -, -, ρ, -, -, -, -, -, -, -, -, -, -, -, hfixer⟩ :=
      CFSG.RankThree.PartOne.KE.odd_E6_rational_inner_diagonal_graph_field_automorphism_structure
        hℓ hℓ2 hf K hK (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
        (fun c => by rw [iterateFrobenius_def, hK]) _ _ rfl rfl
    obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, hcent⟩ :=
      odd_entrywise_canonical_core_data_of_fixer (τ := .E6) hℓ2 σ (fixer_of_rational σ hfixer)
    exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_of_data hσp hJC hsimple hnc hNδ hnormal hcent
      (hdvd σ)) ψ hψ

end Core

end CFSG.HardMathSupport.Timmesfeld.CrossChar
