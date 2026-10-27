module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCTools
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Odd

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_comm_conj_of_bar_three (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K}
    (hc : c ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) :
    ∃ ψ : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ c' : K, ((ψ (QuaternionMatrices.slQuatI h.fixedField) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c' • 1 := by
  have := h.finite
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have hn1 : 1 ≤ finrank K (HypIndex r ε → K) := by
    rw [finrank_hypIndex_fun]
    omega
  have hμ : ∀ v, conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) v) =
        ((Units.mk0 c hc : Kˣ) : K) • v := conjOp_conjOp hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hn1 (hypForm_isSymm h) (hypForm_separatingLeft h) _ (conjOp_bijective hc hAA)
    (hypForm_conjOp hA) (Units.mk0 c hc) hμ
  obtain ⟨-, hfin, -, hsym, halt⟩ := hall b t hb ht
  rw [finrank_hypIndex_fun] at hfin
  have hfix : ∀ w ∈ conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)),
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => h.bar (w a)) =
        ((b : K))⁻¹ • w := fun w hw => by
    have h1 : (b : K) • ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        fun a => h.bar (w a)) = w := mem_conjFixed.mp hw
    rw [← h1, smul_smul, inv_mul_cancel₀ b.ne_zero, one_smul, h1]
  rcases hμ1 with hμ1 | hμ1
  ·
    have hc1 : c = 1 := by
      have := congrArg Units.val hμ1
      simpa using this
    subst hc1
    obtain ⟨B, hBH, hBs, hBnd, -⟩ := hsym hμ1
    have h2k : (2 : h.fixedField) ≠ 0 := fun h0 => two_ne_zero_of_odd h hp (by
      rw [← map_ofNat h.fixedField.subtype 2, h0, map_zero])
    have : Invertible (2 : h.fixedField) := invertibleOfNonzero h2k
    obtain ⟨vb, hvb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B)
      ⟨fun x y => hBs.eq x y⟩
    have hbo : B.iIsOrtho vb := hvb
    have hd0 := hbo.not_isOrtho_basis_self_of_nondegenerate hBnd
    have h3 : 3 ≤ finrank h.fixedField
        (conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) := by
      omega
    refine exists_comm_conj_of_orth_triple h hp hA hAA
      (w := fun i => (vb (Fin.castLE h3 i) : HypIndex r ε → K)) (fun i => hfix _ (vb _).2)
      (fun i => B (vb (Fin.castLE h3 i)) (vb (Fin.castLE h3 i))) (fun i => hd0 _)
      fun i j => ?_
    rw [← hBH]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hvb (fun h0 => hij (Fin.castLE_inj.mp h0))]
      simp [hij]
  ·
    have hc1 : c = -1 := by
      have := congrArg Units.val hμ1
      simpa using this
    subst hc1
    obtain ⟨B, hBH, hBalt, hBnd, -, -⟩ := halt hμ1
    have : FiniteDimensional h.fixedField
        (conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) :=
      Module.Finite.of_finite
    obtain ⟨w₁, hw₁⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := h.fixedField)).mp
      (by omega : 0 < finrank h.fixedField
        (conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))))
    obtain ⟨w₂, hw₂⟩ : ∃ w₂, B w₁ w₂ ≠ 0 := by
      by_contra! h0
      exact hw₁ (hBnd.1 w₁ h0)
    have ht0 : (t : K) ≠ 0 := t.ne_zero
    obtain ⟨g, hg⟩ : ∃ g, hypForm h r ε (w₁ : HypIndex r ε → K) w₂ = g := ⟨_, rfl⟩
    have hg0 : g ≠ 0 := fun h0 => hw₂ (Subtype.ext (by rw [hBH, hg, h0, mul_zero]; rfl))
    have h11 : hypForm h r ε (w₁ : HypIndex r ε → K) w₁ = 0 := by
      have h1 := hBH w₁ w₁
      rw [hBalt w₁] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (inv_ne_zero ht0)
    have h22 : hypForm h r ε (w₂ : HypIndex r ε → K) w₂ = 0 := by
      have h1 := hBH w₂ w₂
      rw [hBalt w₂] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (inv_ne_zero ht0)
    have h21 : hypForm h r ε (w₂ : HypIndex r ε → K) w₁ = -g := by
      have h1 := congrArg (fun x : h.fixedField => (x : K)) (hBalt.neg_eq w₁ w₂)
      simp only [Subfield.coe_neg, hBH, hg] at h1
      have h2 : (t : K)⁻¹ * (hypForm h r ε (w₂ : HypIndex r ε → K) w₁ + g) = 0 := by
        linear_combination -h1
      linear_combination (mul_eq_zero.mp h2).resolve_left (inv_ne_zero ht0)
    have hgbar : h.bar g = -g := by
      have h1 := (hypForm_isSymm h).eq (w₁ : HypIndex r ε → K) w₂
      rwa [hg, h21] at h1
    exact exists_comm_conj_of_alt_pair h hA hAA (hfix _ w₁.2) (hfix _ w₂.2) hg0 hgbar h11 h22
      hg h21

theorem exists_fixed_even_sl2_three (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (α : MulAut (hypPSU h r ε)) (hα : α ^ 2 = 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), ringChar k ≠ 2 ∧
      ∃ ρ : SpecialLinearGroup (Fin 2) k →* hypPSU h r ε, Even (Nat.card ρ.range) ∧
        ∀ s ∈ ρ.range, α s = s := by
  have := h.finite
  have hk2 : ringChar h.fixedField ≠ 2 := ringChar_fixedField_ne_two h hp
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := h.charP
    rwa [ringChar.eq K p]
  by_cases hα1 : α = 1
  · subst hα1
    obtain ⟨ψ, -, hψs⟩ := exists_comm_planeHom_of_norm_eq_one h hp (by omega)
      (one_mem (hypUnitary h r ε)) one_ne_zero (by simp) (by simp [UnitaryFieldData.norm])
    exact ⟨h.fixedField, inferInstance, inferInstance, hk2, (hypProj h r ε).comp ψ,
      even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
      fun s _ => rfl⟩
  have hα2 : orderOf α = 2 := orderOf_eq_prime hα hα1
  obtain ⟨A, σ, hx, hA, hαeq, hσ, hrefl, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp hr hε (by omega)).2.2.2 α hα2
  subst hαeq
  rcases hσ with rfl | hσ
  ·
    have hord := hrefl rfl
    have hsq : (QuotientGroup.mk (⟨A, hA⟩ * ⟨A, hA⟩) : hypUnitaryMod h r ε) = 1 := by
      rw [QuotientGroup.mk_mul, ← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
    obtain ⟨d, hd, -, hAA⟩ := mem_normOneScalars.mp ((QuotientGroup.eq_one_iff _).mp hsq)
    obtain ⟨l, hl0, hld⟩ := exists_sq_eq_of_norm_eq_one h hp hd
    have hAA' : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1 := by
      have h1 := congrArg (fun g : GL (HypIndex r ε) K =>
        (g : Matrix (HypIndex r ε) (HypIndex r ε) K)) hAA
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
      rw [h1, hld, scalar_apply, smul_one_eq_diagonal]
    have hN : h.norm l = 1 ∨ h.norm l = -1 := by
      have h1 : h.norm l * h.norm l = 1 := by
        rw [← norm_mul_eq h, ← pow_two, hld, hd]
      exact mul_self_eq_one_iff.mp h1
    rcases hN with hN | hN
    · obtain ⟨ψ, hψ, hψs⟩ := exists_comm_planeHom_of_norm_eq_one h hp (by omega) hA hl0 hAA' hN
      exact ⟨h.fixedField, inferInstance, inferInstance, hk2, (hypProj h r ε).comp ψ,
        even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
        fixed_of_comm h hr hε hx ψ hψ⟩
    · rcases Nat.lt_or_ge (2 * r + ε) 4 with h3 | h4
      ·
        have hM := mulVecLin_mul_self hAA'
        rw [← coe_unitaryOfHyp h hA] at hM
        obtain ⟨-, -, -, h2dim, -⟩ := exists_paired_centralizer_equiv hp (hypForm_isSymm h)
          (hypForm_separatingLeft h) hl0 hM hN
        rw [finrank_hypIndex_fun] at h2dim
        omega
      obtain ⟨ψ, hψ, hψs⟩ := exists_comm_pairHom_of_norm_eq_neg_one h hp h4 hA hl0 hAA' hN
      exact ⟨K, inferInstance, inferInstance, hK2, (hypProj h r ε).comp ψ,
        even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
        fixed_of_comm h hr hε hx ψ hψ⟩
  ·
    obtain ⟨c, hc, hAA⟩ := hbar hσ
    obtain ⟨ψ, hψ, hψs⟩ := exists_comm_conj_of_bar_three h hp hn hA hc hAA
    exact ⟨h.fixedField, inferInstance, inferInstance, hk2, (hypProj h r ε).comp ψ,
      even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
      fixed_of_comm_bar h hr hε hσ hx ψ hψ⟩


theorem not_isPGroup_hypPSU (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) [Finite (hypPSU h r ε)] (α : MulAut (hypPSU h r ε))
    (hα : orderOf α = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  have hα2 := pow_orderOf_eq_one α
  rw [hα] at hα2
  obtain ⟨k, _, _, hk, ρ, heven, hfix⟩ := exists_fixed_even_sl2_three h hp hr hε hn α hα2
  have hpr : (ringChar k).Prime := CharP.char_is_prime k (ringChar k)
  exact not_isPGroup_of_fixed_odd (CatLeafProof.Q81P2.exists_odd_of_hom ρ
    (fun g => hfix _ ⟨g, rfl⟩) LinearGroups.special_linear_elementary_generation
    (fun s hs => GSThmB.Cent516.odd_orderOf_of_mem_elementarySet hpr hk hs)
    (even_iff_two_dvd.mp heven))

theorem oddClsRow_psu : OddClsRow .PSU := by
  intro Y _ _ hY _ _ a ha hP
  obtain ⟨n, p, f, hp2, ⟨hp, hf, hn, -⟩, K, _, _, hcard, ⟨e₀⟩⟩ := hY
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := r) (ε := ε) h
  set e : Y ≃* hypPSU h r ε := e₀.trans (hypPSUEquivStatedProj h hR₀ (by omega)).symm with he
  have : Finite (hypPSU h r ε) := Finite.of_equiv _ e.toEquiv
  exact absurd (L33.isPGroup_fixedPoints_congr e a hP)
    (not_isPGroup_hypPSU h hp2 (by omega) hε hn _ ((L33.orderOf_congr e a).trans ha))

end CFSG.ComponentClassification.HarrisLit.L33.OC
