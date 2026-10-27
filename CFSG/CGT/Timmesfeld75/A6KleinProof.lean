module

public import CFSG.CGT.Timmesfeld75.Sec66A6

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem exists_fixed_of_pow_five {K : Type} [Group K] [Finite K] {V : Subgroup K} {σ : K}
    (hσ : σ ^ 5 = 1) (hN : σ ∈ Subgroup.normalizer (V : Set K)) (hV : Nat.card V % 5 ≠ 1) :
    ∃ v ∈ V, v ≠ 1 ∧ σ * v = v * σ := by
  have hmem : ∀ v : V, σ * (v : K) * σ⁻¹ ∈ V := fun v =>
    (Subgroup.mem_normalizer_iff.1 hN v).1 v.2
  let f : Function.End V := fun v => ⟨σ * (v : K) * σ⁻¹, hmem v⟩
  have hpow : ∀ (n : ℕ) (v : V), (((f ^ n) v : V) : K) = σ ^ n * (v : K) * (σ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro v; simp; rfl
    | succ n ih =>
      intro v
      rw [pow_succ]
      have h1 : (((f ^ n * f) v : V) : K) = (((f ^ n) (f v) : V) : K) := rfl
      rw [h1, ih (f v)]
      show σ ^ n * (σ * (v : K) * σ⁻¹) * (σ ^ n)⁻¹ = σ ^ (n + 1) * (v : K) * (σ ^ (n + 1))⁻¹
      rw [pow_succ', mul_inv_rev]
      group
  have hf : f ^ 5 ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    show (((f ^ 5 ^ 1) v : V) : K) = (v : K)
    rw [pow_one, hpow, hσ]
    simp
  have _ := Fintype.ofFinite V
  have _ := Classical.decEq V
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  have h1 : (1 : V) ∈ Function.fixedPoints f := by
    show f 1 = 1
    apply Subtype.ext
    show σ * ((1 : V) : K) * σ⁻¹ = ((1 : V) : K)
    simp
  by_contra hno
  push Not at hno
  have hone : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, h1⟩, fun ⟨v, hv⟩ => ?_⟩
    apply Subtype.ext
    by_contra hne
    have hv1 : (v : K) ≠ 1 := fun h => hne (Subtype.ext h)
    refine hv1 ?_
    by_contra hv1'
    refine hno v v.2 hv1' ?_
    have hv' : f v = v := hv
    have := congrArg Subtype.val hv'
    show σ * (v : K) = (v : K) * σ
    have h2 : σ * (v : K) * σ⁻¹ = (v : K) := this
    calc σ * (v : K) = σ * (v : K) * σ⁻¹ * σ := by group
      _ = (v : K) * σ := by rw [h2]
  rw [hone] at hmod
  apply hV
  rw [Nat.card_eq_fintype_card]
  unfold Nat.ModEq at hmod
  omega

theorem six_le_index_of_simple {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : Nat.card K = 360) {H : Subgroup K} (hH : H ≠ ⊤) : 6 ≤ H.index := by
  have hfaith : Function.Injective (MulAction.toPermHom K (K ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (MulAction.toPermHom K (K ⧸ H)).ker with h | h
    · exact h
    · exfalso
      apply hH
      rw [eq_top_iff]
      intro g _
      have h1 : MulAction.toPermHom K (K ⧸ H) g = 1 :=
        MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g)
      have h2 : g • ((1 : K) : K ⧸ H) = ((1 : K) : K ⧸ H) := by
        have := congrArg (fun π : Equiv.Perm (K ⧸ H) => π ((1 : K) : K ⧸ H)) h1
        simpa using this
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at h2
      have h3 : g⁻¹ ∈ H := by simpa using h2
      simpa using H.inv_mem h3
  have h1 := Nat.card_le_card_of_injective _ hfaith
  rw [Nat.card_perm, ← Subgroup.index_eq_card, hK] at h1
  by_contra hlt
  push Not at hlt
  have h5 : Nat.factorial H.index ≤ Nat.factorial 5 := Nat.factorial_le (by omega)
  have h6 : Nat.factorial 5 = 120 := by decide
  omega

theorem a6KleinFacts : A6KleinFacts := by
  intro K _ ⟨e⟩ V hV h2
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup K := MulEquiv.isSimpleGroup e
  have hK : Nat.card K = 360 := by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
  have hV8 := card_le_eight_of_elemAbelian e hV
  have hVbot : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h2
    omega
  have hVtop : V ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hK] at hV8
    omega
  have hHtop : Subgroup.normalizer (V : Set K) ≠ ⊤ := by
    intro h
    have : V.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with h' | h'
    · exact hVbot h'
    · exact hVtop h'
  have h6 := six_le_index_of_simple hK hHtop
  have hNH := Subgroup.card_mul_index (Subgroup.normalizer (V : Set K))
  rw [hK] at hNH
  by_contra hlt
  push Not at hlt
  have hidx : (Subgroup.normalizer (V : Set K)).index = 6 := by
    have h7 : (Subgroup.normalizer (V : Set K)).index ≠ 7 := by
      intro h7
      rw [h7] at hNH
      omega
    omega
  rw [hidx] at hNH
  have h60 : Nat.card ↥(Subgroup.normalizer (V : Set K)) = 60 := by omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨σ', hσ'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer (V : Set K))) 5
    (by rw [h60]; norm_num)
  have hσ : orderOf (σ' : K) = 5 := by rw [Subgroup.orderOf_coe, hσ']
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_two_of_isElemAbelian hV)
  have hmod : Nat.card V % 5 ≠ 1 := by
    rw [hn] at h2 hV8 ⊢
    have h3 : n < 4 := by
      by_contra h4
      push Not at h4
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h4
      omega
    interval_cases n <;> omega
  obtain ⟨v, hvV, hv1, hcomm⟩ := exists_fixed_of_pow_five (V := V) (σ := (σ' : K))
    (by rw [← hσ]; exact pow_orderOf_eq_one _) σ'.2 hmod
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by simpa using hV.2 v hvV) hv1
  have h10 : orderOf ((σ' : K) * v) = 10 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm (by rw [hσ, hv2]; norm_num), hσ, hv2]
  exact A6_no_order_ten e _ h10

theorem sec66_of_inputs (h215 : Lemma215Stmt) (h26 : Lemma26Input) (h62 : Sec62) (h63 : Sec63) :
    Sec66 :=
  sec66_of_facts h215 h26 a6KleinFacts h62 h63

end CFSG.CGT.Timmesfeld75
