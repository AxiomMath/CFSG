module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.GroupTheory CFSG.RankThree.Chevalley.SteinbergBT

theorem det_cartan_G2_natAbs : Tag.G2.cartan.det.natAbs = 1 := by
  decide +kernel

section

theorem card_entrywiseFixedGroup_G2 {M : Type} [Field M] [Finite M] (σ : M ≃+* M)
    {q₀ : ℕ} (hq₀ : Nat.card (fixSubfield σ) = q₀) :
    Nat.card (entrywiseFixedGroup Tag.G2 σ) = lieOrderNumerator .G2 0 q₀ := by
  set Γ := entrywiseFixedGroup Tag.G2 σ with hΓ
  set J := fixedFieldImage Tag.G2 σ with hJ
  set Jg := J.subgroupOf Γ with hJg
  have h1 : Nat.card Jg * Jg.index = Nat.card Γ := Subgroup.card_mul_index Jg
  have h2 : Nat.card Jg = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixedFieldImage_le).toEquiv
  have h3 : Nat.card J = Nat.card (adjointGroup Tag.G2 (fixSubfield σ)) :=
    (Nat.card_congr (fixedFieldImageEquiv (τ := Tag.G2) σ).toEquiv).symm
  have h4 : Nat.card (adjointGroup Tag.G2 (fixSubfield σ)) = CFSG.Open.ordG2 q₀ := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hq₀]
  obtain ⟨hd1, -⟩ := fixedFieldImage_index_dvd_card (τ := Tag.G2) σ
  rw [det_cartan_G2_natAbs] at hd1
  have hidx : Jg.index = 1 := Nat.dvd_one.1 hd1
  rw [← h1, h2, h3, h4, hidx, mul_one]
  rfl

theorem exists_conj_eq_entrywiseAdjointAut_of_form (τ : Tag)
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (α : MulAut (adjointGroup τ K)) (hαp : orderOf α = p)
    (x : adjointGroup τ K) (σ : K ≃+* K) (hσp : orderOf σ = p)
    (hασ : α = MulAut.conj x * entrywiseAdjointAut τ σ) :
    ∃ δ : MulAut (adjointGroup τ K), δ * α * δ⁻¹ = entrywiseAdjointAut τ σ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have hαpow : α ^ p = 1 := by rw [← hαp]; exact pow_orderOf_eq_one α
  obtain ⟨φ, hφ, hφord, hφgen, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hpf : p ∣ f := by
    rw [← hcard, ← hσp]
    exact orderOf_dvd_natCard σ
  set e := f / p with he
  have hep : e * p = f := Nat.div_mul_cancel hpf
  have he1 : 1 ≤ e := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hT : ∀ c, (φ ^ e) c = c ^ (ℓ ^ e) := by
    intro c
    rw [ringEquiv_pow_apply]
    have hit : ∀ n : ℕ, (⇑φ)^[n] c = c ^ (ℓ ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hφ, pow_succ, pow_mul]
    exact hit e
  have hσmem : σ ∈ Subgroup.zpowers φ := by rw [hφgen]; exact Subgroup.mem_top σ
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσmem)
  replace hk : φ ^ k = σ := hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [← hk, orderOf_one] at hσp
    exact hp.one_lt.ne hσp
  have hgcd : Nat.gcd f k = e := by
    have h1 := orderOf_pow' φ hk0
    rw [hk, hσp, hφord] at h1
    rw [he, h1, Nat.div_div_self (Nat.gcd_dvd_left f k) (by omega)]
  have hzp : Subgroup.zpowers σ = Subgroup.zpowers (φ ^ e) := by
    rw [← hk, ← zpow_natCast, ← zpow_natCast φ e, Subgroup.zpowers_eq_zpowers_iff', hφord,
      Int.gcd_natCast_natCast, Int.gcd_natCast_natCast, Nat.gcd_comm, hgcd,
      Nat.gcd_eq_left ⟨p, hep.symm⟩]
  have hTσ : φ ^ e ∈ Subgroup.zpowers σ := by rw [hzp]; exact Subgroup.mem_zpowers _
  have hσT : σ ∈ Subgroup.zpowers (φ ^ e) := by rw [← hzp]; exact Subgroup.mem_zpowers _
  obtain ⟨j', -, hj'⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hTσ)
  replace hj' : σ ^ j' = φ ^ e := hj'
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσT)
  replace hj : (φ ^ e) ^ j = σ := hj
  have hjj : α ^ (j' * j) = α := by
    have h1 : σ ^ (j' * j) = σ ^ 1 := by rw [pow_mul, hj', hj, pow_one]
    rw [pow_eq_pow_iff_modEq, hσp] at h1
    have h2 : α ^ (j' * j) = α ^ 1 := by rw [pow_eq_pow_iff_modEq, hαp]; exact h1
    rwa [pow_one] at h2
  have hβ : α ^ j' = MulAut.conj (((List.range j').map fun i =>
      (entrywiseAdjointAut τ σ ^ i) x).prod) * entrywiseAdjointAut τ (φ ^ e) := by
    rw [hασ, conj_mul_pow, ← entrywiseAdjointAut_pow, hj']
  have hβp : (MulAut.conj (((List.range j').map fun i =>
      (entrywiseAdjointAut τ σ ^ i) x).prod) * entrywiseAdjointAut τ (φ ^ e)) ^ p = 1 := by
    rw [← hβ, ← pow_mul, mul_comm, pow_mul, hαpow, one_pow]
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut τ K hK he1 hp.one_lt.le hep (φ ^ e) hT
    (AlgebraicClosure K) _ hβp
  refine ⟨δ, ?_⟩
  have hαβ : α = (α ^ j') ^ j := by rw [← pow_mul, hjj]
  rw [hαβ, ← conj_pow, hβ, hδ, ← entrywiseAdjointAut_pow, hj]

theorem outerFixedOrder_G2_of_conj {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (α : MulAut (adjointGroup Tag.G2 K))
    (σ : K ≃+* K) (hσp : orderOf σ = p) (δ : MulAut (adjointGroup Tag.G2 K))
    (hδ : δ * α * δ⁻¹ = entrywiseAdjointAut Tag.G2 σ) :
    ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (ℓ ^ f₀) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  obtain ⟨hpf, hcard⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp] at hpf hcard
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [← card_fixedSubgroup_conj δ α, hδ, card_fixedSubgroup_entrywiseAdjointAut,
    card_entrywiseFixedGroup_G2 σ hcard]

end

end CFSG.HardMathSupport.Lang.E6Descent
