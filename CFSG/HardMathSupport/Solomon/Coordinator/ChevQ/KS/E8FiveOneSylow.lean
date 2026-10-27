module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveFourGrp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveSylowWeyl
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExcFiveOrders
public import CFSG.RankThree.PartOne.KE8F.Stab5Fix
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess (card_closure_pair)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Monomial

variable (K : Type) [Field K] [Finite K]

theorem torusGroup_eq_range : torusGroup Tag.E8 K = (rootDiagUnitHom Tag.E8 K).range := by
  refine le_antisymm ?_ ?_
  · rintro h hh
    obtain ⟨a, ha⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup hh
    exact ⟨a, ha⟩
  · rintro _ ⟨a, rfl⟩
    exact SeitzExcOpenRest4Griess.rootDiagUnit_mem_torus_E8 a

theorem card_torusGroup : Nat.card (torusGroup Tag.E8 K) = (Nat.card K - 1) ^ 8 := by
  rw [torusGroup_eq_range]
  have hinj : Function.Injective (rootDiagUnitHom Tag.E8 K) := rootDiagUnit_injective
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_fun, Nat.card_units]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem weylQuotientHom_surjective : Function.Surjective (weylQuotientHom Tag.E8 K) := fun w =>
  ⟨⟨canonicalRep (coxeterSystem Tag.E8) K w, canonicalRep_mem_monomialSubgroup K w⟩,
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)⟩

theorem card_monomialSubgroup :
    Nat.card (monomialSubgroup Tag.E8 K) = (Nat.card K - 1) ^ 8 * 696729600 := by
  have hker : (weylQuotientHom Tag.E8 K).ker =
      (torusGroup Tag.E8 K).subgroupOf (monomialSubgroup Tag.E8 K) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact Four.weylQuotientHom_eq_one_iff x.2
  have h1 := Subgroup.card_mul_index (weylQuotientHom Tag.E8 K).ker
  rw [Subgroup.index_ker, hker] at h1
  have h2 : Nat.card ((torusGroup Tag.E8 K).subgroupOf (monomialSubgroup Tag.E8 K)) =
      Nat.card (torusGroup Tag.E8 K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe torusGroup_le_monomialSubgroup).toEquiv
  have h3 : Nat.card (weylQuotientHom Tag.E8 K).range = 696729600 := by
    rw [MonoidHom.range_eq_top_of_surjective _ (weylQuotientHom_surjective K), Subgroup.card_top]
    haveI : Fintype (WeylGroup Tag.E8) := Fintype.ofFinite _
    exact (CFSG.RankThree.Chevalley.E8_weyl_length_polynomial).2
  rw [h2, h3, card_torusGroup K] at h1
  exact h1.symm

@[expose] def monomialN : Subgroup (adjointGroup Tag.E8 K) :=
  (monomialSubgroup Tag.E8 K).subgroupOf (adjointGroup Tag.E8 K)

theorem card_monomialN : Nat.card (monomialN K) = (Nat.card K - 1) ^ 8 * 696729600 := by
  rw [monomialN,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe monomialSubgroup_le_adjointGroup').toEquiv]
  exact card_monomialSubgroup K

theorem factorization_card_monomialN (h5 : 5 ∣ Nat.card K - 1) :
    (Nat.card (monomialN K)).factorization 5 =
      (Nat.card (adjointGroup Tag.E8 K)).factorization 5 := by
  rw [CFSG.HardMathSupport.Timmesfeld.Proving.factorization_five_card_adjointGroup_E8 K h5,
    card_monomialN, Nat.factorization_mul (pow_ne_zero _ (by
      have := Finite.one_lt_card (α := K)
      omega)) (by norm_num), Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    CFSG.RankThree.PartOne.KE8F.factorization_five]
  simp

theorem exists_conj_into_monomialN (h5 : 5 ∣ Nat.card K - 1) {Q : Subgroup (adjointGroup Tag.E8 K)}
    (hQ : IsPGroup 5 Q) : ∃ c : adjointGroup Tag.E8 K, ∀ x ∈ Q, c * x * c⁻¹ ∈ monomialN K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact Four.exists_conj_le_of_factorization_eq
    5 (monomialN K) (factorization_card_monomialN K h5) hQ

end Monomial

section SylowW

@[expose] def sylowW : Subgroup (WeylGroup Tag.E8) :=
  Subgroup.closure ({e8FiveG1, e8FiveG2} : Set (WeylGroup Tag.E8))

theorem pow_pair_mul {G : Type*} [Group G] {a b : G} (hc : Commute a b) (i j k l : ℕ) :
    a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
  have h1 : b ^ j * a ^ k = a ^ k * b ^ j := ((hc.pow_pow k j).eq).symm
  calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
        simp only [mul_assoc]
    _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [h1]
    _ = (a ^ i * a ^ k) * (b ^ j * b ^ l) := by simp only [mul_assoc]
    _ = a ^ (i + k) * b ^ (j + l) := by rw [pow_add, pow_add]

theorem e8Five_exp_eq {i j i' j' : ℕ}
    (h : e8FiveG1 ^ i * e8FiveG2 ^ j = e8FiveG1 ^ i' * e8FiveG2 ^ j') :
    i % 5 = i' % 5 ∧ j % 5 = j' % 5 := by
  have hc : Commute e8FiveG1 e8FiveG2 := e8Five_comm
  have h1 : e8FiveG1 ^ (i + 4 * i') * e8FiveG2 ^ (j + 4 * j') = 1 := by
    have e1 := pow_pair_mul hc i j (4 * i') (4 * j')
    have e2 := pow_pair_mul hc i' j' (4 * i') (4 * j')
    rw [← e1, h, e2, show i' + 4 * i' = 5 * i' by ring, show j' + 4 * j' = 5 * j' by ring,
      pow_mul, pow_mul, e8FiveG1_pow, e8FiveG2_pow]
    simp
  obtain ⟨d1, d2⟩ := e8Five_ind _ _ h1
  omega

theorem e8Five_exp_injective :
    Function.Injective fun v : Fin 5 × Fin 5 => e8FiveG1 ^ (v.1 : ℕ) * e8FiveG2 ^ (v.2 : ℕ) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h' : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) =
      e8FiveG1 ^ (i' : ℕ) * e8FiveG2 ^ (j' : ℕ) := h
  obtain ⟨hi, hj⟩ := e8Five_exp_eq h'
  have hi' : (i : ℕ) = i' := by omega
  have hj' : (j : ℕ) = j' := by omega
  exact Prod.ext (Fin.ext hi') (Fin.ext hj')

theorem card_sylowW : Nat.card sylowW = 25 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact card_closure_pair (p := 5) e8Five_comm e8FiveG1_pow e8FiveG2_pow e8Five_exp_injective

theorem exists_conj_le_sylowW {R : Subgroup (WeylGroup Tag.E8)} (hR : IsPGroup 5 R) :
    ∃ x : WeylGroup Tag.E8, ∀ r ∈ R, x * r * x⁻¹ ∈ sylowW := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fintype (WeylGroup Tag.E8) := Fintype.ofFinite _
  refine Four.exists_conj_le_of_factorization_eq 5 sylowW ?_ hR
  rw [card_sylowW, (CFSG.RankThree.Chevalley.E8_weyl_length_polynomial).2,
    CFSG.RankThree.PartOne.KE8F.factorization_five, show (25 : ℕ) = 5 ^ 2 by norm_num,
    Nat.Prime.factorization_pow Nat.prime_five]
  simp

end SylowW

section Combined

variable (K : Type) [Field K] [Finite K]

@[expose] def rhoN : monomialN K →* WeylGroup Tag.E8 :=
  (weylQuotientHom Tag.E8 K).comp
    (Subgroup.subgroupOfEquivOfLe
      (monomialSubgroup_le_adjointGroup' (τ := Tag.E8) (K := K))).toMonoidHom

theorem rhoN_apply (x : monomialN K) :
    rhoN K x = weylQuotientHom Tag.E8 K ⟨((x : adjointGroup Tag.E8 K) : ModGL Tag.E8 K), x.2⟩ :=
  rfl

theorem rhoN_surjective : Function.Surjective (rhoN K) := fun w => by
  obtain ⟨g, hg⟩ := weylQuotientHom_surjective K w
  refine ⟨(Subgroup.subgroupOfEquivOfLe
    (monomialSubgroup_le_adjointGroup' (τ := Tag.E8) (K := K))).symm g, ?_⟩
  exact (rhoN_apply K _).trans hg

theorem exists_conj_monomialN_weyl_le (h5 : 5 ∣ Nat.card K - 1)
    {Q : Subgroup (adjointGroup Tag.E8 K)} (hQ : IsPGroup 5 Q) :
    ∃ c : adjointGroup Tag.E8 K, ∃ h : ∀ x ∈ Q, c * x * c⁻¹ ∈ monomialN K,
      ∀ (x : adjointGroup Tag.E8 K) (hx : x ∈ Q), rhoN K ⟨c * x * c⁻¹, h x hx⟩ ∈ sylowW := by
  obtain ⟨c₁, hc₁⟩ := exists_conj_into_monomialN K h5 hQ
  let ψ₀ : Q →* monomialN K :=
    ((MulAut.conj c₁).toMonoidHom.comp Q.subtype).codRestrict (monomialN K) (fun x => hc₁ x x.2)
  let ψ : Q →* WeylGroup Tag.E8 := (rhoN K).comp ψ₀
  have hR : IsPGroup 5 ψ.range := hQ.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨w, hw⟩ := exists_conj_le_sylowW hR
  obtain ⟨n, hn⟩ := rhoN_surjective K w
  have hψ₀ : ∀ (x : adjointGroup Tag.E8 K) (hx : x ∈ Q),
      ((ψ₀ ⟨x, hx⟩ : monomialN K) : adjointGroup Tag.E8 K) = c₁ * x * c₁⁻¹ := fun x hx => rfl
  have hmem : ∀ x ∈ Q, (n : adjointGroup Tag.E8 K) * c₁ * x * ((n : adjointGroup Tag.E8 K) * c₁)⁻¹ ∈
      monomialN K := fun x hx => by
    have := mul_mem (mul_mem n.2 (hc₁ x hx)) (inv_mem n.2)
    simpa [mul_assoc] using this
  refine ⟨(n : adjointGroup Tag.E8 K) * c₁, hmem, fun x hx => ?_⟩
  have hx' : rhoN K ⟨(n : adjointGroup Tag.E8 K) * c₁ * x * ((n : adjointGroup Tag.E8 K) * c₁)⁻¹,
      hmem x hx⟩ = w * ψ ⟨x, hx⟩ * w⁻¹ := by
    have : (⟨(n : adjointGroup Tag.E8 K) * c₁ * x * ((n : adjointGroup Tag.E8 K) * c₁)⁻¹,
        hmem x hx⟩ : monomialN K) = n * ψ₀ ⟨x, hx⟩ * n⁻¹ := by
      apply Subtype.ext
      simp [hψ₀, mul_assoc]
    rw [this, map_mul, map_mul, map_inv, hn]
    rfl
  rw [hx']
  exact hw _ ⟨⟨x, hx⟩, rfl⟩

end Combined

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
