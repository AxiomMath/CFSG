module

public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddProof
public import CFSG.RankThree.PartOne.SEITZ5.UPair

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.Classical CFSG.LieType.Chevalley

namespace OuterSUField

theorem mem_zpowers_of_pow_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G] {p : ℕ}
    (hp : p.Prime) {σ τ : G} (hσ : orderOf σ = p) (hτ : τ ^ p = 1) :
    τ ∈ Subgroup.zpowers σ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set S : Finset G := Finset.univ.filter fun a => a ^ p = 1 with hS
  have hcardS : S.card ≤ p := IsCyclic.card_pow_eq_one_le (α := G) hp.pos
  set Z : Finset G := (Subgroup.zpowers σ : Set G).toFinset with hZ
  have hZS : Z ⊆ S := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (by simpa [hZ] using ha)
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hσ,
      pow_orderOf_eq_one, _root_.one_zpow]
  have hZcard : Z.card = p := by
    have h1 : Nat.card (Subgroup.zpowers σ) = p := by rw [Nat.card_zpowers, hσ]
    rw [hZ, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact h1
  have hZeq : Z = S := Finset.eq_of_subset_of_card_le hZS (by rw [hZcard]; exact hcardS)
  have hτS : τ ∈ S := by simp [hS, hτ]
  rw [← hZeq] at hτS
  simpa [hZ] using hτS

end OuterSUField

theorem planeGen_of_mem_fieldHom {ℓ f p n : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {σ : K ≃+* K} (hσ : orderOf σ = p)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2)
    (hfσ : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ ∈ E) : PlaneGen E := by
  classical
  have hfin : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set ι := primeFormFieldFactor h hC hn3 hne with hι
  set κ := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hκ
  set fσ := primeFormFieldHom h hC σ with hfσdef
  have hισ : ι fσ = σ := by
    have := primeFormFieldFactor_apply h hC hn3 hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hfσ1 : fσ ≠ 1 := fun h1 => hσ1 (by rw [← hισ, h1, map_one])
  have hfσp : fσ ^ p = 1 := by
    rw [hfσdef, ← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  have hfσord : orderOf fσ = p := orderOf_eq_prime hfσp hfσ1
  obtain ⟨x₀, hx₀E, hx₀⟩ : ∃ x₀ ∈ E, x₀ ∉ Subgroup.zpowers fσ := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers fσ := fun x hx => hcon x hx
    have hfin' : Finite (Subgroup.zpowers fσ) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hfσord]; exact hp.ne_zero)
    have h1 := Subgroup.card_le_of_le hle
    rw [hc, Nat.card_zpowers, hfσord] at h1
    nlinarith [hp.two_le]
  have hτp : (ι x₀) ^ p = 1 := by rw [← map_pow, hE.2 x₀ hx₀E, map_one]
  have hKcard : Nat.card K = ℓ ^ (2 * f) := h.card
  have hcyc : IsCyclic (K ≃+* K) :=
    isCyclic_ringEquiv_of_card h.prime (by have := h.one_le; omega) hKcard
  have hfinAut : Finite (K ≃+* K) := Finite.of_injective _ DFunLike.coe_injective
  have hτ : ι x₀ ∈ Subgroup.zpowers σ := OuterSUField.mem_zpowers_of_pow_eq_one hp hσ hτp
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hτ
  set b := x₀ * (fσ ^ j)⁻¹ with hbdef
  have hbE : b ∈ E := E.mul_mem hx₀E (E.inv_mem (zpow_mem hfσ j))
  have hιb : ι b = 1 := by
    rw [hbdef, map_mul, map_inv, map_zpow, hισ, hj, mul_inv_cancel]
  have hb1 : b ≠ 1 := by
    intro h1
    apply hx₀
    rw [mul_inv_eq_one.mp h1]
    exact Subgroup.zpow_mem_zpowers _ _
  have ha'E : b * fσ ∈ E := E.mul_mem hbE hfσ
  have ha'ι : ι (b * fσ) = σ := by rw [map_mul, hιb, one_mul, hισ]
  have ha'1 : b * fσ ≠ 1 := fun h1 => hσ1 (by rw [← ha'ι, h1, map_one])
  have ha'ord : orderOf (b * fσ) = p := orderOf_eq_prime (hE.2 _ ha'E) ha'1
  obtain ⟨-, -, -, -, -, M', hM'⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hpℓ
      (b * fσ) ha'ord σ ha'ι hσ
  have h₀ : UnitaryFieldData ℓ (f / p) (fixSubfield σ) := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hpf : p ∣ f := (dvd_and_card_fixSubfield_unitary h hp hp2 hσ).1
  have hfeq : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  set Q := QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) with hQ
  have hFmk : (subfieldPSU h h₀ hbar n).range = (suSub h h₀ hbar n).map Q :=
    range_subfieldPSU_eq_map h h₀ hbar n
  have hfixF : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, fσ x = x := fun x hx =>
    range_subfieldPSU_le h n h₀ hbar hx
  have hQmem : ∀ g ∈ suSub h h₀ hbar n, Q g ∈ (subfieldPSU h h₀ hbar n).range := fun g hg => by
    rw [hFmk]
    exact ⟨g, hg, rfl⟩
  have hconj : (κ M')⁻¹ * (b * fσ) * κ M' = fσ := hM'
  have hconj' : (b * fσ) * κ M' = κ M' * fσ := by
    calc (b * fσ) * κ M' = κ M' * ((κ M')⁻¹ * (b * fσ) * κ M') := by group
      _ = κ M' * fσ := by rw [hconj]
  have hne' : (suSub h h₀ hbar n).map (primeFormConjSU h _ M').toMonoidHom ≠
      suSub h h₀ hbar n := by
    intro heq
    have hFmap : ((subfieldPSU h h₀ hbar n).range).map (κ M').toMonoidHom =
        (subfieldPSU h h₀ hbar n).range := by
      rw [hFmk, map_primeFormConjHom_map_mk h h₀ hbar n M', heq]
    have hfix' : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, (b * fσ) x = x := by
      intro x hx
      have hx' : x ∈ ((subfieldPSU h h₀ hbar n).range).map (κ M').toMonoidHom := by
        rw [hFmap]
        exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      have h2 := congrArg (fun z : MulAut (primeFormP h (idGram K n)) => z y) hconj'
      simp only [MulAut.mul_apply] at h2
      change (b * fσ) (κ M' y) = κ M' y
      rw [show (b * fσ) (κ M' y) = (b * fσ * κ M') y from rfl, hconj', MulAut.mul_apply,
        hfixF y hy]
    have hβ : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, b x = x := by
      intro x hx
      have h3 : (b * fσ) x = b (fσ x) := rfl
      rw [hfixF x hx] at h3
      rw [← h3]
      exact hfix' x hx
    obtain ⟨τ, -, hτ⟩ := eq_primeFormFieldHom_of_fix h n h₀ hbar hn3 hne hq₀ b hβ
    have hτ1 : τ = 1 := by
      have e1 := primeFormFieldFactor_apply h hC hn3 hne 1 τ
      rw [map_one, one_mul] at e1
      rw [← e1, ← hτ]
      exact hιb
    apply hb1
    rw [hτ, hτ1, map_one]
  have hgen : Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
      ((suSub h h₀ hbar n).map (primeFormConjSU h _ M').toMonoidHom : Set (gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤ := by
    by_cases hq2 : ℓ ^ (f / p) = 2
    · have hn4 : 4 ≤ n := by
        by_contra h4
        exact hq₀ ⟨by omega, hq2⟩
      obtain ⟨hℓ2, hf₀1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq2
      subst hℓ2
      exact CFSG.RankThree.PartOne.SEITZ5.subfieldPairSUF2Odd_of_four_le hn4 f (f / p) K h
        (fixSubfield σ) h₀ hbar p hp hp2 hfeq hf₀1 M' hne'
    · exact subfieldPairSUOdd_of_ne_two ℓ f (f / p) K h (fixSubfield σ) h₀ hbar p hp hp2 hfeq hq2
        n hn3 M' hne'
  have h1 : ∀ g ∈ suSub h h₀ hbar n, Q g ∈ planeClosure E := fun g hg =>
    mem_planeClosure_of_fixed hfσ hfσ1 (hfixF _ (hQmem g hg))
  have h2 : ∀ g ∈ (suSub h h₀ hbar n).map (primeFormConjSU h _ M').toMonoidHom,
      Q g ∈ planeClosure E := by
    rintro _ ⟨g, hg, rfl⟩
    have hQg : Q ((primeFormConjSU h _ M').toMonoidHom g) = κ M' (Q g) :=
      (primeFormConjHom_mk h _ M' g).symm
    refine mem_planeClosure_of_fixed ha'E ha'1 ?_
    rw [hQg]
    have h3 := congrArg (fun z : MulAut (primeFormP h (idGram K n)) => z (Q g)) hconj'
    simp only [MulAut.mul_apply] at h3
    show b (fσ (κ M' (Q g))) = κ M' (Q g)
    rw [h3, hfixF _ (hQmem g hg)]
  have hcomap : (planeClosure E).comap Q = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (hg | hg)
    · exact h1 g hg
    · exact h2 g hg
  unfold PlaneGen
  rw [eq_top_iff]
  intro z _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have : g ∈ (planeClosure E).comap Q := by
    rw [hcomap]
    exact Subgroup.mem_top g
  exact this

theorem planeGen_outer_su_field {ℓ f p n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hout : ¬ E ≤ primeFormD h (idGram K n))
    (hexc : n = 3 → ℓ ^ (f / p) = 2 → p ∣ f → PlaneGen E) : PlaneGen E := by
  classical
  have hfin : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨a, haE, haD⟩ : ∃ a ∈ E, a ∉ primeFormD h (idGram K n) := by
    by_contra hcon
    push Not at hcon
    exact hout fun a ha => hcon a ha
  have haι : primeFormFieldFactor h hC hn3 hne a ≠ 1 := fun h1 => haD (by
    rw [← ker_primeFormFieldFactor h hC hn3 hne]
    exact h1)
  have ha1 : a ≠ 1 := fun h1 => haι (by rw [h1, map_one])
  have hap : a ^ p = 1 := hE.2 a haE
  have haord : orderOf a = p := orderOf_eq_prime hap ha1
  have hσp : (primeFormFieldFactor h hC hn3 hne a) ^ p = 1 := by rw [← map_pow, hap, map_one]
  have hσord : orderOf (primeFormFieldFactor h hC hn3 hne a) = p := orderOf_eq_prime hσp haι
  have hpf : p ∣ f := (dvd_and_card_fixSubfield_unitary h hp hp2 hσord).1
  by_cases hq₀ : n = 3 ∧ ℓ ^ (f / p) = 2
  · exact hexc hq₀.1 hq₀.2 hpf
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hpℓ a
      haord _ rfl hσord
  have hmem : primeFormFieldHom h hC (primeFormFieldFactor h hC hn3 hne a) ∈
      E.map (MulAut.congr (primeFormConjHom h _ M)⁻¹).toMonoidHom := by
    refine ⟨a, haE, ?_⟩
    change (primeFormConjHom h _ M)⁻¹ * a * ((primeFormConjHom h _ M)⁻¹)⁻¹ = _
    rw [inv_inv]
    exact hM
  exact planeGen_of_outer_model (primeFormConjHom h _ M)⁻¹
    (planeGen_of_mem_fieldHom h hn3 hne hq₀ hp hp2 hpℓ hσord
      (isElemAbelian_map_congr _ hE) ((card_map_congr _ E).trans hc) hmem)

end CFSG.LieType.SeitzGeneration
