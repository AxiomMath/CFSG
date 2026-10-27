module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Cover

variable {X : Type} [Group X] [Finite X]

@[expose] def toQuotOdd {A N : Subgroup X} (hAN : A ≤ N) : ↥A →* ↥N ⧸ pPrimeCore 2 ↥N :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (Subgroup.inclusion hAN)

omit [Finite X] in
theorem toQuotOdd_apply {A N : Subgroup X} (hAN : A ≤ N) (a : ↥A) :
    toQuotOdd hAN a = QuotientGroup.mk (⟨a.1, hAN a.2⟩ : ↥N) := rfl

omit [Finite X] in
theorem toQuotOdd_surjective {A N : Subgroup X} (hAN : A ≤ N)
    (hsurj : ∀ c ∈ N, ∃ a ∈ A, ∃ o ∈ oddCoreOf N, c = a * o) :
    Function.Surjective (toQuotOdd hAN) := by
  intro q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, o, ho, hc'⟩ := hsurj c c.2
  refine ⟨⟨a, ha⟩, ?_⟩
  obtain ⟨hoN, hoP⟩ := mem_oddCoreOf_iff.1 ho
  have h1 : (⟨a, hAN ha⟩ : ↥N) = c * (⟨o, hoN⟩ : ↥N)⁻¹ := by
    apply Subtype.ext
    simp [hc']
  rw [toQuotOdd_apply]
  show (QuotientGroup.mk (⟨a, hAN ha⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = QuotientGroup.mk c
  rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have : (QuotientGroup.mk (⟨o, hoN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hoP
  rw [this]
  simp

theorem oddCoreOf_eq_inf_of_cover {A N : Subgroup X} (hAN : A ≤ N)
    (hsurj : ∀ c ∈ N, ∃ a ∈ A, ∃ o ∈ oddCoreOf N, c = a * o) :
    oddCoreOf A = A ⊓ oddCoreOf N := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_inf (oddCoreOf_le A) ?_
    rintro x ⟨a, ha, rfl⟩
    have hsurjπ := toQuotOdd_surjective hAN hsurj
    set Q := (pPrimeCore 2 ↥A).map (toQuotOdd hAN) with hQ
    have hQn : Q.Normal := Subgroup.Normal.map inferInstance _ hsurjπ
    have hQc : Nat.Coprime 2 (Nat.card Q) :=
      Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ _) pPrimeCore_coprime_card
    have hQle : Q ≤ pPrimeCore 2 (↥N ⧸ pPrimeCore 2 ↥N) := le_sSup ⟨hQn, hQc⟩
    rw [pPrimeCore_quotient_eq_bot Nat.prime_two] at hQle
    have h1 : toQuotOdd hAN a = 1 := Subgroup.mem_bot.1 (hQle ⟨a, ha, rfl⟩)
    rw [toQuotOdd_apply] at h1
    exact mem_oddCoreOf_iff.2 ⟨hAN a.2, (QuotientGroup.eq_one_iff _).1 h1⟩
  · have hodd : Odd (Nat.card ↥(A ⊓ oddCoreOf N)) :=
      Odd.of_dvd_nat (odd_card_oddCoreOf N) (Subgroup.card_dvd_of_le inf_le_right)
    refine le_oddCoreOf_of_normalized inf_le_left ?_ hodd
    intro a ha
    exact mem_normalizer_inf (Subgroup.le_normalizer ha)
      (le_normalizer_oddCoreOf N (hAN ha))

theorem quotOddCore_equiv_of_cover {A N : Subgroup X} (hAN : A ≤ N)
    (hsurj : ∀ c ∈ N, ∃ a ∈ A, ∃ o ∈ oddCoreOf N, c = a * o) :
    ∃ e : (↥A ⧸ pPrimeCore 2 ↥A) ≃* (↥N ⧸ pPrimeCore 2 ↥N),
      ∀ a : ↥A, e (QuotientGroup.mk a) = toQuotOdd hAN a := by
  have hker : (toQuotOdd hAN).ker = pPrimeCore 2 ↥A := by
    ext a
    rw [MonoidHom.mem_ker, toQuotOdd_apply, QuotientGroup.eq_one_iff]
    have h1 : (a : X) ∈ oddCoreOf A ↔ (a : X) ∈ A ⊓ oddCoreOf N := by
      rw [oddCoreOf_eq_inf_of_cover hAN hsurj]
    constructor
    · intro h
      have h2 : (a : X) ∈ oddCoreOf N := mem_oddCoreOf_iff.2 ⟨hAN a.2, h⟩
      obtain ⟨_, hP⟩ := mem_oddCoreOf_iff.1 (h1.2 ⟨a.2, h2⟩)
      exact hP
    · intro h
      have h2 : (a : X) ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨a.2, h⟩
      have h3 : (a : X) ∈ oddCoreOf N := (h1.1 h2).2
      obtain ⟨_, hP⟩ := mem_oddCoreOf_iff.1 h3
      exact hP
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (toQuotOdd hAN)
      (toQuotOdd_surjective hAN hsurj)), fun a => ?_⟩
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem LPlusIn_eq_oddCore_sup_of_cover {C C₁ : Subgroup X} (hC₁ : C₁ ≤ C)
    (hcov : ∀ c ∈ C, ∃ a ∈ C₁, ∃ o ∈ oddCoreOf C, c = a * o) :
    LPlusIn C = oddCoreOf C ⊔ LPlusIn C₁ := by
  obtain ⟨e, he⟩ := quotOddCore_equiv_of_cover hC₁ hcov
  have hE := EPlus_map e
  have hmemC : ∀ x : X, x ∈ LPlusIn C ↔ ∃ hx : x ∈ C,
      (QuotientGroup.mk (⟨x, hx⟩ : ↥C) : ↥C ⧸ pPrimeCore 2 ↥C) ∈
        EPlus (↥C ⧸ pPrimeCore 2 ↥C) := by
    intro x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, hc⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hmemC₁ : ∀ x : X, x ∈ LPlusIn C₁ ↔ ∃ hx : x ∈ C₁,
      (QuotientGroup.mk (⟨x, hx⟩ : ↥C₁) : ↥C₁ ⧸ pPrimeCore 2 ↥C₁) ∈
        EPlus (↥C₁ ⧸ pPrimeCore 2 ↥C₁) := by
    intro x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, hc⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hcorr : ∀ a : ↥C₁,
      (QuotientGroup.mk (⟨a.1, hC₁ a.2⟩ : ↥C) : ↥C ⧸ pPrimeCore 2 ↥C) ∈
          EPlus (↥C ⧸ pPrimeCore 2 ↥C) ↔
        (QuotientGroup.mk a : ↥C₁ ⧸ pPrimeCore 2 ↥C₁) ∈ EPlus (↥C₁ ⧸ pPrimeCore 2 ↥C₁) := by
    intro a
    have h1 : (QuotientGroup.mk (⟨a.1, hC₁ a.2⟩ : ↥C) : ↥C ⧸ pPrimeCore 2 ↥C) =
        e (QuotientGroup.mk a) := (he a).symm
    rw [h1, ← hE, Subgroup.mem_map_equiv]
    simp
  apply le_antisymm
  · intro x hx
    obtain ⟨hxC, hxE⟩ := (hmemC x).1 hx
    obtain ⟨a, ha, o, ho, hxao⟩ := hcov x hxC
    obtain ⟨hoC, hoP⟩ := mem_oddCoreOf_iff.1 ho
    have h1 : (QuotientGroup.mk (⟨x, hxC⟩ : ↥C) : ↥C ⧸ pPrimeCore 2 ↥C) =
        QuotientGroup.mk (⟨a, hC₁ ha⟩ : ↥C) := by
      have : (⟨x, hxC⟩ : ↥C) = ⟨a, hC₁ ha⟩ * ⟨o, hoC⟩ := Subtype.ext hxao
      rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hoP, mul_one]
    rw [h1] at hxE
    have ha' : a ∈ LPlusIn C₁ := (hmemC₁ a).2 ⟨ha, (hcorr ⟨a, ha⟩).1 hxE⟩
    rw [hxao]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha') (Subgroup.mem_sup_left ho)
  · refine sup_le ?_ ?_
    · intro o ho
      obtain ⟨hoC, hoP⟩ := mem_oddCoreOf_iff.1 ho
      refine (hmemC o).2 ⟨hoC, ?_⟩
      rw [(QuotientGroup.eq_one_iff _).2 hoP]
      exact one_mem _
    · intro a ha
      obtain ⟨ha₁, haE⟩ := (hmemC₁ a).1 ha
      exact (hmemC a).2 ⟨hC₁ ha₁, (hcorr ⟨a, ha₁⟩).2 haE⟩

end Cover

section T2

variable {G : Type} [Group G]

theorem exists_fixed_mem_coset {P : Subgroup G} (hodd : Odd (Nat.card P)) {a : G} {k : ℕ}
    (ha : a ^ (2 ^ k) = 1) (haP : a ∈ Subgroup.normalizer (P : Set G)) {y : G}
    (hy : y⁻¹ * (a * y * a⁻¹) ∈ P) : ∃ p ∈ P, a * (y * p) * a⁻¹ = y * p := by
  classical
  have hfin : Finite P := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hmem : ∀ g : G, y⁻¹ * g ∈ P → y⁻¹ * (a * g * a⁻¹) ∈ P := by
    intro g hg
    have h : y⁻¹ * (a * g * a⁻¹) = (y⁻¹ * (a * y * a⁻¹)) * (a * (y⁻¹ * g) * a⁻¹) := by group
    rw [h]
    exact P.mul_mem hy ((mem_set_normalizer_iff.mp haP _).mp hg)
  let f : P → P := fun p => ⟨y⁻¹ * (a * (y * (p : G)) * a⁻¹), hmem _ (by simp)⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have h := congrArg Subtype.val hpq
    simp only [f, mul_right_inj, mul_left_inj] at h
    exact Subtype.ext h
  let σ : Equiv.Perm P := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hpow : ∀ n : ℕ, ∀ p : P,
      ((σ ^ n) p : G) = y⁻¹ * (a ^ n * (y * (p : G)) * (a ^ n)⁻¹) := by
    intro n
    induction n with
    | zero => intro p; simp
    | succ n ih =>
      intro p
      rw [pow_succ', Equiv.Perm.mul_apply]
      show (f ((σ ^ n) p) : G) = _
      simp only [f, ih]
      group
  have hσ : σ ^ (2 ^ k) = 1 := by
    ext p
    rw [hpow, ha]
    simp
  let _ : Fintype P := Fintype.ofFinite P
  have hcard : ¬ 2 ∣ Fintype.card P := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨p, p.2, ?_⟩
  have h : y⁻¹ * (a * (y * (p : G)) * a⁻¹) = p := congrArg Subtype.val hp
  calc a * (y * (p : G)) * a⁻¹ = y * (y⁻¹ * (a * (y * (p : G)) * a⁻¹)) := by group
    _ = y * p := by rw [h]

theorem exists_mul_mem_centralizer_of_fixes_coset {P : Subgroup G} (hodd : Odd (Nat.card P))
    {a : G} {k : ℕ} (ha : a ^ (2 ^ k) = 1) (haP : a ∈ Subgroup.normalizer (P : Set G)) {y : G}
    (hy : y⁻¹ * (a * y * a⁻¹) ∈ P) :
    ∃ p ∈ P, y * p ∈ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨p, hp, h⟩ := exists_fixed_mem_coset hodd ha haP hy
  refine ⟨p, hp, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have : a * (y * p) = y * p * a := by
    calc a * (y * p) = a * (y * p) * a⁻¹ * a := by group
      _ = y * p * a := by rw [h]
  exact this.symm

end T2

section T3

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_normalized {Y B : Subgroup G} (hB : IsPGroup 2 ↥B)
    (hBY : B ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ Q : Sylow 2 ↥Y, B ≤ Subgroup.normalizer
      ((((Q : Subgroup ↥Y).map Y.subtype : Subgroup G)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction B Y :=
    MulDistribMulAction.compHom Y (Y.normalizerMonoidHom.comp (Subgroup.inclusion hBY))
  have h1 := hB.card_modEq_card_fixedPoints (Sylow 2 Y)
  have h2 := card_sylow_modEq_one 2 Y
  have h3 : Nat.card (MulAction.fixedPoints B (Sylow 2 Y)) ≡ 1 [MOD 2] := h1.symm.trans h2
  have h4 : Nat.card (MulAction.fixedPoints B (Sylow 2 Y)) ≠ 0 := by
    intro h
    rw [h] at h3
    exact absurd h3 (by decide)
  have h5 : (MulAction.fixedPoints B (Sylow 2 Y)).Nonempty := by
    rcases Set.eq_empty_or_nonempty (MulAction.fixedPoints B (Sylow 2 Y)) with h | h
    · rw [h] at h4
      simp at h4
    · exact h
  obtain ⟨Q, hQ⟩ := h5
  refine ⟨Q, ?_⟩
  rw [Subgroup.le_normalizer_iff]
  intro b hb k hk
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk
  have hfix : (⟨b, hb⟩ : B) • Q = Q := hQ ⟨b, hb⟩
  have hmem : (⟨b, hb⟩ : B) • y ∈ ((⟨b, hb⟩ : B) • Q : Sylow 2 Y) :=
    Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : B) (Q : Subgroup Y) hy
  rw [hfix] at hmem
  refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
  rfl

end T3

section T4

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_oddCoreOf {A W : Subgroup G} {s : G}
    (hs : s ∈ normalizer (A : Set G)) (hW : Odd (Nat.card W)) (h : ∀ a ∈ A, ⁅a, s⁆ ∈ W) :
    ∀ a ∈ A, ⁅a, s⁆ ∈ oddCoreOf A := by
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = Subgroup.closure {x | ∃ a ∈ A, x = ⁅a, s⁆} := ⟨_, rfl⟩
  have hgen : ∀ a ∈ A, ⁅a, s⁆ ∈ C := fun a ha => hC ▸ Subgroup.subset_closure ⟨a, ha, rfl⟩
  have hCA : C ≤ A := by
    rw [hC, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    have e : ⁅a, s⁆ = a * (s * a⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hs a⁻¹).mp (A.inv_mem ha))
  have hCW : C ≤ W := by
    rw [hC, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have hodd : Odd (Nat.card C) := hW.of_dvd_nat (Subgroup.card_dvd_of_le hCW)
  have hconj : ∀ b ∈ A, ∀ x ∈ C, b * x * b⁻¹ ∈ C := by
    intro b hb x hx
    rw [hC] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      have e : b * ⁅a, s⁆ * b⁻¹ = ⁅b * a, s⁆ * ⁅b, s⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact C.mul_mem (hgen _ (A.mul_mem hb ha)) (C.inv_mem (hgen _ hb))
    | one => simp
    | mul y z _ _ hy hz =>
      have e : b * (y * z) * b⁻¹ = (b * y * b⁻¹) * (b * z * b⁻¹) := by group
      rw [e]; exact C.mul_mem hy hz
    | inv y _ hy =>
      have e : b * y⁻¹ * b⁻¹ = (b * y * b⁻¹)⁻¹ := by group
      rw [e]; exact C.inv_mem hy
  have hnorm : A ≤ normalizer (C : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj b hb x, fun hx => ?_⟩
    have := hconj b⁻¹ (A.inv_mem hb) _ hx
    simpa [mul_assoc] using this
  have hle : C ≤ oddCoreOf A := le_oddCoreOf_of_normalized hCA hnorm hodd
  exact fun a ha => hle (hgen a ha)

end T4

end CFSG.OddStandard.Solomon75
