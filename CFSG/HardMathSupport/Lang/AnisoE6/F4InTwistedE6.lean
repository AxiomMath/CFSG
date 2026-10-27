module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Construction

variable {F K : Type} [Field F] [Finite F] [Field K] [Finite K] [Algebra F K]

@[expose] noncomputable def f4InTwistedE6 (σ : K ≃+* K)
    (hfix : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    Subgroup ↥(twistedE6RootGroup K σ) :=
  ((phiG σ hfix).comp (e6FixedF4EquivAll F).symm.toMonoidHom).range

theorem f4InTwistedE6_injective (σ : K ≃+* K)
    (hfix : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    Function.Injective ((phiG σ hfix).comp
      (e6FixedF4EquivAll F).symm.toMonoidHom) :=
  (phiG_injective σ hfix).comp (e6FixedF4EquivAll F).symm.injective

@[expose] noncomputable def f4InTwistedE6Equiv (σ : K ≃+* K)
    (hfix : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    adjointGroup Tag.F4 F ≃* f4InTwistedE6 (F := F) σ hfix :=
  MonoidHom.ofInjective (f4InTwistedE6_injective (F := F) σ hfix)

theorem card_f4InTwistedE6 (σ : K ≃+* K)
    (hfix : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    Nat.card (f4InTwistedE6 (F := F) σ hfix) = ordF4 (Nat.card F) := by
  rw [← Nat.card_congr (f4InTwistedE6Equiv (F := F) σ hfix).toEquiv]
  exact card_adjointGroup_F4_eq F

theorem card_twistedE6RootGroup_eq_card (σ : K ≃+* K)
    (hfix : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c)
    (hK : Nat.card K = (Nat.card F) ^ 2)
    (hσ : ∀ c : K, σ c = c ^ Nat.card F) :
    Nat.card (twistedE6RootGroup K σ) = ordTwistedE6 (Nat.card F) := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hFcard⟩ := FiniteField.card F (ringChar F)
  have hFq : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  rw [hFq]
  exact card_twistedE6RootGroup_eq hp n.pos σ (by rwa [← hFq]) (by rwa [← hFq])

theorem ordF4_pos {q : ℕ} (hq : 2 ≤ q) : 0 < ordF4 q := by
  have hq1 : 0 < q := by omega
  have h2 : 0 < q ^ 2 - 1 := by
    have h : 1 < q ^ 2 := by
      simpa using Nat.pow_lt_pow_left (by omega : 1 < q) (by norm_num : 2 ≠ 0)
    omega
  have h6 : 0 < q ^ 6 - 1 := by
    have h : 1 < q ^ 6 := by
      simpa using Nat.pow_lt_pow_left (by omega : 1 < q) (by norm_num : 6 ≠ 0)
    omega
  have h8 : 0 < q ^ 8 - 1 := by
    have h : 1 < q ^ 8 := by
      simpa using Nat.pow_lt_pow_left (by omega : 1 < q) (by norm_num : 8 ≠ 0)
    omega
  have h12 : 0 < q ^ 12 - 1 := by
    have h : 1 < q ^ 12 := by
      simpa using Nat.pow_lt_pow_left (by omega : 1 < q) (by norm_num : 12 ≠ 0)
    omega
  unfold ordF4
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos hq1 24) h12) h8) h6) h2

theorem relIndex_f4InTwistedE6 (σ : K ≃+* K)
    (hfix : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c)
    (hK : Nat.card K = (Nat.card F) ^ 2)
    (hσ : ∀ c : K, σ c = c ^ Nat.card F)
    (hq3 : Nat.card F % 3 = 1) :
    (f4InTwistedE6 (F := F) σ hfix).relIndex ⊤ =
      (Nat.card F) ^ 12 * ((Nat.card F) ^ 9 + 1) * ((Nat.card F) ^ 5 + 1) := by
  have hcardH : Nat.card (f4InTwistedE6 (F := F) σ hfix) = ordF4 (Nat.card F) :=
    card_f4InTwistedE6 σ hfix
  have hcardG : Nat.card (twistedE6RootGroup K σ) = ordTwistedE6 (Nat.card F) :=
    card_twistedE6RootGroup_eq_card σ hfix hK hσ
  have hmul := Subgroup.relIndex_mul_card (H := f4InTwistedE6 (F := F) σ hfix) (K := ⊤)
  have hprod : (f4InTwistedE6 (F := F) σ hfix).relIndex ⊤ * ordF4 (Nat.card F) =
      ordTwistedE6 (Nat.card F) := by
    simpa [Subgroup.card_top, hcardH, hcardG] using hmul
  have hfac := ordTwistedE6_eq_mul_ordF4 hq3
  have hq2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hpos : 0 < ordF4 (Nat.card F) := ordF4_pos hq2
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hprod, hfac]

theorem not_three_dvd_relIndex_f4InTwistedE6 (σ : K ≃+* K)
    (hfix : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c)
    (hK : Nat.card K = (Nat.card F) ^ 2)
    (hσ : ∀ c : K, σ c = c ^ Nat.card F)
    (hq3 : Nat.card F % 3 = 1) :
    ¬ 3 ∣ (f4InTwistedE6 (F := F) σ hfix).relIndex ⊤ := by
  rw [relIndex_f4InTwistedE6 σ hfix hK hσ hq3]
  exact not_three_dvd_mul hq3

end Construction

theorem exists_f4_in_twistedE6 {F K : Type} [Field F] [Finite F] [Field K] [Finite K]
    {q : ℕ} (hF : Nat.card F = q) (hK : Nat.card K = q ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ q) (hq3 : q % 3 = 1) :
    ∃ H : Subgroup ↥(twistedE6RootGroup K σ),
      Nonempty (adjointGroup Tag.F4 F ≃* H) ∧ ¬ 3 ∣ H.relIndex ⊤ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hFcard⟩ := FiniteField.card F (ringChar F)
  have hFq : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  haveI : Fact (ringChar F).Prime := ⟨hp⟩
  have hKq : Nat.card K = (ringChar F ^ (n : ℕ)) ^ 2 := by
    rw [← hFq, hF]
    exact hK
  have hKcard : Fintype.card K = ringChar F ^ ((n : ℕ) * 2) := by
    rw [← Nat.card_eq_fintype_card, hKq, pow_mul]
  haveI : CharP K (ringChar F) := charP_of_card_eq_prime_pow hKcard
  obtain ⟨φ⟩ := nonempty_ringHom_of_card_sq (ℓ := ringChar F) (f := (n : ℕ))
    (k := F) (K := K) hFq hKq
  letI : Algebra F K := φ.toAlgebra
  have hfix : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c := by
    intro c
    rw [RingHom.algebraMap_toAlgebra, hσ, ← map_pow]
    have hcq : c ^ q = c := by
      rw [← hF, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [hcq]
  exact ⟨f4InTwistedE6 (F := F) (K := K) σ hfix,
    ⟨f4InTwistedE6Equiv (F := F) (K := K) σ hfix⟩,
    not_three_dvd_relIndex_f4InTwistedE6 (F := F) (K := K) σ hfix
      (by rw [hF]; exact hK) (by rw [hF]; exact hσ) (by rw [hF]; exact hq3)⟩

end CFSG.HardMathSupport.Lang.AnisoE6
