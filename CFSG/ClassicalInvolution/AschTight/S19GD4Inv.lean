module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Class
public import CFSG.ClassicalInvolution.AschTight.S19GSL2
public import CFSG.ClassicalInvolution.AschTight.S19FSL2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19F Matrix
open scoped MatrixGroups

section Conj

variable {G : Type*} [Group G]

theorem eq_one_or_mem_conjSub_of_chart {F : Type} [Field F] (Φ : SL2 F →* G)
    (hΦ : ∀ x : G, x * x = 1 → (∀ C, x * Φ C = Φ C * x) → x = 1 ∨ x = Φ (-1)) (g : G) {y : G}
    (hy : y ∈ Subgroup.centralizer (Generic.conjSub g Φ.range : Set G)) (hy2 : y * y = 1) :
    y = 1 ∨ y ∈ Generic.conjSub g Φ.range := by
  have hc : ∀ C, (g⁻¹ * y * g) * Φ C = Φ C * (g⁻¹ * y * g) := by
    intro C
    have h := Subgroup.mem_centralizer_iff.mp hy (g * Φ C * g⁻¹) ⟨_, ⟨C, rfl⟩, rfl⟩
    calc g⁻¹ * y * g * Φ C = g⁻¹ * (y * (g * Φ C * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * Φ C * g⁻¹) * y) * g := by rw [h]
      _ = Φ C * (g⁻¹ * y * g) := by group
  have hx2 : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by
    calc (g⁻¹ * y * g) * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hy2]; group
  rcases hΦ _ hx2 hc with h | h
  · left
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    refine ⟨Φ (-1), ⟨-1, rfl⟩, ?_⟩
    change g * Φ (-1) * g⁻¹ = y
    rw [← h]
    group

theorem mem_second_derived_of_partner {F F' : Type} [Field F] [Field F'] (h2 : (2 : F') ≠ 0)
    (Φ : SL2 F →* G) (Φ' : SL2 F' →* G) (hcomm : ∀ C C', Φ' C * Φ C' = Φ C' * Φ' C)
    (hneg : Φ' (-1) = Φ (-1)) (g : G) :
    g * Φ (-1) * g⁻¹ ∈
      ⁅⁅Subgroup.centralizer (Generic.conjSub g Φ.range : Set G),
        Subgroup.centralizer (Generic.conjSub g Φ.range : Set G)⁆,
        ⁅Subgroup.centralizer (Generic.conjSub g Φ.range : Set G),
          Subgroup.centralizer (Generic.conjSub g Φ.range : Set G)⁆⁆ := by
  set Ψ : SL2 F' →* G := (MulAut.conj g).toMonoidHom.comp Φ' with hΨ
  have hle : Ψ.range ≤ Subgroup.centralizer (Generic.conjSub g Φ.range : Set G) := by
    rintro _ ⟨C, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨C', rfl⟩, rfl⟩
    change g * Φ C' * g⁻¹ * (g * Φ' C * g⁻¹) = g * Φ' C * g⁻¹ * (g * Φ C' * g⁻¹)
    calc g * Φ C' * g⁻¹ * (g * Φ' C * g⁻¹) = g * (Φ C' * Φ' C) * g⁻¹ := by group
      _ = g * (Φ' C * Φ C') * g⁻¹ := by rw [hcomm C C']
      _ = _ := by group
  have hmem := map_neg_one_mem_second_derived h2 Ψ
  have hΨ1 : Ψ (-1) = g * Φ (-1) * g⁻¹ := by
    rw [hΨ, MonoidHom.comp_apply, hneg]
    rfl
  rw [hΨ1] at hmem
  exact Subgroup.commutator_mono (Subgroup.commutator_mono hle hle)
    (Subgroup.commutator_mono hle hle) hmem

theorem conj_involution {x : G} (hx1 : x ≠ 1) (hx2 : x * x = 1) (g : G) :
    g * x * g⁻¹ ≠ 1 ∧ (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
  refine ⟨fun h => hx1 ?_, ?_⟩
  · calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group

end Conj

section Charts

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem eq_one_or_eq_of_centralizing_slLong (hK : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {x : twistedGroup σ} (hx2 : x * x = 1)
    (hc : ∀ C : SL(2, fixedField σ), x * slLong σ hσ C = slLong σ hσ C * x) :
    x = 1 ∨ x = slLong σ hσ (-1) :=
  involution_centralizing_slLong hσ hK (mem_SProd_of_centralizes hσ hK hC₀ hgF (hc (-1))) hx2 hc

include hσ in
theorem eq_one_or_eq_of_centralizing_slShort (hK : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {x : twistedGroup σ} (hx2 : x * x = 1)
    (hc : ∀ C : SL(2, K), x * slShort σ hσ C = slShort σ hσ C * x) :
    x = 1 ∨ x = slShort σ hσ (-1) := by
  have hcB : ∀ C, (nB σ * x * (nB σ)⁻¹) * slB σ hσ C = slB σ hσ C * (nB σ * x * (nB σ)⁻¹) := by
    intro C
    rw [slB_apply]
    calc nB σ * x * (nB σ)⁻¹ * (nB σ * slShort σ hσ C * (nB σ)⁻¹) =
          nB σ * (x * slShort σ hσ C) * (nB σ)⁻¹ := by group
      _ = nB σ * (slShort σ hσ C * x) * (nB σ)⁻¹ := by rw [hc C]
      _ = _ := by group
  have hy2 : (nB σ * x * (nB σ)⁻¹) * (nB σ * x * (nB σ)⁻¹) = 1 := by
    calc (nB σ * x * (nB σ)⁻¹) * (nB σ * x * (nB σ)⁻¹) = nB σ * (x * x) * (nB σ)⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hmem : nB σ * x * (nB σ)⁻¹ ∈ SProd σ hσ :=
    mem_SProd_of_centralizes hσ hK hC₀ hgF (by rw [← slB_neg_one hσ]; exact hcB (-1))
  rcases involution_centralizing_slB hσ hK hmem hy2 hcB with h | h
  · left
    calc x = (nB σ)⁻¹ * (nB σ * x * (nB σ)⁻¹) * nB σ := by group
      _ = 1 := by rw [h]; group
  · right
    calc x = (nB σ)⁻¹ * (nB σ * x * (nB σ)⁻¹) * nB σ := by group
      _ = (nB σ)⁻¹ * slB σ hσ (-1) * nB σ := by rw [h, slB_neg_one hσ]
      _ = slShort σ hσ (-1) := by rw [slB_apply]; group

omit [Finite K] in
include hσ in
theorem exists_partner_slShort :
    ∃ Φ' : SL(2, fixedField σ) →* twistedGroup σ,
      (∀ C C', Φ' C * slShort σ hσ C' = slShort σ hσ C' * Φ' C) ∧
        Φ' (-1) = slShort σ hσ (-1) := by
  have hS : ∀ C', slShort σ hσ C' = (nB σ)⁻¹ * slB σ hσ C' * nB σ := fun C' => by
    rw [slB_apply]
    group
  refine ⟨(MulAut.conj (nB σ)⁻¹).toMonoidHom.comp (slLong σ hσ), fun C C' => ?_, ?_⟩
  · change (nB σ)⁻¹ * slLong σ hσ C * (nB σ)⁻¹⁻¹ * slShort σ hσ C' =
      slShort σ hσ C' * ((nB σ)⁻¹ * slLong σ hσ C * (nB σ)⁻¹⁻¹)
    rw [hS, inv_inv]
    calc (nB σ)⁻¹ * slLong σ hσ C * nB σ * ((nB σ)⁻¹ * slB σ hσ C' * nB σ) =
          (nB σ)⁻¹ * (slLong σ hσ C * slB σ hσ C') * nB σ := by group
      _ = (nB σ)⁻¹ * (slB σ hσ C' * slLong σ hσ C) * nB σ := by rw [slLong_comm_slB hσ]
      _ = _ := by group
  · change (nB σ)⁻¹ * slLong σ hσ (-1) * (nB σ)⁻¹⁻¹ = slShort σ hσ (-1)
    rw [hS, slB_neg_one hσ, inv_inv]

end Charts

section Model

variable {p : ℕ} [Fact p.Prime]

theorem d4_model_data (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) :
    (∀ c, iterateFrobenius (GaloisField p (3 * e)) p e
        (iterateFrobenius (GaloisField p (3 * e)) p e
          (iterateFrobenius (GaloisField p (3 * e)) p e c)) = c) ∧
      (-1 : (GaloisField p (3 * e))ˣ) ≠ 1 ∧
      graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
          (iterateFrobenius (GaloisField p (3 * e)) p e) ≤
        (twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e)).range ∧
      (∀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
        twistedIncl _ g ∈ graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
          (iterateFrobenius (GaloisField p (3 * e)) p e)) ∧
      Odd (Nat.card (GaloisField p (3 * e))) ∧
      Odd (Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e))) := by
  have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hfin : Finite (GaloisField p (3 * e)) := Nat.finite_of_card_ne_zero (by
    rw [hK3]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hσq : ∀ c : GaloisField p (3 * e), iterateFrobenius (GaloisField p (3 * e)) p e c =
      c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hoddK : Odd (Nat.card (GaloisField p (3 * e))) := by rw [hK3]; exact hpodd.pow.pow
  have h3 := RouteD.G2D4.map_twistedGroup_eq_graphFixedRootGroup p e hp2 he
  refine ⟨sigma_three_of_card hK3 hσq, fun h => two_ne_zero_of_odd hoddK ?_, ?_, ?_, hoddK, ?_⟩
  · have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    linear_combination -h'
  · rw [← h3]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · intro x
    rw [← h3]
    exact ⟨x, x.2, rfl⟩
  · have hcF : Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) = p ^ e :=
      ModelFacts.card_fixedField_iterateFrobenius he
    rw [hcF]
    exact hpodd.pow

theorem eq_one_or_mem_of_centralizing_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)))
    {y : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)}
    (hy : y ∈ Subgroup.centralizer
      (R : Set (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))))
    (hy2 : y * y = 1) : y = 1 ∨ y ∈ R := by
  obtain ⟨hσ3, hK1, hC₀, hgF, -, -⟩ := d4_model_data hp2 he
  obtain ⟨i, g₀, hRg⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e ⟨Fact.out, he, rfl⟩ hR
  obtain ⟨g, hg⟩ : ∃ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e), g = g₀ :=
    ⟨g₀, rfl⟩
  have hR' : R = Generic.conjSub g (CFSG.LieType.CurtisTits.rankOne
      (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) := by
    rw [hg]
    exact hRg
  subst hR'
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = ng 0 := Fin.ext h0
    subst hi'
    rw [ModelFacts.rankOne_long_eq_range hσ3] at hy ⊢
    exact eq_one_or_mem_conjSub_of_chart _
      (fun x hx2 hc => eq_one_or_eq_of_centralizing_slLong hσ3 hK1 hC₀ hgF hx2 hc) g hy hy2
  · have hi' : i = ng 1 := Fin.ext h1
    subst hi'
    rw [ModelFacts.rankOne_short_eq_range hσ3] at hy ⊢
    exact eq_one_or_mem_conjSub_of_chart _
      (fun x hx2 hc => eq_one_or_eq_of_centralizing_slShort hσ3 hK1 hC₀ hgF hx2 hc) g hy hy2

theorem exists_inv_mem_second_derived_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e))) :
    ∃ x ∈ R, x ≠ 1 ∧ x * x = 1 ∧
      x ∈ ⁅⁅Subgroup.centralizer
          (R : Set (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))),
        Subgroup.centralizer
          (R : Set (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)))⁆,
        ⁅Subgroup.centralizer
          (R : Set (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))),
          Subgroup.centralizer
            (R : Set (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)))⁆⁆ := by
  obtain ⟨hσ3, -, -, -, hoddK, hoddF⟩ := d4_model_data hp2 he
  obtain ⟨i, g₀, hRg⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e ⟨Fact.out, he, rfl⟩ hR
  obtain ⟨g, hg⟩ : ∃ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e), g = g₀ :=
    ⟨g₀, rfl⟩
  have hR' : R = Generic.conjSub g (CFSG.LieType.CurtisTits.rankOne
      (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) := by
    rw [hg]
    exact hRg
  subst hR'
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = ng 0 := Fin.ext h0
    subst hi'
    rw [ModelFacts.rankOne_long_eq_range hσ3]
    have hU := isUniqueInvolution_range_sl2 hoddF (slLong_injective hσ3)
    obtain ⟨hne, hsq⟩ := conj_involution hU.ne_one hU.sq g
    exact ⟨_, ⟨_, ⟨-1, rfl⟩, rfl⟩, hne, hsq, mem_second_derived_of_partner
      (two_ne_zero_of_odd hoddK) _ (slB _ hσ3) (fun C C' => (slLong_comm_slB hσ3 C' C).symm)
      (slB_neg_one hσ3) g⟩
  · have hi' : i = ng 1 := Fin.ext h1
    subst hi'
    rw [ModelFacts.rankOne_short_eq_range hσ3]
    have hU := isUniqueInvolution_range_sl2 hoddK (slShort_injective hσ3)
    obtain ⟨hne, hsq⟩ := conj_involution hU.ne_one hU.sq g
    obtain ⟨Φ', hcomm, hneg⟩ := exists_partner_slShort hσ3
    exact ⟨_, ⟨_, ⟨-1, rfl⟩, rfl⟩, hne, hsq,
      mem_second_derived_of_partner (two_ne_zero_of_odd hoddF) _ Φ' hcomm hneg g⟩

end Model

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
