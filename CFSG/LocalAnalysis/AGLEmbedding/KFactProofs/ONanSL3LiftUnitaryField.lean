module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitary
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
open CFSG.LieType.Chevalley (fixSubfield)

@[expose] def SubfieldDiagGenAll {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) :
    Prop :=
  ∀ K₀ : Subfield F, Nat.card K₀ = p ^ (2 * (f / 3)) → SubfieldDiagGen h K₀

theorem exists_generating_elemAbelian_unitary_field_of_equiv
    {X : Type} [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) (h3 : 3 ∣ p ^ f + 1)
    (hq : 2 < p ^ f) (hgen : SubfieldDiagGenAll h) (ψ : unitarySU p f F 3 ≃* K)
    (hzc : z ∈ Subgroup.center X) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    (hrank : Open.pRank 3 (R : Subgroup X) = 3) :
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      Subgroup.closure {x : K | ∃ a ∈ A, a ∉ Subgroup.centralizer (K : Set X) ∧
        a * (x : X) * a⁻¹ = x} = ⊤ := by
  classical
  have := h.finite
  obtain ⟨A, hAR, hAe, hAcard⟩ := exists_elemAbelian_card_27 hrank
  have hzR : z ∈ (R : Subgroup X) := mem_sylow_of_central R hzc hz3
  have hzA : z ∈ A := mem_of_pRank_eq_three hrank hzc hz3 hzR hAR hAe hAcard
  refine ⟨A, hAR, hAe, hAcard, ?_⟩
  have hCz : ∀ c ∈ Subgroup.centralizer (K : Set X), c ^ 3 = 1 → c ∈ Subgroup.zpowers z :=
    fun c hc hc3 => mem_zpowers_of_pow_three_eq_one R hzc hz3 hΩ hc hc3
  by_cases hall : ∀ a : A, ∃ B : unitaryIsom3 h, actionAut K ψ (a : X) = suConj h B
  · exact SL3LiftUnitary.closure_fixed_eq_top_unitary_of_conj R K z h h3 hq ψ hzc hz3 hΩ hAe
      hAcard hzA hall
  · obtain ⟨a₀, ha₀⟩ := not_forall.1 hall
    have hβ3 : actionAut K ψ (a₀ : X) ^ 3 = 1 := by
      rw [← map_pow, hAe.2 a₀ a₀.2, map_one]
    rcases exists_suConj_or_conj_suField h hq hβ3 with ⟨B, hB⟩ | ⟨σ, H, hσ, hβ⟩
    · exact absurd ⟨B, hB⟩ ha₀
    · obtain ⟨T, i, hi, hTσ⟩ := FrobData.exists_of_orderOf_eq_three hσ
      have hτ : orderOf T.τ = 3 := by
        rcases hi with rfl | rfl
        · rw [hTσ, pow_one]
          exact hσ
        · rw [hTσ, orderOf_pow' σ (by norm_num), hσ]
          norm_num
      have hact : actionAut K ψ ((a₀ : X) ^ i) = suConj h H * suField h T.τ * (suConj h H)⁻¹ := by
        rw [map_pow, hβ, conj_pow, ← map_pow, hTσ]
      obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Classical.dvd_and_card_fixSubfield_unitary h
        Nat.prime_three (by norm_num) hτ
      refine closure_fixed_eq_top_unitary_of_field K z h h3 hq T hτ (hgen _ hcard)
        ((suConj h H).trans ψ) hzc hCz hAe hAcard hzA (pow_mem a₀.2 i) ?_
      ext1 s
      rw [actionAut_trans, hact]
      simp

@[expose] def PlaneGen : Prop :=
  ∀ {p f₀ : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p (3 * f₀) F), 4 ≤ p ^ f₀ →
    ∀ K₀ : Subfield F, Nat.card K₀ = p ^ (2 * f₀) → SubfieldDiagGen h K₀

@[expose] def EightGen : Prop :=
  ∀ {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) (K₀ : Subfield F), Nat.card K₀ = 4 →
    SubfieldDiagGen h K₀

theorem subfieldDiagGenAll_of_cases {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (h3 : 3 ∣ p ^ f + 1) (hf3 : 3 ∣ f) (hZ : PlaneGen) (h8 : EightGen) : SubfieldDiagGenAll h := by
  intro K₀ hK₀
  obtain ⟨f₀, rfl⟩ := hf3
  have hf₀ : 3 * f₀ / 3 = f₀ := Nat.mul_div_cancel_left _ (by norm_num)
  rw [hf₀] at hK₀
  have hp1 : 1 < p := h.prime.one_lt
  have hf₀1 : 1 ≤ f₀ := by
    have := h.one_le
    omega
  by_cases h8' : p ^ (3 * f₀) = 8
  · have hpd : p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8']
      exact dvd_pow_self p (by omega)
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 (h.prime.dvd_of_dvd_pow hpd)
    subst hp2
    have hf₀' : f₀ = 1 := by
      have : 2 ^ (3 * f₀) = 2 ^ 3 := by rw [h8']; norm_num
      have := Nat.pow_right_injective (le_refl 2) this
      omega
    subst hf₀'
    exact h8 h K₀ (by simpa using hK₀)
  · have h3' : 3 ∣ p ^ f₀ + 1 := by
      apply dvd_add_one_of_dvd_pow_three_add_one
      rwa [← pow_mul, mul_comm]
    have hx2 : 2 ≤ p ^ f₀ := by
      calc 2 ≤ p := hp1
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f₀ := Nat.pow_le_pow_right (by omega) hf₀1
    have hx2' : p ^ f₀ ≠ 2 := by
      intro hx
      apply h8'
      rw [pow_mul', hx]
      norm_num
    have hq₀ : 4 ≤ p ^ f₀ := by omega
    exact hZ h hq₀ K₀ hK₀

theorem kFactSL3LiftGenUnitaryField_of_gen
    (hZ : PlaneGen)
    (h8 : EightGen) : KFactSL3LiftGenFor SL3LiftUnitary.IsUnitaryFieldIndex := by
  intro X _ _ R K _ z d _ hfd hK ⟨e⟩ hzc hzK hz3 hΩ hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hqd, h3, h3e⟩ := hfd
  simp only at hqd
  subst hqd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq3 : 3 ≤ q.card := hrange.2 rfl
  rw [TauCeti.PrimePower.card_def] at hq3 h3
  have hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨-, F, _, _, hFcard, ⟨e'⟩⟩ := hm
  have hU : UnitaryFieldData q.p q.exponent F :=
    ⟨q.prime_p, q.exponent_pos, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hcenne : Subgroup.center K ≠ ⊥ := by
    intro hbot
    have hmem : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.1 hzc g)
    rw [hbot, Subgroup.mem_bot] at hmem
    have : z = 1 := congrArg Subtype.val hmem
    rw [this, orderOf_one] at hz3
    omega
  obtain ⟨ψ⟩ := SL3LiftUnitary.exists_mulEquiv_unitarySU_three hU (by omega) hK.1
    (e'.trans (unitaryPSUEquiv hU (by norm_num)).symm) hcenne
  obtain ⟨A, hAR, hAe, hAcard, hAgen⟩ := exists_generating_elemAbelian_unitary_field_of_equiv R K z
    hU h3 (by omega) (subfieldDiagGenAll_of_cases hU h3 h3e hZ h8) ψ hzc hz3 hΩ hrank
  exact ⟨A, hAR, hAe, SL3Lift.three_le_pRank_of_card hAe hAcard, hAgen⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
