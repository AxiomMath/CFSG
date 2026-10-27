module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcG2
public import CFSG.RankThree.PartOne.S11d.HighRankExc
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.RankThree.PartOne.S11c.Sec66D4Tri

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti
open CFSG.RankThree.Chevalley SteinbergBT CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.K1214
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (rankLE1_of_pRank)
open CFSG.RankThree.PartOne.KE (cycloVal cycloVal_twelve)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem hasIndepPair_of_sylowShape {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {G : Type*} [Group G]
    [Finite G] (h : SylowShape p 2 e G) : HasIndepPair p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.arbitrary _
  obtain ⟨Φ⟩ := h (P : Subgroup G) P.isPGroup' P.not_dvd_index
  exact hasIndepPair_of_injective_pi hp he ((P : Subgroup G).subtype.comp Φ.symm.toMonoidHom)
    (Subtype.val_injective.comp Φ.symm.injective)

theorem fixesPair_of_injective_fixed {p : ℕ} {P Q : Type*} [Group P] [Group Q] {β : MulAut P}
    (ι : Q →* P) (hι : Function.Injective ι) (hfix : ∀ y, β (ι y) = ι y)
    (h : HasIndepPair p Q) : FixesIndepPair p β := by
  obtain ⟨y₁, y₂, hc, h1, h2, hi⟩ := h
  refine ⟨ι y₁, ι y₂, hc.map ι, ?_, ?_, fun i j hij => ?_, hfix y₁, hfix y₂⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    exact hi i j (hι (hij.trans (map_one ι).symm))

section


theorem fixesPair_trialityD4 {L : Type} [Group L] [Finite L] {f p : ℕ} (hf : 1 ≤ f)
    (hCEM : ChevalleyExceptionalModel L .trialityD4 2 f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk1 : ¬ RankLE1 p L) {α : MulAut L} (hαp : α ^ p = 1) (hα : α ∉ inner L) :
    FixesIndepPair p α := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hpT : p ∣ Nat.card L := by
    by_contra hnd
    exact hrk1 (rankLE1_of_pRank hp (fun h => absurd h hnd))
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hCEM.2
  have hK : Nat.card K = (2 ^ f) ^ 3 := hKcard
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv L e.toEquiv
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hα
  set α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.congr e α with hα'
  obtain ⟨-, -, ⟨Θ, hΘ, -⟩, hcyc, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK σ hσ
      Θ hΘ hp (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · subst h; omega
    · exact h
  have hK3 : Nat.card K = 2 ^ (3 * (p * f₀)) := by rw [hK, ← pow_mul, mul_comm]
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 3 * (p * f₀)) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f₀) = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ 2 ^ (3 * f₀) := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord]; exact ⟨p, by ring⟩),
      hφord, show 3 * (p * f₀) = 3 * f₀ * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ α') = Subgroup.zpowers δc := by
    have h1 : Nat.card (Subgroup.zpowers (Θ α')) = p := by rw [Nat.card_zpowers]; exact hηord
    have h2 : Nat.card (Subgroup.zpowers δc) = p := by rw [Nat.card_zpowers, hδcord]
    have : Finite (Subgroup.zpowers (Θ α')) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
    have : Finite (Subgroup.zpowers δc) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
  have hfix_eq : fixSub (MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹) =
      fixSub (fieldActor σ δc) := by
    have h1 : MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹ = fieldActor σ (Θ α') := hh₀
    rw [h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (fieldActorHom (t := TwistTag.D4) σ)) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hK' : Nat.card K = 2 ^ (3 * f₀ * p) := by rw [hK3]; ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (f₀ * p) := fun c => by rw [hσ, mul_comm]
  obtain ⟨-, -, hk, hres, -, hJC, hfixJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel Nat.prime_two hf₀ hp.two_le hm3
      K hK' σ hσ' δc hδc
  haveI : Finite (fixSubfield δc) := Subtype.finite
  haveI : Fintype (fixSubfield δc) := Fintype.ofFinite _
  set J := trialityFieldImage σ δc
  have hK0 : Nat.card (fixSubfield δc) = (2 ^ f₀) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hcardK0 : Fintype.card (fixSubfield δc) = 2 ^ (3 * f₀) := by
    rw [← Nat.card_eq_fintype_card, hk]
  have hσ0pow : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ (f₀ * p) := fun c =>
    Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow])
  obtain ⟨j, r, hr, hpjr⟩ : ∃ j r : ℕ, (r = 1 ∨ r = 2) ∧ p = 3 * j + r := by
    have h3 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h
    · exact ⟨p / 3, 1, Or.inl rfl, by omega⟩
    · exact ⟨p / 3, 2, Or.inr rfl, by omega⟩
  have hpowj : ∀ c : fixSubfield δc, c ^ (2 ^ (3 * f₀)) ^ j = c := fun c => by
    have h := FiniteField.pow_card_pow j c
    rwa [hcardK0] at h
  have hσ0pow' : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ (f₀ * r) := fun c => by
    have h2 : 2 ^ (f₀ * p) = (2 ^ (3 * f₀)) ^ j * 2 ^ (f₀ * r) := by
      rw [hpjr]
      ring
    rw [hσ0pow c, h2, pow_mul, hpowj c]
  have hσ0orient : (∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ f₀) ∨
      ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ (2 ^ f₀) ^ 2 := by
    rcases hr with rfl | rfl
    · exact Or.inl fun c => by rw [hσ0pow' c, mul_one]
    · exact Or.inr fun c => by rw [hσ0pow' c, ← pow_mul]
  have hXmodel : LieModel ↥J .trialityD4 0 2 f₀ :=
    lieModel_of_mulEquiv
      ((graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
        (fixSubfieldRestrict σ δc).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _))
      (lieModel_graphFixedRootGroup_trialityD4 hf₀ hK0 (fixSubfieldRestrict σ δc) hσ0orient)
  have hfixsub : fixSub (fieldActor σ δc) =
      J.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    ext x
    rw [Subgroup.mem_subgroupOf, ← hfixJ]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx) ▸ hy
  set φ' : L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e.trans (MulAut.conj h₀) with hφ'
  have hφα : MulAut.congr φ' α = MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹ := rfl
  have hfixβ : fixSub (MulAut.congr φ' α) = fixSub (fieldActor σ δc) := by rw [hφα, hfix_eq]
  have hch' := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hXmodel
  obtain ⟨K₁, hK₁f, hK₁fin, σ₁, hK₁, hσ₁, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf₀ hch'.2
  have hK₁3 : Nat.card K₁ = (2 ^ f₀) ^ 3 := hK₁
  obtain ⟨m, hmem, hdvd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp
    (by omega) (by omega : 2 ≠ p) hCEM).1 hpT).2.2.2.2 rfl
  have hd : (p : ℤ) ∣ cycloVal m 2 (p * f₀) := hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hq1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_pow _ _ (by norm_num)
  have hq1' : 1 ≤ 2 ^ f₀ := Nat.one_le_pow _ _ (by norm_num)
  have hq2' : 2 ≤ 2 ^ f₀ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have hQ : 2 ^ (p * f₀) = (2 ^ f₀) ^ p := by rw [← pow_mul, mul_comm]
  have hrk1C : ¬ RankLE1 p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    fun h => hrk1 (RankLE1.of_mulEquiv e.symm h)
  by_cases h12 : m = 12
  ·
    exfalso
    subst h12
    rw [cycloVal_twelve] at hd
    have hpd : p ∣ (2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 := by
      have h24 : (2 ^ (p * f₀)) ^ 2 ≤ (2 ^ (p * f₀)) ^ 4 :=
        Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        exact hd
      exact_mod_cast h1
    exact hrk1C (rankLE1_of_pRank hp (fun _ =>
      pRank_le_one_D4_twelve Nat.prime_two (Nat.mul_pos hp.pos hf₀) K hK σ hσ hp hp5 hpd))
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
  have hpdQ : p ∣ phiNat m (2 ^ (p * f₀)) := dvd_phiNat_of_dvd_cycloVal hq1 hm' hd
  have hpdq : p ∣ phiNat m (2 ^ f₀) := by
    refine dvd_phiNat_of_dvd_pow hp hq1' hm' ?_
    rw [← hQ]
    exact hpdQ
  have hshN := sylowShape_D4 hf₀ K₁ hK₁3 σ₁ hσ₁ hm' hp hp5 hpdq
  have hne : phiNat m (2 ^ f₀) ≠ 0 := by
    rcases hm' with rfl | rfl | rfl | rfl <;> simp only [phiNat] <;> omega
  have hone : 1 ≤ (phiNat m (2 ^ f₀)).factorization p :=
    (hp.dvd_iff_one_le_factorization hne).1 hpdq
  haveI : Finite ↥J :=
    Finite.of_injective (Subgroup.inclusion hJC) (Subgroup.inclusion_injective hJC)
  have hpairJ : HasIndepPair p ↥J :=
    hasIndepPair_of_sylowShape hp hone (SylowShape.of_mulEquiv e₁ hshN)
  have hfixα : ∀ y : ↥J, MulAut.congr φ' α (Subgroup.inclusion hJC y) =
      Subgroup.inclusion hJC y := by
    intro y
    have hy : Subgroup.inclusion hJC y ∈
        J.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      Subgroup.mem_subgroupOf.2 y.2
    rw [← hfixsub, ← hfixβ] at hy
    exact mem_fixSub.1 hy
  exact FixesIndepPair.of_mulEquiv φ'
    (fixesPair_of_injective_fixed (Subgroup.inclusion hJC) (Subgroup.inclusion_injective hJC)
      hfixα hpairJ)

theorem chevTwoOuterFixesPair_trialityD4_geFive :
    ChevTwoOuterFixesPairAt (fun p => 5 ≤ p) LieIndexTrialityD4 := by
  intro p hp hp2 hp5 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | trialityD4 q =>
    have hq2 : q.p = 2 := hchar
    have hCEM0 := (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46).trialityD4 q hv hq2
    have hCEM : ChevalleyExceptionalModel L .trialityD4 2 q.exponent :=
      CFSG.RankThree.PartOne.chevalleyExceptionalModel_congr e.symm hCEM0
    obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk (MulEquiv.refl L)
    exact fixesPair_trialityD4 q.exponent_pos hCEM hp hp5 (not_rankLE1_of_sq hp hE hEc) hαp hα
  | A _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | B _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | C _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | D _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | E6 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | E7 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | E8 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | F4 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | G2 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | suzuki _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | reeG2 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | reeF4 _ => exact absurd hF (by simp [LieIndexTrialityD4])
  | tits => exact absurd hF (by simp [LieIndexTrialityD4])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
