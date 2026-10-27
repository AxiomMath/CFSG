module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78SwapBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASmallReeExclusion
public import CFSG.Milestones.CL_LIT_signalizer_functor_theorem
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup

variable {X : Type} [Group X]

theorem le_normalizer_map_subtype {H : Subgroup X} (N : Subgroup H) [N.Normal] :
    H ≤ normalizer ((N.map H.subtype : Subgroup X) : Set X) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨⟨c, hc⟩ * o * ⟨c, hc⟩⁻¹, Subgroup.Normal.conj_mem ‹_› o ho _, by simp⟩
  · rintro ⟨o, ho, hoe⟩
    refine ⟨⟨c, hc⟩⁻¹ * o * ⟨c, hc⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem ‹_› o ho (⟨c, hc⟩⁻¹)
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hoe ⊢
      rw [hoe]
      group

theorem mem_normalizer_of_commute {E : Subgroup X} {x : X} (hx : ∀ e ∈ E, x * e = e * x) :
    x ∈ normalizer (E : Set X) := by
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have : x * w * x⁻¹ = w := by rw [hx w hw]; group
    rw [this]
    exact hw
  · intro hw
    have h1 := hx _ hw
    have : w = x * w * x⁻¹ := by
      calc w = x⁻¹ * ((x * w * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * w * x⁻¹)) := by rw [h1]
        _ = x * w * x⁻¹ := by group
    rw [this]
    exact hw

theorem thetaFunctor_le_core {E : Subgroup X} {b : X} (hE : E ≤ centralizer ({b} : Set X)) :
    SolAltLit.thetaFunctor E b ≤
      (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype := by
  refine sup_le ?_ inf_le_left
  rw [commutator_le]
  intro o ho e he
  have hN := le_normalizer_map_subtype (pPrimeCore 2 (centralizer ({b} : Set X))) (hE he)
  have h1 : e * o⁻¹ * e⁻¹ ∈
      (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype :=
    (mem_normalizer_iff.mp hN _).mp (inv_mem ho)
  rw [commutatorElement_def]
  have : o * e * o⁻¹ * e⁻¹ = o * (e * o⁻¹ * e⁻¹) := by group
  rw [this]
  exact mul_mem ho h1

theorem coprime_card_thetaFunctor [Finite X] {E : Subgroup X} {b : X}
    (hE : E ≤ centralizer ({b} : Set X)) :
    Nat.Coprime 2 (Nat.card (SolAltLit.thetaFunctor E b)) := by
  have h1 := Subgroup.card_dvd_of_le (thetaFunctor_le_core hE)
  rw [Subgroup.card_map_of_injective (centralizer ({b} : Set X)).subtype_injective] at h1
  exact Nat.Coprime.coprime_dvd_right h1 (pPrimeCore_coprime_card (p := 2) (G := _))

theorem map_conj_thetaFunctor {E : Subgroup X} {b x : X} (hxb : x ∈ centralizer ({b} : Set X))
    (hxE : ∀ e ∈ E, x * e = e * x) :
    (SolAltLit.thetaFunctor E b).map (MulAut.conj x).toMonoidHom =
      SolAltLit.thetaFunctor E b := by
  have hO : ((pPrimeCore 2 (centralizer ({b} : Set X))).map
      (centralizer ({b} : Set X)).subtype).map (MulAut.conj x).toMonoidHom =
      (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype :=
    mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_map_subtype (pPrimeCore 2 (centralizer ({b} : Set X))) hxb)
  have hxCE : x ∈ centralizer (E : Set X) :=
    mem_centralizer_iff.mpr fun e he => (hxE e he).symm
  have hOE : ((pPrimeCore 2 (centralizer (E : Set X))).map
      (centralizer (E : Set X)).subtype).map (MulAut.conj x).toMonoidHom =
      (pPrimeCore 2 (centralizer (E : Set X))).map (centralizer (E : Set X)).subtype :=
    mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_map_subtype (pPrimeCore 2 (centralizer (E : Set X))) hxCE)
  have hEE : E.map (MulAut.conj x).toMonoidHom = E :=
    mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_of_commute hxE)
  unfold SolAltLit.thetaFunctor
  rw [Subgroup.map_sup, Subgroup.map_commutator,
    Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hO, hOE, hEE]

@[expose] def signalizerCompletion (E B : Subgroup X) : Subgroup X :=
  ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), SolAltLit.thetaFunctor E b

theorem signalizerCompletion_of_balance [Finite X] {B E : Subgroup X} (hBc : IsMulCommutative B)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hB8 : 8 ∣ Nat.card B) (hEB : E ≤ B)
    (hbal : ∀ a ∈ B, a ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b) :
    Odd (Nat.card (signalizerCompletion E B)) ∧
      (∀ b ∈ B, b ≠ 1 →
        signalizerCompletion E B ⊓ centralizer ({b} : Set X) = SolAltLit.thetaFunctor E b) ∧
      ∀ B₀ : Subgroup X, B₀ ≤ B → Nat.card B₀ = 4 →
        signalizerCompletion E B = signalizerCompletion E B₀ := by
  classical
  set θ := SolAltLit.thetaFunctor E with hθdef
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBC : ∀ a ∈ B, E ≤ centralizer ({a} : Set X) := fun a ha e he =>
    mem_centralizer_singleton_iff.mpr (hcomm e (hEB he) a ha)
  have hinv : ∀ a ∈ B, ∀ x ∈ B, (θ a).map (MulAut.conj x).toMonoidHom = θ a := fun a ha x hx =>
    map_conj_thetaFunctor (mem_centralizer_singleton_iff.mpr (hcomm x hx a ha))
      fun e he => hcomm x hx e (hEB he)
  have hfun : Open.IsSolvableSignalizerFunctor 2 B θ :=
    { le_centralizer := fun a ha _ =>
        (thetaFunctor_le_core (hBC a ha)).trans (map_subtype_le _)
      coprime := fun a ha _ => coprime_card_thetaFunctor (hBC a ha)
      invariant := fun a ha _ x hx => hinv a ha x hx
      balance := hbal
      solvable := fun a ha _ =>
        CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp (coprime_card_thetaFunctor (hBC a ha))) }
  have hB8' : 2 ^ 3 ∣ Nat.card B := by norm_num; exact hB8
  obtain ⟨hcop, -, hcent⟩ :=
    Milestones.cl_lit_signalizer_functor_theorem_2 X 2 Nat.prime_two B hBc hB2 hB8' θ hfun
  set W := signalizerCompletion E B with hW
  have hWodd : Odd (Nat.card W) := Nat.coprime_two_left.mp hcop
  have hcent' : ∀ a ∈ B, a ≠ 1 → θ a = W ⊓ centralizer ({a} : Set X) := hcent
  refine ⟨hWodd, fun b hb hb1 => (hcent' b hb hb1).symm, fun B₀ hB₀ hB₀4 => le_antisymm ?_ ?_⟩
  ·
    have hBW : B ≤ normalizer (W : Set X) := by
      intro x hx
      rw [mem_normalizer_iff_map_conj_eq]
      change W.map (MulAut.conj x).toMonoidHom = W
      rw [hW, signalizerCompletion]
      simp only [Subgroup.map_iSup]
      refine iSup_congr fun a => iSup_congr fun ha => iSup_congr fun _ => hinv a ha x hx
    have hnt : Nontrivial B₀ := by
      rw [← Finite.one_lt_card_iff_nontrivial, hB₀4]; norm_num
    obtain ⟨⟨a₁, ha₁⟩, ha₁1⟩ := exists_ne (1 : B₀)
    have ha₁1' : a₁ ≠ 1 := fun h => ha₁1 (Subtype.ext h)
    have hexp : Monoid.exponent B₀ = 2 := by
      have hdvd : Monoid.exponent B₀ ∣ 2 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hB2 g (hB₀ g.2))
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exfalso
        have h1 := Monoid.pow_exponent_eq_one (⟨a₁, ha₁⟩ : B₀)
        rw [h, pow_one] at h1
        exact ha₁1 h1
      · exact h
    have : IsKleinFour B₀ := ⟨hB₀4, hexp⟩
    obtain ⟨a₂, ha₂, ha₂1, ha₂a₁⟩ : ∃ a₂ ∈ B₀, a₂ ≠ 1 ∧ a₂ ≠ a₁ := by
      by_contra hc
      push Not at hc
      have hsub : (B₀ : Set X) ⊆ {1, a₁} := fun g hg => by
        by_cases hg1 : g = 1
        · exact Or.inl hg1
        · exact Or.inr (hc g hg hg1)
      have h1 : Nat.card B₀ ≤ 2 := by
        calc Nat.card B₀ = (B₀ : Set X).ncard := (Nat.card_coe_set_eq _)
          _ ≤ ({1, a₁} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ ({a₁} : Set X).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      omega
    have hsq : a₁ * a₁ = 1 := by rw [← sq]; exact hB2 a₁ (hB₀ ha₁)
    have ha₃1 : a₁ * a₂ ≠ 1 := by
      intro h
      apply ha₂a₁
      calc a₂ = a₁ * (a₁ * a₂) := by rw [← mul_assoc, hsq, one_mul]
        _ = a₁ := by rw [h, mul_one]
    have ha₁₃ : a₁ ≠ a₁ * a₂ := fun h => ha₂1 (by
      calc a₂ = a₁⁻¹ * (a₁ * a₂) := by group
        _ = 1 := by rw [← h]; group)
    have ha₂₃ : a₂ ≠ a₁ * a₂ := fun h => ha₁1' (by
      calc a₁ = (a₁ * a₂) * a₂⁻¹ := by group
        _ = 1 := by rw [← h]; group)
    have hgen := ABGLocalTools.four_group_odd_eq_mul_centralizers (K := W) (T := B₀) hWodd
      (hB₀.trans hBW) ha₁ ha₂ (mul_mem ha₁ ha₂) ha₁1' ha₂1 ha₃1 (Ne.symm ha₂a₁) ha₁₃ ha₂₃
    have hθle : ∀ a ∈ B₀, a ≠ 1 → W ⊓ centralizer ({a} : Set X) ≤
        ⨆ (b : X) (_ : b ∈ B₀) (_ : b ≠ 1), θ b := by
      intro a ha ha1
      rw [← hcent' a (hB₀ ha) ha1]
      exact le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)
    intro w hw
    have hw' : w ∈ (W : Set X) := hw
    rw [hgen] at hw'
    obtain ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, c₃, hc₃, rfl⟩ := hw'
    exact mul_mem (mul_mem (hθle a₁ ha₁ ha₁1' hc₁) (hθle a₂ ha₂ ha₂1 hc₂))
      (hθle _ (mul_mem ha₁ ha₂) ha₃1 hc₃)
  · exact iSup₂_le fun b hb => iSup_le fun hb1 =>
      le_iSup₂_of_le (f := fun (b : X) (_ : b ∈ B) => ⨆ (_ : b ≠ 1), θ b) b (hB₀ hb)
        (le_iSup_of_le hb1 le_rfl)

@[expose] def IsSolomonPair (t : X) (J : Subgroup X) (n : ℕ) : Prop :=
  SolAltLit.IsAltTwoComponent t J n ∧ Odd n ∧ 9 ≤ n ∧
    (∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' → Odd n' →
      n' ≤ n) ∧
    (∀ (t' : X) (J' : Subgroup X), SolAltLit.IsAltTwoComponent t' J' n →
      (Nat.card (normalizer (J' : Set X))).factorization 2 ≤
        (Nat.card (normalizer (J : Set X))).factorization 2) ∧
    ∃ S : Subgroup X, S ≤ normalizer (J : Set X) ∧ IsPGroup 2 S ∧
      Nat.card S = 2 ^ (Nat.card (normalizer (J : Set X))).factorization 2 ∧ t ∈ S ∧
      S ≤ centralizer ({t} : Set X)

@[expose] def BalanceLemmaInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X) (n : ℕ), IsSolomonPair t J n →
    ∀ (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X), E ≤ J →
      Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      (∃ D : Finset (Fin n), D.card = 4 ∧ ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω =
          ω) →
    ∀ y : X, orderOf y = 2 → y ∈ centralizer (E : Set X) →
      y ∈ UnbalancedLayer.coreActionKernel J → y ∉ J →
    ∀ a ∈ E ⊔ zpowers y, a ≠ 1 → ∀ b ∈ E ⊔ zpowers y, b ≠ 1 →
      SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b

private theorem klein_sq : ∀ u : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u ^ 2 = 1 := by
  decide +kernel

private theorem klein_comm :
    ∀ u v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u * v = v * u := by
  decide +kernel

theorem four_sup_zpowers_elementary [Finite X] {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) {y : X}
    (hy : orderOf y = 2) (hyE : y ∈ centralizer (E : Set X)) (hyE' : y ∉ E) :
    IsElementaryAbelian 2 ↥(E ⊔ zpowers y) ∧ Nat.card ↥(E ⊔ zpowers y) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hE
  have hsq := klein_sq
  have hcomm := klein_comm
  have hEel : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := ⟨⟨fun a b => φ.injective (by rw [map_mul, map_mul, hcomm])⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        φ.injective (by rw [map_pow, hsq, map_one]) }
  have hyel : IsElementaryAbelian 2 (zpowers y) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hy ▸ pow_orderOf_eq_one y)
  have hcent : zpowers y ≤ centralizer (E : Set X) := zpowers_le.mpr hyE
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hcent, ?_⟩
  have hN : zpowers y ≤ normalizer (E : Set X) := zpowers_le.mpr
    (mem_normalizer_of_commute fun e he => (mem_centralizer_iff.mp hyE e he).symm)
  have h := card_sup_mul_card_inf' hN
  rw [sup_comm, inf_comm] at h
  have hinf : E ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
    rcases UnbalancedGS.SmallReeExclusion.eq_one_or_eq_of_mem_zpowers hyy (mem_inf.mp hg).2 with
      h1 | h1
    · rw [h1]; exact one_mem _
    · exact absurd (h1 ▸ (mem_inf.mp hg).1) hyE'
  have hE4 : Nat.card E = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hy, hE4] at h
  rw [h]

theorem signalizerCompletion_of_balanceLemma (h33 : BalanceLemmaInput)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hP : IsSolomonPair t J n) (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n))
    {E : Subgroup X} (hEJ : E ≤ J)
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hD : ∃ D : Finset (Fin n), D.card = 4 ∧ ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω)
    {y : X} (hy : orderOf y = 2) (hyE : y ∈ centralizer (E : Set X))
    (hyK : y ∈ UnbalancedLayer.coreActionKernel J) (hyJ : y ∉ J) :
    Odd (Nat.card (signalizerCompletion E (E ⊔ zpowers y))) ∧
      (∀ b ∈ E ⊔ zpowers y, b ≠ 1 → signalizerCompletion E (E ⊔ zpowers y) ⊓
        centralizer ({b} : Set X) = SolAltLit.thetaFunctor E b) ∧
      ∀ B₀ : Subgroup X, B₀ ≤ E ⊔ zpowers y → Nat.card B₀ = 4 →
        signalizerCompletion E (E ⊔ zpowers y) = signalizerCompletion E B₀ := by
  obtain ⟨hel, hcard⟩ := four_sup_zpowers_elementary hE hy hyE fun h => hyJ (hEJ h)
  have hB2 : ∀ b ∈ E ⊔ zpowers y, b ^ 2 = 1 := fun b hb =>
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E ⊔ zpowers y) b hb
  exact signalizerCompletion_of_balance hel.toIsMulCommutative hB2 (by rw [hcard]) le_sup_left
    (h33 X hnonab hK hz hU t J n hP e E hEJ hE hD y hy hyE hyK hyJ)

end CFSG.ComponentClassification.Sol78
