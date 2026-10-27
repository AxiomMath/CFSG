module

public import CFSG.ClassicalInvolution.AschTight.S19FChartD4

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic Matrix
open scoped MatrixGroups

theorem map_conjSub {G : Type*} [Group G] (ψ : MulAut G) (h : G) (X : Subgroup G) :
    (conjSub h X).map ψ.toMonoidHom = conjSub (ψ h) (X.map ψ.toMonoidHom) := by
  have e : ψ.toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (ψ h)).toMonoidHom.comp ψ.toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  rw [conjSub, conjSub, Subgroup.map_map, e, ← Subgroup.map_map]

section G2

variable {K : Type} [Field K]

theorem range_g2Chart_eq_sup (i : Fin Tag.G2.rank) :
    (g2Chart K i).range = simplePosSubgroup .G2 K i ⊔ simpleNegSubgroup .G2 K i := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [MonoidHom.range_eq_map,
      ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K),
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨M, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
    · exact Subgroup.mem_sup_left ⟨c, by rw [coe_g2Chart]; exact simpleRootSL2_uSL i c⟩
    · exact Subgroup.mem_sup_right ⟨c, by rw [coe_g2Chart]; exact simpleRootSL2_vSL i c⟩
  · rintro g ⟨c, hc⟩
    exact ⟨uSL c, Subtype.ext (by rw [coe_g2Chart, simpleRootSL2_uSL, hc])⟩
  · rintro g ⟨c, hc⟩
    exact ⟨vSL c, Subtype.ext (by rw [coe_g2Chart, simpleRootSL2_vSL, hc])⟩

theorem map_range_g2Chart_of_entrywise (σ : K ≃+* K) (α : MulAut ↥(adjointGroup .G2 K))
    (g : adjointGroup .G2 K)
    (hα : ∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (g : ModGL .G2 K) *
      Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹)
    (i : Fin Tag.G2.rank) :
    (g2Chart K i).range.map α.toMonoidHom = conjSub g (g2Chart K i).range := by
  have key : ∀ A, α (g2Chart K i A) =
      g * g2Chart K i (SpecialLinearGroup.map σ.toRingHom A) * g⁻¹ := fun A =>
    Subtype.ext (by
      rw [hα, coe_g2Chart, simpleRootSL2_entrywise, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_g2Chart])
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨_, ⟨SpecialLinearGroup.map σ.toRingHom A, rfl⟩, (key A).symm⟩
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    refine ⟨g2Chart K i (SpecialLinearGroup.map σ.symm.toRingHom A), ⟨_, rfl⟩, ?_⟩
    change α _ = _
    rw [key]
    congr 3
    apply Subtype.ext
    ext a b
    simp

theorem map_range_g2Chart_finiteExceptionalAut [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.G2.prime] (i : Fin Tag.G2.rank) :
    (g2Chart K i).range.map (CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K).toMonoidHom =
      (g2Chart K (CFSG.LieType.Ree.ReeTag.G2.perm i)).range := by
  have hr : ∀ j, ((g2Chart K j).range :
      Subgroup ↥(adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K)) =
      simplePosSubgroup CFSG.LieType.Ree.ReeTag.G2.tag K j ⊔
        simpleNegSubgroup CFSG.LieType.Ree.ReeTag.G2.tag K j := range_g2Chart_eq_sup
  rw [hr i, Subgroup.map_sup,
    map_simplePosSubgroup_finiteExceptionalAut CFSG.LieType.Ree.ReeTag.G2 i,
    map_simpleNegSubgroup_finiteExceptionalAut CFSG.LieType.Ree.ReeTag.G2 i]
  exact (hr _).symm

theorem exists_map_range_g2Chart_pow [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.G2.prime]
    (k : ℕ) (i : Fin Tag.G2.rank) : ∃ j : Fin Tag.G2.rank,
      (g2Chart K i).range.map
        ((CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K) ^ k).toMonoidHom =
      (g2Chart K j).range := by
  induction k generalizing i with
  | zero =>
    refine ⟨i, ?_⟩
    rw [pow_zero]
    exact Subgroup.map_id _
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih (CFSG.LieType.Ree.ReeTag.G2.perm i)
    refine ⟨j, ?_⟩
    rw [← hj, ← map_range_g2Chart_finiteExceptionalAut]
    have e : ∀ y, ((CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K) ^ (k + 1)) y =
        ((CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K) ^ k)
          ((CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K) y) := fun y => by
      rw [pow_succ, MulAut.mul_apply]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨y, hy, rfl⟩, (e y).symm⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, e y⟩

theorem map_conj_mul {G : Type*} [Group G] (g : G) (ψ : MulAut G) (X : Subgroup G) :
    X.map (MulAut.conj g * ψ).toMonoidHom = conjSub g (X.map ψ.toMonoidHom) := by
  rw [conjSub, Subgroup.map_map]
  rfl

theorem conjSub_range_g2Chart_mem (g : adjointGroup .G2 K) (j : Fin Tag.G2.rank) :
    conjSub g (g2Chart K j).range ∈
      fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum K) := by
  refine ⟨g, Pi.single j 1, Or.inr (Or.inl ⟨rfl, ?_⟩), ?_⟩
  · exact CFSG.LieType.Steinberg.Adjoint.mem_adjDatum_roots.mpr (isRoot_single .G2 j)
  · rw [← rankOne_g2_eq_range]
    rfl

theorem map_mem_fund_g2 [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (ψ : MulAut ↥(adjointGroup .G2 K))
    {R : Subgroup ↥(adjointGroup .G2 K)}
    (hR : R ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum K)) :
    R.map ψ.toMonoidHom ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum K) := by
  obtain ⟨i, h, rfl⟩ := exists_eq_conjSub_g2Chart hR
  obtain ⟨j, g, hj⟩ : ∃ (j : Fin Tag.G2.rank) (g : adjointGroup .G2 K),
      (g2Chart K i).range.map ψ.toMonoidHom = conjSub g (g2Chart K j).range := by
    by_cases h3 : p = 3
    · subst h3
      have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
      obtain ⟨-, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
      obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF ψ
      obtain ⟨j, hj⟩ := exists_map_range_g2Chart_pow (K := K) (k : ℕ) i
      refine ⟨j, g, ?_⟩
      rw [hgk]
      exact (map_conj_mul g _ _).trans (congrArg (conjSub g) hj)
    · obtain ⟨hNF, -⟩ :=
        odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK .G2 (Or.inr ⟨rfl, h3⟩)
      obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF ψ
      exact ⟨i, g, map_range_g2Chart_of_entrywise σ ψ g hgσ i⟩
  rw [map_conjSub, hj, ← conjSub_mul]
  exact conjSub_range_g2Chart_mem _ j

end G2

section D4Charts

open CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K] {σ : K →+* K} (hσ3 : ∀ c, σ (σ (σ c)) = c)

include hσ3 in
theorem map_range_slLong_of_formula (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (ψ : MulAut ↥(twistedGroup σ)) (h : twistedGroup σ)
    (hψ : ∀ u, twistedIncl σ (ψ u) = twistedIncl σ h *
      Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ u) * (twistedIncl σ h)⁻¹) :
    (slLong σ hσ3).range.map ψ.toMonoidHom = conjSub h (slLong σ hσ3).range := by
  have key : ∀ A, ψ (slLong σ hσ3 A) =
      h * slLong σ hσ3 (SpecialLinearGroup.map (fixRestrict δ hδσ).toRingHom A) * h⁻¹ :=
    fun A => twistedIncl_injective σ (by
      rw [hψ, slLong_entrywise hσ3 δ hδσ, map_mul, map_mul, map_inv])
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, (key A).symm⟩
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    refine ⟨slLong σ hσ3 (SpecialLinearGroup.map (fixRestrict δ hδσ).symm.toRingHom A), ⟨_, rfl⟩,
      ?_⟩
    change ψ _ = _
    rw [key]
    congr 3
    apply Subtype.ext
    ext a b
    simp

include hσ3 in
theorem map_range_slShort_of_formula (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (ψ : MulAut ↥(twistedGroup σ)) (h : twistedGroup σ)
    (hψ : ∀ u, twistedIncl σ (ψ u) = twistedIncl σ h *
      Units.map (entrywiseHom δ.toRingHom) (twistedIncl σ u) * (twistedIncl σ h)⁻¹) :
    (slShort σ hσ3).range.map ψ.toMonoidHom = conjSub h (slShort σ hσ3).range := by
  have key : ∀ A, ψ (slShort σ hσ3 A) =
      h * slShort σ hσ3 (SpecialLinearGroup.map δ.toRingHom A) * h⁻¹ :=
    fun A => twistedIncl_injective σ (by
      rw [hψ, slShort_entrywise hσ3 δ hδσ, map_mul, map_mul, map_inv])
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, (key A).symm⟩
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    refine ⟨slShort σ hσ3 (SpecialLinearGroup.map δ.symm.toRingHom A), ⟨_, rfl⟩, ?_⟩
    change ψ _ = _
    rw [key]
    congr 3
    apply Subtype.ext
    ext a b
    simp

end D4Charts

section D4

open CFSG.LieType.Steinberg.TwistedD4

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def frobEquiv (p e : ℕ) [Fact p.Prime] :
    GaloisField p (3 * e) ≃+* GaloisField p (3 * e) :=
  RingEquiv.ofBijective (iterateFrobenius (GaloisField p (3 * e)) p e)
    ⟨RingHom.injective _, Finite.surjective_of_injective (RingHom.injective _)⟩

theorem frobEquiv_toRingHom (p e : ℕ) [Fact p.Prime] :
    (frobEquiv p e).toRingHom = iterateFrobenius (GaloisField p (3 * e)) p e :=
  rfl

@[expose] noncomputable def twistedEquivC0 (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e)) (frobEquiv p e).toRingHom) :=
  (Subgroup.equivMapOfInjective _ (adjointGroup d4 (GaloisField p (3 * e))).subtype
    (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr (RouteD.G2D4.map_twistedGroup_eq_graphFixedRootGroup p e hp2 he))

theorem coe_twistedEquivC0 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (u : ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))) :
    ((twistedEquivC0 p e hp2 he u : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (frobEquiv p e).toRingHom) : ModGL d4 (GaloisField p (3 * e))) = twistedIncl _ u :=
  rfl

theorem map_mem_fund_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (ψ : MulAut ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)))
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e))) :
    R.map ψ.toMonoidHom ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)) := by
  classical
  have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hfin : Finite (GaloisField p (3 * e)) := Nat.finite_of_card_ne_zero (by
    rw [hK3]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hσq : ∀ c : GaloisField p (3 * e), iterateFrobenius (GaloisField p (3 * e)) p e c =
      c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  have hσ3 := sigma_three_of_card hK3 hσq
  obtain ⟨hcoe, hNF, -⟩ := odd_triality_exact_automorphism_normal_form (Fact.out : p.Prime) hp2
    he (GaloisField p (3 * e)) hK3 (frobEquiv p e) hσq
  obtain ⟨⟨g₁, δ₁⟩, hgδ, -⟩ :=
    hNF ((twistedEquivC0 p e hp2 he).symm.trans (ψ.trans (twistedEquivC0 p e hp2 he)))
  set h₁ := (twistedEquivC0 p e hp2 he).symm g₁ with hh₁
  have hh₁' : twistedIncl _ h₁ = ((g₁ : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (frobEquiv p e).toRingHom) : ModGL d4 (GaloisField p (3 * e))) := by
    rw [← coe_twistedEquivC0 hp2 he, hh₁, MulEquiv.apply_symm_apply]
  have hψ : ∀ u, twistedIncl _ (ψ u) = twistedIncl _ h₁ *
      Units.map (entrywiseHom δ₁.toRingHom) (twistedIncl _ u) * (twistedIncl _ h₁)⁻¹ := by
    intro u
    have h1 : twistedEquivC0 p e hp2 he (ψ u) =
        ((twistedEquivC0 p e hp2 he).symm.trans (ψ.trans (twistedEquivC0 p e hp2 he)))
          (twistedEquivC0 p e hp2 he u) := by
      change _ = (twistedEquivC0 p e hp2 he) (ψ ((twistedEquivC0 p e hp2 he).symm
        ((twistedEquivC0 p e hp2 he) u)))
      rw [MulEquiv.symm_apply_apply]
    rw [hgδ, MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 := congrArg (fun x : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (frobEquiv p e).toRingHom => (x : ModGL d4 (GaloisField p (3 * e)))) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [← coe_twistedEquivC0 hp2 he, h2, hcoe, coe_twistedEquivC0 hp2 he, hh₁']
  have hδσ : ∀ c, δ₁ (iterateFrobenius (GaloisField p (3 * e)) p e c) =
      iterateFrobenius (GaloisField p (3 * e)) p e (δ₁ c) := fun c => by
    rw [hσq, hσq, map_pow]
  obtain ⟨i, h, hRe⟩ : ∃ (i : Fin (Tag.rank .G2))
      (h : ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))),
      R = conjSub h (CFSG.LieType.CurtisTits.rankOne
        (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) :=
    Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e ⟨Fact.out, he, rfl⟩ hR
  subst hRe
  have key : (CFSG.LieType.CurtisTits.rankOne
      (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i).map ψ.toMonoidHom =
      conjSub h₁ (CFSG.LieType.CurtisTits.rankOne
        (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) := by
    have hi : (i : ℕ) < 2 := i.2
    rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
    · have hi' : i = ng 0 := Fin.ext h0
      subst hi'
      rw [ModelFacts.rankOne_long_eq_range hσ3]
      exact map_range_slLong_of_formula hσ3 δ₁ hδσ ψ h₁ hψ
    · have hi' : i = ng 1 := Fin.ext h1
      subst hi'
      rw [ModelFacts.rankOne_short_eq_range hσ3]
      exact map_range_slShort_of_formula hσ3 δ₁ hδσ ψ h₁ hψ
  rw [map_conjSub, key, ← conjSub_mul]
  exact ⟨_, Pi.single i 1, Or.inr (Or.inr ⟨rfl, Or.inl ⟨1, i, by simp⟩⟩), rfl⟩

end D4

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
