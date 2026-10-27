module

public import CFSG.ClassicalInvolution.AschTight.S19FAut
public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.AschTight.S19GD4Inv

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19F Matrix
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem apply_eq_of_congr_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) (α : MulAut G)
    (g : H) (F : MulAut H) (h : MulAut.congr e α = MulAut.conj g * F) (x : G) :
    α x = e.symm g * MulAut.congr e.symm F x * (e.symm g)⁻¹ := by
  have hx := DFunLike.congr_fun h (e x)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.mul_apply, MulAut.conj_apply] at hx
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm]
  apply e.injective
  rw [hx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem exists_fieldActor_form_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (α₁ : MulAut ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (frobEquiv p e).toRingHom)) {n : ℕ} (hn : α₁ ^ (2 ^ n) = 1) :
    ∃ (g₁ : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e)) (frobEquiv p e).toRingHom)
      (δ : GaloisField p (3 * e) ≃+* GaloisField p (3 * e))
      (F : MulAut ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
        (frobEquiv p e).toRingHom)),
      α₁ = MulAut.conj g₁ * F ∧
      (∀ y, ((F y : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
        (frobEquiv p e).toRingHom) : ModGL d4 (GaloisField p (3 * e))) =
        Units.map (entrywiseHom δ.toRingHom) (y : ModGL d4 (GaloisField p (3 * e)))) ∧
      δ ^ (2 ^ n) = 1 ∧ (δ = 1 → F = 1) := by
  have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσq : ∀ c : GaloisField p (3 * e), frobEquiv p e c = c ^ (p ^ e) := fun c =>
    iterateFrobenius_def p e c
  obtain ⟨hcoe, hNF, ⟨Θ, hΘ, -, -, -⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form (Fact.out : p.Prime) hp2 he
      (GaloisField p (3 * e)) hK3 (frobEquiv p e) hσq
  obtain ⟨⟨g₁, δ₁⟩, hgδ, -⟩ := hNF α₁
  refine ⟨g₁, δ₁, fieldActor (t := TwistTag.D4) (frobEquiv p e) δ₁, hgδ, hcoe δ₁, ?_,
    fun h => by rw [h]; exact fieldActor_one _⟩
  rw [← hΘ _ g₁ δ₁ hgδ, ← map_pow, hn, map_one]

theorem exists_field_form_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (α : MulAut ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))) {n : ℕ}
    (hαn : α ^ (2 ^ n) = 1) :
    ∃ (g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
      (δ : GaloisField p (3 * e) ≃+* GaloisField p (3 * e))
      (β : MulAut ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))),
      (∀ x, α x = g * β x * g⁻¹) ∧
      (∀ u, twistedIncl _ (β u) = Units.map (entrywiseHom δ.toRingHom) (twistedIncl _ u)) ∧
      δ ^ (2 ^ n) = 1 ∧ (δ = 1 → ∀ x, β x = x) := by
  obtain ⟨eT, heT⟩ : ∃ eT : ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e)) (frobEquiv p e).toRingHom),
      eT = twistedEquivC0 p e hp2 he := ⟨_, rfl⟩
  have hcoeT : ∀ u, ((eT u : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (frobEquiv p e).toRingHom) : ModGL d4 (GaloisField p (3 * e))) = twistedIncl _ u := by
    intro u
    rw [heT]
    rfl
  obtain ⟨g₁, δ₁, F₁, hgδ, hcoeF, hδn, hF1⟩ := exists_fieldActor_form_d4 hp2 he
    (MulAut.congr eT α) (n := n) (by rw [← map_pow, hαn, map_one])
  refine ⟨eT.symm g₁, δ₁, MulAut.congr eT.symm F₁, apply_eq_of_congr_eq eT α g₁ F₁ hgδ,
    fun u => ?_, hδn, fun hδ1 x => ?_⟩
  swap
  · change eT.symm (F₁ (eT x)) = x
    rw [hF1 hδ1]
    exact eT.symm_apply_apply x
  have h2 := hcoeT (eT.symm (F₁ (eT u)))
  rw [MulEquiv.apply_symm_apply] at h2
  exact h2.symm.trans ((hcoeF (eT u)).trans (congrArg _ (hcoeT u)))

theorem eq_one_of_fixes_field_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
    (δ : GaloisField p (3 * e) ≃+* GaloisField p (3 * e))
    (β : MulAut ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (hβ : ∀ u, twistedIncl _ (β u) = Units.map (entrywiseHom δ.toRingHom) (twistedIncl _ u))
    {n : ℕ} (hδn : δ ^ (2 ^ n) = 1)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (hfix : ∀ x ∈ R, g * β x * g⁻¹ = x) : δ = 1 := by
  obtain ⟨hσ3, hK1, hC₀, hgF, hoddK, hoddF⟩ := d4_model_data hp2 he
  obtain ⟨i, g₀, hRg⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e ⟨Fact.out, he, rfl⟩ hR
  obtain ⟨h, hh⟩ : ∃ h : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e), h = g₀ :=
    ⟨g₀, rfl⟩
  have hR' : R = Generic.conjSub h (CFSG.LieType.CurtisTits.rankOne
      (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) := by
    rw [hh]
    exact hRg
  subst hR'
  have hδσ : ∀ c, δ (iterateFrobenius (GaloisField p (3 * e)) p e c) =
      iterateFrobenius (GaloisField p (3 * e)) p e (δ c) := fun c => by
    rw [iterateFrobenius_def, iterateFrobenius_def, map_pow]
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  ·
    have hi' : i = ng 0 := Fin.ext h0
    subst hi'
    rw [ModelFacts.rankOne_long_eq_range hσ3] at hfix
    have hres := eq_of_fixes_conjSub (slLong _ hσ3) (slLong_injective hσ3) β
      (fixRestrict δ hδσ).toRingHom
      (fun A => twistedIncl_injective _ ((hβ _).trans (slLong_entrywise hσ3 δ hδσ A)))
      (fun c hc => linAct_of_centralizes_long hσ3 hK1 (two_ne_zero_of_odd hoddF) hC₀ hgF hc)
      g h hfix
    have hcF : Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) = p ^ e :=
      ModelFacts.card_fixedField_iterateFrobenius he
    exact eq_one_of_fixes_subfield (Fact.out : p.Prime) he (GaloisField.card p (3 * e) (by omega))
      (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) hcF
      (fun c hc => (iterateFrobenius_def p e c).symm.trans hc) hδn
      (fun c hc => congrArg Subtype.val (hres ⟨c, hc⟩))
  ·
    have hi' : i = ng 1 := Fin.ext h1
    subst hi'
    rw [ModelFacts.rankOne_short_eq_range hσ3] at hfix
    exact RingEquiv.ext (eq_of_fixes_conjSub (slShort _ hσ3) (slShort_injective hσ3) β
      δ.toRingHom (fun A => twistedIncl_injective _ ((hβ _).trans (slShort_entrywise hσ3 δ hδσ A)))
      (fun c hc => linAct_of_centralizes_short hσ3 hK1 (two_ne_zero_of_odd hoddK) hC₀ hgF hc)
      g h hfix)

theorem exists_conj_of_fixes_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (α : MulAut ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))) {n : ℕ}
    (hαn : α ^ (2 ^ n) = 1)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)))
    (hfix : ∀ x ∈ R, α x = x) : ∃ g, α = MulAut.conj g := by
  obtain ⟨g, δ, β, hαβ, hβ, hδn, hβ1⟩ := exists_field_form_d4 hp2 he α hαn
  have hδ1 := eq_one_of_fixes_field_d4 hp2 he g δ β hβ hδn hR
    (fun x hx => (hαβ x).symm.trans (hfix x hx))
  exact ⟨g, MulEquiv.ext fun x =>
    (hαβ x).trans (congrArg (fun y => g * y * g⁻¹) (hβ1 hδ1 x))⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
