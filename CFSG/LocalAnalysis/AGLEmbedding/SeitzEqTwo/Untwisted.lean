module

public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Cube
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedF4
public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow

public section

namespace CFSG.AGLEmbedding.SeitzEqTwo

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.PreuniquenessRankFour.Helpers (elementary_abelian_map)


variable {τ : Tag} {K : Type} [Field K]

theorem conj_injective_adjointGroup [Finite K] :
    Function.Injective (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : g ∈ Subgroup.center (adjointGroup τ K) := Subgroup.mem_center_iff.2 fun x => by
    have h1 := congrArg (fun φ : MulAut (adjointGroup τ K) => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rwa [center_adjointGroup_eq_bot] at hc

@[expose] noncomputable def fixedEmbed (σ : K ≃+* K) :
    adjointGroup τ (fixSubfield σ) →* adjointGroup τ K :=
  (Subgroup.inclusion (fixedFieldImage_le.trans inf_le_left)).comp
    (fixedFieldImageEquiv (τ := τ) σ).toMonoidHom

theorem fixedEmbed_injective (σ : K ≃+* K) : Function.Injective (fixedEmbed (τ := τ) σ) :=
  (Subgroup.inclusion_injective (fixedFieldImage_le.trans inf_le_left)).comp
    (fixedFieldImageEquiv (τ := τ) σ).injective

theorem entrywiseAdjointAut_fixedEmbed (σ : K ≃+* K) (b : adjointGroup τ (fixSubfield σ)) :
    entrywiseAdjointAut τ σ (fixedEmbed σ b) = fixedEmbed σ b := by
  apply Subtype.ext
  rw [coe_entrywiseAdjointAut]
  exact (fixedFieldImage_le (fixedFieldImageEquiv (τ := τ) σ b).2).2

theorem not_rankLE2_sup_of_descent [Finite K] {p : ℕ} (hp : p.Prime) {T : K ≃+* K}
    (hTp : T ^ p = 1) {E : Subgroup (MulAut (adjointGroup τ K))} {α : MulAut (adjointGroup τ K)}
    (hαE : α ∈ E) (hα : α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    {r j : ℕ} (hj : (α ^ r) ^ j = α) (ψ : MulAut (adjointGroup τ K))
    (hψ : ψ * α ^ r * ψ⁻¹ = entrywiseAdjointAut τ T)
    {A : Subgroup (adjointGroup τ (fixSubfield T))} (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) :
    ¬ RankLE2 p ↥((MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ⊔ E) := by
  refine not_rankLE2_sup_of_conj hp conj_injective_adjointGroup ?_ ?_
    (elementary_abelian_map p hA (fixedEmbed T)) ?_ ?_ hαE ψ r hψ
  · rw [← entrywiseAdjointAut_pow, hTp, entrywiseAdjointAut_one]
  · rintro ⟨g, hg⟩
    apply hα
    have hαr : α ^ r = MulAut.conj (ψ⁻¹ g) := by
      have e : α ^ r = ψ⁻¹ * entrywiseAdjointAut τ T * ψ := by
        rw [← hψ]
        group
      rw [e, ← hg]
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]
    rw [← hj, hαr, ← map_pow]
    exact ⟨_, rfl⟩
  · rw [Subgroup.card_map_of_injective (fixedEmbed_injective T), hAc]
  · rintro _ ⟨b, -, rfl⟩
    exact entrywiseAdjointAut_fixedEmbed T b

@[expose] def FieldDescentAt (τ : Tag) (K : Type) [Field K] (p : ℕ) : Prop :=
  ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 →
    α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
      ∃ (T : K ≃+* K) (r j : ℕ) (ψ : MulAut (adjointGroup τ K)), orderOf T = p ∧
        (α ^ r) ^ j = α ∧ ψ * α ^ r * ψ⁻¹ = entrywiseAdjointAut τ T

theorem fieldDescentAt_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ f p : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ¬ p ∣ τ.cartan.det.natAbs) : FieldDescentAt τ K p := fun α hαp hα => by
  obtain ⟨-, T, r, j, ψ, -, hT, -, hj, hψ⟩ :=
    exists_conj_entrywise_of_outer_E τ hτ hf K hK hp hp2 hdet α hαp hα
  exact ⟨T, r, j, ψ, hT, hj, hψ⟩

theorem fieldDescentAt_F4 {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) :
    FieldDescentAt .F4 K p := fun α hαp hα => by
  have : Fact p.Prime := ⟨hp⟩
  have hα1 : α ≠ 1 := fun h => hα ⟨1, by rw [h, map_one]⟩
  have hαo : orderOf α = p := orderOf_eq_prime hαp hα1
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hf hK
    obtain ⟨σ, ψ, hσ, hψ⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.even_F4_odd_prime_field_descent hf K hK hp hp2 α hαo hα
    exact ⟨σ, 1, 1, ψ, hσ, by rw [pow_one, pow_one], by rw [pow_one]; exact hψ⟩
  · obtain ⟨-, σ, δ, hσ, -, hδ, -, -⟩ :=
      odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hp α hαo hα
    exact ⟨σ, 1, 1, δ, hσ, by rw [pow_one, pow_one], by rw [pow_one]; exact hδ⟩

theorem not_planeRank2_of_fieldDescent [Finite K] {d : TauCeti.ValidLieTypeIndex} {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hdesc : FieldDescentAt τ K p)
    (hplane : ∀ k : Subfield K, ((Nat.card k : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p) →
      ∃ A : Subgroup (adjointGroup τ k), IsElemAbelian p A ∧ Nat.card A = p ^ 2)
    (e : Cat d ≃* adjointGroup τ K) {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E)
    (hout : ¬ InnerPlane d p E) : ¬ PlaneRank2 p E := by
  intro hPR
  have : Fact p.Prime := ⟨hp⟩
  have hPR' : PlaneRank2 p (E.map (MulAut.congr e).toMonoidHom) := hPR.map_congr e
  have hout' : ¬ E.map (MulAut.congr e).toMonoidHom ≤
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
    intro h
    apply hout
    rw [← map_range_conj_congr e] at h
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.congr e).injective).1 h
  obtain ⟨α, hαE, hα⟩ : ∃ α ∈ E.map (MulAut.congr e).toMonoidHom,
      α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
    by_contra h
    push Not at h
    exact hout' fun x hx => h x hx
  have hαp : α ^ p = 1 := (elementary_abelian_map p hE _).2 α hαE
  obtain ⟨T, r, j, ψ, hT, hj, hψ⟩ := hdesc α hαp hα
  obtain ⟨hTf, hTcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hK T
  rw [hT] at hTf hTcard
  obtain ⟨d', rfl⟩ := hTf
  have hcard : ((Nat.card (fixSubfield T) : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p) := by
    rw [hTcard, hK, Nat.mul_div_cancel_left d' hp.pos, pow_mul']
    exact (ZMod.pow_card _).symm.trans (Nat.cast_pow _ _).symm
  obtain ⟨A, hA, hAc⟩ := hplane _ hcard
  exact not_rankLE2_sup_of_descent hp (by rw [← hT]; exact pow_orderOf_eq_one T) hαE hα hj ψ hψ
    hA hAc hPR'

end CFSG.AGLEmbedding.SeitzEqTwo
