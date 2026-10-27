module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
import CFSG.HardMathSupport.Dickson.DefCharOuter.EntrywiseFixed
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.HardMathSupport.Lang.E6Descent (G2_form_odd G2_form_three
  exists_conj_eq_entrywiseAdjointAut_of_form exists_conj_entrywise_of_not_innerDiag
  prime_dvd_of_diag_noninner)

section Helpers

variable {S : Type*} [Group S]

private theorem fixSubgroup_le_pow (α : MulAut S) (n : ℕ) :
    fixSubgroup α ≤ fixSubgroup (α ^ n) := by
  intro x hx
  rw [mem_fixSubgroup] at hx ⊢
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx]; exact ih

private theorem fixSubgroup_pow_eq {α : MulAut S} {r j : ℕ} (h : (α ^ r) ^ j = α) :
    fixSubgroup α = fixSubgroup (α ^ r) :=
  le_antisymm (fixSubgroup_le_pow α r) (by
    have := fixSubgroup_le_pow (α ^ r) j
    rwa [h] at this)

end Helpers

section Base


private theorem perfectInLayer_of_model {τ : Tag} {S : Type} [Group S] {q p : ℕ}
    (hmodel : UntwistedChevalleyModel S τ q) {β : MulAut S} (hβ : β ^ p = 1)
    (hout : ∀ a : S, MulAut.conj a ≠ β)
    (hdesc : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 → α ∉ inner (adjointGroup τ K) →
        PerfectInLayer α) : PerfectInLayer β := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  let θ : S ≃* adjointGroup τ K := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  refine LieSemisimple.perfectInLayer_of_congr θ β (hdesc K hK _ ?_ ?_)
  · rw [← map_pow, hβ, map_one]
  · rintro ⟨g, hg⟩
    apply hout (θ.symm g)
    apply (MulAut.congr θ).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, θ.apply_symm_apply]
    exact hg

private theorem perfectInLayer_adjointG2 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hp : p.Prime) (hpℓ : p = ℓ) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.G2 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.G2 K)) : PerfectInLayer α := by
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.G2 K)).one_mem)
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hM : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hp2 : p ≠ 2 := hpℓ ▸ hℓ2
  have hform : ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      exact G2_form_three hf K hK hp hp2 α hαord hα
    · exact G2_form_odd hℓ hℓ2 hℓ3 hf K hK hp α hαord hα
  obtain ⟨x, σ, hσp, hασ⟩ := hform
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_form Tag.G2 hℓ hf K hK hp α hαord x σ
    hσp hασ
  have h2 := LieSemisimple.perfectInLayer_conj δ⁻¹ _
    (perfectInLayer_entrywiseAdjointAut Tag.G2 hM σ)
  rwa [← hδ, show δ⁻¹ * (δ * α * δ⁻¹) * δ⁻¹⁻¹ = α by group] at h2

private theorem perfectInLayer_adjointF4 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hp : p.Prime) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.F4 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.F4 K)) : PerfectInLayer α := by
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.F4 K)).one_mem)
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hM : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  obtain ⟨x, σ, δ, hσp, -, hδ, -, -⟩ :=
    odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hp α hαord hα
  have h2 := LieSemisimple.perfectInLayer_conj δ⁻¹ _
    (perfectInLayer_entrywiseAdjointAut Tag.F4 hM σ)
  rwa [← hδ, show δ⁻¹ * (δ * α * δ⁻¹) * δ⁻¹⁻¹ = α by group] at h2

private theorem perfectInLayer_adjointE {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hp : p.Prime) (hpℓ : p = ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1) (hα : α ∉ inner (adjointGroup τ K)) :
    PerfectInLayer α := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hM : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hp2 : p ≠ 2 := hpℓ ▸ hℓ2
  have hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut τ K a := by
    intro g a h
    have hdvd := (prime_dvd_of_diag_noninner τ hτ K hp g a α h hαp hα).2
    rw [hK] at hdvd
    have h1 : p ∣ ℓ ^ f := by
      rw [hpℓ]
      exact dvd_pow_self ℓ (by omega)
    have h2 : p ∣ ℓ ^ f - (ℓ ^ f - 1) := Nat.dvd_sub h1 hdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨d, T, r, j, ψ, -, -, -, -, -, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_not_innerDiag τ hτ hf K hK hp hp2 α hαp hnd
  have h2 := LieSemisimple.perfectInLayer_conj ψ⁻¹ _ (perfectInLayer_entrywiseAdjointAut τ hM T)
  rw [← hψ, show ψ⁻¹ * (ψ * α ^ r * ψ⁻¹) * ψ⁻¹⁻¹ = α ^ r by group] at h2
  intro P hP hperf
  rw [fixSubgroup_pow_eq hαβ] at hP ⊢
  exact h2 P hP hperf

end Base

theorem perfectInLayer_G2_outer
    (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  have hq2 : q.p ≠ 2 := hpc ▸ hp2
  refine perfectInLayer_of_model
    (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_G2 q hv hq2 e)
    hβ hout fun K _ _ hK α hαp hα => ?_
  exact perfectInLayer_adjointG2 q.prime_p hq2 q.exponent_pos hp hpc K hK α hαp hα

theorem perfectInLayer_F4_outer
    (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.F4 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  have hq2 : q.p ≠ 2 := hpc ▸ hp2
  refine perfectInLayer_of_model
    (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_F4 q hv hq2 e)
    hβ hout fun K _ _ hK α hαp hα => ?_
  exact perfectInLayer_adjointF4 q.prime_p hq2 q.exponent_pos hp K hK α hαp hα

theorem perfectInLayer_E6_outer
    (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.E6 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  have hq2 : q.p ≠ 2 := hpc ▸ hp2
  refine perfectInLayer_of_model
    (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_E6 q hv hq2 e)
    hβ hout fun K _ _ hK α hαp hα => ?_
  exact perfectInLayer_adjointE (Or.inl rfl) q.prime_p hq2 q.exponent_pos hp hpc K hK α hαp hα

theorem perfectInLayer_E7_outer
    (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.E7 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  have hq2 : q.p ≠ 2 := hpc ▸ hp2
  refine perfectInLayer_of_model
    (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_E7 q hv hq2 e)
    hβ hout fun K _ _ hK α hαp hα => ?_
  exact perfectInLayer_adjointE (Or.inr (Or.inl rfl)) q.prime_p hq2 q.exponent_pos hp hpc K hK α
    hαp hα

theorem perfectInLayer_E8_outer
    (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.E8 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  have hq2 : q.p ≠ 2 := hpc ▸ hp2
  refine perfectInLayer_of_model
    (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_E8 q hv hq2 e)
    hβ hout fun K _ _ hK α hαp hα => ?_
  exact perfectInLayer_adjointE (Or.inr (Or.inr rfl)) q.prime_p hq2 q.exponent_pos hp hpc K hK α
    hαp hα

end CFSG.HardMathSupport.Dickson.DefCharOuter
