module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveMain

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open scoped MatrixGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.Chevalley.E6GraphLevi CFSG.Open
  CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem exists_elemAbelian_conj_le_six
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h5 : 5 ∣ ℓ ^ f + 1) :
    ∃ V : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 5 V ∧ Nat.card V = 5 ^ 6 ∧
      V ≤ frameTorusGroup σ.toRingHom ∧
      ∀ A : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 5 A →
        ∃ g : twistedE6RootGroup K σ, A.map (MulAut.conj g).toMonoidHom ≤ V := by
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    subst hf0
    have hcard : Nat.card K = 1 := by simpa using hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, hK'⟩
  haveI : CharP K ℓ := hU.charP
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  obtain ⟨ψ₁, hk₁, -, hX₁⟩ := twE6SU6Cover_five K σ ℓ f hℓ hf hK hσ 5 le_rfl h5
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨e₂⟩ := exists_mulEquiv_sl2_su2 (K := K) hK σ.toRingHom hσ'
  let θ : SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K)) × unitarySL σ.toRingHom ≃*
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K 2 ×
        CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K 6 :=
    e₂.prodCongr (unitarySLEquivStated hK hσ')
  obtain ⟨Ew, hEwe, hEwc, hEwle⟩ := exists_elemAbelian_six hℓ hf K hK σ hσ h5
  have hEwr : Ew ≤ ψ₁.range := hEwle.trans (le_sup_left.trans hX₁)
  obtain ⟨Ew', hEw'e, hEw'm, hEw'c⟩ := exists_lift_of_le_range ψ₁ hk₁ hEwr hEwe
  have hord := five_hord hℓ hf hK σ hσ h5
  refine ⟨Ew, hEwe, hEwc, hEwle, ?_⟩
  intro A hAe
  obtain ⟨g, E', hE'e, hE'm⟩ := exists_conj_lift_elemAbelian ψ₁ hk₁ hord A hAe
  obtain ⟨c, hc⟩ :=
    exists_conj_le_toral_of_equiv hU h5 θ Ew' hEw'e (hEw'c.trans hEwc) E' hE'e
  refine ⟨(ψ₁ c)⁻¹ * g, ?_⟩
  rintro y ⟨e, he, rfl⟩
  have h1 : g * e * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
    ⟨e, he, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  rw [← hE'm] at h1
  obtain ⟨y', hy', hy'e⟩ := h1
  obtain ⟨z, hz, hzy⟩ := hc hy'
  have hzψ : ψ₁ z ∈ Ew := hEw'm ▸ ⟨z, hz, rfl⟩
  have hψ : g * e * g⁻¹ = ψ₁ c * ψ₁ z * (ψ₁ c)⁻¹ := by
    rw [← hy'e, ← hzy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hconj : (MulAut.conj ((ψ₁ c)⁻¹ * g)).toMonoidHom e = ψ₁ z := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, _root_.mul_inv_rev, inv_inv]
    calc (ψ₁ c)⁻¹ * g * e * (g⁻¹ * ψ₁ c) = (ψ₁ c)⁻¹ * (g * e * g⁻¹) * ψ₁ c := by group
      _ = ψ₁ z := by rw [hψ]; group
  rw [hconj]
  exact hzψ

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive
