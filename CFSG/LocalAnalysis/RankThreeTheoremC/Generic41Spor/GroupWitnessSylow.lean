module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupWitness

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

theorem sylow_eq_map_conj {K : Type} [Group K] {p : ℕ} (g : K) (S₀ : Sylow p K) :
    ((g • S₀ : Sylow p K) : Subgroup K) = (S₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem TwoWitness.of_sylow_pred {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (Pr : Subgroup K → K → Prop)
    (hPr : ∀ (S : Subgroup K) (x g : K), Pr S x →
      Pr (S.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹))
    {S₀ : Sylow p K} {u₀ : K} (hu₀Pr : Pr (S₀ : Subgroup K) u₀) (h₀ : TwoWitness u₀)
    (horb : ∀ x ∈ (S₀ : Subgroup K), x ≠ 1 → Pr (S₀ : Subgroup K) x →
      ∃ n ∈ normalizer ((S₀ : Subgroup K) : Set K), n * u₀ * n⁻¹ = x)
    (S : Sylow p K) {u : K} (huS : u ∈ (S : Subgroup K)) (hu1 : u ≠ 1)
    (hu : Pr (S : Subgroup K) u) : TwoWitness u := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S₀ S
  have hSmap : (S : Subgroup K) = (S₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact sylow_eq_map_conj g S₀
  have hx : g⁻¹ * u * g ∈ (S₀ : Subgroup K) := by
    rw [hSmap] at huS
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 huS
    simpa [MulAut.conj_apply, mul_assoc] using hy
  have hx1 : g⁻¹ * u * g ≠ 1 := by
    intro h
    apply hu1
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hPrx : Pr (S₀ : Subgroup K) (g⁻¹ * u * g) := by
    have h1 := hPr (S : Subgroup K) u g⁻¹ hu
    have h2 : (S : Subgroup K).map (MulAut.conj g⁻¹).toMonoidHom = (S₀ : Subgroup K) := by
      rw [hSmap, Subgroup.map_map]
      conv_rhs => rw [← Subgroup.map_id (S₀ : Subgroup K)]
      congr 1
      ext x
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
        Function.comp_apply, MonoidHom.id_apply]
      group
    rw [h2] at h1
    simpa using h1
  obtain ⟨n, -, hn⟩ := horb _ hx hx1 hPrx
  have : u = (g * n) * u₀ * (g * n)⁻¹ := by
    have h3 : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [h3, ← hn]
    group
  rw [this]
  exact h₀.conj (g * n)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
