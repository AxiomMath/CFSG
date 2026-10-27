module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

theorem signalizerThreeOn_of_signalizerTrivialOn {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {K : Type} [Group K] [Finite K] (h : SignalizerTrivialOn p K) : SignalizerThreeOn p K := by
  intro T W hW hnorm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  refine h T W ?_ hnorm
  rw [hk]
  exact ((Nat.coprime_primes hp Nat.prime_three).2 hp3).pow_right k

theorem signalizerTrivialOn_of_model {p : ℕ} (hp : p.Prime) {M : Type} [Group M] [Finite M]
    {B₀ : Subgroup M} (hB₀ : IsPGroup p B₀)
    (h : ∀ V : Subgroup (MulAut M), Nat.Coprime p (Nat.card V) →
      (∀ b ∈ B₀, ∀ v ∈ V, MulAut.conj b * v * (MulAut.conj b)⁻¹ ∈ V) → V = ⊥)
    {K : Type} [Group K] [Finite K] (e : K ≃* M) : SignalizerTrivialOn p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro P W hW hnorm
  obtain ⟨T₀, hBT₀⟩ := hB₀.exists_le_sylow
  obtain ⟨Φ, hPT⟩ : ∃ Φ : K ≃* M, (P : Subgroup K).map Φ.toMonoidHom = (T₀ : Subgroup M) := by
    have hfs : Function.Surjective e.toMonoidHom := e.surjective
    set P' : Sylow p M := P.mapSurjective hfs with hP'
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P' T₀
    refine ⟨e.trans (MulAut.conj g), ?_⟩
    have h2 : ((g • P' : Sylow p M) : Subgroup M) =
        (P' : Subgroup M).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      rfl
    rw [hg, hP', Sylow.coe_mapSurjective, Subgroup.map_map] at h2
    exact h2.symm
  set ψ : MulAut K ≃* MulAut M := MulAut.congr Φ with hψ
  have hψc : ∀ x : K, ψ (MulAut.conj x) = MulAut.conj (Φ x) := by
    intro x
    ext a
    simp [hψ, MulAut.conj_apply]
  refine (Subgroup.map_eq_bot_iff_of_injective (f := ψ.toMonoidHom) W ψ.injective).1
    (h _ (by rwa [Subgroup.card_map_of_injective ψ.injective]) ?_)
  intro b hb v hv
  obtain ⟨x, hx, rfl⟩ : b ∈ (P : Subgroup K).map Φ.toMonoidHom := hPT ▸ hBT₀ hb
  obtain ⟨w, hw, rfl⟩ := hv
  refine ⟨MulAut.conj x * w * (MulAut.conj x)⁻¹, hnorm x hx w hw, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hψc]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
