module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainStabNormalizer
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CensusSU7Rank

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

theorem false_of_rank_survivor {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    (J : Subgroup (StatedSU (2 * 3 + 1) (2 ^ 1) K))
    (ψ : hypSU h 3 1 ≃* StatedSU (2 * 3 + 1) (2 ^ 1) K)
    (hJ : J = (flagStabilizer h 3 1 {2}).map ψ.toMonoidHom)
    (hZ : (hypScalars h 3 1).map ψ.toMonoidHom =
      (StatedScalars (Fin (2 * 3 + 1)) K).subgroupOf (StatedSU (2 * 3 + 1) (2 ^ 1) K))
    (hrank : ∀ A : Subgroup (StatedSU (2 * 3 + 1) (2 ^ 1) K), A ≤ J →
      CFSG.Open.IsElemAbelian 3 A →
      A ⊓ (StatedScalars (Fin (2 * 3 + 1)) K).subgroupOf (StatedSU (2 * 3 + 1) (2 ^ 1) K) = ⊥ →
      ∀ j : ℕ, Nat.card A = 3 ^ j → j ≤ 3) : False := by
  obtain ⟨A, hAle, ⟨hAcomm, hA3⟩, hAcard, hAbot⟩ := exists_elemAbelian_rank_four h
  have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
  have h1 : A.map ψ.toMonoidHom ≤ J := hJ ▸ Subgroup.map_mono hAle
  have h2 : CFSG.Open.IsElemAbelian 3 (A.map ψ.toMonoidHom) := by
    refine ⟨isMulCommutative_iff.mpr fun x y => ?_, ?_⟩
    · obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      apply Subtype.ext
      show (x : StatedSU (2 * 3 + 1) (2 ^ 1) K) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul]
      have : (⟨a, ha⟩ : A) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := isMulCommutative_iff.mp hAcomm _ _
      exact congrArg (fun t : A => ψ.toMonoidHom (t : hypSU h 3 1)) this
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA3 a ha, map_one]
  have h3 : A.map ψ.toMonoidHom ⊓
      (StatedScalars (Fin (2 * 3 + 1)) K).subgroupOf (StatedSU (2 * 3 + 1) (2 ^ 1) K) = ⊥ := by
    rw [← hZ, ← Subgroup.map_inf_eq _ _ _ hinj, hAbot, Subgroup.map_bot]
  have h4 : Nat.card (A.map ψ.toMonoidHom) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hinj, hAcard]
  have := hrank _ h1 h2 h3 4 h4
  omega

theorem hBA_core {K : Type} [Field K] [Finite K] [CharP K 2] {r ε f : ℕ}
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 4 ≤ 2 * r + ε) (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (J : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K))
    (S₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K))
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤ J) (hJ : J ≠ ⊤)
    (Dt : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) (hDtJ : Dt ≤ J) (hDt : ⁅Dt, Dt⁆ = Dt)
    (d : StatedSU (2 * r + ε) (2 ^ f) K) (hd : d ∈ Dt)
    (hds : (d : GL (Fin (2 * r + ε)) K) ∉ StatedScalars (Fin (2 * r + ε)) K)
    (hd3 : (d : GL (Fin (2 * r + ε)) K) ^ 3 ∈ StatedScalars (Fin (2 * r + ε)) K)
    (hfree : ∀ H : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), ⁅H, H⁆ = H →
      (∀ w ∈ H, Commute w d) → H = ⊥)
    (hcyc : ∀ V : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), V ≤ J → ⁅V, V⁆ = V →
      ∀ A : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), A ≤ V → IsPGroup 3 A →
        IsCyclic (A.map (QuotientGroup.mk' (Subgroup.center (StatedSU (2 * r + ε) (2 ^ f) K)))))
    (hrank : ∀ A : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), A ≤ J →
      CFSG.Open.IsElemAbelian 3 A →
      A ⊓ (StatedScalars (Fin (2 * r + ε)) K).subgroupOf (StatedSU (2 * r + ε) (2 ^ f) K) = ⊥ →
      ∀ j : ℕ, Nat.card A = 3 ^ j → j ≤ 3)
    (Ũ : Subgroup (GL (Fin (2 * r + ε)) K))
    (hUiso : ∀ u ∈ Ũ, ∀ x y : Fin (2 * r + ε) → K,
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε)
        ((u : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ x)
        ((u : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ y) =
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε) x y)
    (hUthree : ∀ u ∈ Ũ, ∃ k : ℕ, u ^ 3 ^ k = 1)
    (hUnorm : ∀ u ∈ Ũ, ∀ y y' : StatedSU (2 * r + ε) (2 ^ f) K,
      (y' : GL (Fin (2 * r + ε)) K) = u * y * u⁻¹ → (y ∈ J ↔ y' ∈ J))
    (hUcomm : ∀ u ∈ Ũ, ∀ x ∈ Dt,
      u * (x : GL (Fin (2 * r + ε)) K) * u⁻¹ * (x : GL (Fin (2 * r + ε)) K)⁻¹ ∈
        StatedScalars (Fin (2 * r + ε)) K) :
    ∀ u ∈ Ũ, ∀ u' ∈ Ũ, u * u' = u' * u := by
  obtain ⟨hf1, I, ψ, hIne, hIsub, hJI, hZψ, s, m, k₀, W', hW0, hs, hlt, -, -, -, -, -, -, hm, htab, hcsd⟩ :=
    chainStabData_of_normalizer hr hε hn hK hf J S₀ hNJ hJ Dt hDtJ hDt d hd hds hd3 hfree hcyc Ũ
      hUiso hUthree hUnorm hUcomm
  subst hf1
  have hm2 : m ≤ 2 := by
    by_contra hm2
    obtain ⟨rfl, rfl, rfl⟩ := htab.eq_last_of_not_le_two hm2
    exact false_of_rank_survivor _ J ψ hJI hZψ hrank
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  intro u hu u' hu'
  have key := ChainStabData.mul_comm_of_finrank_le hW0 hlt hs hcsd hK4 (hm ▸ hm2)
    ⟨glToLin _ K u, u, hu, rfl⟩ ⟨glToLin _ K u', u', hu', rfl⟩
  exact glToLin_injective (by simpa using congrArg Subtype.val key)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
