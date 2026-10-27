module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem fusionIsBenderGroup_of_stated_psl_two {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel X .PSL 2 2 f) : fusionIsBenderGroup X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Or.inl ⟨f, hf, ⟨e.trans
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f (by omega) hK)⟩⟩

theorem fusionIsBenderGroup_of_stated_psu_three {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel X .PSU 3 2 f) : fusionIsBenderGroup X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
  exact Or.inr (Or.inl ⟨f, hf, ⟨e'.trans
    (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)⟩⟩)

end CFSG.QuasithinUnique.K1
