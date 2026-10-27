module

public import CFSG.LieType.SeitzGeneration.HeisTorusUDefs
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalInvolution.Phan

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem ug84_isCoordBlockOn_blockMat {m : ℕ} (i : Fin m) (A : Matrix (Fin 2) (Fin 2) K) :
    IsCoordBlockOn (Fin.castSucc i) (Fin.succ i) (blockMat (m + 1) (i : ℕ) A) := by
  have hz : ∀ c : Fin (m + 1), c ≠ Fin.castSucc i → c ≠ Fin.succ i →
      ∀ x : Fin 2, blockSel K (m + 1) 2 (i : ℕ) c x = 0 := by
    intro c hc1 hc2 x
    rw [blockSel_apply, if_neg]
    intro hx
    fin_cases x
    · exact hc1 (Fin.ext (by simpa using hx))
    · exact hc2 (Fin.ext (by simpa [Fin.val_succ, add_comm] using hx))
  intro a b hab
  rw [blockMat, Matrix.add_apply, Matrix.one_apply]
  rcases hab with ⟨ha1, ha2⟩ | ⟨hb1, hb2⟩
  · simp [Matrix.mul_apply, hz a ha1 ha2]
  · simp [Matrix.mul_apply, hz b hb1 hb2]

theorem unitarySU_le_of_blocks (h : UnitaryFieldData ℓ f K) (hq : 4 ≤ ℓ ^ f) {n : ℕ}
    (hn : 2 ≤ n) (M : Subgroup (GL (Fin n) K))
    (hM : ∀ a b : Fin n, a ≠ b → ∀ g ∈ unitarySU ℓ f K n,
      IsCoordBlockOn a b (g : Matrix (Fin n) (Fin n) K) → g ∈ M) :
    unitarySU ℓ f K n ≤ M := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  let ε : Su K ℓ f (m + 1) ≃* unitarySU ℓ f K (m + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK (m + 1))
  have hgen : ⨆ i : Fin m, (ε.toMonoidHom.comp (blockEmb2 K ℓ f m i)).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) hK (by omega) m
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [MonoidHom.range_comp] using h2
  have hle : (⨆ i : Fin m, (ε.toMonoidHom.comp (blockEmb2 K ℓ f m i)).range) ≤
      M.comap (unitarySU ℓ f K (m + 1)).subtype := by
    refine iSup_le fun i => ?_
    rintro _ ⟨x, rfl⟩
    exact hM (Fin.castSucc i) (Fin.succ i) Fin.castSucc_lt_succ.ne _
      (ε (blockEmb2 K ℓ f m i x)).2
      (ug84_isCoordBlockOn_blockMat i ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
  rw [hgen] at hle
  exact fun g hg => hle (Subgroup.mem_top ⟨g, hg⟩)

end CFSG.LieType.SeitzGeneration
