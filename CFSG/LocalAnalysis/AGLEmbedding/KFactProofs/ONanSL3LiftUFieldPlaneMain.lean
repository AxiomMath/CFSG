module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldDef
import CFSG.ClassicalInvolution.Phan.Standard
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldPlaneTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalInvolution.Phan

section Blocks

variable {K : Type} [Field K] {m i : ℕ}

private theorem blockMat_mem_subfield {K₀ : Subfield K} {A : Matrix (Fin 2) (Fin 2) K}
    (hA : ∀ a b, A a b ∈ K₀) (a b : Fin m) : blockMat m i A a b ∈ K₀ := by
  rw [blockMat_apply]
  split_ifs with hab
  · exact hA _ _
  · rw [Matrix.one_apply]
    split_ifs
    · exact K₀.one_mem
    · exact K₀.zero_mem

private theorem blockMat_isDiag {A : Matrix (Fin 2) (Fin 2) K} (hA : A.IsDiag) :
    (blockMat m i A).IsDiag := by
  intro a b hab
  rw [blockMat_apply]
  split_ifs with hh
  · refine hA fun hne => hab (Fin.ext ?_)
    have := congrArg Fin.val hne
    simp only at this
    omega
  · simp [hab]

end Blocks

theorem subfieldDiagGen_of_four_le
    {p f f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hf : f = 3 * f₀) (hq₀ : 4 ≤ p ^ f₀) (K₀ : Subfield K)
    (hK₀ : Nat.card K₀ = p ^ (2 * f₀)) : SubfieldDiagGen h K₀ := by
  intro H hK hD
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hq2 : p ^ f ≠ 2 := by
    have h1 : (p ^ f₀) ^ 3 ≤ p ^ f := by rw [← pow_mul, hf, mul_comm]
    have h2 : 4 ^ 3 ≤ (p ^ f₀) ^ 3 := Nat.pow_le_pow_left hq₀ 3
    omega
  let ε₂ : Su K p f 2 ≃* unitarySU p f K 2 :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq 2)
  let ε₃ : Su K p f 3 ≃* unitarySU p f K 3 :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq 3)
  let φ : Fin 2 → (unitarySU p f K 2 →* unitarySU p f K 3) := fun i =>
    ε₃.toMonoidHom.comp ((blockEmb2 K p f 2 i).comp ε₂.symm.toMonoidHom)
  have hφmat : ∀ (i : Fin 2) (g : unitarySU p f K 2),
      (((φ i g : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        blockMat 3 i (((g : unitarySU p f K 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    fun _ _ => rfl
  have hplane : ∀ i : Fin 2, ∀ g : unitarySU p f K 2, φ i g ∈ H := by
    intro i
    have htop : H.comap (φ i) = ⊤ := by
      refine eq_top_of_subfield_diag_two h hf hq₀ K₀ hK₀ (H.comap (φ i)) ?_ ?_
      · intro g hg
        exact hK _ fun a b => by
          rw [hφmat]
          exact blockMat_mem_subfield hg a b
      · intro g hg
        exact hD _ (by rw [hφmat]; exact blockMat_isDiag hg)
    intro g
    have : g ∈ H.comap (φ i) := htop ▸ Subgroup.mem_top g
    exact this
  have hgen : ⨆ i : Fin 2, (ε₃.toMonoidHom.comp (blockEmb2 K p f 2 i)).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := p) (f := f) h.card_eq_sq hq2 2
    have h2 := congrArg (Subgroup.map ε₃.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε₃.surjective] at h2
    simpa [MonoidHom.range_comp] using h2
  have hle : ⨆ i : Fin 2, (ε₃.toMonoidHom.comp (blockEmb2 K p f 2 i)).range ≤ H := by
    refine iSup_le fun i => ?_
    rintro _ ⟨A, rfl⟩
    have := hplane i (ε₂ A)
    simpa [φ] using this
  rw [hgen] at hle
  exact top_unique hle

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
