module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusModel
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusFamily
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthPlus

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section P145
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbedding.LeviBlock CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding TauCeti
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg


section LeviPlus2

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem block_decomp_D (hn : 3 ≤ n) {Y : Type} [Group Y]
    (π : spinGroup (quadPlus n F) →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center (spinGroup (quadPlus n F)))
    (A : Subgroup (spinGroup (quadPlus n F))) {J : Set (Fin n)}
    (hA : A ≤ Subgroup.normalizer ((leviM (plusDatum n F hn) J : Subgroup _) : Set _))
    (hJ : IsABlock J ∨ ∃ a, a + 3 ≤ n ∧ J = blkNodes n a) :
    ∃ E C : Subgroup (spinGroup (quadPlus n F)),
      E ≤ leviM (plusDatum n F hn) J ∧ C ≤ leviM (plusDatum n F hn) J ∧
      leviM (plusDatum n F hn) J ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧
      E ≤ Subgroup.normalizer (C : Set (spinGroup (quadPlus n F))) ∧
      A ≤ Subgroup.normalizer (E : Set (spinGroup (quadPlus n F))) ∧
      A ≤ Subgroup.normalizer (C : Set (spinGroup (quadPlus n F))) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) := by
  rcases hJ with ⟨ι, _, _, ch, hch, hcard⟩ | ⟨a, ha, rfl⟩
  · subst hch
    exact ablock_decomp hn ch π hker A hA hcard
  · obtain ⟨k, hk⟩ : ∃ k, a + k = n := ⟨n - a, by omega⟩
    have hk3 : 3 ≤ k := by omega
    refine decomp_of_chev π hker A _ hA (blkEquiv (F := F) hk hn hk3) ?_
    by_cases hk4 : 4 ≤ k
    · exact isChevComponent_spinPlus hk4
    · have : k = 3 := by omega
      subst this
      exact chev_spinPlus_three

theorem leviOb_spinPlus (m : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ m + 1)
    {Y : Type} [Group Y] (π : spinGroup (quadPlus (m + 1) F) →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center (spinGroup (quadPlus (m + 1) F)))
    (I : Set (Fin (m + 1))) :
    LeviOb (plusDatum (m + 1) F hn) (fun k => (torusD F hn k).range) π I := by
  classical
  obtain ⟨β, hβ, J, hGood⟩ := comb m hm I
  obtain ⟨hJI, hcov, hnonadj, hty⟩ := hGood
  have hct := plusDatum_isCTGroupDatum (K := F) hn (plusDatum_iSup_eq_top (m + 1) F hn)
  have hext := plusDatum_steinbergExtras (K := F) hn
  have hTn : ∀ b, (⨆ k, (torusD F hn k).range) ≤
      Subgroup.normalizer ((leviM (plusDatum (m + 1) F hn) (J b) : Subgroup _) : Set _) :=
    fun b => torus_le_normalizer_leviM (D := plusDatum (m + 1) F hn)
      (H := fun k => (torusD F hn k).range) (n := weylD F hn) (I := J b) hct
  exact leviOb_of_node_family hct hext π I J hJI hcov
    (fun b b' hbb' i hi j hj => rankOne_commute hn (hnonadj b b' hbb' i hi j hj).1
      (hnonadj b b' hbb' i hi j hj).2)
    (fun b => block_decomp_D hn π hker _ (hTn b) (hty b))

theorem orthPlusLeviOb : OrthPlusLeviOb := by
  intro n f F _ _ _ hadm hn hcard Y _ π hker I hI
  have h4 : 4 ≤ n := hadm.2.2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact leviOb_spinPlus m (by omega) hn π hker I

end LeviPlus2


end P145

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
