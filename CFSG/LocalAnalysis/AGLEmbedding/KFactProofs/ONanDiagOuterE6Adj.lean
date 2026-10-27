module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Torus
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem mem_torusGroup_of_conj_mem_unipotentPairAut
    {τ : Tag} {K : Type} [Field K] {g : adjointGroup τ K}
    (hA : MulAut.conj g ∈ unipotentPairAut τ K) : (g : ModGL τ K) ∈ torusGroup τ K := by
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf posUnipotent_le_adjointGroup hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf negUnipotent_le_adjointGroup hV
  have hB : (g : ModGL τ K) ∈ borelGroup τ K := by
    rw [← (borel_self_normalizers τ K).1]
    exact Subgroup.mem_inf.2 ⟨g.2, hNU⟩
  have hB' : (g : ModGL τ K) ∈ oppositeBorel τ K := by
    rw [← oppositeBorel_normalizer τ K]
    exact Subgroup.mem_inf.2 ⟨g.2, hNV⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  rw [← (opposite_Borel_intersection τ K w₀ hw₀).2.2.1]
  exact Subgroup.mem_inf.2 ⟨hB, hB'⟩

theorem hasDiagOuterThree_adjointE6
    {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    HasDiagOuterThree (adjointGroup Tag.E6 K) := by
  obtain ⟨μ, hμ⟩ := exists_not_cube h3
  let i₀ : Fin Tag.E6.rank := ⟨0, by decide⟩
  let a : Fin Tag.E6.rank → Kˣ := Pi.mulSingle i₀ μ
  refine ⟨rootDiagAut Tag.E6 K a, fun k hk => ?_⟩
  obtain ⟨g, hg⟩ := hk
  have hpow : rootDiagAut Tag.E6 K a ^ 2 ^ k = rootDiagAut Tag.E6 K (a ^ 2 ^ k) :=
    (map_pow (rootDiagAutHom Tag.E6 K) a (2 ^ k)).symm
  have hA : MulAut.conj g ∈ unipotentPairAut Tag.E6 K := by
    rw [hg, hpow, rootDiagAut_eq_exactNormalAut]
    exact exactNormalAut_mem _ _ _
  obtain ⟨b, hb, z, hz⟩ :=
    exists_cube_of_mem_torusGroup (mem_torusGroup_of_conj_mem_unipotentPairAut hA)
  have hconj : rootDiagAut Tag.E6 K b = rootDiagAut Tag.E6 K (a ^ 2 ^ k) := by
    rw [← hpow, ← hg]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [coe_rootDiagAut, MulAut.conj_apply, hb]
    rfl
  have hba : b = a ^ 2 ^ k := rootDiagAutHom_injective hconj
  have ha : e6Invariant K a = μ := by
    rw [e6Invariant_apply, Finset.prod_eq_single i₀]
    · have hw : e6Weight i₀ = 1 := rfl
      simp [a, hw]
    · intro l _ hl
      simp [a, Pi.mulSingle_eq_of_ne hl]
    · simp
  rw [hba, map_pow, ha] at hz
  obtain ⟨y, hy⟩ := isCube_of_pow_eq_cube (Nat.Coprime.pow_left k (by norm_num)) hz.symm
  exact hμ y hy

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
