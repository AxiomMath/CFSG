module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four3
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.LieType.AlgebraicGroups.KernelRootDescent

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.CatLeafProof

section


theorem centralizer_le_d8Chain_of_adjEmb_eq {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Field L] [Algebra K L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Lˣ}
    (hζo : orderOf ζ = p) {lam : ZMod p} (hlam : lam * lam = -1)
    {g : ModGL .E8 L}
    (hgM : g ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char))
    {x : adjointGroup .E8 K}
    (hx : adjEmb .E8 K L x = g * rootDiagUnit .E8 (d6TorsionChar p ζ lam) * g⁻¹) :
    Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) ≤ ⨆ k, e8D8Chain K k := by
  intro c hc
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  set a : Fin Tag.E8.rank → Lˣ := d6TorsionChar p ζ lam with ha
  set d : ModGL .E8 L := rootDiagUnit Tag.E8 a with hd
  have hM8 : g ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d8Char) :=
    (sup_le_sup_left (rootSpan_mono kernelRoots_d4d4Char_subset_d8Char) _) hgM
  have hxd : g⁻¹ * adjEmb .E8 K L x * g = d := by
    rw [hx]; group
  set y : ModGL .E8 L := g⁻¹ * adjEmb .E8 K L c * g with hy
  have hyA : y ∈ adjointGroup .E8 L := by
    refine mul_mem (mul_mem (inv_mem ?_) (adjEmb_mem c)) ?_
    · exact (sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _)) hM8
    · exact (sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _)) hM8
  have hyd : y * d = d * y := by
    have hcomm : adjEmb .E8 K L x * adjEmb .E8 K L c = adjEmb .E8 K L c * adjEmb .E8 K L x := by
      rw [← map_mul, ← map_mul, hcx]
    calc y * d = g⁻¹ * (adjEmb .E8 K L c * adjEmb .E8 K L x) * g := by
          rw [hy, ← hxd]; group
      _ = g⁻¹ * (adjEmb .E8 K L x * adjEmb .E8 K L c) * g := by rw [hcomm]
      _ = d * y := by rw [hy, ← hxd]; group
  have hyC : y ∈ toralCentralizer Tag.E8 L a :=
    Subgroup.mem_inf.2 ⟨hyA, Subgroup.mem_centralizer_singleton_iff.2 hyd⟩
  have hy8 : y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d8Char) :=
    toralCentralizer_d6TorsionChar_le_sup_rootSpan hp hp2 hζo hlam hyC
  have hmem : adjEmb .E8 K L c ∈
      torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d8Char) := by
    have heq : adjEmb .E8 K L c = g * y * g⁻¹ := by rw [hy]; group
    rw [heq]
    exact mul_mem (mul_mem hM8 hy8) (inv_mem hM8)
  have hdes : (c : ModGL .E8 K) ∈
      torusGroup .E8 K ⊔ rootSpan .E8 K (kernelRoots d8Char) := by
    refine mem_torus_sup_rootSpan_of_baseChangeGL_mem (algebraMap K L) d8Char c.2 ?_
    simpa only [adjEmb_apply] using hmem
  have hfin : (c : ModGL .E8 K) ∈ d8Target K :=
    (sup_le (torusGroup_le_d8Chain K) rootSpan_kernelRoots_d8Char_le_d8Chain) hdes
  obtain ⟨q, hq, hqeq⟩ := hfin
  have hqc : q = c := Subtype.ext hqeq
  rwa [hqc] at hq

end

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
