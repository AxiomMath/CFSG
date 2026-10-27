module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End5a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End7a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End7b

public section

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

theorem false_of_psl2_even {Y : Type} [Group Y] [Finite Y] (hlayer : goldschmidtLayer Y = ⊤)
    (hZ : Subgroup.center Y = ⊥) (D : Sylow 2 Y) {W : Fin 4 → Subgroup Y}
    (hP : IsPlanes (D : Subgroup Y) W)
    (hperm : ∀ y : Y, (∀ x ∈ (D : Subgroup Y), y * x * y⁻¹ ∈ (D : Subgroup Y)) →
      ∀ i, ∃ j, ∀ w ∈ W i, y * w * y⁻¹ ∈ W j)
    {J : Subgroup Y} (hJ : IsComponentOf J ⊤) {f : ℕ} (hf : f = 4 ∨ f = 6 ∨ f = 8)
    (e : ↥J ≃* PSL(2, GaloisField 2 f)) : False := by
  classical
  have hf2 : 2 ≤ f := by rcases hf with rfl | rfl | rfl <;> norm_num
  let p : ℕ := if f = 6 then 7 else 5
  have hp : p.Prime := by
    rcases hf with rfl | rfl | rfl <;> simp [p] <;> norm_num
  have hpf : p ∣ 2 ^ f - 1 := by
    rcases hf with rfl | rfl | rfl <;> simp [p] <;> norm_num
  have hp57 : p = 5 ∨ p = 7 := by
    rcases hf with rfl | rfl | rfl <;> simp [p]
  haveI : J.Normal := CFSG.GH74.GLS.Th2.P412.GoldY.component_normal hlayer hJ
  obtain ⟨d, hdJ, hdJinf, hdp, u, hu, hne⟩ :=
    exists_p_element_of_component D (f := f) (p := p) hf2 hp hpf e
  have hdD : ∀ x ∈ (D : Subgroup Y), d * x * d⁻¹ ∈ (D : Subgroup Y) :=
    conj_mem_of_mem_component hlayer hZ hJ D hdJ hdJinf
  have hcent : ∀ x ∈ (D : Subgroup Y), d * x * d⁻¹ = x :=
    centralizes_of_pow_centralizes hP d hdD (hperm d hdD) hp57
      (fun x _ => by rw [hdp]; simp)
  exact hne (hcent u hu.1)

end CFSG.OddStandard.SmallF3.Omega
