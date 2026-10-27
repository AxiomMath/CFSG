module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Line
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.PlaneAssembly
public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Lattice
open scoped Matrix

theorem cert_good3 : ∀ c ∈ e7T3Certs, c.comps.map E7T3Comp.kind = [3] → c.Good := by
  decide +kernel


theorem e7SixLinesKind_3 :
    E7SixLinesKind [3] := by
  intro K _ _ ℓ f p _ _ L _ _ _ _ F hf hK hp hp3 hpf c E hE hEc hT y hy hy1 b hb cert hcert hker
    hkinds hσ0 k hk
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hgood := cert_good3 cert hcert hkinds
  have hinj : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  rcases hcc : cert.comps with _ | ⟨cm₀, _ | ⟨cm₁, rest⟩⟩
  · rw [hcc] at hkinds
    simp at hkinds
  · rw [hcc] at hkinds
    have hkind : cm₀.kind = 3 := by simpa using hkinds
    have hg₀ : cm₀.Good e7T3Word cert.w := hgood.1 cm₀ (by rw [hcc]; exact List.mem_singleton_self _)
    have hk₀ : cm₀.kind < 4 := by rw [hkind]; norm_num
    have hset := e7T3_rootSet_single hcc hk₀
    rw [hkind] at hset
    obtain ⟨hg, hact⟩ := e7T3_comp_eps hε F.hnW hg₀
    have hg' : (coxeterSystem Tag.E7).wordProd cm₀.u ∈
        parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7) := by
      rw [hkind] at hg
      exact hg
    have hcl := centralizer_le_hyperClosure_of_a5_line F hf hK hp hp3 hpf hE hEc hT hy hy1
      ((coxeterSystem Tag.E7).wordProd cert.w)
      (fun b' hb' => by
        have hbb : b' = b := hinj (hb'.trans hb.symm)
        rw [hbb, hker]
        exact hset)
      ⟨(coxeterSystem Tag.E7).wordProd cm₀.u, hg', fun α hα => by
        have h1 := hact α (by rw [hkind]; exact hα)
        rw [h1, hkind, weyl_smul_zsmul_pm _ hε]
        simp [e7T3Beta, permLattice_one]⟩
    exact hcl (Subgroup.mem_centralizer_singleton_iff.2 hk)
  · rw [hcc] at hkinds
    simp at hkinds

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
