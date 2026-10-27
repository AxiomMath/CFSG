module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Open

variable {Q Q' : Type} [Group Q] [Group Q']

theorem subgroupOf_pCoreOf {p : ℕ} {A B : Subgroup Q} (hAB : A ≤ B) :
    (pCoreOf p A).subgroupOf B = (CFSG.pCore p ↥(A.subgroupOf B)).map (A.subgroupOf B).subtype := by
  have hφ : CFSG.pCore p ↥A =
      (CFSG.pCore p ↥(A.subgroupOf B)).map (Subgroup.subgroupOfEquivOfLe hAB).toMonoidHom :=
    (CFSG.pCore_map_iso p (Subgroup.subgroupOfEquivOfLe hAB)).symm
  have hpc : pCoreOf p A = (CFSG.pCore p ↥A).map A.subtype := by
    unfold pCoreOf
    try with_reducible rfl
  ext ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, hpc, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [hφ, Subgroup.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    refine Subgroup.mem_map.mpr ⟨w, hw, ?_⟩
    subst hwz
    apply Subtype.ext
    exact hzy
  · intro hmem
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hmem
    refine ⟨(Subgroup.subgroupOfEquivOfLe hAB) w, ?_, ?_⟩
    · rw [hφ]
      exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    · have hv : ((w : ↥B) : Q) = y := congrArg Subtype.val hwy
      exact hv

theorem pCoreOf_map_subgroupOf {p : ℕ} {A B : Subgroup Q} {A' B' : Subgroup Q'}
    (e : ↥B ≃* ↥B') (he : (A.subgroupOf B).map e.toMonoidHom = A'.subgroupOf B')
    (hAB : A ≤ B) (hA'B' : A' ≤ B') :
    ((pCoreOf p A).subgroupOf B).map e.toMonoidHom = (pCoreOf p A').subgroupOf B' := by
  let ψ : ↥(A.subgroupOf B) ≃* ↥(A'.subgroupOf B') :=
    (e.subgroupMap (A.subgroupOf B)).trans (MulEquiv.subgroupCongr he)
  have hcomp : e.toMonoidHom.comp (A.subgroupOf B).subtype =
      (A'.subgroupOf B').subtype.comp ψ.toMonoidHom :=
    MonoidHom.ext fun x => rfl
  rw [subgroupOf_pCoreOf hAB, subgroupOf_pCoreOf hA'B', Subgroup.map_map, hcomp,
    ← CFSG.pCore_map_iso p ψ, Subgroup.map_map]

end CFSG.HardMathSupport.Cooperstein.Proving

end
