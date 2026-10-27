module

public import CFSG.Quasithin.Recognition.G23TypeDefs
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G23Type
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem G23Two.conj_mem_fitting {M : Subgroup G} (hM : G23Two M) {g : G} (hg : g ∈ M)
    {v : G} (hv : v ∈ quasithinGenFitting M) : g * v * g⁻¹ ∈ quasithinGenFitting M := by
  obtain ⟨θ, _, hθk⟩ := hM.quot
  have hvM : v ∈ M := CFSG.Quasithin.quasithinGenFitting_le M hv
  have hmem : (⟨v, hvM⟩ : ↥M) ∈ θ.ker := by
    rw [hθk]
    exact Subgroup.mem_subgroupOf.mpr hv
  have hnorm : (⟨g, hg⟩ : ↥M) * ⟨v, hvM⟩ * (⟨g, hg⟩ : ↥M)⁻¹ ∈ θ.ker :=
    (inferInstance : θ.ker.Normal).conj_mem _ hmem _
  rw [hθk] at hnorm
  have h3 := Subgroup.mem_subgroupOf.mp hnorm
  simpa using h3

theorem G23Two.fitting_comm {M : Subgroup G} (hM : G23Two M) {x y : G}
    (hx : x ∈ quasithinGenFitting M) (hy : y ∈ quasithinGenFitting M) : x * y = y * x := by
  have hI : IsMulCommutative ↥(quasithinGenFitting M) := hM.elem.1
  have hc : Std.Commutative (fun a b : ↥(quasithinGenFitting M) => a * b) := inferInstance
  exact congrArg Subtype.val (hc.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem G23Two.inf_centralizer_fitting [Finite G] {M : Subgroup G} (hM : G23Two M) :
    M ⊓ Subgroup.centralizer (quasithinGenFitting M : Set G) = quasithinGenFitting M := by
  apply le_antisymm (CFSG.Quasithin.centralizer_quasithinGenFitting_le M)
  intro x hx
  refine ⟨CFSG.Quasithin.quasithinGenFitting_le M hx, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun h hh => G23Two.fitting_comm hM hh hx

end CFSG.GH74.QTGen4.Recog.G23
