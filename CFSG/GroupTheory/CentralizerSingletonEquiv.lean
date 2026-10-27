module

public import CFSG.GroupTheory.CentralizerMapMulEquiv

public section

namespace CFSG.GroupTheory

@[expose] def centralizerSingletonMulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {x : G} {y : H} (h : e x = y) :
    ↥(Subgroup.centralizer ({x} : Set G)) ≃* ↥(Subgroup.centralizer ({y} : Set H)) :=
  (e.subgroupMap _).trans
    (MulEquiv.subgroupCongr ((centralizer_singleton_map_mulEquiv e x).trans (by rw [h])))

@[simp] theorem coe_centralizerSingletonMulEquiv_apply {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {x : G} {y : H} (h : e x = y) (z : ↥(Subgroup.centralizer ({x} : Set G))) :
    (centralizerSingletonMulEquiv e h z : H) = e z :=
  rfl

end CFSG.GroupTheory
