module

public import CFSG.Blueprint.CatalogGenerators

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint
open scoped LinearAlgebra.Projectivization

variable (a : ℕ) (K : Type) [Field K]

@[expose] noncomputable def suzukiSElt (u v : K) : suzukiGroup a K :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiS a u v)
    (by rw [det_suzukiS]; exact one_ne_zero), Subgroup.subset_closure (Or.inl ⟨u, v, rfl⟩)⟩

@[expose] noncomputable def suzukiDElt (l : Kˣ) : suzukiGroup a K :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l)
    (by rw [det_suzukiD]; exact one_ne_zero), Subgroup.subset_closure (Or.inr (Or.inl ⟨l, rfl⟩))⟩

theorem coe_suzukiSElt (u v : K) :
    (((suzukiSElt a K u v : suzukiGroup a K) : Matrix.GeneralLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = suzukiS a u v :=
  rfl

theorem coe_suzukiDElt (l : Kˣ) :
    (((suzukiDElt a K l : suzukiGroup a K) : Matrix.GeneralLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = suzukiD a l :=
  rfl

@[expose] noncomputable def suzukiU : Subgroup (suzukiGroup a K) :=
  Subgroup.closure (Set.range fun p : K × K => suzukiSElt a K p.1 p.2)

@[expose] noncomputable def suzukiT : Subgroup (suzukiGroup a K) :=
  Subgroup.closure (Set.range (suzukiDElt a K))

@[expose] noncomputable def suzukiB : Subgroup (suzukiGroup a K) :=
  suzukiU a K ⊔ suzukiT a K

@[expose] noncomputable def suzukiLine (u v : K) : ℙ K (Fin 4 → K) :=
  Projectivization.mk K (![1, u, v, suzukiN a u v] : Fin 4 → K) fun h => by
    simpa using congrFun h 0

@[expose] noncomputable def suzukiInfty : ℙ K (Fin 4 → K) :=
  Projectivization.mk K (![0, 0, 0, 1] : Fin 4 → K) fun h => by
    simpa using congrFun h 3

@[expose] noncomputable def suzukiOmega : Set (ℙ K (Fin 4 → K)) :=
  Set.range (fun p : K × K => suzukiLine a K p.1 p.2) ∪ {suzukiInfty K}

theorem suzukiSElt_mem_suzukiU
    (u v : K) : suzukiSElt a K u v ∈ suzukiU a K :=
  Subgroup.subset_closure ⟨(u, v), rfl⟩

theorem suzukiDElt_mem_suzukiT
    (l : Kˣ) : suzukiDElt a K l ∈ suzukiT a K :=
  Subgroup.subset_closure ⟨l, rfl⟩

theorem suzukiU_le_suzukiB : suzukiU a K ≤ suzukiB a K := le_sup_left

theorem suzukiT_le_suzukiB : suzukiT a K ≤ suzukiB a K := le_sup_right

theorem suzukiInfty_mem_suzukiOmega : suzukiInfty K ∈ suzukiOmega a K :=
  Or.inr rfl

theorem suzukiLine_mem_suzukiOmega (u v : K) : suzukiLine a K u v ∈ suzukiOmega a K :=
  Or.inl ⟨(u, v), rfl⟩

end CFSG.LieType.Ree
