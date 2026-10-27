module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenE11
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEData
import CFSG.ClassicalInvolution.Q3.TL3S8BE2
import CFSG.ClassicalInvolution.Q3.Q3T6OpenTL3
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEEtaY

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section End

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem TightStd3.exists_wSet_le_normal (ht : TightStd3 K z) (S : Sylow 2 G) :
    ∃ W ∈ WSet (CoreAssembly.conjClass K), W ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
  CFSG.ClassicalInvolution.Q3.TightMemStd.exists_wSet_le_normal ht.toTL3 S

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem inf_centralizer_t_le (h11b : C19_11b3) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({t} : Set G) ≤
      W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  rintro a ⟨⟨haS, haR⟩, hat⟩
  refine ⟨hd.mem_W_of_comm_U h11b haS hat fun u hu => ?_, haR⟩
  exact (Subgroup.mem_centralizer_iff.mp haR u ⟨hd.hWS hu.2, hu.1⟩).symm

theorem isCyclic_inf_centralizer_t (h11b : C19_11b3) :
    IsCyclic ↥((S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({t} : Set G)) := by
  have hcyc := hd.isCyclic_inf_sec19Y
  rw [hd.toSec19Data3.inf_sec19Y_eq] at hcyc
  exact Subgroup.isCyclic_of_le (hd.inf_centralizer_t_le h11b)

theorem inv_mul_mem_centralizer_t (hSW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G))
    {x y : G} (hxS : x ∈ (S : Subgroup G)) (hyS : y ∈ (S : Subgroup G))
    (hx : x ∉ Subgroup.centralizer ({t} : Set G)) (hy : y ∉ Subgroup.centralizer ({t} : Set G)) :
    x⁻¹ * y ∈ Subgroup.centralizer ({t} : Set G) :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.inv_mul_mem_centralizer_t hd.toTL3 hSW hxS hyS hx hy

end Sec19DataT3

theorem c19_E2Prime3_of (h11b : C19_11b3) : C19_E2Prime3 := by
  intro G _ _ _ K z S W hd
  obtain ⟨W₀, hW₀, hW₀S, hSW₀⟩ := hd.tight.exists_wSet_le_normal S
  have hd₀ : Sec19Data3 K z S W₀ := { hd with hW := hW₀, hWS := hW₀S }
  obtain ⟨L, t, V, hdT⟩ := hd₀.exists_sec19DataT3
  refine ⟨_, hdT.isCyclic_inf_centralizer_t h11b, inf_le_left, fun x hx y hy hxC hyC => ?_⟩
  have hxt : x ∉ Subgroup.centralizer ({t} : Set G) := fun h => hxC ⟨hx, h⟩
  have hyt : y ∉ Subgroup.centralizer ({t} : Set G) := fun h => hyC ⟨hy, h⟩
  exact ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy,
    hdT.inv_mul_mem_centralizer_t hSW₀ hx.1 hy.1 hxt hyt⟩

end End

end CFSG.ClassicalInvolution.Q3.Q3T6
