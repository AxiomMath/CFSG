module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Core

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

@[expose] def zCent (z : G) : ↥(centralizer ({z} : Set G)) :=
  ⟨z, Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]⟩

private lemma sec5b517_prod_coe {H : Subgroup G} (k : Fin 4 → H) :
    ((Sec5B517Prod k : H) : G) = Sec5B517Prod (fun i => (k i : G)) := rfl

theorem quad_subgroupOf (hq : Sec5B517Quad K z) {Hc : Subgroup G} (hK : ∀ i, K i ≤ Hc)
    (hz : z ∈ Hc) : Sec5B517Quad (fun i => (K i).subgroupOf Hc) (⟨z, hz⟩ : Hc) where
  comm i j hij a ha b hb := Subtype.ext (hq.comm i j hij (a : G) ha (b : G) hb)
  iso i := by
    obtain ⟨e⟩ := hq.iso i
    exact ⟨(Subgroup.subgroupOfEquivOfLe (hK i)).trans e⟩
  z_mem i := Subgroup.mem_subgroupOf.2 (hq.z_mem i)
  z_sq := Subtype.ext hq.z_sq
  z_ne h := hq.z_ne (congrArg Subtype.val h)

theorem q8_subgroupOf (hq : Sec5B517Quad K z) {Hc : Subgroup G} (hK : ∀ i, K i ≤ Hc)
    (hz : z ∈ Hc) :
    Sec5B517Q8 (quad_subgroupOf hq hK hz) = (Sec5B517Q8 hq).subgroupOf Hc := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff (quad_subgroupOf hq hK hz)).mp hx
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [sec5b517_prod_coe]
    exact (Sec5B517Q8.mem_iff hq).mpr
      ⟨fun i => (k i : G), fun i => ⟨(hk i).1, by simpa using congrArg Subtype.val (hk i).2⟩,
        rfl⟩
  · intro hx
    have hx' : (x : G) ∈ Sec5B517Q8 hq := hx
    obtain ⟨k, hk, hx'⟩ := (Sec5B517Q8.mem_iff hq).mp hx'
    refine (Sec5B517Q8.mem_iff (quad_subgroupOf hq hK hz)).mpr
      ⟨fun i => (⟨k i, hK i (hk i).1⟩ : Hc), ?_, ?_⟩
    · intro i
      exact ⟨Subgroup.mem_subgroupOf.2 (hk i).1, Subtype.ext (by simpa using (hk i).2)⟩
    · apply Subtype.ext
      rw [sec5b517_prod_coe, hx']

theorem le_centralizer_of_quad (hq : Sec5B517Quad K z) (i : Fin 4) :
    K i ≤ centralizer ({z} : Set G) := by
  intro u hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hq.z_comm hu).symm

end CFSG.OddStandard.SmallF3.Omega
