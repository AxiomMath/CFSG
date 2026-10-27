module

public import CFSG.ClassicalInvolution.Q3.TL3LeafClass

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

namespace TightDatum

variable {R : Subgroup G} {S : Sylow 2 R} {t : G} (h : TightDatum R S t)
include h

omit [Finite G] in
theorem le_centralizer_core : tightCore R ≤ Subgroup.centralizer ({t} : Set G) :=
  (tightCore_le R).trans h.cent

theorem normalizer_core_eq :
    Subgroup.normalizer (tightCore R : Set G) = Subgroup.centralizer ({t} : Set G) := by
  refine le_antisymm (fun x hx => ?_) h.le_normalizer_core
  have hconj : conjSub x (tightCore R) = tightCore R := mem_normalizer_iff_conjSub_eq.mp hx
  have h1 : IsUniqueInvolution (tightCore R) (x * t * x⁻¹) := by
    simpa only [hconj] using h.isUniqueInvolution_core.conj x
  have h2 : x * t * x⁻¹ = t := (h1.eq h.isUniqueInvolution_core)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * t = x * t * x⁻¹ * x := by group
    _ = t * x := by rw [h2]

omit [Finite G] in
theorem normal_core :
    ((tightCore R).subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_centralizer_core).mpr h.le_normalizer_core

theorem sylow_core : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := by
  have d : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S h.quat h.mem h.order h.cent h.normal h.twoGroup
  refine ⟨?_, d.S_two, fun V hVK hV2 hle => d.sylow.2.2 V (hVK.trans (tightCore_le R)) hV2 hle⟩
  intro s hs
  exact Subgroup.subset_closure ⟨d.S_le hs, d.S_two.to_le (Subgroup.zpowers_le.mpr hs)⟩

theorem nonabelian : ∃ x y : G, x * y ≠ y * x := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.sylow_nonabelian S
  exact ⟨x, y, fun hc => hxy (Subtype.ext hc)⟩

end TightDatum

structure TightSylowStd (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G) : Prop where
  datum : TightDatum R S t
  q8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)
  edgeless : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R))
  notFour : ¬ TwoSubgroupsFourGenerated (genFittingFStar G)
  hST : (S : Subgroup R).map R.subtype ≤ (T : Subgroup G)
  hTt : (T : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G)

namespace TightSylowStd

variable {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G} (h : TightSylowStd R S t T)
include h

theorem isUniqueInvolution : IsUniqueInvolution (tightCore R) t :=
  h.datum.isUniqueInvolution_core

omit [Finite G] in
theorem le_centralizer_core : tightCore R ≤ Subgroup.centralizer ({t} : Set G) :=
  h.datum.le_centralizer_core

theorem normalizer_core_eq :
    Subgroup.normalizer (tightCore R : Set G) = Subgroup.centralizer ({t} : Set G) :=
  h.datum.normalizer_core_eq

theorem hypOmegaGen : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.datum.hypOmegaGen

theorem partIHypG : Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) := h.datum.partIHypG

theorem twinSet_eq :
    twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R} :=
  h.datum.twinSet_eq

theorem aEmpty : ∀ J ∈ CoreAssembly.conjClass (tightCore R),
    AEmpty (CoreAssembly.conjClass (tightCore R)) J := h.datum.aEmpty

theorem sylow_core : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) :=
  h.datum.sylow_core

theorem hTN : (T : Subgroup G) ≤ Subgroup.normalizer (tightCore R : Set G) := by
  rw [h.normalizer_core_eq]
  exact h.hTt

omit [Finite G] in
theorem mem_T : t ∈ (T : Subgroup G) := h.hST h.datum.mem

theorem nonabelian : ∃ x y : G, x * y ≠ y * x := h.datum.nonabelian

end TightSylowStd

theorem TightSylowStd.exists_of_sylowCase {R : Subgroup G} {S : Sylow 2 R} {t : G}
    (hd : TightDatum R S t) (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2))
    (he : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)))
    (hn : ¬ TwoSubgroupsFourGenerated (genFittingFStar G)) {T : Subgroup G}
    (hT : IsSylow2Of T
      (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)))
    (hTG : IsSylow2Of T ⊤) :
    ∃ T' : Sylow 2 G, (T' : Subgroup G) = T ∧ TightSylowStd R S t T' := by
  classical
  set S0 : Subgroup G := (S : Subgroup R).map R.subtype with hS0
  have d : OddByQuat R S0 t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  let T' : Sylow 2 G :=
    { toSubgroup := T
      isPGroup' := hTG.2.1
      is_maximal' := fun {Q} hQ hle => hTG.2.2 Q le_top hQ hle }
  have hS0N : S0 ≤ Subgroup.normalizer (S0 : Set G) := Subgroup.le_normalizer
  have hST : S0 ≤ T := by
    have hsup : IsPGroup 2 ↥(T ⊔ S0) :=
      hT.2.1.to_sup_of_normal_right' d.S_two hT.1
    have heq := hT.2.2 (T ⊔ S0) (sup_le hT.1 hS0N) hsup le_sup_left
    rw [← heq]
    exact le_sup_right
  have hTt : T ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (S0 : Set G) := hT.1 hx
    have hxt : x * t * x⁻¹ ∈ S0 := (Subgroup.mem_normalizer_iff.mp hxN t).mp d.t_mem
    have hord : orderOf (x * t * x⁻¹) = 2 := by
      have := (MulAut.conj x).orderOf_eq t
      rwa [MulAut.conj_apply, hd.order] at this
    have h2 : x * t * x⁻¹ = t := d.unique _ hxt hord
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [h2]
  exact ⟨T', rfl, ⟨hd, hq, he, hn, hST, hTt⟩⟩

end CFSG.ClassicalInvolution.Q3
