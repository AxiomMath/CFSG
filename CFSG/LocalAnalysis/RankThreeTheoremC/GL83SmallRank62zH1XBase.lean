module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1YComp
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
import CFSG.Walter.AStar.Subnormal
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {f : ℕ} {X Q : Subgroup G}

abbrev k631aMk (f : ℕ) (X : Subgroup G) (x : G) (hx : x ∈ X) :
    ↥X ⧸ GLAPPrimeCore f ↥X :=
  QuotientGroup.mk' (GLAPPrimeCore f ↥X) ⟨x, hx⟩

omit [Finite G] in
theorem k631a_mem_core_iff {x : G} (hx : x ∈ X) :
    x ∈ GLAPPrimeCoreOf f X ↔ k631aMk f X x hx = 1 := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (QuotientGroup.eq_one_iff z).2 hz
  · intro h
    exact ⟨⟨x, hx⟩, (QuotientGroup.eq_one_iff _).1 h, rfl⟩

omit [Finite G] in
theorem k631a_mem_barX {K : Subgroup G} {z : ↥X ⧸ GLAPPrimeCore f ↥X} :
    z ∈ barX f X K ↔ ∃ (x : G) (hx : x ∈ X), x ∈ K ∧ k631aMk f X x hx = z := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x.2, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  · rintro ⟨x, hx, hxK, rfl⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.2 hxK, rfl⟩

omit [Finite G] in
theorem k631a_mk_mem_barX {K : Subgroup G} {x : G} (hx : x ∈ X) (hxK : x ∈ K) :
    k631aMk f X x hx ∈ barX f X K :=
  k631a_mem_barX.2 ⟨x, hx, hxK, rfl⟩

omit [Finite G] in
theorem k631a_mk_eq_iff {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    k631aMk f X x hx = k631aMk f X y hy ↔ x⁻¹ * y ∈ GLAPPrimeCoreOf f X := by
  have hxy : x⁻¹ * y ∈ X := X.mul_mem (X.inv_mem hx) hy
  rw [k631a_mem_core_iff hxy]
  have h1 : k631aMk f X (x⁻¹ * y) hxy = (k631aMk f X x hx)⁻¹ * k631aMk f X y hy := by
    show QuotientGroup.mk' (GLAPPrimeCore f ↥X) ((⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩) = _
    rw [map_mul, map_inv]
  rw [h1, inv_mul_eq_one]

omit [Finite G] in
theorem k631a_mk_mul {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    k631aMk f X (x * y) (X.mul_mem hx hy) = k631aMk f X x hx * k631aMk f X y hy :=
  map_mul (QuotientGroup.mk' (GLAPPrimeCore f ↥X)) ⟨x, hx⟩ ⟨y, hy⟩

omit [Finite G] in
theorem k631a_mk_inv {x : G} (hx : x ∈ X) :
    k631aMk f X x⁻¹ (X.inv_mem hx) = (k631aMk f X x hx)⁻¹ :=
  map_inv (QuotientGroup.mk' (GLAPPrimeCore f ↥X)) ⟨x, hx⟩

omit [Finite G] in
theorem k631a_mk_comm {x y : G} (hx : x ∈ X) (hy : y ∈ X) (hc : ⁅x, y⁆ ∈ X) :
    k631aMk f X ⁅x, y⁆ hc = ⁅k631aMk f X x hx, k631aMk f X y hy⁆ :=
  map_commutatorElement (QuotientGroup.mk' (GLAPPrimeCore f ↥X)) ⟨x, hx⟩ ⟨y, hy⟩

omit [Finite G] in
theorem k631a_comm_mem {x y : G} (hx : x ∈ X) (hy : y ∈ X) : ⁅x, y⁆ ∈ X := by
  rw [commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)

omit [Finite G] in
theorem k631a_mem_triv_iff {J : Subgroup G} (hJX : J ≤ X) {q : G} (hq : q ∈ X)
    (hqJ : q ∈ normalizer (J : Set G)) :
    q ∈ k631Triv (GLAPPrimeCoreOf f X) J ↔
      ∀ j ∈ barX f X J, k631aMk f X q hq * j = j * k631aMk f X q hq := by
  have hqO : q ∈ normalizer (GLAPPrimeCoreOf f X : Set G) := le_normalizer_glaPPrimeCoreOf f X hq
  refine ⟨fun ⟨_, _, hc⟩ j hj => ?_, fun hc => ⟨hqO, hqJ, fun j hj => ?_⟩⟩
  · obtain ⟨y, hyX, hyJ, rfl⟩ := k631a_mem_barX.1 hj
    have h1 := (k631a_mem_core_iff (k631a_comm_mem hq hyX)).1 (hc y hyJ)
    rw [k631a_mk_comm hq hyX] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · have hjX := hJX hj
    rw [k631a_mem_core_iff (k631a_comm_mem hq hjX), k631a_mk_comm hq hjX]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hc _ (k631a_mk_mem_barX hjX hj))

omit [Finite G] in
theorem k631a_isComponent_barX {J : Subgroup G} (hJ : GLAPComponent f X J) :
    IsComponent (barX f X J) :=
  (CFSG.isComponent_iff_open _).2 hJ.2.2.1

theorem k631a_normalized (h : k631aHyp f X Q) {J : Subgroup G} (hJ : GLAPComponent f X J) :
    Q ≤ normalizer (J : Set G) := by
  intro q hq
  have hqX : q ∈ X := h.le hq
  have hN := k631a_normalizes (k631a_bhyp_barX h) (k631a_isComponent_barX hJ)
    (k631a_mk_mem_barX (K := Q) hqX hq)
  exact mem_normalizer_of_barX_normalizes h.prime le_rfl hJ hqX (Subgroup.le_normalizer hqX) hN

theorem k631a_sylow_comp (h : k631aHyp f X Q) {J : Subgroup G} (hJ : GLAPComponent f X J) :
    ∃ P : Sylow f ↥J, (P : Subgroup J).map J.subtype = Q ⊓ J := by
  have := Fact.mk h.prime
  have hQ'p : IsPGroup f (Q.subgroupOf X) :=
    h.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
  let S : Sylow f ↥X := hQ'p.toSylow h.sylow
  have hJsn : (J.subgroupOf X).IsSubnormal := by
    have h1 := isSubnormal_comap' X.subtype hJ.2.1
    rw [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at h1
    exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h1
      Subgroup.IsSubnormal.top
  obtain ⟨P', hP'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hJsn
  let e : ↥(J.subgroupOf X) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJ.1
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P'.mapSurjective he, ?_⟩
  have hcomp : J.subtype.comp e.toMonoidHom = X.subtype.comp (J.subgroupOf X).subtype := by
    ext p
    rfl
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp, ← Subgroup.map_map, hP']
  rw [Subgroup.map_inf_eq _ _ X.subtype X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hJ.1]
  simp only [IsPGroup.toSylow_coe, S, Subgroup.map_subgroupOf_eq_of_le h.le]

end CFSG.LocalAnalysis.RankThreeTheoremC
