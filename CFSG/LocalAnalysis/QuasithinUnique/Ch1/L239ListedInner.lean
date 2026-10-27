module

public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.Blueprint
open scoped commutatorElement

section Projection

variable {G : Type} [Group G] {L : Subgroup G} {z zL : G}

theorem proj_comm_iff (h : IsProjectionOn z zL L) {x : G} (hx : x ∈ L) :
    x * zL = zL * x ↔ x * z = z * x := by
  have h1 := h.2 x hx
  constructor
  · intro hc
    have : z⁻¹ * x * z = x := by
      rw [h1]
      calc zL⁻¹ * x * zL = zL⁻¹ * (x * zL) := by group
        _ = zL⁻¹ * (zL * x) := by rw [hc]
        _ = x := by group
    calc x * z = z * (z⁻¹ * x * z) := by group
      _ = z * x := by rw [this]
  · intro hc
    have : zL⁻¹ * x * zL = x := by
      rw [← h1]
      calc z⁻¹ * x * z = z⁻¹ * (x * z) := by group
        _ = z⁻¹ * (z * x) := by rw [hc]
        _ = x := by group
    calc x * zL = zL * (zL⁻¹ * x * zL) := by group
      _ = zL * x := by rw [this]

theorem proj_inf_centralizer_eq (h : IsProjectionOn z zL L) :
    L ⊓ Subgroup.centralizer ({zL} : Set G) = L ⊓ Subgroup.centralizer ({z} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact and_congr_right fun hx => proj_comm_iff h hx

theorem proj_ne_one (h : IsProjectionOn z zL L) (hcomm : ⁅L, Subgroup.zpowers z⁆ = L)
    (hL : L ≠ ⊥) : zL ≠ 1 := by
  intro h1
  apply hL
  rw [← hcomm]
  refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun x hx g hg => ?_)
  have hxz : x * z = z * x := (proj_comm_iff h hx).mp (by rw [h1, mul_one, one_mul])
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr ((Commute.zpow_right hxz k).eq)

theorem proj_mem_centralizer_inf (h : IsProjectionOn z zL L) {S : Subgroup G}
    (hz : z ∈ Subgroup.centralizer (S : Set G)) :
    zL ∈ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  exact (proj_comm_iff h hp.2).mpr (Subgroup.mem_centralizer_iff.mp hz p hp.1)

theorem proj_sq_eq_one (h : IsProjectionOn z zL L) (hz2 : z ^ 2 = 1)
    (hZ : Subgroup.center ↥L = ⊥) : zL ^ 2 = 1 := by
  have hz2' : z * z = 1 := by rw [← sq, hz2]
  have hzinv : z⁻¹ * z⁻¹ = 1 := by rw [← mul_inv_rev, hz2', inv_one]
  have hcom : ∀ x ∈ L, x * zL ^ 2 = zL ^ 2 * x := by
    intro x hx
    have hy : zL⁻¹ * x * zL ∈ L := L.mul_mem (L.mul_mem (L.inv_mem h.1) hx) h.1
    have e1 := h.2 (zL⁻¹ * x * zL) hy
    have e2 := h.2 x hx
    have e3 : z⁻¹ * (zL⁻¹ * x * zL) * z = x := by
      rw [← e2]
      calc z⁻¹ * (z⁻¹ * x * z) * z = (z⁻¹ * z⁻¹) * x * (z * z) := by group
        _ = x := by rw [hzinv, hz2']; group
    rw [e3] at e1
    have e4 : zL ^ 2 * (zL⁻¹ * (zL⁻¹ * x * zL) * zL) = x * zL ^ 2 := by simp only [sq]; group
    have e5 : zL ^ 2 * (zL⁻¹ * (zL⁻¹ * x * zL) * zL) = zL ^ 2 * x :=
      congrArg (fun w => zL ^ 2 * w) e1.symm
    exact e4.symm.trans e5
  have hmem : (⟨zL ^ 2, L.pow_mem h.1 2⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcom g g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end Projection

section Cases

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_isSimpleGroup {K : Type*} [Group K] [Group.IsPerfect K]
    (hs : IsSimpleGroup K) : Subgroup.center K = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have := hs.toNontrivial
    have hc : IsMulCommutative K := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ Subgroup.center K := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.1 ha b).symm
    exact Group.IsPerfect.not_isMulCommutative (G := K) hc

theorem inf_eq_centralizer_of_l33 (hl33 : L239L33Overgroups) {L M : Subgroup G} {z zL : G}
    (hq : CFSG.IsQuasisimple ↥L) (hmodel : StatedClassicalModel ↥L .PSL 3 3 1)
    (hproj : IsProjectionOn z zL L) (hz2 : z ^ 2 = 1) (hcomm : ⁅L, Subgroup.zpowers z⁆ = L)
    (hLM : ¬ L ≤ M) (hCz : Subgroup.centralizer ({z} : Set G) ≤ M) (hML : CharTwo (L ⊓ M)) :
    L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G) := by
  have hL0 : L ≠ ⊥ := fun h => hLM (h ▸ bot_le)
  have : Group.IsPerfect ↥L := hq.1
  have hsimple : IsSimpleGroup ↥L :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L 3 3 1 hmodel).2
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isSimpleGroup hsimple
  have hC : L ⊓ Subgroup.centralizer ({zL} : Set G) ≤ L ⊓ M := by
    rw [proj_inf_centralizer_eq hproj]
    exact inf_le_inf_left L hCz
  exact hl33 G L zL hmodel hproj.1 (proj_sq_eq_one hproj hz2 hZ) (proj_ne_one hproj hcomm hL0) (L ⊓ M)
    inf_le_left hC (fun h => hLM (inf_eq_left.mp h)) hML

theorem inf_eq_centralizer_of_m11 (hm11 : L239M11Overgroups) {L M : Subgroup G} {z zL : G}
    (hmodel : Nonempty (↥L ≃* NativeSporadic.Carrier .M11)) (hZ : Subgroup.center ↥L = ⊥)
    (hproj : IsProjectionOn z zL L) (hz2 : z ^ 2 = 1) (hcomm : ⁅L, Subgroup.zpowers z⁆ = L)
    (hLM : ¬ L ≤ M) (hCz : Subgroup.centralizer ({z} : Set G) ≤ M) :
    L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G) := by
  have hL0 : L ≠ ⊥ := fun h => hLM (h ▸ bot_le)
  have hC : L ⊓ Subgroup.centralizer ({zL} : Set G) ≤ L ⊓ M := by
    rw [proj_inf_centralizer_eq hproj]
    exact inf_le_inf_left L hCz
  exact hm11 G L zL hmodel hproj.1 (proj_sq_eq_one hproj hz2 hZ) (proj_ne_one hproj hcomm hL0) (L ⊓ M)
    inf_le_left hC (fun h => hLM (inf_eq_left.mp h))

theorem inf_eq_centralizer_of_l42 (hl42 : L239L42Overgroups) {L M S : Subgroup G} {z zL : G}
    (hmodel : StatedClassicalModel ↥L .PSL 4 2 1) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hSL : IsSylowTwoOf (S ⊓ L) L)
    (hout : ∃ s ∈ S, InducesOuter s L) (hSM : S ≤ M) (hzS : z ∈ Subgroup.centralizer (S : Set G))
    (hproj : IsProjectionOn z zL L) (hcomm : ⁅L, Subgroup.zpowers z⁆ = L) (hLM : ¬ L ≤ M)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ M) :
    L ⊓ M = L ⊓ Subgroup.centralizer ({zL} : Set G) := by
  have hL0 : L ≠ ⊥ := fun h => hLM (h ▸ bot_le)
  have hC : L ⊓ Subgroup.centralizer ({zL} : Set G) ≤ L ⊓ M := by
    rw [proj_inf_centralizer_eq hproj]
    exact inf_le_inf_left L hCz
  have hSX : S ≤ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hSN hs, Subgroup.le_normalizer (hSM hs)⟩
  exact hl42 G L S zL hmodel hS2 hSN hSL hout hproj.1 (proj_ne_one hproj hcomm hL0)
    (proj_mem_centralizer_inf hproj hzS) (L ⊓ M) inf_le_left hSX hC (fun h => hLM (inf_eq_left.mp h))

theorem inf_eq_sylow_of_psl2 (hl2p : L239Sylow2PSL2) {L M S : Subgroup G} {p : ℕ}
    (hp : Ch1.IsFermatOrMersennePrime p) (hp7 : 7 < p) (hmodel : StatedClassicalModel ↥L .PSL 2 p 1)
    (hSL : IsSylowTwoOf (S ⊓ L) L) (hSM : S ≤ M) (hLM : ¬ L ≤ M) : L ⊓ M = S ⊓ L := by
  have hle : S ⊓ L ≤ L ⊓ M := le_inf inf_le_right (inf_le_left.trans hSM)
  rcases hl2p G L (S ⊓ L) p hp hp7 hmodel hSL (L ⊓ M) hle inf_le_left with h | h
  · exact h
  · exact absurd (inf_eq_left.mp h) hLM

end Cases

end CFSG.QuasithinUnique.Vol2Native.L239
