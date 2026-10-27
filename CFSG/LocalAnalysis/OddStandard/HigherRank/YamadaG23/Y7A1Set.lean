module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Cfg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Set5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57D
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev y7aX (c : Ctx7 G L) : Subgroup G :=
  normalizer (C1 c.e : Set G) ⊓ normalizer (V1 c.e : Set G)

abbrev y7aK (c : Ctx7 G L) : Subgroup G :=
  CFSG.GH74.GLS.centralizerSection (C1 c.e) (V1 c.e)

abbrev y7aY (c : Ctx7 G L) : Subgroup G :=
  normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)

theorem Ctx7.y7acfg (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    Y7ACfg c.s.fr.A (C0 c.e) (V1 c.e) c.s.fr.a₁ c.s.fr.b₁ c.s.fr.a₂ c.s.fr.b₂ c.s.fr.z c.s.t
      c.d :=
  ⟨c.toCtx5.y6cfg5 hH, c.hV, c.d_order⟩

theorem y7a_V1_le_M3 (c : Ctx7 G L) : V1 c.e ≤ M3 c.s := inf_le_right

theorem y7a_d_mem_M3 (c : Ctx7 G L) : c.d ∈ M3 c.s := by
  apply y7a_V1_le_M3 c
  rw [c.hV]
  exact Subgroup.subset_closure (by simp)

theorem y7a_M3_elemAbelian (c : Ctx7 G L) (hH : F33Hyp c.s c.e) : IsElemAbelian 2 (M3 c.s) :=
  y57_caseA c.toCtx5 hH (y7a_d_mem_M3 c)

theorem y7a_F_le_M3 (c : Ctx7 G L) : c.s.fr.F ≤ M3 c.s := le_sup_right

theorem y7a_card_M3 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) : Nat.card ↥(M3 c.s) = 64 := by
  have hrel := y54_M3_relIndex c.toCtx5 hH
  have hF : Nat.card ↥c.s.fr.F = 8 := by
    rw [(y54_F_isE3 hH).2]
    norm_num
  have hcard : Nat.card ↥(c.s.fr.F.subgroupOf (M3 c.s)) = Nat.card ↥c.s.fr.F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (y7a_F_le_M3 c)).toEquiv
  have h := Subgroup.index_mul_card (H := c.s.fr.F.subgroupOf (M3 c.s))
  have hidx : (c.s.fr.F.subgroupOf (M3 c.s)).index = 8 := hrel
  rw [hidx, hcard, hF] at h
  omega

theorem y7a_M3_le_X (c : Ctx7 G L) (hF : c.toCtx5.Facts5) : M3 c.s ≤ y7aX c := by
  obtain ⟨-, ⟨⟨hC3, -, hcomm⟩, -⟩⟩ := hF.2.2.1
  have hcommC1 : ⁅C1 c.e, C3 c.s⁆ ≤ C1 c.e :=
    hcomm.trans (sup_le_sup_right (s3_F_le_A c.s) (C0 c.e))
  haveI : IsMulCommutative ↥(M3 c.s) := by
    rcases hF.2.2.2.2.2.2 with ⟨-, hE⟩ | ⟨-, hMC, -⟩
    · exact hE.1
    · exact hMC
  have hconj : ∀ m ∈ M3 c.s, ∀ x ∈ C1 c.e, m * x * m⁻¹ ∈ C1 c.e := by
    intro m hm x hx
    have hM3C3 : M3 c.s ≤ C3 c.s := hC3 ▸ le_sup_left
    have hmC3 : m ∈ C3 c.s := hM3C3 hm
    have hcm : ⁅m, x⁆ ∈ C1 c.e := by
      refine hcommC1 ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hmC3 hx
    have he : m * x * m⁻¹ = ⁅m, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact (C1 c.e).mul_mem hcm hx
  intro m hm
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj m hm x hx
    · intro hx
      have h := hconj m⁻¹ ((M3 c.s).inv_mem hm) (m * x * m⁻¹) hx
      have he : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x := by group
      rwa [he] at h
  · have hfix : ∀ y ∈ M3 c.s, m * y * m⁻¹ = y := by
      intro y hy
      have hc := Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) hm hy
      calc m * y * m⁻¹ = y * m * m⁻¹ := by rw [hc]
        _ = y := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have hvM : v ∈ M3 c.s := (Subgroup.mem_inf.mp hv).2
      rw [hfix v hvM]
      exact hv
    · intro hv
      have hvM : m * v * m⁻¹ ∈ M3 c.s := (Subgroup.mem_inf.mp hv).2
      have hvM3 : v ∈ M3 c.s := by
        have he : m⁻¹ * (m * v * m⁻¹) * m = v := by group
        rw [← he]
        exact (M3 c.s).mul_mem ((M3 c.s).mul_mem ((M3 c.s).inv_mem hm) hvM) hm
      rw [← hfix v hvM3]
      exact hv

end CFSG.OddStandard.HigherRank.YamadaG23
