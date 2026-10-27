module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z23
public import CFSG.ClassicalInvolution.Asc77.AscT7Z16

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace C22P

set_option linter.unusedSectionVars false

section ZStar

variable {G : Type} [Group G] [Finite G]

theorem commutes_of_mem_zStar {Y : Subgroup G} {w : G} (hwY : w ∈ Y) (hw2 : w * w = 1)
    (hOw : ∀ n ∈ oddCoreOf Y, n * w = w * n) (hwZ : w ∈ zStarOf Y) :
    ∀ y ∈ Y, y * w = w * y := by
  intro y hy
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  obtain ⟨x₀, hx₀, hx₀t⟩ := Subgroup.mem_map.mp hwZ
  have hcen := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hx₀)
    (QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩)
  have hx₀' : x₀ = ⟨w, hwY⟩ := Subtype.ext hx₀t
  rw [hx₀'] at hcen
  have hmk : QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ *
      QuotientGroup.mk' N₀ ⟨w, hwY⟩ *
      (QuotientGroup.mk' N₀ ⟨y⁻¹, Subgroup.inv_mem _ hy⟩)⁻¹ =
      QuotientGroup.mk' N₀ ⟨w, hwY⟩ := by
    rw [hcen, mul_inv_cancel_right]
  have ho := T7L.mem_oddCore_of_mk_conj hwY hwY ⟨y⁻¹, Subgroup.inv_mem _ hy⟩ hmk
  simp only [inv_inv] at ho
  set o : G := w⁻¹ * (y * w * y⁻¹) with hodef
  have hot : o * w = w * o := hOw o ho
  have hyt : y * w * y⁻¹ = w * o := by simp only [hodef]; group
  have hsq : (w * o) * (w * o) = 1 := by
    rw [← hyt]
    calc (y * w * y⁻¹) * (y * w * y⁻¹) = y * (w * w) * y⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  have hoo : o * o = 1 := by
    have h1 : (w * o) * (w * o) = o * o := by
      calc (w * o) * (w * o) = w * (o * w) * o := by group
        _ = w * (w * o) * o := by rw [hot]
        _ = (w * w) * (o * o) := by group
        _ = o * o := by rw [hw2, one_mul]
    exact h1.symm.trans hsq
  have ho1 : o = 1 := T7Y.eq_one_of_sq_eq_one_of_mem_odd (oddCoreOf_odd_natCard _) ho hoo
  rw [ho1, mul_one] at hyt
  exact mul_inv_eq_iff_eq_mul.mp hyt

end ZStar

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem oddCore_layer_eq_bot (hodd : T7Z.OddCenterClassical) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : ConjInvariant Ω) {c z : G} (hc1 : c ≠ 1)
    (hα : alphaOf (Subgroup.closure ({c, z} : Set G)) = ⊥)
    (hL : LayerOrthType p f Ω c 6 true) (hzY : z ∈ exactLayer Ω c) (hz2 : z * z = 1)
    (hmove : ¬ ∀ y ∈ exactLayer Ω c, y * z = z * y) :
    classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥ := by
  have hcomm : ∀ n ∈ oddCoreOf (exactLayer Ω c), n * z = z * n := fun n hn =>
    T7Z.oddCore_commutes_of_alphaOf hΩ hc1 (A := Subgroup.closure ({c, z} : Set G))
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hα hn
  refine T7Z.oddCore_exactLayer_eq_bot hodd hp2 hq (Or.inr rfl) hL hzY hcomm ?_
  intro hZ
  exact hmove (commutes_of_mem_zStar hzY hz2 hcomm hZ)

end Layer

section Exact

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem oddCore_le_centralizer_S (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥) :
    oddCoreOf K ≤ Subgroup.centralizer (K : Set G) := by
  have hst := hs.stand
  have hu1 := (T7S22.mul_ne_one_of_twins hst.hyp hst.mem hs.hK'.1 hs.hne.symm hs.hz hs.hu₁.1
    hs.hu₂.1 hs.hu₂.2)
  have htw := ExactD.TwinPair.of_twinSet hst.odd hst.five hst.hyp hst.mem hs.hz hs.hK' hs.hne.symm
  exact htw.oddCoreOf_le_centralizer_of_alphaOf_bot (Subgroup.mul_mem_sup hs.hu₁.1 hs.hu₂.1)
    hs.sq_12 hu1.1 hu1.2 hα

theorem exactMembers_S (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥)
    (hOc : classicalInvolutionOddCore ↥(exactLayer Ω (u₁ * u₂)) = ⊥) {d : ℕ} {ε : Bool}
    (hY : LayerOrthType p f Ω (u₁ * u₂) d ε) : ExactMembers Ω :=
  T7Z.exactMembers_of_layerOrth hs.stand (oddCore_le_centralizer_S hs hα) hs.sq_12 hOc hY

theorem commutes_of_twins (hst : AscStand p f Ω K) {z : G} (hz : IsUniqueInvolution K z)
    {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ twinSet Ω K) (hM₂ : M₂ ∈ twinSet Ω K) (hne : M₁ ≠ M₂)
    (hex : ExactMembers Ω) : Commutes M₁ M₂ := by
  have hz₁ : IsUniqueInvolution M₁ z := isUniqueInvolution_of_mem_twinSet hz hM₁
  have hM₂' : M₂ ∈ twinSet Ω M₁ := by
    rw [twinSet_eq_of_mem_twinSet hz hM₁]
    exact hM₂
  have d := ExactD.TwinPair.of_twinSet hst.odd hst.five hst.hyp hM₁.1 hz₁ hM₂' hne
  have h := d.comm_le
  rw [oddCoreOf_eq_bot_of_exact hex hM₁.1, bot_inf_eq, le_bot_iff] at h
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅M₁, M₂⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

end Exact

end C22P

end CFSG.ClassicalInvolution.Asc77
