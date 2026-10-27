module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA7

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Eight2

theorem mul_conj_comm_of_index_two {G : Type*} [Group G] {S H : Subgroup G} {p : G}
    (hidx : (H.subgroupOf S).index = 2) (hpS : p ∈ S) (hpH : p ∈ H)
    (hpc : ∀ w ∈ S, w ∈ H → p * w = w * p) (hpp : p * p = 1) {u : G} (hu : u ∈ S)
    {v : G} (hv : v ∈ S) : p * (u * p * u⁻¹) * v = v * (p * (u * p * u⁻¹)) := by
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  have hconj : ∀ {g w : G}, g ∈ S → w ∈ S → w ∈ H → g * w * g⁻¹ ∈ H := by
    intro g w hg hwS hwH
    exact mem_subgroupOf.mp (hnorm.conj_mem ⟨w, hwS⟩ (mem_subgroupOf.mpr hwH) ⟨g, hg⟩)
  by_cases huH : u ∈ H
  · rw [← hpc u hu huH, mul_inv_cancel_right, hpp, one_mul, mul_one]
  have hq : ∀ w ∈ S, w ∈ H → u * p * u⁻¹ * w = w * (u * p * u⁻¹) := by
    intro w hwS hwH
    have h1 := hconj (inv_mem hu) hwS hwH
    rw [inv_inv] at h1
    have h2 := hpc _ (mul_mem (mul_mem (inv_mem hu) hwS) hu) h1
    calc u * p * u⁻¹ * w = u * (p * (u⁻¹ * w * u)) * u⁻¹ := by group
      _ = u * ((u⁻¹ * w * u) * p) * u⁻¹ := by rw [h2]
      _ = w * (u * p * u⁻¹) := by group
  have huu : u * u ∈ H := mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx ⟨u, hu⟩)
  have hpq : p * (u * p * u⁻¹) = (u * p * u⁻¹) * p := (hq p hpS hpH).symm
  have h3 : p * (u * u) = (u * u) * p := hpc _ (mul_mem hu hu) huu
  have heu : u * (p * (u * p * u⁻¹)) = p * (u * p * u⁻¹) * u := by
    calc u * (p * (u * p * u⁻¹)) = (u * p * u⁻¹) * ((u * u) * p * u⁻¹) := by group
      _ = (u * p * u⁻¹) * (p * (u * u) * u⁻¹) := by rw [h3]
      _ = (u * p * u⁻¹) * p * u := by group
      _ = p * (u * p * u⁻¹) * u := by rw [← hpq]
  by_cases hvH : v ∈ H
  · rw [mul_assoc, hq v hv hvH, ← mul_assoc, hpc v hv hvH, mul_assoc]
  have huv : u⁻¹ * v ∈ H := by
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨u⁻¹, inv_mem hu⟩)
      (b := ⟨v, hv⟩)).mpr ⟨fun h2 => absurd (by simpa using inv_mem (mem_subgroupOf.mp h2)) huH,
        fun h2 => absurd (mem_subgroupOf.mp h2) hvH⟩
    exact mem_subgroupOf.mp h1
  have huvS : u⁻¹ * v ∈ S := mul_mem (inv_mem hu) hv
  have h4 : p * (u * p * u⁻¹) * (u⁻¹ * v) = (u⁻¹ * v) * (p * (u * p * u⁻¹)) := by
    rw [mul_assoc, hq _ huvS huv, ← mul_assoc, hpc _ huvS huv, mul_assoc]
  calc p * (u * p * u⁻¹) * v = p * (u * p * u⁻¹) * u * (u⁻¹ * v) := by group
    _ = u * (p * (u * p * u⁻¹) * (u⁻¹ * v)) := by rw [← heu]; group
    _ = u * ((u⁻¹ * v) * (p * (u * p * u⁻¹))) := by rw [h4]
    _ = v * (p * (u * p * u⁻¹)) := by group

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

theorem ab_comm_of_mem_S0 {w : X} (hw : w ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y) :
    c.s.h.a * c.b * w = w * (c.s.h.a * c.b) := by
  have htw : c.s.t * w * c.s.t⁻¹ ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y :=
    (mem_normalizer_iff.mp c.s.t_norm w).mp hw
  have h1 := c.Z.hzS _ (mem_inf.mp htw).1
  calc c.s.h.a * c.b * w = c.s.t⁻¹ * c.Z.z * c.s.t * w := by rw [c.hzb]
    _ = c.s.t⁻¹ * (c.Z.z * (c.s.t * w * c.s.t⁻¹)) * c.s.t := by group
    _ = c.s.t⁻¹ * ((c.s.t * w * c.s.t⁻¹) * c.Z.z) * c.s.t := by rw [h1]
    _ = w * (c.s.t⁻¹ * c.Z.z * c.s.t) := by group
    _ = w * (c.s.h.a * c.b) := by rw [c.hzb]

theorem b_mem_upperP_two_of_relIndex_eq_two
    (hidx : (c.s.h.secG0 c.s.y).relIndex c.s.h.S = 2) : c.b ∈ c.s.h.upperP 2 := by
  have hidx' : ((c.s.h.secG0 c.s.y).subgroupOf c.s.h.S).index = 2 := hidx
  have haa : c.s.h.a * c.s.h.a = 1 := Six.a_mul_a_self c.s.h
  have haS : c.s.h.a ∈ c.s.h.S := c.s.h.P_le_S c.s.h.a_mem_P
  have hbS : c.b ∈ c.s.h.S := c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y c.hbB)
  have hbP : c.b ∈ c.s.h.P := c.s.B0_le_P c.hbB
  have hba : c.b * c.s.h.a = c.s.h.a * c.b := c.s.h.comm_a hbS
  have hpS : c.s.h.a * c.b ∈ c.s.h.S := mul_mem haS hbS
  have hpH : c.s.h.a * c.b ∈ c.s.h.secG0 c.s.y :=
    mul_mem (Hyp52.a_mem_secG0 c.s.secCond.Q_le) (le_normalizer c.hbB)
  have hpP : c.s.h.a * c.b ∈ c.s.h.P := mul_mem c.s.h.a_mem_P hbP
  have hpp : c.s.h.a * c.b * (c.s.h.a * c.b) = 1 := by
    calc c.s.h.a * c.b * (c.s.h.a * c.b) = c.s.h.a * (c.b * c.s.h.a) * c.b := by group
      _ = 1 := by rw [hba, ← mul_assoc, haa, one_mul, c.hbb]
  have hpc : ∀ w ∈ c.s.h.S, w ∈ c.s.h.secG0 c.s.y → c.s.h.a * c.b * w = w * (c.s.h.a * c.b) :=
    fun w hwS hwH => c.ab_comm_of_mem_S0 (mem_inf.mpr ⟨hwS, hwH⟩)
  have hkey : ∀ s ∈ c.s.h.S, s * (c.s.h.a * c.b) * s⁻¹ = c.s.h.a * c.b ∨
      s * (c.s.h.a * c.b) * s⁻¹ = c.s.h.a * c.b * c.s.h.a := by
    intro s hs
    have he : c.s.h.a * c.b * (s * (c.s.h.a * c.b) * s⁻¹) ∈ zpowers c.s.h.a := by
      rw [← c.s.C_eq]
      refine mem_inf.mpr ⟨mul_mem hpP (Six.conj_mem_P c.s.h hs hpP),
        mem_centralizer_iff.mpr fun v hv => ?_⟩
      exact (mul_conj_comm_of_index_two hidx' hpS hpH hpc hpp hs hv).symm
    have hq : s * (c.s.h.a * c.b) * s⁻¹ =
        c.s.h.a * c.b * (c.s.h.a * c.b * (s * (c.s.h.a * c.b) * s⁻¹)) := by
      rw [← mul_assoc (c.s.h.a * c.b) (c.s.h.a * c.b), hpp, one_mul]
    rcases Six.eq_one_or_eq_a he with h1 | h1
    · left
      rw [hq, h1, mul_one]
    · right
      rw [hq, h1]
  have haZ : c.s.h.a ∈ c.s.h.upperS 1 :=
    c.s.h.mem_upperS_one.mpr ⟨haS, fun s hs => (c.s.h.comm_a hs).symm⟩
  refine mem_inf.mpr ⟨c.s.h.mem_upperS_succ.mpr ⟨hbS, fun s hs => ?_⟩, hbP⟩
  have hsa : s * c.s.h.a * s⁻¹ = c.s.h.a := by
    rw [c.s.h.comm_a hs, mul_inv_cancel_right]
  have hsb : s * c.b * s⁻¹ = c.s.h.a * (s * (c.s.h.a * c.b) * s⁻¹) := by
    calc s * c.b * s⁻¹ = s * (c.s.h.a * (c.s.h.a * c.b)) * s⁻¹ := by
          rw [← mul_assoc c.s.h.a c.s.h.a c.b, haa, one_mul]
      _ = (s * c.s.h.a * s⁻¹) * (s * (c.s.h.a * c.b) * s⁻¹) := by group
      _ = c.s.h.a * (s * (c.s.h.a * c.b) * s⁻¹) := by rw [hsa]
  have hcomm : ⁅c.b, s⁆ = c.b * (s * c.b * s⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rcases hkey s hs with h1 | h1
  · have h2 : s * c.b * s⁻¹ = c.b := by
      rw [hsb, h1, ← mul_assoc, haa, one_mul]
    rw [hcomm, h2, mul_inv_cancel]
    exact one_mem _
  · have h2 : s * c.b * s⁻¹ = c.s.h.a * c.b := by
      rw [hsb, h1, ← mul_assoc, ← mul_assoc, haa, one_mul, hba]
    have h3 : c.b * (c.s.h.a * c.b)⁻¹ = c.s.h.a := by
      rw [mul_inv_rev, mul_inv_cancel_left, inv_eq_of_mul_eq_one_right haa]
    rw [hcomm, h2, h3]
    exact haZ

end CtxA0

end Eight2

end CFSG.ComponentClassification.GSThmB
