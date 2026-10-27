module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CSetup

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

private theorem mem_zpowers_of_sq_eq_one {z : G} (hz : z ^ 2 = 1) (x : G) :
    x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    rw [Subgroup.zpowers_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      exact Or.inr hy
    | one => exact Or.inl rfl
    | mul a b _ _ ha hb =>
      rcases ha with ha1 | haz
      · rcases hb with hb1 | hbz
        · left; rw [ha1, hb1, one_mul]
        · right; rw [ha1, hbz, one_mul]
      · rcases hb with hb1 | hbz
        · right; rw [haz, hb1, mul_one]
        · left; rw [haz, hbz, ← pow_two, hz]
    | inv a _ ha =>
      rcases ha with ha1 | haz
      · left; rw [ha1, inv_one]
      · right; rw [haz, inv_eq_of_mul_eq_one_left (by rw [← pow_two, hz])]
  · rintro (hx1 | hxz)
    · rw [hx1]; exact one_mem _
    · rw [hxz]; exact Subgroup.mem_zpowers z

theorem mem_Jg_iff_comm_mem (h : KleinPair t z) {g : G} (hg : g * z = z * g) :
    g ∈ Jg t z ↔ g * t * g⁻¹ * t⁻¹ ∈ zpowers z := by
  have hzp : ∀ x : G, x ∈ zpowers z ↔ x = 1 ∨ x = z :=
    fun x => mem_zpowers_of_sq_eq_one h.z_sq x
  have hgz : g * z * g⁻¹ = z := by rw [hg]; group
  have hgz' : g⁻¹ * z * g = z := by
    rw [show g⁻¹ * z = z * g⁻¹ from (Commute.inv_left (show Commute g z from hg)).eq]
    group
  constructor
  · intro hgJ
    have ht' : g * t * g⁻¹ ∈ Vtz t z := ((mem_normalizer_iff.mp hgJ) t).mp t_mem_Vtz
    rcases (mem_Vtz_iff h).mp ht' with h1 | ht | hz | htz
    · exfalso
      have : t = 1 := by
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h1]
          _ = 1 := by group
      exact h.t_ne this
    · rw [ht, mul_inv_cancel]
      exact one_mem _
    · exfalso
      have : t = z := by
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = g⁻¹ * z * g := by rw [hz]
          _ = z := hgz'
      exact h.tz_ne this
    · rw [htz]
      have hz' : (t * z) * t⁻¹ = z := by
        have htt : t * t = 1 := by rw [← pow_two, h.t_sq]
        rw [inv_eq_of_mul_eq_one_left htt]
        calc t * z * t = z * (t * t) := by rw [h.comm]; group
          _ = z := by rw [htt, mul_one]
      rw [hz']
      exact Subgroup.mem_zpowers z
  · intro hcomm
    have hcases : g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z := by
      rcases (hzp _).mp hcomm with hw | hw
      · left
        exact mul_inv_eq_one.mp hw
      · right
        have ha : g * t * g⁻¹ = z * t := mul_inv_eq_iff_eq_mul.mp hw
        exact ha.trans h.comm.symm
    have hgi : g⁻¹ * t * g = t ∨ g⁻¹ * t * g = t * z := by
      rcases hcases with hgt | hgt
      · left
        have hc := congrArg (fun x => g⁻¹ * x * g) hgt
        have hl : g⁻¹ * (g * t * g⁻¹) * g = t := by group
        rw [hl] at hc
        exact hc.symm
      · right
        have hc := congrArg (fun x => g⁻¹ * x * g) hgt
        have hl : g⁻¹ * (g * t * g⁻¹) * g = t := by group
        have hr : g⁻¹ * (t * z) * g = (g⁻¹ * t * g) * z := by
          rw [show g⁻¹ * (t * z) * g = (g⁻¹ * t * g) * (g⁻¹ * z * g) by group, hgz']
        rw [hl, hr] at hc
        have hz2 : z * z = 1 := by rw [← pow_two, h.z_sq]
        calc g⁻¹ * t * g = (g⁻¹ * t * g) * (z * z) := by rw [hz2, mul_one]
          _ = ((g⁻¹ * t * g) * z) * z := by group
          _ = t * z := by rw [← hc]
    have hgi_mem : g⁻¹ * t * g ∈ Vtz t z := by
      rcases hgi with h | h
      · rw [h]; exact t_mem_Vtz
      · rw [h]; exact mul_mem t_mem_Vtz z_mem_Vtz
    rw [Jg, mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rcases (mem_Vtz_iff h).mp hy with hy1 | hyt | hyz | hytz
      · rw [hy1]; simp
      · rcases hcases with hgt | hgt
        · rw [hyt, hgt]; exact t_mem_Vtz
        · rw [hyt, hgt]; exact mul_mem t_mem_Vtz z_mem_Vtz
      · rw [hyz, hgz]; exact z_mem_Vtz
      · rw [hytz]
        have hconj : g * (t * z) * g⁻¹ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
        rw [hconj, hgz]
        rcases hcases with hgt | hgt
        · rw [hgt]; exact mul_mem t_mem_Vtz z_mem_Vtz
        · rw [hgt, mul_assoc, ← pow_two, h.z_sq, mul_one]; exact t_mem_Vtz
    · intro hy
      rcases (mem_Vtz_iff h).mp hy with hy1 | hyt | hyz | hytz
      · have : y = 1 := by
          calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
            _ = g⁻¹ * 1 * g := by rw [hy1]
            _ = 1 := by group
        rw [this]; exact one_mem _
      · have : y = g⁻¹ * t * g := by
          calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
            _ = g⁻¹ * t * g := by rw [hyt]
        rw [this]; exact hgi_mem
      · have : y = z := by
          calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
            _ = g⁻¹ * z * g := by rw [hyz]
            _ = z := hgz'
        rw [this]; exact z_mem_Vtz
      · have : y = (g⁻¹ * t * g) * z := by
          calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
            _ = g⁻¹ * (t * z) * g := by rw [hytz]
            _ = (g⁻¹ * t * g) * z := by
              rw [show g⁻¹ * (t * z) * g = (g⁻¹ * t * g) * (g⁻¹ * z * g) by group, hgz']
        rw [this]; exact mul_mem hgi_mem z_mem_Vtz

theorem jData (c : Core1 E t z) :
    JData (czInv z c.klein.z_sq c.klein.z_ne) (⟨t, mem_Cz_of_comm c.klein.comm⟩ : ↥(Cz z))
      ((Rg t z).subgroupOf (Cz z)) ((Jg t z).subgroupOf (Cz z)) := by
  let t' : ↥(Cz z) := ⟨t, mem_Cz_of_comm c.klein.comm⟩
  have ht' : (t' : G) = t := rfl
  refine
    { t_sq := Subtype.ext (by simpa using c.klein.t_sq)
      t_not := ?_
      t_mem := ?_
      R_le := ?_
      mem_iff := ?_
      R_normal := ?_
      two := ?_
      quot := ?_ }
  · intro hmem
    have hz : t ∈ zpowers z :=
      (mem_zpowers_czInv z c.klein.z_sq c.klein.z_ne t').mp hmem
    rcases (mem_zpowers_of_sq_eq_one c.klein.z_sq t).mp hz with h1 | hz1
    · exact c.klein.t_ne h1
    · exact c.klein.tz_ne hz1
  · exact Subgroup.mem_subgroupOf.mpr (c.jr.V_le_R t_mem_Vtz)
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Rg_le_Jg t z hx
  · intro g
    rw [Subgroup.mem_subgroupOf, mem_Jg_iff_comm_mem c.klein (mem_Cz.mp g.2),
      mem_zpowers_czInv z c.klein.z_sq c.klein.z_ne]
    have hcoe : ((g * t' * g⁻¹ * t'⁻¹ : ↥(Cz z)) : G) = (g : G) * t * (g : G)⁻¹ * t⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht']
    rw [hcoe]
  · intro j hj r hr
    rw [Subgroup.mem_subgroupOf] at hj hr ⊢
    simpa using c.jr.R_normal (j : G) hj (r : G) hr
  · intro W hWJ hWnorm hW2
    let W₀ : Subgroup G := W.map (Cz z).subtype
    have hW₀J : W₀ ≤ Jg t z := by
      intro w hw
      rcases (Subgroup.mem_map.mp hw) with ⟨x, hxW, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hWJ hxW)
    have hW₀2 : IsPGroup 2 W₀ := by
      simpa only [W₀] using hW2.map (Cz z).subtype
    have hnorm : (W₀.subgroupOf (Jg t z)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hW₀J]
      intro w k hwW hkJ
      rcases (Subgroup.mem_map.mp hwW) with ⟨x, hxW, rfl⟩
      have hkC : k ∈ Cz z := c.jr.J_le_C hkJ
      have hmem : (⟨k, hkC⟩ : ↥(Cz z)) * x * (⟨k, hkC⟩ : ↥(Cz z))⁻¹ ∈ W :=
        hWnorm ⟨k, hkC⟩ (Subgroup.mem_subgroupOf.mpr hkJ) x hxW
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    have hle : W₀ ≤ Rg t z := TwoB.le_O2In hW₀J hnorm hW₀2
    intro w hwW
    rw [Subgroup.mem_subgroupOf]
    exact hle (Subgroup.mem_map.mpr ⟨w, hwW, rfl⟩)
  · obtain ⟨X, hX, π, hπs, hπk, hXU⟩ := c.jr.quot
    letI : Group X := hX
    obtain ⟨π', hπ's, hπ'k⟩ := quot_subgroupOf c.jr.J_le_C π hπs hπk
    exact ⟨X, hX, π', hπ's, hπ'k, hXU⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
