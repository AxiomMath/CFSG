module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CII
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Ker2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  {c : I13Ctx L z t T₀ E Q x β B S α}

theorem IsRs.exists_conj_of_not_mem_R {π : MulAut ↥E →* Equiv.Perm (Fin 5)} {Rs : Subgroup G}
    (hR : c.IsRs Rs) (hII : c.CaseII π) {y : G} (hy : y ∈ Rs) (hyR : y ∉ Rs ⊓ c.N1)
    (hy2 : y * y = 1) : ∃ u ∈ Rs ⊓ c.N1, y = u * z * u⁻¹ := by
  have hzz : z * z = 1 := c.h.z_sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hidx : ((Rs ⊓ c.N1).subgroupOf Rs).index = 2 := hR.relIndex_R.1
  have hzR : z ∉ Rs ⊓ c.N1 := hR.relIndex_R.2
  have hr : y * z ∈ Rs ⊓ c.N1 := by
    have h2 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨y, hy⟩ : ↥Rs))
      (b := (⟨z, hR.z_mem⟩ : ↥Rs))).2 ⟨fun h => absurd h hyR, fun h => absurd h hzR⟩
    exact h2
  obtain ⟨r, hrdef⟩ : ∃ r : G, r = y * z := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hrN : r ∈ c.N1 := hr.2
  have hzr : z * r * z⁻¹ = r⁻¹ := by
    have e1 : z * r * z⁻¹ = z * y := by
      rw [hrdef, hzi]
      calc z * (y * z) * z = z * y * (z * z) := by group
        _ = z * y := by rw [hzz, mul_one]
    have e2 : r⁻¹ = z * y := by rw [hrdef, mul_inv_rev, hzi, hyi]
    exact e1.trans e2.symm
  have hzr' : z * r = r⁻¹ * z := by
    calc z * r = (z * r * z⁻¹) * z := by group
      _ = r⁻¹ * z := by rw [hzr]
  let n : ↥c.N1 := ⟨r, hrN⟩
  have hzn : c.zconjN1 n = n⁻¹ := Subtype.ext (by
    show z * r * z⁻¹ = r⁻¹
    exact hzr)
  have hρn : c.rho (c.zconjN1 n) = (c.rho n)⁻¹ := by rw [hzn, map_inv]
  rw [c.rho_zconj] at hρn
  have hb : (c.rho n).2 = (c.rho n).1⁻¹ := congrArg Prod.fst hρn
  obtain ⟨S₁, S₂, h1, h2, hA1, hA2, hm1, hm2, hRh⟩ := hR.Rhat_prod hII
  have hρn_mem : c.rho n ∈ c.Rhat (Rs ⊓ c.N1) := c.mem_Rhat.2 ⟨n, hr, rfl⟩
  rw [hRh] at hρn_mem
  have ha1 : (c.rho n).1 ∈ S₁ := hρn_mem.1
  have ha2 : (c.rho n).1 ∈ S₂ := by
    have h3 := hρn_mem.2
    rw [hb] at h3
    exact (inv_mem_iff.1 h3)
  have hmem1 : ((c.rho n).1, (1 : MulAut ↥E)) ∈ c.Rhat (Rs ⊓ c.N1) := by
    rw [hRh]
    exact ⟨ha1, S₂.one_mem⟩
  obtain ⟨u', hu'R, hu'⟩ := c.mem_Rhat.1 hmem1
  obtain ⟨u, hudef⟩ : ∃ u : G, u = (u' : G) := ⟨_, rfl⟩
  rw [← hudef] at hu'R
  have hzu : z * u * z⁻¹ ∈ Rs ⊓ c.N1 := hR.z_conj_R hu'R
  have hρu'' : c.rho (c.zconjN1 u') = (1, (c.rho n).1) := by
    rw [c.rho_zconj, hu']
  have hk0 : c.rho (n⁻¹ * (u' * (c.zconjN1 u')⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, hu', hρu'']
    ext
    · simp
    · simp [hb]
  have hk0coe : ((n⁻¹ * (u' * (c.zconjN1 u')⁻¹) : ↥c.N1) : G) =
      r⁻¹ * (u * (z * u * z⁻¹)⁻¹) := by
    rw [hudef]
    rfl
  have hk0R : r⁻¹ * (u * (z * u * z⁻¹)⁻¹) ∈ Rs ⊓ c.N1 :=
    mul_mem (inv_mem hr) (mul_mem hu'R (inv_mem hzu))
  have hk0KR : r⁻¹ * (u * (z * u * z⁻¹)⁻¹) ∈ c.KR := by
    rw [← hk0coe]
    exact c.mem_KR.2 ⟨(n⁻¹ * (u' * (c.zconjN1 u')⁻¹)).2, hk0⟩
  obtain ⟨k, hkdef⟩ : ∃ k : G, k = r⁻¹ * (u * (z * u * z⁻¹)⁻¹) := ⟨_, rfl⟩
  rw [← hkdef] at hk0R hk0KR
  have hkZ : k ∈ c.Zs := hR.R_inf_KR_le ⟨hk0R, hk0KR⟩
  have hu_eq : u * z * u⁻¹ = r * k * z := by
    rw [hkdef]
    group
  have hrk : r * k = k * r := c.Zs_comm_N1 hkZ hrN
  have hrkr : r * k * r⁻¹ = k := by
    rw [hrk]
    group
  have h_inv : r * k * z * (r * k * z) = 1 := by
    rw [← hu_eq]
    calc u * z * u⁻¹ * (u * z * u⁻¹) = u * (z * z) * u⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hkz : k * z * (k * z) = 1 := by
    calc k * z * (k * z) = k * (z * k * z) := by group
      _ = (r * k * r⁻¹) * (z * k * z) := by rw [hrkr]
      _ = r * k * (r⁻¹ * z) * k * z := by group
      _ = r * k * (z * r) * k * z := by rw [hzr']
      _ = r * k * z * (r * k * z) := by group
      _ = 1 := h_inv
  have hyrz : r * z = y := by
    rw [hrdef]
    calc y * z * z = y * (z * z) := by group
      _ = y := by rw [hzz, mul_one]
  rcases c.eq_one_or_t_of_sq hkZ hkz with hk | hk
  · refine ⟨u, hu'R, ?_⟩
    rw [hu_eq, hk, mul_one, hyrz]
  · have hαR : α ∈ Rs ⊓ c.N1 := hR.Zs_le_R c.alpha_mem_Zs
    refine ⟨α * u, mul_mem hαR hu'R, ?_⟩
    have hαr : r * α = α * r := c.Zs_comm_N1 c.alpha_mem_Zs hrN
    have hαt : α * t = t * α := c.Zs_comm c.alpha_mem_Zs c.t_mem_Zs
    have hαrt : α * (r * t) * α⁻¹ = r * t := by
      have e : α * (r * t) = (r * t) * α := by
        calc α * (r * t) = (α * r) * t := by group
          _ = (r * α) * t := by rw [hαr]
          _ = r * (α * t) := by group
          _ = r * (t * α) := by rw [hαt]
          _ = (r * t) * α := by group
      rw [e]
      group
    calc y = r * z := hyrz.symm
      _ = r * (t * t) * z := by rw [c.h.t_sq, mul_one]
      _ = (r * t) * (t * z) := by group
      _ = (α * (r * t) * α⁻¹) * (α * z * α⁻¹) := by rw [hαrt, ← c.t_mul_z]
      _ = α * (r * t * z) * α⁻¹ := by group
      _ = α * (u * z * u⁻¹) * α⁻¹ := by rw [hu_eq, hk]
      _ = α * u * z * (α * u)⁻¹ := by group

theorem caseII_false {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hII : c.CaseII π) : False := by
  have : IsSimpleGroup G := c.h.conf.std.simple
  obtain ⟨Rs, hRs2, hzRs, -, hRsN, hmax, hcent⟩ := c.h.exists_Rs c.hα
  have hR : c.IsRs Rs := ⟨hRs2, hzRs, hRsN, hmax⟩
  refine false_of_fusion_pair c.h.conf.std.nonabelian c.h.conf.cfg.z_order hRs2
    (inf_le_left : Rs ⊓ c.N1 ≤ Rs) hR.relIndex_R.1 hzRs hR.relIndex_R.2 ?_ hcent
  intro g hg
  have hgg : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [c.h.z_sq]; group
  by_cases hgR : g * z * g⁻¹ ∈ Rs ⊓ c.N1
  · exact (c.not_conj_z_of_mem_R hR hII hgR hgg ⟨g, rfl⟩).elim
  · obtain ⟨u, hu, hu_eq⟩ := hR.exists_conj_of_not_mem_R hII hg hgR hgg
    exact ⟨u, hu.1, hu_eq⟩

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
