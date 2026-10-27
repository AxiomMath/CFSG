module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Syl2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Ker

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c in
theorem Qs_pgroup : IsPGroup 2 c.Qs := by
  refine IsPGroup.of_card (n := 10) ?_
  rw [c.card_Qs]; norm_num

structure IsRs (Rs : Subgroup G) : Prop where
  pgroup : IsPGroup 2 Rs
  z_mem : z ∈ Rs
  le_Nc : Rs ≤ c.Nc
  max : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ c.Nc → Rs ≤ P → P = Rs

theorem exists_isRs : ∃ Rs : Subgroup G, c.IsRs Rs ∧ T ≤ Rs := by
  obtain ⟨Rs, h1, h2, h3, h4, h5, -⟩ := c.h.exists_Rs c.hα c.hF c.hM c.hp
  exact ⟨Rs, ⟨h1, h2, h4, h5⟩, h3⟩

variable {c}

namespace IsRs

variable {Rs : Subgroup G} (hR : c.IsRs Rs)

include hR

theorem max' : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ c.Nc → Rs ≤ P → P ≤ Rs :=
  fun P hP hPN hle => (hR.max P hP hPN hle).le

theorem Qs_le : c.Qs ≤ Rs := by
  have h2 : IsPGroup 2 (Rs ⊔ c.Qs : Subgroup G) :=
    hR.pgroup.to_sup_of_normal_right' c.Qs_pgroup hR.le_Nc
  have hle : Rs ⊔ c.Qs ≤ c.Nc := sup_le hR.le_Nc c.Qs_le_Nc
  have := hR.max _ h2 hle le_sup_left
  rw [← this]
  exact le_sup_right

theorem R_eq : Rs ⊓ c.N1 = Rs ⊓ centralizer ({α} : Set G) := by
  ext g
  simp only [mem_inf, N1]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, hR.le_Nc h1, h3⟩

theorem relIndex_R : (Rs ⊓ c.N1).relIndex Rs = 2 ∧ z ∉ Rs ⊓ c.N1 := by
  rw [hR.R_eq]
  exact c.h.relIndex_inf_cent_alpha c.hα c.hF c.hM c.hp hR.z_mem
    (fun g hg => c.mem_Nc.1 (hR.le_Nc hg))

theorem R_pgroup : IsPGroup 2 (Rs ⊓ c.N1 : Subgroup G) := hR.pgroup.to_le inf_le_left

theorem Zs_le_R : c.Zs ≤ Rs ⊓ c.N1 := le_inf (c.Zs_le_Qs.trans hR.Qs_le) c.Zs_le_N1

theorem z_conj_R {g : G} (hg : g ∈ Rs ⊓ c.N1) : z * g * z⁻¹ ∈ Rs ⊓ c.N1 :=
  ⟨(mul_mem (mul_mem hR.z_mem hg.1) (inv_mem hR.z_mem) : z * g * z⁻¹ ∈ Rs), c.z_conj_N1 hg.2⟩

theorem R_odd : ¬ 2 ∣ (Rs ⊓ c.N1).relIndex c.N1 := by
  have h1 := relIndex_mul_relIndex (Rs ⊓ c.N1) Rs c.Nc inf_le_left hR.le_Nc
  have h2 := relIndex_mul_relIndex (Rs ⊓ c.N1) c.N1 c.Nc inf_le_right c.N1_le_Nc
  have hodd := not_two_dvd_relIndex_of_max hR.le_Nc hR.pgroup hR.max'
  rw [hR.relIndex_R.1] at h1
  rw [c.N1_relIndex] at h2
  intro hdvd
  apply hodd
  omega

theorem R_inf_KR_le : (Rs ⊓ c.N1) ⊓ c.KR ≤ c.Zs := by
  refine c.kl (hR.R_pgroup.to_le inf_le_left : IsPGroup 2 ((Rs ⊓ c.N1) ⊓ c.KR : Subgroup G))
    inf_le_right (le_inf hR.Zs_le_R c.Zs_le_KR) ?_
  intro y hy
  exact ⟨hR.z_conj_R hy.1, c.z_conj_KR hy.2⟩

end IsRs

@[expose] noncomputable def Rhat (R : Subgroup G) : Subgroup (MulAut ↥E × MulAut ↥E) :=
  (R.subgroupOf c.N1).map c.rho

theorem mem_Rhat {R : Subgroup G} {p : MulAut ↥E × MulAut ↥E} :
    p ∈ c.Rhat R ↔ ∃ r : ↥c.N1, (r : G) ∈ R ∧ c.rho r = p := by
  simp only [Rhat, Subgroup.mem_map, mem_subgroupOf]

theorem Rhat_le_range (R : Subgroup G) : c.Rhat R ≤ c.rho.range := by
  rintro _ ⟨r, -, rfl⟩
  exact ⟨r, rfl⟩

theorem Rhat_pgroup {R : Subgroup G} (hR : IsPGroup 2 R) : IsPGroup 2 (c.Rhat R) :=
  hR.comap_subtype.map _

theorem Rhat_relIndex_dvd (R : Subgroup G) :
    (c.Rhat R).relIndex c.rho.range ∣ R.relIndex c.N1 := by
  have h1 : (c.Rhat R).relIndex c.rho.range = (R.subgroupOf c.N1 ⊔ c.rho.ker).index := by
    rw [Rhat, MonoidHom.range_eq_map, relIndex_map_map, top_sup_eq, relIndex_top_right]
  rw [h1]
  exact index_dvd_of_le le_sup_left

variable {Rs : Subgroup G}

theorem IsRs.Rhat_max (hR : c.IsRs Rs) :
    ∀ P : Subgroup (MulAut ↥E × MulAut ↥E), IsPGroup 2 P → P ≤ c.rho.range →
      c.Rhat (Rs ⊓ c.N1) ≤ P → P ≤ c.Rhat (Rs ⊓ c.N1) := by
  refine max_of_odd_relIndex (Rhat_pgroup hR.R_pgroup) ?_
  exact fun hd => hR.R_odd (dvd_trans hd (c.Rhat_relIndex_dvd _))

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
