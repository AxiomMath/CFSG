module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Basic
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.IP
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Setting
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

theorem ip_P_closed (x : G) (Kb : Subgroup (CentralizerBar x)) [Kb.Normal] (T : Subgroup G) :
    IP_P_closed x T (Pg x Kb T) := by
  intro c hc v hv hcv
  have hvC : v ∈ Cx x := ((mem_Kg x Kb).1 hv.2).1
  refine ⟨hcv, (mem_Kg x Kb).2 ⟨mul_mem (mul_mem hc hvC) (inv_mem hc), ?_⟩⟩
  rw [pr_mul x (mul_mem hc hvC) (inv_mem hc), pr_mul x hc hvC, pr_inv x hc]
  exact (inferInstance : Kb.Normal).conj_mem _ ((mem_Kg x Kb).1 hv.2).2 _

theorem isDihedralTwoGroup_equiv {Y : Type} [Group Y] {n : ℕ} (h : IVK.IsDihedralTwoGroup Y n) :
    ∃ m : ℕ, 1 ≤ m ∧ n = m + 1 ∧ Nonempty (Y ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨hn2, k, hk, hk2, ⟨e₀⟩⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hkm : k = 2 ^ m := by
    rw [pow_succ] at hk
    omega
  subst hkm
  exact ⟨m, by omega, rfl, ⟨e₀⟩⟩

variable [Finite G]

@[expose] noncomputable def PgHom (h : SitFacts x Kb e N T) : ↥(Pg x Kb T) →* ↥N.P :=
  ((phiC x Kb).comp (Subgroup.inclusion (fun g (hg : g ∈ Pg x Kb T) =>
      ((mem_Kg x Kb).1 hg.2).1))).codRestrict N.P (fun g =>
    (h.hPN _).2 ⟨g, g.2, phig_of_mem x Kb (((mem_Kg x Kb).1 g.2.2).1)⟩)

omit [Finite G] in
theorem PgHom_apply (h : SitFacts x Kb e N T) (g : ↥(Pg x Kb T)) :
    ((PgHom h g : ↥N.P) : MulAut ↥Kb) = phig x Kb g :=
  (phig_of_mem x Kb (((mem_Kg x Kb).1 g.2.2).1)).symm

@[expose] noncomputable def PgEquiv (h : SitFacts x Kb e N T) : ↥(Pg x Kb T) ≃* ↥N.P :=
  MulEquiv.ofBijective (PgHom h) ⟨by
    intro a b hab
    apply Subtype.ext
    apply h.phig_inj_P a.2 b.2
    rw [← PgHom_apply h a, ← PgHom_apply h b, hab], by
    rintro ⟨a, ha⟩
    obtain ⟨g, hg, hga⟩ := (h.hPN a).1 ha
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    rw [PgHom_apply h]
    exact hga⟩

theorem PgEquiv_apply (h : SitFacts x Kb e N T) (g : ↥(Pg x Kb T)) :
    ((PgEquiv h g : ↥N.P) : MulAut ↥Kb) = phig x Kb g := PgHom_apply h g

theorem Pg_dihedral (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(Pg x Kb T) ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨n, hn⟩ := h12c F h.hF ↥Kb e N
  obtain ⟨m, hm, -, ⟨e₀⟩⟩ := isDihedralTwoGroup_equiv hn
  exact ⟨m, hm, ⟨(PgEquiv h).trans e₀⟩⟩

omit [Finite G] in
theorem isFour_map_subtype {H : Subgroup G} {V₀ : Subgroup ↥H} (hV : Dihedral.IsEA V₀)
    (hc : Nat.card V₀ = 4) : IsFour (V₀.map H.subtype) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · have := congrArg Subtype.val (hV a ha).1
      simpa using this
    · rintro _ ⟨b, hb, rfl⟩
      have := congrArg Subtype.val ((hV a ha).2 b hb)
      simpa using this
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hc

omit [Finite G] in
theorem isEA_subgroupOf {H V : Subgroup G} (hV : IsElemAb2 V) : Dihedral.IsEA (V.subgroupOf H) := by
  intro a ha
  have ha' : (a : G) ∈ V := ha
  refine ⟨Subtype.ext ((hV _ ha').1), fun b hb => Subtype.ext ((hV _ ha').2 _ hb)⟩

omit [Finite G] in
theorem card_subgroupOf {H V : Subgroup G} (hVH : V ≤ H) : Nat.card (V.subgroupOf H) = Nat.card V :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv

theorem ip_P_four (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) : IP_P_four (Pg x Kb T) := by
  obtain ⟨m, hm, ⟨eP⟩⟩ := Pg_dihedral h h12c
  have hk : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hk2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨V₀, hV₀, hc₀⟩ := Dihedral.exists_four_of_equiv eP hk hk2
  exact ⟨V₀.map (Pg x Kb T).subtype, Subgroup.map_subtype_le _, isFour_map_subtype hV₀ hc₀⟩

theorem ip_z_V (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) {z : G} (hz : HZ T (Pg x Kb T) z) :
    IP_z_V z (Pg x Kb T) := by
  obtain ⟨m, hm, ⟨eP⟩⟩ := Pg_dihedral h h12c
  have hk : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  intro V hVP hV
  have hzP : z ∈ Pg x Kb T := hz.z_mem_P
  let z' : ↥(Pg x Kb T) := ⟨z, hzP⟩
  have hmem := Dihedral.central_mem_four_of_equiv eP hk
    (isEA_subgroupOf (H := Pg x Kb T) hV.1) (by rw [card_subgroupOf hVP]; exact hV.2)
    (z := z') (Subtype.ext hz.z_sq) (fun h1 => hz.z_ne_one (congrArg Subtype.val h1))
    (fun y => Subtype.ext (hz.z_central _ y.2.1))
  exact hmem

end CFSG.GH74.GLS.Stage1.Thm6.Glue
