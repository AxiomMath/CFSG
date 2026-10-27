module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Cen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1M6b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_V_ab_cen {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}
    (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
  have hzd : Commute z d := y7a_d_cent h z (y7a_z_mem_A h)
  have hpair : ({z, d} : Set G).Pairwise Commute := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hzd
    · exact hzd.symm
    · exact absurd rfl hab
  haveI : IsMulCommutative ↥V := by
    rw [h.hV]
    exact Subgroup.isMulCommutative_closure hpair
  intro v hv w hw
  exact setLike_mul_comm hv hw

theorem y7a_comm_t_AV (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    ∀ m ∈ y7aX c, ⁅m, c.s.t⁆ ∈ AV1 c.e := by
  intro m hm
  have h := c.y7acfg hH
  obtain ⟨hm1, hm2⟩ := Subgroup.mem_inf.mp hm
  have htC1 : c.s.t ∈ C1 c.e := Subgroup.mem_sup_right (y7a_t_mem_C0 h)
  have hx1 : m * c.s.t * m⁻¹ ∈ C1 c.e :=
    (Subgroup.mem_set_normalizer_iff.mp hm1 c.s.t).mp htC1
  have hx2 : m * c.s.t * m⁻¹ ∉ AV1 c.e := by
    intro hx
    exact y7a_t_not_mem_AV h ((y7a_conj_AV h hm1 hm2 c.s.t).mpr hx)
  have ht_inv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right (y7a_t_sq h)
  have ht1 : c.s.t⁻¹ ∈ C1 c.e := by rw [ht_inv]; exact htC1
  have ht2 : c.s.t⁻¹ ∉ AV1 c.e := by rw [ht_inv]; exact y7a_t_not_mem_AV h
  have hprod : (m * c.s.t * m⁻¹) * c.s.t⁻¹ ∈ AV1 c.e :=
    y7a_index_AV h _ hx1 _ ht1 hx2 ht2
  rw [commutatorElement_def]
  exact hprod

theorem y7a_mod_hom (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P)
    [hZ : (c.s.fr.Z.subgroupOf c.s.fr.A).Normal] :
    ∃ f : ↥(M6 c.e) →* ↥c.s.fr.A ⧸ c.s.fr.Z.subgroupOf c.s.fr.A,
      (∀ (m : ↥(M6 c.e)) (a : ↥c.s.fr.A), (a : G)⁻¹ * ⁅(m : G), c.s.t⁆ ∈ V1 c.e →
        f m = (a : ↥c.s.fr.A ⧸ c.s.fr.Z.subgroupOf c.s.fr.A)) ∧
      (∀ m : ↥(M6 c.e), ∃ a : ↥c.s.fr.A, (a : G)⁻¹ * ⁅(m : G), c.s.t⁆ ∈ V1 c.e) ∧
      Function.Surjective f ∧ f.ker = (AV1 c.e).subgroupOf (M6 c.e) := by
  have h := c.y7acfg hH
  have hAV : ∀ a ∈ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  have hVV : ∀ v ∈ V1 c.e, ∀ w ∈ V1 c.e, v * w = w * v := y7a_V_ab_cen h
  have hAA : ∀ a ∈ c.s.fr.A, ∀ a' ∈ c.s.fr.A, ⁅a, a'⁆ ∈ V1 c.e :=
    fun a ha a' ha' => y7a_comm_C1 h a (Subgroup.mem_sup_left ha) a'
      (Subgroup.mem_sup_left ha')
  have hAVZ : c.s.fr.A ⊓ V1 c.e = c.s.fr.Z := y7a_A_inf_V h
  have hWAV : ∀ m ∈ M6 c.e, ∀ x ∈ c.s.fr.A ⊔ V1 c.e, ⁅m, x⁆ ∈ V1 c.e :=
    Subgroup.commutator_le.mp (y7a_comm_M6_AV c hH hF)
  have hmt : ∀ m ∈ M6 c.e, ⁅m, c.s.t⁆ ∈ c.s.fr.A ⊔ V1 c.e :=
    fun m hm => y7a_comm_t_AV c hH m (y7a_C6_le_X c hH hF (y7a_M6_le_C6 c hm))
  obtain ⟨f, hchar, hex⟩ :=
    y7a_commhom (A := c.s.fr.A) (V := V1 c.e) (W := M6 c.e) (Z := c.s.fr.Z) (t := c.s.t)
      hAV hVV hAA hAVZ hWAV hmt
  refine ⟨f, hchar, hex, ?_, ?_⟩
  ·
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (c.s.fr.Z.subgroupOf c.s.fr.A) q
    have htC1 : c.s.t ∈ C1 c.e := Subgroup.mem_sup_right (y7a_t_mem_C0 h)
    have htAV : c.s.t ∉ AV1 c.e := y7a_t_not_mem_AV h
    have hatC1 : (a : G) * c.s.t ∈ C1 c.e :=
      (C1 c.e).mul_mem (Subgroup.mem_sup_left a.2) htC1
    have hatAV : (a : G) * c.s.t ∉ AV1 c.e := by
      intro hx
      have hmem : (a : G)⁻¹ * ((a : G) * c.s.t) ∈ AV1 c.e :=
        (AV1 c.e).mul_mem ((AV1 c.e).inv_mem (Subgroup.mem_sup_left a.2)) hx
      have he : (a : G)⁻¹ * ((a : G) * c.s.t) = c.s.t := by group
      rw [he] at hmem
      exact htAV hmem
    have htrans := y7a_acts_trans c hH hF hP
    unfold ActsTransOutside at htrans
    obtain ⟨-, -, htrans⟩ := htrans
    obtain ⟨k, hkM, hk⟩ := htrans c.s.t htC1 htAV ((a : G) * c.s.t) hatC1 hatAV
    have htN : c.s.t ∈ normalizer (V1 c.e : Set G) :=
      y7a_C1_le_N_V h (Subgroup.mem_sup_right (y7a_t_mem_C0 h))
    have hconj : (a : G)⁻¹ * ⁅(k : G), c.s.t⁆ ∈ V1 c.e := by
      have h1 : c.s.t * (((a : G) * c.s.t)⁻¹ * (k * c.s.t * k⁻¹)) * c.s.t⁻¹ ∈ V1 c.e :=
        (Subgroup.mem_set_normalizer_iff.mp htN _).mp hk
      have he : c.s.t * (((a : G) * c.s.t)⁻¹ * (k * c.s.t * k⁻¹)) * c.s.t⁻¹ =
          (a : G)⁻¹ * ⁅(k : G), c.s.t⁆ := by
        rw [commutatorElement_def]
        group
      rwa [he] at h1
    exact ⟨⟨k, hkM⟩, hchar ⟨k, hkM⟩ a hconj⟩
  ·
    ext m
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hfm
      obtain ⟨a, ha⟩ := hex m
      have hfa : f m = (a : ↥c.s.fr.A ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) := hchar m a ha
      have haZ : (a : G) ∈ c.s.fr.Z := by
        have h1 : (a : ↥c.s.fr.A ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) = 1 := hfa.symm.trans hfm
        rw [QuotientGroup.eq_one_iff] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      have hZle : c.s.fr.Z ≤ V1 c.e := Subgroup.zpowers_le.mpr (y7a_z_mem_V h)
      have haV : (a : G) ∈ V1 c.e := hZle haZ
      have hcommV : ⁅(m : G), c.s.t⁆ ∈ V1 c.e := by
        have h2 : (a : G) * ((a : G)⁻¹ * ⁅(m : G), c.s.t⁆) ∈ V1 c.e :=
          (V1 c.e).mul_mem haV ha
        rwa [mul_inv_cancel_left] at h2
      have hmX : (m : G) ∈ y7aX c := y7a_C6_le_X c hH hF (y7a_M6_le_C6 c m.2)
      have hmN : (m : G) ∈ normalizer (C1 c.e : Set G) := (Subgroup.mem_inf.mp hmX).1
      have hmY : (m : G) ∈ y7aY c := by
        refine (y7a_stab_iff h hmN).mp ?_
        have htN : c.s.t ∈ normalizer (V1 c.e : Set G) :=
          y7a_C1_le_N_V h (Subgroup.mem_sup_right (y7a_t_mem_C0 h))
        have hconj : c.s.t⁻¹ * ⁅(m : G), c.s.t⁆ * c.s.t ∈ V1 c.e := by
          have := (Subgroup.mem_set_normalizer_iff.mp (Subgroup.inv_mem _ htN)
            ⁅(m : G), c.s.t⁆).mp hcommV
          simpa using this
        have he : c.s.t⁻¹ * ((m : G) * c.s.t * (m : G)⁻¹) =
            c.s.t⁻¹ * ⁅(m : G), c.s.t⁆ * c.s.t := by
          rw [commutatorElement_def]
          group
        rw [he]
        exact hconj
      have hmem : (m : G) ∈ M6 c.e ⊓ y7aY c := ⟨m.2, hmY⟩
      rwa [y7a_M6_inf_Y c hH hF hP] at hmem
    · intro hmAV
      have hmC1 : (m : G) ∈ C1 c.e := y7a_AV_le_C1 h hmAV
      have hmN : (m : G) ∈ normalizer (C1 c.e : Set G) := Subgroup.le_normalizer hmC1
      have hmY : (m : G) ∈ y7aY c := y6_C1_le_NAt h.cfg hmC1
      have hw : c.s.t⁻¹ * ((m : G) * c.s.t * (m : G)⁻¹) ∈ V1 c.e :=
        (y7a_stab_iff h hmN).mpr hmY
      have htN : c.s.t ∈ normalizer (V1 c.e : Set G) :=
        y7a_C1_le_N_V h (Subgroup.mem_sup_right (y7a_t_mem_C0 h))
      have hcommV : ⁅(m : G), c.s.t⁆ ∈ V1 c.e := by
        have h1 : c.s.t * (c.s.t⁻¹ * ((m : G) * c.s.t * (m : G)⁻¹)) * c.s.t⁻¹ ∈ V1 c.e :=
          (Subgroup.mem_set_normalizer_iff.mp htN _).mp hw
        have he : c.s.t * (c.s.t⁻¹ * ((m : G) * c.s.t * (m : G)⁻¹)) * c.s.t⁻¹ =
            ⁅(m : G), c.s.t⁆ := by
          rw [commutatorElement_def]
          group
        rwa [he] at h1
      have h1 : f m = ((1 : ↥c.s.fr.A) : ↥c.s.fr.A ⧸ c.s.fr.Z.subgroupOf c.s.fr.A) :=
        hchar m 1 (by
          rw [Subgroup.coe_one, inv_one, one_mul]
          exact hcommV)
      rw [h1]
      exact QuotientGroup.mk_one (c.s.fr.Z.subgroupOf c.s.fr.A)

end CFSG.OddStandard.HigherRank.YamadaG23
