module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Orb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1P1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SGen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_b1_not_mem_W {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}
    (cfg : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u)
    (hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) :
    b₁ ∉ (closure {a₂, b₂} : Subgroup G) := by
  intro hb1W
  have hb1U : b₁ ∈ (closure {a₁, b₁} : Subgroup G) := Subgroup.subset_closure (by simp)
  have hUW := y6q8_card_UW cfg.rel cfg.z_ne hA32
  rcases (hUW.2.2 b₁).mp ⟨hb1U, hb1W⟩ with h1 | h1
  · exact cfg.z_ne (by rw [← cfg.rel.b1_sq, h1]; simp)
  · exact cfg.z_ne (by rw [← cfg.rel.b1_sq, h1, cfg.rel.z_sq])

private lemma y7a_isSylowIn_map_subtype_three {V : Subgroup G} (P : Sylow 3 ↥V) :
    IsSylowIn 3 V ((P : Subgroup ↥V).map V.subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

theorem y7a_trans_Up (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ w ∈ y6Up c.s.fr.A (V1 c.e) c.s.t, w ∈ y7aO (y7aX c) (V1 c.e) c.s.t := by
  intro w hw
  show ∃ x ∈ y7aX c, (x * c.s.t * x⁻¹)⁻¹ * w ∈ V1 c.e
  obtain ⟨a, ha, ha1, v, hv, rfl⟩ := hw
  have cfg := c.toCtx5.y6cfg5 hH
  have h7 := c.y7acfg hH
  have hA32 : Nat.card ↥(closure {c.s.fr.a₁, c.s.fr.b₁, c.s.fr.a₂, c.s.fr.b₂} : Subgroup G) =
      32 := by
    rw [← cfg.hA]; exact cfg.card_A
  have ht2 : c.s.t * c.s.t = 1 := by
    have h := pow_orderOf_eq_one c.s.t
    rw [c.s.t_order] at h
    simpa [pow_two] using h
  have hti : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
  by_cases ha_triv : a = 1 ∨ a = c.s.fr.z
  · rcases ha_triv with rfl | rfl
    · refine ⟨1, (y7aX c).one_mem, ?_⟩
      have hgoal : (1 * c.s.t * 1⁻¹)⁻¹ * (1 * c.s.t * v) = v := by
        simp only [one_mul, inv_one, mul_one]
        rw [hti, ← mul_assoc, ht2, one_mul]
      rw [hgoal]
      exact hv
    · refine ⟨1, (y7aX c).one_mem, ?_⟩
      have hzt : c.s.t * c.s.fr.z * c.s.t = c.s.fr.z := by
        have hcomm : Commute c.s.t c.s.fr.z := (cfg.t_cent c.s.fr.z (y6_z_mem_A cfg)).symm
        rw [hcomm.eq, mul_assoc, ht2, mul_one]
      have hgoal : (1 * c.s.t * 1⁻¹)⁻¹ * (c.s.fr.z * c.s.t * v) = c.s.fr.z * v := by
        simp only [one_mul, inv_one, mul_one]
        rw [hti]
        calc c.s.t * (c.s.fr.z * c.s.t * v) = (c.s.t * c.s.fr.z * c.s.t) * v := by group
          _ = c.s.fr.z * v := by rw [hzt]
      rw [hgoal]
      exact (V1 c.e).mul_mem (y7a_z_mem_V h7) hv
  · have ha_ne1 : a ≠ 1 := fun h => ha_triv (Or.inl h)
    have ha_nez : a ≠ c.s.fr.z := fun h => ha_triv (Or.inr h)
    have hb1A : c.s.fr.b₁ ∈ c.s.fr.A := by
      rw [cfg.hA]; exact Subgroup.subset_closure (by simp)
    have hb2A : c.s.fr.b₂ ∈ c.s.fr.A := by
      rw [cfg.hA]; exact Subgroup.subset_closure (by simp)
    have hb1U : c.s.fr.b₁ ∈ (closure {c.s.fr.a₁, c.s.fr.b₁} : Subgroup G) :=
      Subgroup.subset_closure (by simp)
    have hb2W : c.s.fr.b₂ ∈ (closure {c.s.fr.a₂, c.s.fr.b₂} : Subgroup G) :=
      Subgroup.subset_closure (by simp)
    have hzW : c.s.fr.z ∈ (closure {c.s.fr.a₂, c.s.fr.b₂} : Subgroup G) := by
      rw [← cfg.rel.b2_sq]; exact Subgroup.pow_mem _ hb2W 2
    have hOa : a ∈ (c.s.fr.A : Set G) \
        ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) ∪
          (closure {c.s.fr.a₂, c.s.fr.b₂} : Set G)) := by
      refine ⟨ha, ?_⟩
      intro hUW
      rcases hUW with hU | hW
      · exact cfg.z_ne (((y6q8_sq_U cfg.rel a hU).2 ha_ne1 ha_nez).symm.trans ha1)
      · exact cfg.z_ne (((y6q8_sq_W cfg.rel a hW).2 ha_ne1 ha_nez).symm.trans ha1)
    set r : G := c.s.fr.b₁ * c.s.fr.b₂ with hr
    have hrA : r ∈ c.s.fr.A := by rw [hr]; exact c.s.fr.A.mul_mem hb1A hb2A
    have hr2 : r ^ 2 = 1 := by
      rw [hr]
      have hcomm : Commute c.s.fr.b₁ c.s.fr.b₂ :=
        y6q8_commUW cfg.rel c.s.fr.b₁ hb1U c.s.fr.b₂ hb2W
      calc (c.s.fr.b₁ * c.s.fr.b₂) ^ 2 = c.s.fr.b₁ ^ 2 * c.s.fr.b₂ ^ 2 := hcomm.mul_pow 2
        _ = c.s.fr.z * c.s.fr.z := by rw [cfg.rel.b1_sq, cfg.rel.b2_sq]
        _ = 1 := by simpa [pow_two] using cfg.rel.z_sq
    have hr_notin : r ∉ ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) ∪
        (closure {c.s.fr.a₂, c.s.fr.b₂} : Set G)) := by
      intro hrUW
      have hr1z : r = 1 ∨ r = c.s.fr.z := by
        by_contra hcon
        have h1 : r ≠ 1 := fun h => hcon (Or.inl h)
        have h2 : r ≠ c.s.fr.z := fun h => hcon (Or.inr h)
        have hsqz : r ^ 2 = c.s.fr.z :=
          (y6q8_sqz_iff cfg.rel cfg.z_ne hA32 r (by rw [← cfg.hA]; exact hrA)).mpr
            ⟨hrUW, h1, h2⟩
        exact cfg.z_ne (hsqz.symm.trans hr2)
      rcases hr1z with hr1 | hrz
      · apply y7a_b1_not_mem_W cfg hA32
        have hb1eq : c.s.fr.b₁ = c.s.fr.b₂⁻¹ := by
          rw [hr] at hr1
          exact mul_eq_one_iff_eq_inv.mp hr1
        rw [hb1eq]
        exact Subgroup.inv_mem _ hb2W
      · apply y7a_b1_not_mem_W cfg hA32
        have hb1eq : c.s.fr.b₁ = c.s.fr.z * c.s.fr.b₂⁻¹ := by
          rw [hr] at hrz
          calc c.s.fr.b₁ = (c.s.fr.b₁ * c.s.fr.b₂) * c.s.fr.b₂⁻¹ := by group
            _ = c.s.fr.z * c.s.fr.b₂⁻¹ := by rw [hrz]
        rw [hb1eq]
        exact Subgroup.mul_mem _ hzW (Subgroup.inv_mem _ hb2W)
    have hrO : r ∈ (c.s.fr.A : Set G) \
        ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) ∪
          (closure {c.s.fr.a₂, c.s.fr.b₂} : Set G)) := ⟨hrA, hr_notin⟩
    have hrF : r ∈ c.s.fr.F := by
      rw [hr]
      show c.s.fr.b₁ * c.s.fr.b₂ ∈ closure {c.s.fr.a₁ * c.s.fr.a₂,
        c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z}
      exact Subgroup.subset_closure (by simp)
    have hrt_conj : r * c.s.t ∈ conjClass (M3 c.s) c.s.t := by
      rw [hF.2.2.1.1.2.2.1]
      exact ⟨r, hrF, rfl⟩
    obtain ⟨m, hmM3, hm_eq⟩ := hrt_conj
    obtain ⟨P₃, hP₃⟩ : ∃ P₃ : Subgroup G, IsSylowIn 3 (normIn L c.s.fr.A) P₃ :=
      ⟨_, y7a_isSylowIn_map_subtype_three (default : Sylow 3 ↥(normIn L c.s.fr.A))⟩
    have hP₃_cent : P₃ ≤ centEl L c.s.fr.z := by
      rw [← hH.hLF.fact18.1.1]; exact hP₃.1
    have hTZ : P₃ ≤ normalizer (c.s.fr.Z : Set G) := by
      intro k hk
      have hkz : Commute k c.s.fr.z := by
        have hmem : k ∈ centralizer ({c.s.fr.z} : Set G) := (hP₃_cent hk).2
        rw [Subgroup.mem_centralizer_iff] at hmem
        exact (hmem c.s.fr.z (Set.mem_singleton c.s.fr.z)).symm
      refine Subgroup.centralizer_le_normalizer (c.s.fr.Z : Set G) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hkz.zpow_right i).eq.symm
    have hOrbit : IsOrbitMod P₃ c.s.fr.Z
        ((c.s.fr.A : Set G) \ ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) ∪
          (closure {c.s.fr.a₂, c.s.fr.b₂} : Set G))) :=
      (hH.hLF.fact18.1.2.2 P₃ hP₃).2.2
    obtain ⟨k, hkP, hkζ⟩ := y6_orbitMod_trans hTZ hOrbit hrO hOa
    have hk_norm : k ∈ normIn L c.s.fr.A := hP₃.1 hkP
    have hkL : k ∈ L := hk_norm.1
    have hkX : k ∈ y7aX c := y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH hk_norm)
    have hmX : m ∈ y7aX c := y7a_M3_le_X c hF hmM3
    refine ⟨k * m, (y7aX c).mul_mem hkX hmX, ?_⟩
    have hkt : k * c.s.t = c.s.t * k := by
      have hmem : c.s.t ∈ centralizer (L : Set G) := c.s.t_mem
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem k hkL
    have hkti : c.s.t * k⁻¹ = k⁻¹ * c.s.t := by
      calc c.s.t * k⁻¹ = k⁻¹ * (k * c.s.t) * k⁻¹ := by group
        _ = k⁻¹ * (c.s.t * k) * k⁻¹ := by rw [hkt]
        _ = k⁻¹ * c.s.t := by group
    set ζ : G := (k * r * k⁻¹)⁻¹ * a with hζdef
    have hζZ : ζ ∈ c.s.fr.Z := by rw [hζdef]; exact hkζ
    have hZA : c.s.fr.Z ≤ c.s.fr.A := by
      show zpowers c.s.fr.z ≤ c.s.fr.A
      exact Subgroup.zpowers_le.mpr (y6_z_mem_A cfg)
    have hZV : c.s.fr.Z ≤ V1 c.e := by
      show zpowers c.s.fr.z ≤ V1 c.e
      exact Subgroup.zpowers_le.mpr (y7a_z_mem_V h7)
    have hζA : ζ ∈ c.s.fr.A := hZA hζZ
    have hζV : ζ ∈ V1 c.e := hZV hζZ
    have hzt : c.s.t⁻¹ * ζ * c.s.t = ζ := by
      rw [hti]
      have hcomm : Commute c.s.t ζ := (cfg.t_cent ζ hζA).symm
      rw [hcomm.eq, mul_assoc, ht2, mul_one]
    have hconj : (k * m) * c.s.t * (k * m)⁻¹ = (k * r * k⁻¹) * c.s.t := by
      calc (k * m) * c.s.t * (k * m)⁻¹ = k * (m * c.s.t * m⁻¹) * k⁻¹ := by group
        _ = k * (r * c.s.t) * k⁻¹ := by rw [← hm_eq]
        _ = k * r * (c.s.t * k⁻¹) := by group
        _ = k * r * (k⁻¹ * c.s.t) := by rw [hkti]
        _ = (k * r * k⁻¹) * c.s.t := by group
    have hfinal : ((k * m) * c.s.t * (k * m)⁻¹)⁻¹ * (a * c.s.t * v) = ζ * v := by
      rw [hconj]
      calc ((k * r * k⁻¹) * c.s.t)⁻¹ * (a * c.s.t * v)
          = c.s.t⁻¹ * ζ * c.s.t * v := by rw [hζdef]; group
        _ = ζ * v := by simp only [hzt]
    rw [hfinal]
    exact (V1 c.e).mul_mem hζV hv

end CFSG.OddStandard.HigherRank.YamadaG23
