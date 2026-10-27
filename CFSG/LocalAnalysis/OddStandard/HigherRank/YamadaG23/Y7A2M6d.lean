module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2M6c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Top

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_conj_closure_mem {S : Set G} {K : Subgroup G} {x : G}
    (hgen : ∀ y ∈ S, x * y * x⁻¹ ∈ K) :
    ∀ c ∈ Subgroup.closure S, x * c * x⁻¹ ∈ K := by
  have hle : Subgroup.closure S ≤ K.comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_comap.mpr (show x * y * x⁻¹ ∈ K from hgen y hy)
  intro c hc
  exact Subgroup.mem_comap.mp (hle hc)

private lemma y7a_comm_conj_mem {H : Subgroup G} {x : G}
    (hx : ∀ m ∈ H, x * m * x⁻¹ ∈ H) :
    ∀ d ∈ ⁅H, H⁆, x * d * x⁻¹ ∈ ⁅H, H⁆ := by
  intro d hd
  rw [Subgroup.commutator_def] at hd ⊢
  refine y7a_conj_closure_mem (S := {g | ∃ g₁ ∈ H, ∃ g₂ ∈ H, ⁅g₁, g₂⁆ = g}) ?_ d hd
  rintro g ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  have he : x * ⁅g₁, g₂⁆ * x⁻¹ = ⁅x * g₁ * x⁻¹, x * g₂ * x⁻¹⁆ := by
    rw [commutatorElement_def, commutatorElement_def]; group
  rw [he]
  exact Subgroup.commutator_mem_commutator (hx g₁ hg₁) (hx g₂ hg₂)

private lemma y7a_mem_normalizer_of_conj {H : Subgroup G} {x : G}
    (h : ∀ y ∈ H, x * y * x⁻¹ ∈ H) (hi : ∀ y ∈ H, x⁻¹ * y * x ∈ H) :
    x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have := hi (x * y * x⁻¹) hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

private lemma y7a_mem_normalizer_sup {H K : Subgroup G} {x : G}
    (hH : x ∈ Subgroup.normalizer (H : Set G))
    (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem y7a_M6_comm_eq_V1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : ⁅M6 c.e, M6 c.e⁆ = V1 c.e := by
  have h := c.y7acfg hH
  refine le_antisymm (y7a_M6_comm_le_V1 c hH hF) ?_
  by_contra hVD
  have hD_le_V : ⁅M6 c.e, M6 c.e⁆ ≤ V1 c.e := y7a_M6_comm_le_V1 c hH hF
  have htX : c.s.t ∈ y7aX c :=
    y7a_C6_le_X c hH hF
      (y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_right (y7a_t_mem_C0 h)))
  have htD : ∀ d ∈ ⁅M6 c.e, M6 c.e⁆, c.s.t * d * c.s.t⁻¹ ∈ ⁅M6 c.e, M6 c.e⁆ :=
    y7a_comm_conj_mem (x := c.s.t) (fun m hm => y7a_M6_normal c hH hF c.s.t htX m hm)
  have htz : c.s.t * c.s.fr.z * c.s.t⁻¹ = c.s.fr.z := by
    rw [← s3_comm_t_of_mem_A c.s (y7a_z_mem_A h)]
    group
  have hdD_contra : c.d ∈ ⁅M6 c.e, M6 c.e⁆ → False := by
    intro hdD
    have hzdD : c.s.fr.z * c.d ∈ ⁅M6 c.e, M6 c.e⁆ := by
      have hmem := htD c.d hdD
      rwa [y7a_tdt h] at hmem
    have hzD : c.s.fr.z ∈ ⁅M6 c.e, M6 c.e⁆ := by
      have hmem := (⁅M6 c.e, M6 c.e⁆).mul_mem hzdD ((⁅M6 c.e, M6 c.e⁆).inv_mem hdD)
      have hd_inv : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right (y7a_d_sq h)
      have he : (c.s.fr.z * c.d) * c.d⁻¹ = c.s.fr.z := by
        rw [hd_inv, mul_assoc, y7a_d_sq h, mul_one]
      rwa [he] at hmem
    have hVleD : V1 c.e ≤ ⁅M6 c.e, M6 c.e⁆ := by
      rw [c.hV, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hzD
      · exact hdD
    exact hVD hVleD
  have hzdD_contra : c.s.fr.z * c.d ∈ ⁅M6 c.e, M6 c.e⁆ → False := by
    intro hzdD
    have hdD : c.d ∈ ⁅M6 c.e, M6 c.e⁆ := by
      have hmem := htD (c.s.fr.z * c.d) hzdD
      have he : c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹ = c.d := by
        rw [show c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹ =
            (c.s.t * c.s.fr.z * c.s.t⁻¹) * (c.s.t * c.d * c.s.t⁻¹) by group,
          htz, y7a_tdt h, ← mul_assoc, y7a_z_sq h, one_mul]
      rwa [he] at hmem
    exact hdD_contra hdD
  have hD_elems : ∀ d ∈ ⁅M6 c.e, M6 c.e⁆, d = 1 ∨ d = c.s.fr.z := by
    intro d hd
    rcases y7a_V_elems h d (hD_le_V hd) with h1 | hz | hd' | hzd'
    · exact Or.inl h1
    · exact Or.inr hz
    · exact absurd (hd' ▸ hd) hdD_contra
    · exact absurd (hzd' ▸ hd) hzdD_contra
  have hDA : ⁅M6 c.e, M6 c.e⁆ ≤ c.s.fr.A := by
    intro x hx
    rcases hD_elems x hx with h1 | hz
    · rw [h1]; exact one_mem _
    · rw [hz]; exact y7a_z_mem_A h
  have hM6_norm_A : ∀ m ∈ M6 c.e, ∀ a ∈ c.s.fr.A, m * a * m⁻¹ ∈ c.s.fr.A := by
    intro m hm a ha
    have haAV : a ∈ AV1 c.e := Subgroup.mem_sup_left ha
    have haM6 : a ∈ M6 c.e := y7a_AV1_le_M6 c hH hF haAV
    have hcommA : ⁅m, a⁆ ∈ c.s.fr.A := hDA (Subgroup.commutator_mem_commutator hm haM6)
    have he : m * a * m⁻¹ = ⁅m, a⁆ * a := by rw [commutatorElement_def]; group
    rw [he]
    exact (c.s.fr.A).mul_mem hcommA ha
  have hnormF : ∀ m ∈ M3 c.s,
      m ∈ Subgroup.normalizer ((c.s.fr.F ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
    intro m hmM3
    rw [hF.2.2.1.1.1]
    exact Subgroup.mem_sup_right hmM3
  have hM3_norm_At : ∀ m ∈ M3 c.s,
      m ∈ Subgroup.normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
    intro m hmM3
    have hmM6 : m ∈ M6 c.e := h71.2.2.2.1 hmM3
    have hnormA : m ∈ Subgroup.normalizer (c.s.fr.A : Set G) := by
      refine y7a_mem_normalizer_of_conj (hM6_norm_A m hmM6) ?_
      intro y hy
      have hh := hM6_norm_A m⁻¹ ((M6 c.e).inv_mem hmM6) y hy
      rwa [inv_inv] at hh
    have hFt_eq : (c.s.fr.A ⊔ (c.s.fr.F ⊔ zpowers c.s.t) : Subgroup G) =
        c.s.fr.A ⊔ zpowers c.s.t := by
      rw [← sup_assoc, sup_eq_left.mpr (s3_F_le_A c.s)]
    have hnorm := y7a_mem_normalizer_sup hnormA (hnormF m hmM3)
    rwa [hFt_eq] at hnorm
  have hM3_conj_t : ∀ m ∈ M3 c.s,
      m * c.s.t * m⁻¹ = c.s.t ∨ m * c.s.t * m⁻¹ = c.s.fr.z * c.s.t := by
    intro m hmM3
    have hmX : m ∈ y7aX c := y7a_M3_le_X c hF hmM3
    have hx1 : m ∈ Subgroup.normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hmX).1
    exact (y7a_mem_NAt_iff h hx1).mp (hM3_norm_At m hmM3)
  have hA32 : Nat.card ↥(closure {c.s.fr.a₁, c.s.fr.b₁, c.s.fr.a₂, c.s.fr.b₂} :
      Subgroup G) = 32 := by
    rw [← h.cfg.hA]; exact h.cfg.card_A
  have hrF : c.s.fr.b₁ * c.s.fr.b₂ ∈ c.s.fr.F := by
    show c.s.fr.b₁ * c.s.fr.b₂ ∈
      closure {c.s.fr.a₁ * c.s.fr.a₂, c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z}
    exact Subgroup.subset_closure (by simp)
  have hrt_conj : (c.s.fr.b₁ * c.s.fr.b₂) * c.s.t ∈ conjClass (M3 c.s) c.s.t := by
    rw [hF.2.2.1.1.2.2.1]
    exact ⟨c.s.fr.b₁ * c.s.fr.b₂, hrF, rfl⟩
  obtain ⟨m, hmM3, hm_eq⟩ := hrt_conj
  have hr : c.s.fr.b₁ * c.s.fr.b₂ = 1 ∨ c.s.fr.b₁ * c.s.fr.b₂ = c.s.fr.z := by
    rcases hM3_conj_t m hmM3 with h1 | h1
    · left
      calc c.s.fr.b₁ * c.s.fr.b₂
          = (c.s.fr.b₁ * c.s.fr.b₂) * (c.s.t * c.s.t) := by rw [y7a_t_sq h, mul_one]
        _ = ((c.s.fr.b₁ * c.s.fr.b₂) * c.s.t) * c.s.t := by group
        _ = c.s.t * c.s.t := by rw [hm_eq, h1]
        _ = 1 := y7a_t_sq h
    · right
      calc c.s.fr.b₁ * c.s.fr.b₂
          = (c.s.fr.b₁ * c.s.fr.b₂) * (c.s.t * c.s.t) := by rw [y7a_t_sq h, mul_one]
        _ = ((c.s.fr.b₁ * c.s.fr.b₂) * c.s.t) * c.s.t := by group
        _ = (c.s.fr.z * c.s.t) * c.s.t := by rw [hm_eq, h1]
        _ = c.s.fr.z := by rw [mul_assoc, y7a_t_sq h, mul_one]
  have hnotin := (y7a_b1b2_notin h.cfg.rel h.cfg.z_ne hA32).1
  rcases hr with h1 | hz
  · exact hnotin (by rw [h1]; exact one_mem _)
  · refine hnotin ?_
    rw [hz, ← h.cfg.rel.a1_sq]
    exact pow_mem (Subgroup.subset_closure (by simp)) 2

end CFSG.OddStandard.HigherRank.YamadaG23
