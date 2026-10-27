module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Ctr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1M6a

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

private lemma y7a_isSylowIn_map_subtype_three_cen {V : Subgroup G} (P : Sylow 3 ↥V) :
    IsSylowIn 3 V ((P : Subgroup ↥V).map V.subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

theorem y7a_comm_C6_AV (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ m ∈ C6 c.e, ∀ x ∈ AV1 c.e, ⁅m, x⁆ ∈ V1 c.e := by
  have h := c.y7acfg hH
  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : Subgroup G, IsSylowIn 3 (normIn L c.s.fr.A) P₃ :=
    ⟨_, y7a_isSylowIn_map_subtype_three_cen (default : Sylow 3 ↥(normIn L c.s.fr.A))⟩
  have hP₃_cent : P₃ ≤ centEl L c.s.fr.z := by
    rw [← hH.hLF.fact18.1.1]; exact hP₃.1
  have hP3X : P₃ ≤ y7aX c :=
    le_trans (le_trans hP₃.1 (s5_NLA_le_Y c.toCtx5 hH)) (y7a_Y_le_X c hH)
  have hC6X : C6 c.e ≤ y7aX c := y7a_C6_le_X c hH hF
  have hP3z : ∀ k ∈ P₃, k * c.s.fr.z * k⁻¹ = c.s.fr.z := by
    intro k hk
    have hkz : Commute k c.s.fr.z := by
      have hmem : k ∈ centralizer ({c.s.fr.z} : Set G) := (hP₃_cent hk).2
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact (hmem c.s.fr.z (Set.mem_singleton c.s.fr.z)).symm
    rw [hkz.eq]; group
  have hOW := hH.hLF.fact18.1.2.2 P₃ hP₃
  have hU : IsOrbitMod P₃ (zpowers c.s.fr.z)
      ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) \ (zpowers c.s.fr.z : Set G)) := by
    simpa only [SFrame.Z] using hOW.1
  have hW : IsOrbitMod P₃ (zpowers c.s.fr.z)
      ((closure {c.s.fr.a₂, c.s.fr.b₂} : Set G) \ (zpowers c.s.fr.z : Set G)) := by
    simpa only [SFrame.Z] using hOW.2.1
  have h9 : IsOrbitMod P₃ (zpowers c.s.fr.z)
      ((c.s.fr.A : Set G) \ ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) ∪
        (closure {c.s.fr.a₂, c.s.fr.b₂} : Set G))) := by
    simpa only [SFrame.Z] using hOW.2.2
  have hVc : ∀ a ∈ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  have hVab : ∀ v ∈ V1 c.e, ∀ w ∈ V1 c.e, v * w = w * v := y7a_V_ab_cen h
  have hAVC : c.s.fr.A ⊔ V1 c.e ≤ C6 c.e :=
    le_trans (y7a_AV_le_C1 h) (y7a_C1_le_C6 c hH hF)
  have hCV : ∀ m ∈ C6 c.e, ∀ v ∈ V1 c.e, m * v * m⁻¹ ∈ V1 c.e :=
    fun m hm v hv => (Subgroup.mem_normalizer_iff.mp (hC6X hm).2 v).mp hv
  have hCAV : ∀ m ∈ C6 c.e, ∀ x ∈ c.s.fr.A ⊔ V1 c.e,
      m * x * m⁻¹ ∈ c.s.fr.A ⊔ V1 c.e :=
    fun m hm x hx => (y7a_conj_AV h (hC6X hm).1 (hC6X hm).2 x).mp hx
  have hP3V : ∀ k ∈ P₃, ∀ v ∈ V1 c.e, k * v * k⁻¹ ∈ V1 c.e :=
    fun k hk v hv => (Subgroup.mem_normalizer_iff.mp (hP3X hk).2 v).mp hv
  have hP3AV : ∀ k ∈ P₃, ∀ x ∈ c.s.fr.A ⊔ V1 c.e,
      k * x * k⁻¹ ∈ c.s.fr.A ⊔ V1 c.e :=
    fun k hk x hx => (y7a_conj_AV h (hP3X hk).1 (hP3X hk).2 x).mp hx
  have hP3C : ∀ k ∈ P₃, ∀ m ∈ C6 c.e, k * m * k⁻¹ ∈ C6 c.e :=
    fun k hk m hm => y7a_C6_normal c hH hF k (hP3X hk) m hm
  exact y7a_central_AV (A := c.s.fr.A) (V := V1 c.e) (P3 := P₃) (C := C6 c.e)
    (a₁ := c.s.fr.a₁) (b₁ := c.s.fr.b₁) (a₂ := c.s.fr.a₂) (b₂ := c.s.fr.b₂)
    (z := c.s.fr.z)
    h.cfg.hA h.cfg.rel h.cfg.z_ne h.cfg.card_A (y7a_A_inf_V h) hVc hVab hP3z
    hU hW h9 (y7a_C6_isPGroup c) hAVC hCV hCAV hP3V hP3AV hP3C

theorem y7a_comm_M6_AV (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ⁅M6 c.e, AV1 c.e⁆ ≤ V1 c.e := by
  rw [Subgroup.commutator_le]
  intro m hm x hx
  exact y7a_comm_C6_AV c hH hF m (y7a_M6_le_C6 c hm) x hx

end CFSG.OddStandard.HigherRank.YamadaG23
