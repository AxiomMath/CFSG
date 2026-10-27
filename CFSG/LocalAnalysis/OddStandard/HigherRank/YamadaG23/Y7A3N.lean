module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3C6p
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3Inv

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_V_ab_n {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}
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

private lemma y7a_norm_conj {S : Subgroup G} {x : G} (hx : x ∈ normalizer (S : Set G)) :
    (∀ y ∈ S, x * y * x⁻¹ ∈ S) ∧ (∀ y ∈ S, x⁻¹ * y * x ∈ S) := by
  refine ⟨fun y hy => (Subgroup.mem_set_normalizer_iff.mp hx y).mp hy, fun y hy => ?_⟩
  simpa using (Subgroup.mem_set_normalizer_iff.mp ((normalizer (S : Set G)).inv_mem hx) y).mp hy

theorem y7a_fact73 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) (h72 : c.Fact72) : c.Fact73 := by
  classical
  have h := c.y7acfg hH
  have hC6X : C6 c.e ≤ y7aX c := y7a_C6_le_X c hH hF
  have hM6C6 : M6 c.e ≤ C6 c.e := y7a_M6_le_C6 c
  have h3a : ⁅M6 c.e, M6 c.e⁆ = V1 c.e := h72.2.2.1.1
  have h3b : ∀ m ∈ M6 c.e, m ^ 2 ∈ V1 c.e := y7a_sq_of_secProp h72.2.2.1.2
  have hcomm : ⁅C6 c.e, C6 c.e⁆ = AV1 c.e := y7a_C6_comm_eq c hH hF h71 h3a
  have htC6 : c.s.t ∈ C6 c.e :=
    y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_right (y7a_t_mem_C0 h))
  have ht2 : c.s.t * c.s.t = 1 := y7a_t_sq h
  have hVV : ∀ v ∈ V1 c.e, ∀ w ∈ V1 c.e, v * w = w * v := y7a_V_ab_n h
  have hVA : ∀ a ∈ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  have hVcen : ∀ v ∈ V1 c.e, ∀ u ∈ AV1 c.e, v * u = u * v := by
    intro v hv u hu
    obtain ⟨a, ha, v', hv', rfl⟩ := y7a_AV_elems h u hu
    calc v * (a * v') = (v * a) * v' := by group
      _ = (a * v) * v' := by rw [← hVA a ha v hv]
      _ = a * (v * v') := by group
      _ = a * (v' * v) := by rw [hVV v hv v' hv']
      _ = (a * v') * v := by group
  have hconj : ∀ z ∈ normalizer (C6 c.e : Set G), ∀ g ∈ C1 c.e, z * g * z⁻¹ ∈ C1 c.e := by
    intro z hz g hg
    obtain ⟨hzC, hziC⟩ := y7a_norm_conj hz
    have hAVz : ∀ w ∈ AV1 c.e, z * w * z⁻¹ ∈ AV1 c.e := fun w hw => by
      rw [← hcomm] at hw ⊢
      exact y7a_comm_conj_mem hzC hw
    have hAVzi : ∀ w ∈ AV1 c.e, z⁻¹ * w * z ∈ AV1 c.e := fun w hw => by
      rw [← hcomm] at hw ⊢
      have := y7a_comm_conj_mem (C := C6 c.e) (x := z⁻¹)
        (fun y hy => by simpa using hziC y hy) hw
      simpa using this
    have hV_stab : ∀ z : G, (∀ w ∈ AV1 c.e, z * w * z⁻¹ ∈ AV1 c.e) →
        (∀ w ∈ AV1 c.e, z⁻¹ * w * z ∈ AV1 c.e) → ∀ v ∈ V1 c.e, z * v * z⁻¹ ∈ V1 c.e := by
      intro z hz hzi v hv
      refine y7a_cen_AV h _ (hz v (Subgroup.mem_sup_right hv)) ?_
      intro u hu
      have hu' : z⁻¹ * u * z ∈ AV1 c.e := hzi u hu
      have h1 := hVcen v hv _ hu'
      calc z * v * z⁻¹ * u = z * (v * (z⁻¹ * u * z)) * z⁻¹ := by group
        _ = z * ((z⁻¹ * u * z) * v) * z⁻¹ := by rw [h1]
        _ = u * (z * v * z⁻¹) := by group
    have hzV : ∀ v ∈ V1 c.e, z * v * z⁻¹ ∈ V1 c.e := hV_stab z hAVz hAVzi
    have hzt_notM6 : z * c.s.t * z⁻¹ ∉ M6 c.e := by
      intro hy
      apply y7a_t_not_mem_M6 c hH
      have hteq : c.s.t = z⁻¹ * (z * c.s.t * z⁻¹) * z := by group
      rw [hteq]
      refine Subgroup.mem_inf.mpr ⟨hziC _ (Subgroup.mem_inf.mp hy).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hcy := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 _ (hzV v hv)
      calc v * (z⁻¹ * (z * c.s.t * z⁻¹) * z)
          = z⁻¹ * ((z * v * z⁻¹) * (z * c.s.t * z⁻¹)) * z := by group
        _ = z⁻¹ * ((z * c.s.t * z⁻¹) * (z * v * z⁻¹)) * z := by rw [hcy]
        _ = (z⁻¹ * (z * c.s.t * z⁻¹) * z) * v := by group
    have hzt_sq : (z * c.s.t * z⁻¹) ^ 2 ∈ V1 c.e := by
      have : (z * c.s.t * z⁻¹) ^ 2 = 1 := by
        rw [pow_two]
        calc z * c.s.t * z⁻¹ * (z * c.s.t * z⁻¹) = z * (c.s.t * c.s.t) * z⁻¹ := by group
          _ = 1 := by rw [ht2]; group
      rw [this]
      exact (V1 c.e).one_mem
    have hzt_C1 : z * c.s.t * z⁻¹ ∈ C1 c.e :=
      y7a_inv_mem_C1 c hH hF h3b (hzC _ htC6) hzt_notM6 hzt_sq
    have hle : (c.s.fr.A ⊔ C0 c.e) ≤ (C1 c.e).comap (MulAut.conj z).toMonoidHom := by
      apply sup_le
      · intro a ha
        show z * a * z⁻¹ ∈ C1 c.e
        exact y7a_AV_le_C1 h (hAVz a (Subgroup.mem_sup_left ha))
      · rw [h.cfg.hC0, Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · show z * (c.d * c.s.t) * z⁻¹ ∈ C1 c.e
          have heq : z * (c.d * c.s.t) * z⁻¹ = (z * c.d * z⁻¹) * (z * c.s.t * z⁻¹) := by group
          rw [heq]
          exact (C1 c.e).mul_mem
            (y7a_AV_le_C1 h (Subgroup.mem_sup_right (hzV c.d (y7a_d_mem_V h)))) hzt_C1
        · exact hzt_C1
    exact hle hg
  apply le_antisymm
  · intro x hx
    have h1 : x ∈ normalizer (C1 c.e : Set G) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro g
      constructor
      · exact hconj x hx g
      · intro hg
        have hmem := hconj x⁻¹ ((normalizer (C6 c.e : Set G)).inv_mem hx) _ hg
        have heq : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
        rw [heq] at hmem
        exact hmem
    rw [h71.2.1.1] at h1
    exact h1
  · apply sup_le
    · intro n hn
      have hnX : n ∈ y7aX c := by
        rw [← y7a_NC1_eq c hH hF, h71.2.1.1]
        exact Subgroup.mem_sup_left hn
      rw [Subgroup.mem_set_normalizer_iff]
      intro y
      constructor
      · exact y7a_C6_normal c hH hF n hnX y
      · intro hy
        have hmem := y7a_C6_normal c hH hF n⁻¹ ((y7aX c).inv_mem hnX) _ hy
        have heq : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y := by group
        rw [heq] at hmem
        exact hmem
    · exact hM6C6.trans Subgroup.le_normalizer

end CFSG.OddStandard.HigherRank.YamadaG23
