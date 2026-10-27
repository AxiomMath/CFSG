module

public import CFSG.GH74.Uniqueness.SU.SU4L185

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

variable {G : Type} [Group G]

omit [Group G] in
theorem orderOf_conj' {G : Type} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ := by
  ext y
  simp only [mem_conjSub, Subgroup.mem_bot]
  constructor
  · intro h
    have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, h]; group
  · intro h
    rw [h]; group

theorem conjSub_sup (g : G) (E F : Subgroup G) : conjSub g (E ⊔ F) = conjSub g E ⊔ conjSub g F :=
  Subgroup.map_sup _ _ _

theorem conjSub_zpowers (g x : G) : conjSub g (zpowers x) = zpowers (g * x * g⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

theorem closure_pair_eq (a b : G) : Subgroup.closure ({a, b} : Set G) = zpowers a ⊔ zpowers b := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))

section Finite

variable [Finite G]

theorem Conf181.conj {X V S K : Subgroup G} {x z : G} (h : Conf181 X V x z S K) {m : G}
    (hm : m ∈ X) :
    Conf181 X (conjSub m V) (m * x * m⁻¹) (m * z * m⁻¹) (conjSub m S) (conjSub m K) where
  x_mem := mem_conjSub_of_mem h.x_mem
  z_mem := mem_conjSub_of_mem h.z_mem
  hx := by rw [orderOf_conj']; exact h.hx
  hz := by rw [orderOf_conj']; exact h.hz
  gen := by rw [h.gen, conjSub_sup, conjSub_zpowers, conjSub_zpowers]
  syl := by
    have := h.syl.conj m
    rwa [conjSub_self_of_mem hm] at this
  syl_c := by
    have := h.syl_c.conj m
    rwa [conjSub_inf, conjSub_inf, conjSub_centralizer_singleton, conjSub_self_of_mem hm] at this
  K_le := by
    have := conjSub_mono (g := m) h.K_le
    rwa [conjSub_inf, conjSub_centralizer_singleton] at this
  K_inf := by
    have := congrArg (conjSub m) h.K_inf
    rwa [conjSub_inf, conjSub_zpowers, conjSub_bot] at this
  K_sup := by
    have := congrArg (conjSub m) h.K_sup
    rwa [conjSub_sup, conjSub_inf, conjSub_zpowers, conjSub_centralizer_singleton] at this
  z_K := mem_conjSub_of_mem h.z_K
  K_inv := by
    intro k hk hk2
    rw [mem_conjSub] at hk
    have h1 : (m⁻¹ * k * m) * (m⁻¹ * k * m) = 1 := by
      calc (m⁻¹ * k * m) * (m⁻¹ * k * m) = m⁻¹ * (k * k) * m := by group
        _ = 1 := by rw [hk2]; group
    rcases h.K_inv _ hk h1 with h2 | h2
    · left
      have : k = m * (m⁻¹ * k * m) * m⁻¹ := by group
      rw [this, h2]; group
    · right
      have : k = m * (m⁻¹ * k * m) * m⁻¹ := by group
      rw [this, h2]
  z_cent := by
    intro s hs
    rw [mem_conjSub] at hs
    have := (conj_comm_iff m _ _).mp (h.z_cent _ hs)
    have e1 : m * (m⁻¹ * s * m) * m⁻¹ = s := by group
    rwa [e1] at this
  z_uniq := by
    intro c hc hcc hc2
    rw [mem_conjSub] at hc
    have h1 : ∀ s ∈ S, s * (m⁻¹ * c * m) = (m⁻¹ * c * m) * s := by
      intro s hs
      have := hcc (m * s * m⁻¹) (mem_conjSub_of_mem hs)
      have := (conj_comm_iff m⁻¹ _ _).mp this
      simpa [mul_assoc] using this
    have h2 : (m⁻¹ * c * m) * (m⁻¹ * c * m) = 1 := by
      calc (m⁻¹ * c * m) * (m⁻¹ * c * m) = m⁻¹ * (c * c) * m := by group
        _ = 1 := by rw [hc2]; group
    rcases h.z_uniq _ hc h1 h2 with h3 | h3
    · left
      have : c = m * (m⁻¹ * c * m) * m⁻¹ := by group
      rw [this, h3]; group
    · right
      have : c = m * (m⁻¹ * c * m) * m⁻¹ := by group
      rw [this, h3]
  x_not := by
    intro hxO
    apply h.x_not
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hxO
    refine Subgroup.mem_map.mpr ⟨(⟨m, hm⟩ : ↥X)⁻¹ * y * ⟨m, hm⟩, ?_, ?_⟩
    · simpa using (normal_oResidual ↥X).conj_mem y hy (⟨m, hm⟩ : ↥X)⁻¹
    · have h1 : (y : G) = m * x * m⁻¹ := hyeq
      show m⁻¹ * (y : G) * m = x
      rw [h1]; group

end Finite

variable {G : Type} [Group G]

theorem Conf18H.of_conf181 {S : Sylow 2 G} {M V K : Subgroup G} {x z : G}
    (hV : IsIsolatedVertex M V) (hSM : (S : Subgroup G) ≤ M)
    (hc : Conf181 M V x z (S : Subgroup G) K) : Conf18H S M V x z where
  S_le := hSM
  iso := hV
  gen := by rw [closure_pair_eq]; exact hc.gen
  hx := hc.hx
  hz := hc.hz
  K_ex := ⟨K, hc.K_le, hc.K_inf, hc.K_sup, hc.z_K, hc.K_inv⟩
  syl_c := hc.syl_c
  z_center := hc.z_cent
  z_unique := hc.z_uniq
  x_mem := hV.isFour.1 hc.x_mem
  x_not := fun h => hc.x_not (Subgroup.mem_map.mpr ⟨_, h, rfl⟩)

theorem Conf18H.z_mem_S {S : Sylow 2 G} {M V : Subgroup G} {x z : G} (hc : Conf18H S M V x z) :
    z ∈ (S : Subgroup G) := by
  obtain ⟨K, hK1, -, -, hzK, -⟩ := hc.K_ex
  exact (Subgroup.mem_inf.mp (hK1 hzK)).2

theorem Conf18H.z_mul_self {S : Sylow 2 G} {M V : Subgroup G} {x z : G}
    (hc : Conf18H S M V x z) : z * z = 1 := by
  rw [← pow_two]
  exact hc.hz ▸ pow_orderOf_eq_one z

theorem Conf18H.z_ne_one {S : Sylow 2 G} {M V : Subgroup G} {x z : G}
    (hc : Conf18H S M V x z) : z ≠ 1 := by
  intro h
  have := hc.hz
  rw [h, orderOf_one] at this
  omega

section Finite

variable [Finite G]

theorem lemma18H_core :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M : Subgroup G), Hyp184Core S U M →
      (∃ V : Subgroup G, IsIsolatedVertex M V) → ∃ (V : Subgroup G) (x z : G), Conf18H S M V x z := by
  intro G _ _ S U M h ⟨V₀, hV₀⟩
  have hX : 3 ≤ Open.pRank 2 M := h.rank.trans (SU1.pRank_mono (by norm_num) h.S_le)
  obtain ⟨x, z, S', K, hc⟩ := lemma181_core hX hV₀
  obtain ⟨m, hmM, hSm⟩ := hc.syl.exists_conj_eq h.isSylowIn_M
  have hc' := hc.conj hmM
  rw [← hSm] at hc'
  exact ⟨conjSub m V₀, m * x * m⁻¹, m * z * m⁻¹,
    Conf18H.of_conf181 (isIsolatedVertex_conjSub (conjSub_self_of_mem hmM) hV₀) h.S_le hc'⟩

theorem lemma18H : Lemma18HStmt := by
  intro G _ _ S U M h hV
  exact lemma18H_core G S U M h.toHyp184Core hV

end Finite

end CFSG.GH74.Uniqueness.SU.SU4
