module

public import CFSG.RankThree.Native.ONTripleAut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

theorem on25_perfect_of_simple {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H) = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have : ⁅a, b⁆ ∈ (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem on25_center_eq_bot_of_simple {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) : Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have : a ∈ Subgroup.center H := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem on25_alt6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem on25_alt6_nonabelian : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  have h1 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have h2 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 3 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hne : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 * (Equiv.swap 0 1 * Equiv.swap 1 3) ≠
      Equiv.swap 0 1 * Equiv.swap 1 3 * (Equiv.swap 0 1 * Equiv.swap 1 2) := by decide
  exact ⟨⟨_, h1⟩, ⟨_, h2⟩, fun h => hne (congrArg Subtype.val h)⟩

section


theorem on25_z_mem_commutator_K0 : zG ∈ ⁅K0G, K0G⁆ := by
  have hz3 : zG ^ 3 = 1 := relG.xcube
  have hx1 : xG 1 ∈ centralizer {xG 0} := by
    rw [mem_centralizer_singleton_iff]
    have h := relG.comm (0 : Fin 4) 1
    rw [show (omegaZ 0 1).val = 0 by rw [omegaZ_val]; decide, pow_zero,
      commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  have hx2 : xG 2 ∈ centralizer {xG 0} := by
    rw [mem_centralizer_singleton_iff]
    have h := relG.comm (0 : Fin 4) 2
    rw [show (omegaZ 0 2).val = 0 by rw [omegaZ_val]; decide, pow_zero,
      commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  obtain ⟨a, k, hk, e1⟩ := mem_centralizer_x0_iff.1 ((centralizer {xG 0}).inv_mem hx1)
  obtain ⟨b, k', hk', e2⟩ := mem_centralizer_x0_iff.1 ((centralizer {xG 0}).inv_mem hx2)
  have hk0 : Commute k (xG 0) := K0_comm hk
  have hk0' : Commute k' (xG 0) := K0_comm hk'
  have hc := comm_central (X := xG 0 ^ a) (Y := xG 0 ^ b) (k := k) (k' := k')
    (hk0'.pow_right a).symm (Commute.pow_pow_self _ _ _) (hk0.pow_right b).symm
  rw [← e1, ← e2] at hc
  have h12 : ⁅xG 1, xG 2⁆ = zG ^ 2 := by
    have h := relG.comm (1 : Fin 4) 2
    rw [show (omegaZ 1 2).val = 2 by rw [omegaZ_val]; decide] at h
    exact h
  have hcomm : zG ^ 2 ∈ ⁅K0G, K0G⁆ := by
    rw [← h12, commutatorElement_def]
    have : xG 1 * xG 2 * (xG 1)⁻¹ * (xG 2)⁻¹ = (xG 1)⁻¹⁻¹ * (xG 2)⁻¹⁻¹ * (xG 1)⁻¹ * (xG 2)⁻¹ := by
      simp
    rw [this, hc]
    have := Subgroup.commutator_mem_commutator ((K0G).inv_mem hk) ((K0G).inv_mem hk')
    simpa [commutatorElement_def] using this
  have : zG = (zG ^ 2) ^ 2 := by
    rw [← pow_mul]
    calc zG = zG ^ 3 * zG := by rw [hz3, one_mul]
      _ = zG ^ 4 := by rw [← pow_succ]
  rw [this]
  exact pow_mem hcomm 2

theorem on25_K0_perfect : (⁅(⊤ : Subgroup ↥K0G), ⊤⁆ : Subgroup ↥K0G) = ⊤ := by
  set D : Subgroup ↥K0G := ⁅(⊤ : Subgroup ↥K0G), ⊤⁆ with hD
  have hz : (⟨zG, zG_mem_K0⟩ : ↥K0G) ∈ D := by
    have h := on25_z_mem_commutator_K0
    have e : D.map K0G.subtype = ⁅K0G, K0G⁆ := by
      rw [hD, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [← e] at h
    obtain ⟨d, hd, hdz⟩ := h
    have : d = ⟨zG, zG_mem_K0⟩ := Subtype.ext hdz
    rwa [this] at hd
  have hA6 : ⁅alternatingGroup (Fin 6), alternatingGroup (Fin 6)⁆ =
      alternatingGroup (Fin 6) := by
    have := on25_alt6_simple
    have h1 := Subgroup.map_commutator (f := (alternatingGroup (Fin 6)).subtype)
      (⊤ : Subgroup ↥(alternatingGroup (Fin 6))) ⊤
    rw [on25_perfect_of_simple on25_alt6_nonabelian, Subgroup.map_top,
      Subgroup.range_subtype] at h1
    exact h1.symm
  have hmap : D.map actK = alternatingGroup (Fin 6) := by
    rw [hD, Subgroup.map_commutator, Subgroup.map_top, range_actK, hA6]
  rw [eq_top_iff]
  intro g _
  have hg : actK g ∈ D.map actK := by
    rw [hmap, ← range_actK]
    exact ⟨g, rfl⟩
  obtain ⟨d, hd, hdg⟩ := hg
  have hker : g * d⁻¹ ∈ actK.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdg]
    group
  rw [ker_actK] at hker
  have : g * d⁻¹ ∈ D := (Subgroup.zpowers_le.2 hz) hker
  have e : g = (g * d⁻¹) * d := by group
  rw [e]
  exact D.mul_mem this hd

theorem on25_center_K0 : Subgroup.center ↥K0G = actK.ker := by
  apply le_antisymm
  · intro c hc
    rw [MonoidHom.mem_ker]
    have hz : ∀ y : alternatingGroup (Fin 6), (⟨actK c, by rw [← range_actK]; exact ⟨c, rfl⟩⟩ :
        alternatingGroup (Fin 6)) * y = y * ⟨actK c, by rw [← range_actK]; exact ⟨c, rfl⟩⟩ := by
      intro y
      have hy : (y : Equiv.Perm (Fin 6)) ∈ actK.range := by rw [range_actK]; exact y.2
      obtain ⟨k, hk⟩ := hy
      apply Subtype.ext
      show actK c * y = y * actK c
      rw [← hk, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hc k).symm]
    have := on25_alt6_simple
    have hmem : (⟨actK c, by rw [← range_actK]; exact ⟨c, rfl⟩⟩ : alternatingGroup (Fin 6)) ∈
        Subgroup.center (alternatingGroup (Fin 6)) := Subgroup.mem_center_iff.2 fun y => (hz y).symm
    rw [on25_center_eq_bot_of_simple on25_alt6_nonabelian, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · intro c hc
    rw [ker_actK] at hc
    have hz' : (⟨zG, zG_mem_K0⟩ : ↥K0G) ∈ Subgroup.center ↥K0G :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (zG_central g.1).symm
    exact (Subgroup.zpowers_le.2 hz') hc

theorem on25_card_center_K0 : Nat.card (Subgroup.center ↥K0G) = 3 := by
  rw [on25_center_K0]
  exact card_ker_actK

theorem on25_K0_quasisimple : CFSG.Open.IsQuasisimple ↥K0G := by
  refine ⟨on25_K0_perfect, ?_⟩
  have e : (↥K0G ⧸ Subgroup.center ↥K0G) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq on25_center_K0).trans
      ((QuotientGroup.quotientKerEquivRange actK).trans (MulEquiv.subgroupCongr range_actK))
  have := on25_alt6_simple
  exact e.isSimpleGroup

end

end CFSG.HardMathSupport.Solomon.Coordinator
