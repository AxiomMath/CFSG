module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelAction

public section

namespace CFSG.ComponentClassification.J2Cover.CyclicKernel

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_normalizer_action
  exists_mul_of_mem_sup_of_commute mul_comm_of_isCyclic)
open scoped Pointwise

section Action

variable {X : Type*} [Group X] {Q : Type*} [Group Q] {L H : Subgroup X} (hLH : L ≤ H)
  {π : L →* Q} (hπ : Function.Surjective π) {θ : H →* MulAut Q}
  (hθ : ∀ (h : H) (l l' : L), (l' : X) = h * l * (h : X)⁻¹ → θ h (π l) = π l')

include hπ hθ in
theorem action_eq_conj (l : L) : θ ⟨l, hLH l.2⟩ = MulAut.conj (π l) := by
  ext q
  obtain ⟨m, rfl⟩ := hπ q
  rw [hθ ⟨l, hLH l.2⟩ m (l * m * l⁻¹) rfl, MulAut.conj_apply, map_mul, map_mul, map_inv]

include hLH hπ hθ in
theorem inner_le_range_action : inner Q ≤ θ.range := by
  rintro _ ⟨m, rfl⟩
  obtain ⟨l, rfl⟩ := hπ m
  exact ⟨⟨l, hLH l.2⟩, action_eq_conj hLH hπ hθ l⟩

include hLH hπ hθ in
theorem action_mem_inner_iff (hθ1 : ∀ h : H, θ h = 1 ↔ (h : X) ∈ centralizer (L : Set X))
    (h : H) : θ h ∈ inner Q ↔ (h : X) ∈ L ⊔ (centralizer (L : Set X) ⊓ H) := by
  have hc : ∀ k ∈ L, ∀ n ∈ centralizer (L : Set X) ⊓ H, k * n = n * k :=
    fun k hk n hn => mem_centralizer_iff.mp hn.1 k hk
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨l, rfl⟩ := hπ m
    have h1 : θ (⟨l, hLH l.2⟩⁻¹ * h) = 1 := by
      rw [map_mul, map_inv, action_eq_conj hLH hπ hθ, ← hm, inv_mul_cancel]
    rw [hθ1] at h1
    have h2 : (h : X) = l * ((l : X)⁻¹ * h) := by group
    rw [h2]
    exact mul_mem (mem_sup_left l.2) (mem_sup_right ⟨h1, H.mul_mem (H.inv_mem (hLH l.2)) h.2⟩)
  · intro hh
    obtain ⟨k, hk, n, hn, hkn⟩ := exists_mul_of_mem_sup_of_commute hc hh
    have hsplit : h = ⟨k, hLH hk⟩ * ⟨n, hn.2⟩ := Subtype.ext hkn
    have hn1 : θ ⟨n, hn.2⟩ = 1 := (hθ1 _).mpr hn.1
    rw [hsplit, map_mul, hn1, mul_one, action_eq_conj hLH hπ hθ ⟨k, hk⟩]
    exact ⟨_, rfl⟩

include hLH hπ hθ in
theorem sq_mem_sup_of_action (hidx : (inner Q).index = 2)
    (hθ1 : ∀ h : H, θ h = 1 ↔ (h : X) ∈ centralizer (L : Set X)) (h : H) :
    (h : X) ^ 2 ∈ L ⊔ (centralizer (L : Set X) ⊓ H) := by
  have h2 := (action_mem_inner_iff hLH hπ hθ hθ1 (h ^ 2)).mp (by
    rw [map_pow]
    exact sq_mem_of_index_two hidx _)
  rwa [SubgroupClass.coe_pow] at h2

end Action

section Obstruction

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem sq_mul_comm_of_kernel {Q : Type*} [Group Q] (hidx : (inner Q).index = 2)
    {L T : Subgroup G} {t : G} (hLq : CFSG.Assembly.IsQuasisimple L) (π : L →* Q)
    (hπ : Function.Surjective π) (hker : π.ker = center L) (hLH : L ≤ centralizer {t})
    (hHN : centralizer {t} ≤ normalizer (L : Set G))
    (hT : centralizer (L : Set G) ⊓ centralizer {t} = T) (hTc : IsCyclic T) :
    (∀ h ∈ centralizer {t}, ∀ s ∈ T, h * s * h⁻¹ ∈ T) ∧
      ∀ h ∈ centralizer {t}, ∀ s ∈ T, h ^ 2 * s = s * h ^ 2 := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  obtain ⟨θ, hθ, hθ1⟩ := exists_normalizer_action hHN π hπ hker
  refine ⟨fun h hh s hs => ?_, fun h hh s hs => ?_⟩
  · rw [← hT] at hs ⊢
    refine ⟨mem_centralizer_iff.mpr fun l hl => ?_,
      (centralizer {t}).mul_mem ((centralizer {t}).mul_mem hh hs.2) ((centralizer {t}).inv_mem hh)⟩
    have hl' : h⁻¹ * l * h ∈ L := by
      have := (mem_normalizer_iff.mp (hHN (inv_mem hh)) l).mp hl
      rwa [inv_inv] at this
    have hsl := mem_centralizer_iff.mp hs.1 _ hl'
    calc l * (h * s * h⁻¹) = h * (h⁻¹ * l * h * s) * h⁻¹ := by group
      _ = h * (s * (h⁻¹ * l * h)) * h⁻¹ := by rw [hsl]
      _ = h * s * h⁻¹ * l := by group
  · have h2 := sq_mem_sup_of_action hLH hπ hθ hidx hθ1 ⟨h, hh⟩
    rw [hT] at h2
    have hc : ∀ k ∈ L, ∀ n ∈ T, k * n = n * k := fun k hk n hn => by
      rw [← hT] at hn
      exact mem_centralizer_iff.mp hn.1 k hk
    obtain ⟨k, hk, n, hn, hkn⟩ := exists_mul_of_mem_sup_of_commute hc h2
    simp only at hkn
    rw [hkn, mul_assoc, mul_comm_of_isCyclic hTc hn hs, ← mul_assoc, hc k hk s hs, mul_assoc]

theorem j2_cyclic_kernel_obstruction {L T : Subgroup G} {t : G}
    (hLq : CFSG.Assembly.IsQuasisimple L) (π : L →* P) (hπ : Function.Surjective π)
    (hker : π.ker = center L) (hLH : L ≤ centralizer {t})
    (hHN : centralizer {t} ≤ normalizer (L : Set G))
    (hT : centralizer (L : Set G) ⊓ centralizer {t} = T) (hTc : IsCyclic T)
    (hT2 : IsPGroup 2 T) (hT4 : 4 ≤ Nat.card T) (htT : t ∈ T) (ht : orderOf t = 2) (g : G)
    (hg : ∀ s ∈ T, g⁻¹ * s * g ∈ centralizer {t}) : g ∈ centralizer {t} := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  obtain ⟨θ, hθ, hθ1⟩ := exists_normalizer_action hHN π hπ hker
  obtain ⟨hTn, hsq⟩ := sq_mul_comm_of_kernel index_inner_P hLq π hπ hker hLH hHN hT hTc
  have hSH : (T.subgroupOf (centralizer {t})).Normal := by
    constructor
    intro n hn c
    rw [mem_subgroupOf] at hn ⊢
    exact hTn c c.2 n hn
  have hker' : θ.rangeRestrict.ker = T.subgroupOf (centralizer {t}) := by
    ext h
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hθ1, mem_subgroupOf, ← hT]
    exact ⟨fun h1 => ⟨h1, h.2⟩, fun h1 => h1.1⟩
  have hJ := (ctss_j2_automorphism_involution_centralizers_exclude_small_normal_four_groups).2.1
    θ.range (inner_le_range_action hLH hπ hθ)
  have hg' : MulAut.conj g⁻¹ • T ≤ centralizer {t} := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, MulAut.smul_def,
      MulAut.conj_apply] at hx
    have h := hg _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
  exact (CentralCover.cyclic_centralizer_kernel_small_normal_four_obstruction hTc hT2 hT4 htT ht
    rfl hSH hsq θ.rangeRestrict θ.rangeRestrict_surjective hker'
    (fun v hv N hN h => by
      obtain ⟨-, hN'⟩ := hJ v hv
      rcases h with h | h
      · exact h.elim (hN' N hN).1.false
      · exact h.elim (hN' N hN).2.false) g hg').2

end Obstruction

end CFSG.ComponentClassification.J2Cover.CyclicKernel
