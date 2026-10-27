module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3SimpSec

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

private theorem normal_map_subgroupOf_map {X Y : Type} [Group X] [Group Y] (φ : X →* Y)
    (H N : Subgroup X) (hNH : N ≤ H) [hn : (N.subgroupOf H).Normal] :
    ((N.map φ).subgroupOf (H.map φ)).Normal := by
  refine ⟨fun n hn' g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn' ⊢
  obtain ⟨x, hx, hxn⟩ := Subgroup.mem_map.mp hn'
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp g.2
  have hc : y * x * y⁻¹ ∈ N := by
    have h1 := hn.conj_mem ⟨x, hNH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  refine Subgroup.mem_map.mpr ⟨y * x * y⁻¹, hc, ?_⟩
  simp only [map_mul, map_inv, hyg, hxn, Subgroup.coe_mul, Subgroup.coe_inv]

theorem isSimpleSection_map_injective {X Y : Type} [Group X] [Group Y] (φ : X →* Y)
    (hφ : Function.Injective φ) {H N : Subgroup X} (h : S622IsSimpleSection H N) :
    S622IsSimpleSection (H.map φ) (N.map φ) := by
  obtain ⟨hNH, hnorm, hne, hmax, hnc⟩ := h
  unfold S622IsSimpleSection
  refine ⟨Subgroup.map_mono hNH, normal_map_subgroupOf_map φ H N hNH, ?_, ?_, ?_⟩
  · intro heq
    exact hne (Subgroup.map_injective hφ heq)
  · intro M hNM hMH hMn
    have hrange : M ≤ φ.range := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp (hMH hy)
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    have hN0 : N ≤ M.comap φ := by
      intro x hx
      exact Subgroup.mem_comap.mpr (hNM (Subgroup.mem_map_of_mem φ hx))
    have hH0 : M.comap φ ≤ H := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hMH (Subgroup.mem_comap.mp hx))
      have hyx' : y = x := hφ hyx
      rw [← hyx']
      exact hy
    have hn0 : ((M.comap φ).subgroupOf H).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hn ⊢
      have hmem := hMn.conj_mem ⟨φ (n : X), Subgroup.mem_map_of_mem φ n.2⟩
        (Subgroup.mem_subgroupOf.mpr hn) ⟨φ (g : X), Subgroup.mem_map_of_mem φ g.2⟩
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    rcases hmax (M.comap φ) hN0 hH0 hn0 with h0 | h0
    · left
      rw [← h0]
      exact (Subgroup.map_comap_eq_self hrange).symm
    · right
      rw [← h0]
      exact (Subgroup.map_comap_eq_self hrange).symm
  · intro hall
    apply hnc
    intro a ha b hb
    have hc := hall (φ a) (Subgroup.mem_map_of_mem φ ha) (φ b) (Subgroup.mem_map_of_mem φ hb)
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hc
    have hza : z = a * b * a⁻¹ * b⁻¹ := hφ (by rw [hzeq]; simp only [map_mul, map_inv])
    rw [← hza]
    exact hz

theorem isSimpleSection_of_quotient_equiv {A : Type} [Group A] {H N : Subgroup A} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] {Q : Type} [Group Q] (e : ↥H ⧸ N.subgroupOf H ≃* Q)
    (hQ : IsSimpleGroup Q) (hnc : ∃ a b : Q, a * b ≠ b * a) : S622IsSimpleSection H N := by
  have hsimple : IsSimpleGroup (↥H ⧸ N.subgroupOf H) := e.isSimpleGroup
  have hnc' : ∃ a b : ↥H ⧸ N.subgroupOf H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h2 := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
  have hD : N.subgroupOf H ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (↥H ⧸ N.subgroupOf H) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨a, b, hab⟩ := hnc
    have hsubQ : Subsingleton Q := ⟨fun x y => by
      have h3 := congrArg e (Subsingleton.elim (e.symm x) (e.symm y))
      simpa only [MulEquiv.apply_symm_apply] using h3⟩
    apply hab
    rw [Subsingleton.elim a b]
  have h := isSimpleSection_range_map H.subtype H.subtype_injective (N.subgroupOf H) hD hsimple
    hnc'
  rw [Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le hNH] at h
  exact h

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
