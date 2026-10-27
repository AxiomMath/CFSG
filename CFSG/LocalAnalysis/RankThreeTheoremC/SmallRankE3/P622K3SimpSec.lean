module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

private theorem image_mem_iff {G A : Type} [Group G] [Group A] (φ : G →* A)
    (hφ : Function.Injective φ) (D : Subgroup G) (g : G) :
    φ g ∈ D.map φ ↔ g ∈ D := by
  refine ⟨fun h => ?_, fun h => Subgroup.mem_map_of_mem φ h⟩
  obtain ⟨d, hd, hdg⟩ := Subgroup.mem_map.mp h
  obtain rfl := hφ hdg
  exact hd

private theorem map_ne_range {G A : Type} [Group G] [Group A] (φ : G →* A)
    (hφ : Function.Injective φ) (D : Subgroup G) (hD : D ≠ ⊤) :
    D.map φ ≠ φ.range := by
  intro h
  apply hD
  rw [eq_top_iff]
  intro g _
  have hmem : φ g ∈ D.map φ := by
    rw [h]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  exact (image_mem_iff φ hφ D g).mp hmem

private theorem normal_map_subgroupOf {G A : Type} [Group G] [Group A] (φ : G →* A)
    (D : Subgroup G) [hDn : D.Normal] :
    ((D.map φ).subgroupOf φ.range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨d, hd, hdn⟩ := Subgroup.mem_map.mp hn
  obtain ⟨x, hxg⟩ := MonoidHom.mem_range.mp g.2
  have h1 : φ (x * d * x⁻¹) ∈ D.map φ :=
    Subgroup.mem_map_of_mem φ (hDn.conj_mem d hd x)
  rw [map_mul, map_mul, map_inv] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hxg, ← hdn]
  exact h1

private theorem eq_or_eq_range {G A : Type} [Group G] [Group A] (φ : G →* A)
    (hφ : Function.Injective φ) (D : Subgroup G) [D.Normal]
    (hsimple : IsSimpleGroup (G ⧸ D)) (N : Subgroup A) (hN1 : D.map φ ≤ N)
    (hN2 : N ≤ φ.range) (hN3 : (N.subgroupOf φ.range).Normal) :
    N = D.map φ ∨ N = φ.range := by
  have hDN : D ≤ N.comap φ := by
    intro d hd
    rw [Subgroup.mem_comap]
    exact hN1 (Subgroup.mem_map_of_mem φ hd)
  have hN' : (N.comap φ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    have hn' : (⟨φ n, MonoidHom.mem_range.mpr ⟨n, rfl⟩⟩ : φ.range) ∈ N.subgroupOf φ.range :=
      Subgroup.mem_subgroupOf.mpr hn
    have key := hN3.conj_mem _ hn' ⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
    rw [Subgroup.mem_subgroupOf] at key
    rw [map_mul, map_mul, map_inv]
    exact key
  have hMn : ((N.comap φ).map (QuotientGroup.mk' D)).Normal :=
    hN'.map (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((N.comap φ).map (QuotientGroup.mk' D)) with hM | hM
  · have hEq : N.comap φ = D := by
      refine le_antisymm ?_ hDN
      intro g hg
      have hgM : QuotientGroup.mk' D g ∈ (N.comap φ).map (QuotientGroup.mk' D) :=
        Subgroup.mem_map_of_mem _ hg
      rw [hM, Subgroup.mem_bot] at hgM
      exact (QuotientGroup.eq_one_iff (N := D) g).mp hgM
    left
    rw [← Subgroup.map_comap_eq_self hN2, hEq]
  · have htop : N.comap φ = ⊤ := by
      refine eq_top_iff.mpr ?_
      intro g _
      have hgM : QuotientGroup.mk' D g ∈ (N.comap φ).map (QuotientGroup.mk' D) := by
        rw [hM]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hgM
      have hng' : (n : G ⧸ D) = (g : G ⧸ D) := hng
      have hkey : n⁻¹ * g ∈ D := QuotientGroup.eq.mp hng'
      have h2 := (N.comap φ).mul_mem hn (hDN hkey)
      simpa only [mul_inv_cancel_left] using h2
    right
    rw [← Subgroup.map_comap_eq_self hN2, htop, MonoidHom.range_eq_map]

theorem isSimpleSection_range_map {G A : Type} [Group G] [Group A] (φ : G →* A)
    (hφ : Function.Injective φ) (D : Subgroup G) [D.Normal] (hD : D ≠ ⊤)
    (hsimple : IsSimpleGroup (G ⧸ D)) (hnc : ∃ a b : G ⧸ D, a * b ≠ b * a) :
    S622IsSimpleSection φ.range (D.map φ) := by
  unfold S622IsSimpleSection
  refine ⟨?_, normal_map_subgroupOf φ D, map_ne_range φ hφ D hD,
    fun N hN1 hN2 hN3 => eq_or_eq_range φ hφ D hsimple N hN1 hN2 hN3, ?_⟩
  · rintro y hy
    obtain ⟨g, _, rfl⟩ := Subgroup.mem_map.mp hy
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  · intro hall
    obtain ⟨a, b, hab⟩ := hnc
    obtain ⟨g1, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨g2, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hc := hall (φ g1) (MonoidHom.mem_range.mpr ⟨g1, rfl⟩)
      (φ g2) (MonoidHom.mem_range.mpr ⟨g2, rfl⟩)
    have hc' : g1 * g2 * g1⁻¹ * g2⁻¹ ∈ D := by
      rw [← image_mem_iff φ hφ D]
      simpa only [map_mul, map_inv] using hc
    have h1 := ‹D.Normal›.conj_mem _ hc' (g2 * g1)⁻¹
    have h2 : (g2 * g1)⁻¹ * (g1 * g2 * g1⁻¹ * g2⁻¹) * ((g2 * g1)⁻¹)⁻¹
        = (g2 * g1)⁻¹ * (g1 * g2) := by
      group
    rw [h2] at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq.mpr h1).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
