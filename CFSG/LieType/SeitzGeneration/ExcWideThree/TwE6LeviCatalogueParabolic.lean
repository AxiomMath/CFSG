module

public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogueWeyl

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.LieType.Steinberg.Adjoint

section Parabolic


variable {K : Type} [Field K]

theorem mem_parabolicSubgroup_of_conj_mem_rootSubgroup {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ adjointGroup TwistTag.E6.tag K) {c₀ : K} (hc₀ : c₀ ≠ 0)
    (h : g * pinnedX TwistTag.E6.tag K e6HighestRoot c₀ * g⁻¹ ∈
      rootSubgroup TwistTag.E6.tag K e6HighestRoot) :
    g ∈ parabolicSubgroup TwistTag.E6.tag K E6GraphLevi.setA := by
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 h
  have hg' : g ∈ ⋃ w, bruhatCell TwistTag.E6.tag K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  have hB := borelGroup_le_normalizer_rootSubgroup (E := K)
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB hb') _).1
    (mem_rootSubgroup.2 ⟨c₀, rfl⟩))
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hd
    have h1 : pinnedX TwistTag.E6.tag K e6HighestRoot c₀ = 1 := by
      calc pinnedX TwistTag.E6.tag K e6HighestRoot c₀ =
            b'⁻¹ * (b' * pinnedX TwistTag.E6.tag K e6HighestRoot c₀ * b'⁻¹) * b' := by group
        _ = 1 := by rw [← hd]; group
    exact hc₀ (pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot
      (h1.trans (pinnedX_zero _ _ _).symm))
  obtain ⟨e, he⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB (inv_mem hb)) _).1
    (mem_rootSubgroup.2 ⟨c, rfl⟩))
  obtain ⟨ε, hε, hn⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w isRoot_e6HighestRoot
  have hkey : pinnedX TwistTag.E6.tag K (w • e6HighestRoot) (ε * d) =
      pinnedX TwistTag.E6.tag K e6HighestRoot e := by
    rw [← hn, he, hd, hc]
    group
  have hεd : ε * d ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hd0
  have hwθ := eq_e6HighestRoot_of_pinnedX_eq (IsRoot.smul isRoot_e6HighestRoot w) hεd hkey
  have hwA : w ∈ parabolicWeylGroup TwistTag.E6.tag E6GraphLevi.setA := by
    have hset := (parabolic_Weyl_coordinate_stabilizer TwistTag.E6.tag E6GraphLevi.setA).1
    have hmem : w ∈ (parabolicWeylGroup TwistTag.E6.tag E6GraphLevi.setA : Set (WeylGroup _)) := by
      rw [hset]
      intro v i hi
      have hi' : i = e6Idx 1 := by
        by_contra h'
        exact hi h'
      subst hi'
      rw [← iform_e6HighestRoot (w • v), ← iform_e6HighestRoot v]
      calc iform e6HighestRoot (w • v) = iform (w • e6HighestRoot) (w • v) := by rw [hwθ]
        _ = iform e6HighestRoot v := iform_smul w e6HighestRoot v
    exact hmem
  have hP := (standard_parabolic_cells TwistTag.E6.tag K).1 E6GraphLevi.setA
  have hmem : b * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * b' ∈
      (parabolicSubgroup TwistTag.E6.tag K E6GraphLevi.setA : Set (ModGL TwistTag.E6.tag K)) := by
    rw [hP]
    exact Set.mem_biUnion hwA hw
  exact hmem

theorem mem_parabolicLevi_of_commute_rootElements {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ adjointGroup TwistTag.E6.tag K) {u v : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot) (hu1 : u ≠ 1)
    (hv : v ∈ rootSubgroup TwistTag.E6.tag K (-e6HighestRoot)) (hv1 : v ≠ 1)
    (hgu : g * u * g⁻¹ = u) (hgv : g * v * g⁻¹ = v) :
    g ∈ parabolicLevi TwistTag.E6.tag K E6GraphLevi.setA := by
  have hP : g ∈ parabolicSubgroup TwistTag.E6.tag K E6GraphLevi.setA := by
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hu
    have hc : c ≠ 0 := fun h => hu1 (by rw [h, pinnedX_zero])
    exact mem_parabolicSubgroup_of_conj_mem_rootSubgroup hg hc (by rw [hgu]; exact hu)
  set n := twE6LeviN0 K with hn_def
  have hn : n ∈ adjointGroup TwistTag.E6.tag K := canonicalRep_mem_adjointGroup _ K _
  have hx : n⁻¹ * v * n ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot := by
    have h1 : v ∈ (rootSubgroup TwistTag.E6.tag K e6HighestRoot).map
        (MulAut.conj n).toMonoidHom := by
      rw [hn_def, map_conj_twE6LeviN0_rootSubgroup_e6HighestRoot]
      exact hv
    obtain ⟨y, hy, hyv⟩ := h1
    have : n⁻¹ * v * n = y := by
      rw [← hyv]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  have hx1 : n⁻¹ * v * n ≠ 1 := by
    intro h
    apply hv1
    have : v = n * (n⁻¹ * v * n) * n⁻¹ := by group
    rw [this, h]
    group
  obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 hx
  have hc'0 : c' ≠ 0 := fun h => hx1 (by rw [← hc', h, pinnedX_zero])
  have hg' : n⁻¹ * g * n ∈ adjointGroup TwistTag.E6.tag K :=
    mul_mem (mul_mem (inv_mem hn) hg) hn
  have hP' : n⁻¹ * g * n ∈ parabolicSubgroup TwistTag.E6.tag K E6GraphLevi.setA := by
    refine mem_parabolicSubgroup_of_conj_mem_rootSubgroup hg' hc'0 ?_
    have : (n⁻¹ * g * n) * pinnedX TwistTag.E6.tag K e6HighestRoot c' * (n⁻¹ * g * n)⁻¹ =
        pinnedX TwistTag.E6.tag K e6HighestRoot c' := by
      rw [hc']
      calc n⁻¹ * g * n * (n⁻¹ * v * n) * (n⁻¹ * g * n)⁻¹ = n⁻¹ * (g * v * g⁻¹) * n := by group
        _ = n⁻¹ * v * n := by rw [hgv]
    rw [this]
    exact mem_rootSubgroup.2 ⟨c', rfl⟩
  have hP'set : n⁻¹ * g * n ∈
      (parabolicSubgroup TwistTag.E6.tag K E6GraphLevi.setA : Set (ModGL TwistTag.E6.tag K)) :=
    hP'
  rw [coe_parabolicSubgroup_eq_mul] at hP'set
  obtain ⟨q, hq, m, hm, hqm⟩ := hP'set
  have hg_eq : g = (n * q * n⁻¹) * (n * m * n⁻¹) := by
    have : g = n * (n⁻¹ * g * n) * n⁻¹ := by group
    rw [this, ← hqm]
    group
  have hq' : n * q * n⁻¹ ∈ oppRadical TwistTag.E6.tag K E6GraphLevi.setA :=
    map_conj_twE6LeviN0_parabolicRadical_le_oppRadical K ⟨q, hq, rfl⟩
  have hm' : n * m * n⁻¹ ∈ parabolicLevi TwistTag.E6.tag K E6GraphLevi.setA :=
    map_conj_twE6LeviN0_parabolicLevi_le K ⟨m, hm, rfl⟩
  have hmP : n * m * n⁻¹ ∈ parabolicSubgroup TwistTag.E6.tag K E6GraphLevi.setA :=
    parabolicLevi_le_parabolicSubgroup _ hm'
  have hq1 : n * q * n⁻¹ = 1 := by
    have hmem : n * q * n⁻¹ ∈ parabolicSubgroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        oppRadical TwistTag.E6.tag K E6GraphLevi.setA := by
      refine Subgroup.mem_inf.2 ⟨?_, hq'⟩
      have : n * q * n⁻¹ = g * (n * m * n⁻¹)⁻¹ := by rw [hg_eq]; group
      rw [this]
      exact mul_mem hP (inv_mem hmP)
    rw [parabolicSubgroup_inf_oppRadical, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hg_eq, hq1, one_mul]
  exact hm'

end Parabolic

end CFSG.LieType.SeitzGeneration.ExcWideThree
