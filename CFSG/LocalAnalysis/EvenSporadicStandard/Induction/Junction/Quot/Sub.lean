module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Lift
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.GroupLemmas

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {G : Type} [Group G] (M : Subgroup G) [M.Normal] (U : Subgroup G)

abbrev cenM : Subgroup G := M ⊓ centralizer (U : Set G)

abbrev tildeU : Subgroup G :=
  M ⊓ (centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M))).comap (cq M)

abbrev cenQ : Subgroup (CQ M) :=
  M.map (cq M) ⊓ centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M))

theorem cenM_le_tildeU : cenM M U ≤ tildeU M U := fun x hx =>
  ⟨hx.1, mem_centralizer_iff.2 fun _ ⟨u, hu, hy⟩ => by
    rw [← hy, ← map_mul, ← map_mul, mem_centralizer_iff.1 hx.2 u hu]⟩

theorem map_tildeU : (tildeU M U).map (cq M) = cenQ M U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, hx.2⟩
  · rintro ⟨⟨m, hm, rfl⟩, hy⟩
    exact ⟨m, ⟨hm, hy⟩, rfl⟩

theorem normal_cenM_tildeU : ((cenM M U).subgroupOf (tildeU M U)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ cenM M U := hn
  have hgM : (g : G) ∈ M := g.2.1
  have hgq : cq M g ∈ centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M)) := g.2.2
  show (g : G) * n * (g : G)⁻¹ ∈ cenM M U
  refine ⟨?_, mem_centralizer_iff.2 fun u hu => ?_⟩
  · exact M.mul_mem (M.mul_mem hgM hn'.1) (M.inv_mem hgM)
  · have hz : u * g * u⁻¹ * (g : G)⁻¹ ∈ centralizer (M : Set G) := by
      rw [← cq_eq_one_iff M, map_mul, map_mul, map_mul, map_inv, map_inv]
      have := mem_centralizer_iff.1 hgq (cq M u) ⟨u, hu, rfl⟩
      calc cq M u * cq M g * (cq M u)⁻¹ * (cq M g)⁻¹
          = (cq M u * cq M g) * (cq M u)⁻¹ * (cq M g)⁻¹ := rfl
        _ = (cq M g * cq M u) * (cq M u)⁻¹ * (cq M g)⁻¹ := by rw [this]
        _ = 1 := by group
    set x : G := (g : G) with hx
    set c : G := (n : G) with hc
    set z : G := u * x * u⁻¹ * x⁻¹ with hzdef
    have e1 : u * x * u⁻¹ = z * x := by rw [hzdef]; group
    have e2 : u * c * u⁻¹ = c := by
      have := mem_centralizer_iff.1 hn'.2 u hu
      calc u * c * u⁻¹ = (c * u) * u⁻¹ := by rw [this]
        _ = c := by group
    have hxc : x * c * x⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hn'.1) (M.inv_mem hgM)
    have hzc : (x * c * x⁻¹) * z = z * (x * c * x⁻¹) := (mem_centralizer_iff.1 hz _ hxc)
    have h3 : u * (x * c * x⁻¹) * u⁻¹ = x * c * x⁻¹ := by
      calc u * (x * c * x⁻¹) * u⁻¹ = (u * x * u⁻¹) * (u * c * u⁻¹) * (u * x * u⁻¹)⁻¹ := by group
        _ = (z * x) * c * (z * x)⁻¹ := by rw [e1, e2]
        _ = z * (x * c * x⁻¹) * z⁻¹ := by group
        _ = x * c * x⁻¹ := by rw [← hzc]; group
    calc u * (x * c * x⁻¹) = (u * (x * c * x⁻¹) * u⁻¹) * u := by group
      _ = (x * c * x⁻¹) * u := by rw [h3]

theorem isSubnormal_map_cq {L : Subgroup G} (hL : L ≤ cenM M U)
    (h : (L.subgroupOf (cenM M U)).IsSubnormal) :
    ((L.map (cq M)).subgroupOf (cenQ M U)).IsSubnormal := by
  have h1 : (L.subgroupOf (tildeU M U)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hL (cenM_le_tildeU M U) h
      (normal_cenM_tildeU M U).isSubnormal
  have h2 := isSubnormal_subgroupOf_map (cq M) (hL.trans (cenM_le_tildeU M U)) h1
  rwa [map_tildeU] at h2

theorem lf_le_centralizer {Q : Subgroup (CQ M)} (hQ : ⁅Q, Q⁆ = Q) (hQN : Q ≤ cenQ M U) :
    lf M Q ≤ centralizer (U : Set G) :=
  le_centralizer_of_map_le M (lf_le M Q) (commutator_lf M hQ (hQN.trans inf_le_left))
    (by rw [map_lf M hQ (hQN.trans inf_le_left)]; exact hQN.trans inf_le_right)

theorem isSubnormal_lf {Q : Subgroup (CQ M)} (hQ : ⁅Q, Q⁆ = Q) (hQN : Q ≤ cenQ M U)
    (h : (Q.subgroupOf (cenQ M U)).IsSubnormal) :
    ((lf M Q).subgroupOf (cenM M U)).IsSubnormal := by
  have hlfC := lf_le_centralizer M U hQ hQN
  have h1 : ((Q.comap (cq M)).subgroupOf (tildeU M U)).IsSubnormal :=
    isSubnormal_subgroupOf_comap (cq M) (by rw [map_tildeU]) h
  set B : Subgroup G := Q.comap (cq M) ⊓ M with hB
  have hBU : B ≤ tildeU M U := fun x hx =>
    ⟨hx.2, hQN hx.1 |>.2⟩
  have hBeq : (B.subgroupOf (tildeU M U)) = (Q.comap (cq M)).subgroupOf (tildeU M U) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, hB, Subgroup.mem_inf]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2.1⟩⟩
  have hlfB : lf M Q ≤ B := by
    rw [lf_eq]
    exact commutator_self_le B
  have h2 : ((lf M Q).subgroupOf B).IsSubnormal := by
    have hn : (⁅B, B⁆.subgroupOf B).Normal := normal_commutator_subgroupOf B
    rw [lf_eq]
    exact hn.isSubnormal
  have h3 : ((lf M Q).subgroupOf (tildeU M U)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hlfB hBU h2 (by rw [hBeq]; exact h1)
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (cenM_le_tildeU M U) h3

theorem isCompIn_map_cq {Z : Subgroup G} (hZM : Z ≤ M)
    (h : IsCompIn Z (centralizer (U : Set G))) :
    IsCompIn (Z.map (cq M)) (centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M))) := by
  have hZC : Z ≤ cenM M U := le_inf hZM h.1
  have hsub : (Z.subgroupOf (cenM M U)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_right h.2.2
  have h1 := isSubnormal_map_cq M U hZC hsub
  have hMq : (M.map (cq M)).Normal := Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  have hnorm : ((cenQ M U).subgroupOf
      (centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M)))).Normal := by
    have : (cenQ M U).subgroupOf
        (centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M))) =
        (M.map (cq M)).subgroupOf
          (centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M))) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
    rw [this]
    exact hMq.subgroupOf _
  have hZq : Z.map (cq M) ≤ cenQ M U :=
    le_inf (Subgroup.map_mono hZM) (map_le_centralizer M h.1)
  have h2 : ((Z.map (cq M)).subgroupOf
      (centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M)))).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hZq inf_le_right h1 hnorm.isSubnormal
  exact isCompIn_of_subnormal (map_le_centralizer M h.1)
    (isQuasisimple_map_cq M hZM h.isQuasisimple) h2

theorem isCompIn_lf {Z : Subgroup (CQ M)} (hZM : Z ≤ M.map (cq M)) (hq : CFSG.IsQuasisimple ↥Z)
    (h : IsCompIn Z (centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M)))) :
    IsCompIn (lf M Z) (centralizer (U : Set G)) := by
  have hZp : ⁅Z, Z⁆ = Z := Subgroup.isPerfect_iff.1 hq.1
  have hZN : Z ≤ cenQ M U := le_inf hZM h.1
  have hsub : (Z.subgroupOf (cenQ M U)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_right h.2.2
  have h1 := isSubnormal_lf M U hZp hZN hsub
  have hnorm : ((cenM M U).subgroupOf (centralizer (U : Set G))).Normal := by
    have : (cenM M U).subgroupOf (centralizer (U : Set G)) =
        M.subgroupOf (centralizer (U : Set G)) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
    rw [this]
    exact Subgroup.Normal.subgroupOf ‹M.Normal› _
  have hlfC := lf_le_centralizer M U hZp hZN
  have h2 : ((lf M Z).subgroupOf (centralizer (U : Set G))).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans (le_inf (lf_le M Z) hlfC) inf_le_right h1
      hnorm.isSubnormal
  exact isCompIn_of_subnormal hlfC
    (isQuasisimple_of_map_cq M (lf_le M Z) (commutator_lf M hZp hZM)
      (by rwa [map_lf M hZp hZM])) h2

end CFSG.EvenSporadicStandard.Induction.Junction
