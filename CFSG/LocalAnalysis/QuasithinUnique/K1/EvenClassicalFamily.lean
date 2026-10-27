module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalInner
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog

theorem exists_inner_of_sylowCentralizing {G : Type} [Group G] [Finite G] {H S L : Subgroup G}
    (hS : IsSylowTwoOf S H) (hLH : L ≤ H) (hsub : (L.subgroupOf H).IsSubnormal)
    (hperf : Group.IsPerfect L) (hA : SylowCentralizingAutInner (L ⧸ Subgroup.center L))
    {w : G} (hwN : w ∈ Subgroup.normalizer (L : Set G))
    (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    ∃ x ∈ L, ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_inf_of_subnormal hS hLH hsub
  let c : L ≃* L := conjAutOfNormalizer L hwN
  have hcc : (Subgroup.center L).map c.toMonoidHom = Subgroup.center L :=
    Subgroup.map_center_eq c
  let β : L ⧸ Subgroup.center L ≃* L ⧸ Subgroup.center L :=
    QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) c hcc
  have hβ : ∀ y : L, β (y : L ⧸ Subgroup.center L) = ((c y : L) : L ⧸ Subgroup.center L) :=
    fun y => rfl
  let T : Sylow 2 (L ⧸ Subgroup.center L) := P.mapSurjective (QuotientGroup.mk'_surjective _)
  have hT : IsSylowTwoOf (T : Subgroup (L ⧸ Subgroup.center L)) ⊤ :=
    isSylowTwoOf_top_iff.mpr ⟨T.isPGroup', T.not_dvd_index⟩
  have hTfix : ∀ q ∈ (T : Subgroup (L ⧸ Subgroup.center L)), β q = q := by
    intro q hq
    rw [Sylow.coe_mapSurjective] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpS : (p : G) ∈ S := by
      have : (p : G) ∈ (P : Subgroup L).map L.subtype := Subgroup.mem_map_of_mem _ hp
      rw [hP] at this
      exact this.1
    have h1 : (p : G) * w = w * (p : G) := Subgroup.mem_centralizer_iff.mp hwS _ hpS
    have h2 : (c p : L) = p := Subtype.ext (by
      change w⁻¹ * (p : G) * w = p
      rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul])
    show β ((QuotientGroup.mk' (Subgroup.center L)) p) = (QuotientGroup.mk' (Subgroup.center L)) p
    change β (p : L ⧸ Subgroup.center L) = (p : L ⧸ Subgroup.center L)
    rw [hβ, h2]
  obtain ⟨xb, hxb⟩ := hA _ hT β hTfix
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hcen : ∀ y : L, (x⁻¹ * y * x)⁻¹ * c y ∈ Subgroup.center L := by
    intro y
    have h1 := hxb (y : L ⧸ Subgroup.center L)
    rw [hβ] at h1
    rw [← QuotientGroup.eq]
    rw [h1]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hc := eq_conj_of_central_displacement c x hcen
  exact ⟨(x : G), x.2, fun y hy => congrArg (fun z : L => (z : G)) (hc ⟨y, hy⟩)⟩

theorem centralizes_of_family {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L)
    (hX : NoStronglyClosedElemAbelian (L ⧸ Subgroup.center L))
    (hA : SylowCentralizingAutInner (L ⧸ Subgroup.center L))
    {w : G} (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  by_contra hnc
  have hperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr h.perfect
  have hinner := exists_inner_of_sylowCentralizing h.sylow h.le_H h.subnormal hperf hA
    (h.normalizes hwU) hwS
  obtain ⟨P, A, hW, hA'⟩ := exists_stronglyClosedWitness_of_inner_action h.sylow h.le_S h.elem
    h.closed h.le_H h.normalizes hwU hinner hnc
  exact hA' (hX P A hW)

end CFSG.QuasithinUnique.K1
