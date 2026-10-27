module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.OddKernel.RankOneQuotients

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def outerAction {X : Type*} [Group X] (L : Subgroup X) [L.Normal] :
    X →* Outer (↥L ⧸ Subgroup.center ↥L) :=
  (QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L))).comp
    ((PerfectAutomorphisms.centerQuotientHom ↥L).comp MulAut.conjNormal)

theorem mem_sup_centralizer_of_outerAction_eq_one {X : Type*} [Group X] (L : Subgroup X)
    [L.Normal] [Group.IsPerfect ↥L] {x : X} (hx : outerAction L x = 1) :
    x ∈ L ⊔ Subgroup.centralizer (L : Set X) := by
  have h1 : PerfectAutomorphisms.centerQuotientHom ↥L (MulAut.conjNormal x) ∈
      inner (↥L ⧸ Subgroup.center ↥L) := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) k
  have h2 : MulAut.conj l = (MulAut.conjNormal x : MulAut ↥L) := by
    apply PerfectAutomorphisms.centerQuotientHom_injective ↥L
    rw [centerQuotient_conj]
    exact hk
  have hy : (l : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h3 := congrArg (fun φ : MulAut ↥L => ((φ ⟨g, hg⟩ : ↥L) : X)) h2
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      at h3
    have h4 : x * g = (l : X) * g * (l : X)⁻¹ * x := by
      calc x * g = (x * g * x⁻¹) * x := by group
        _ = (l : X) * g * (l : X)⁻¹ * x := by rw [← h3]
    calc g * ((l : X)⁻¹ * x) = (l : X)⁻¹ * ((l : X) * g * (l : X)⁻¹ * x) := by group
      _ = (l : X)⁻¹ * (x * g) := by rw [← h4]
      _ = ((l : X)⁻¹ * x) * g := by group
  have hx' : x = (l : X) * ((l : X)⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem_sup l.2 hy

theorem quotient_center_nonabelian {G : Type*} [Group G] (hq : CFSG.Open.IsQuasisimple G) :
    ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  have hmap := Subgroup.map_commutator (⊤ : Subgroup G) ⊤ (QuotientGroup.mk' (Subgroup.center G))
  have hcomm : (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) = ⊤ := hq.1
  rw [hcomm, Subgroup.map_top, QuotientGroup.range_mk'] at hmap
  have hbot : (⁅(⊤ : Subgroup (G ⧸ Subgroup.center G)), ⊤⁆ :
      Subgroup (G ⧸ Subgroup.center G)) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact hcon b a
  rw [hbot] at hmap
  exact top_ne_bot hmap

theorem isCatalogGroup_quotient_center {X : Type} [Group X] (hK : CFSG.Open.IsKGroup X)
    (L : Subgroup X) [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L) :
    CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) := by
  have hK' : CFSG.KCore.KGroupNonab @CFSG.Open.IsCatalogGroup X := hK
  let L' : Subgroup X := (Subgroup.center ↥L).map L.subtype
  have hle : L' ≤ L := Subgroup.map_subtype_le _
  have heq : L'.subgroupOf L = Subgroup.center ↥L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  haveI : (L'.subgroupOf L).Normal := heq ▸ inferInstance
  let e : (↥L ⧸ L'.subgroupOf L) ≃* (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.quotientMulEquivOfEq heq
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  haveI : IsSimpleGroup (↥L ⧸ L'.subgroupOf L) := e.isSimpleGroup
  have hnab : ∃ a b : ↥L ⧸ L'.subgroupOf L, a * b ≠ b * a :=
    CFSG.KCore.nonabelian_of_mulEquiv e (quotient_center_nonabelian hq)
  obtain ⟨i, ⟨φ⟩⟩ := hK' L L' hle inferInstance hnab
  exact ⟨i, ⟨e.symm.trans φ⟩⟩

theorem pRank_quotient_center_le_one {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (L : Subgroup X) (hr : CFSG.Open.pRank p L ≤ 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ≤ 1 := by
  have h1 : CFSG.pRank p ↥L ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hr
  have h2 := CFSG.RankThree.OddKernel.pRank_le_one_of_surjective hp hp2
    (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _) h1
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2

end CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof
