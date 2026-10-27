module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open scoped commutatorElement

theorem map_centralizer_singleton {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (s : G) :
    (Subgroup.centralizer ({s} : Set G)).map (e : G →* G') =
      Subgroup.centralizer ({e s} : Set G') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    show e x * e s = e s * e x
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    simp only [Subgroup.mem_centralizer_singleton_iff] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa [map_mul] using hy

theorem centralizer_inv_singleton {G : Type} [Group G] (y : G) :
    Subgroup.centralizer ({y⁻¹} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem commutator_self_eq_of_quasisimple_sub {G : Type} [Group G] {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ L.subtype
  change Subgroup.map L.subtype (commutator ↥L) = _ at h
  rw [hq.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.symm

theorem center_eq_bot_of_simple_not_comm {G : Type} [Group G] (K : Subgroup G)
    [IsSimpleGroup ↥K] (hnc : ¬ IsMulCommutative ↥K) : Subgroup.center ↥K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
  · exact h
  · exfalso
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : a ∈ Subgroup.center ↥K := by
      rw [h]
      exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem not_isComponentOf_of_solvable {G : Type} [Group G] {X L : Subgroup G}
    (hX : Group.IsSolvable ↥X) (hL : CFSG.Open.IsComponentOf L X) : False := by
  haveI := hX
  have hLs : Group.IsSolvable ↥L :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hL.1).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hL.1).surjective
  haveI : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  haveI := hL.2.2.2
  haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  exact Group.IsPerfect.not_isSolvable (↥L) hLs

theorem comp_yM5_catalog {L : Subgroup M5}
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({yM5} : Set M5))) :
    catalogIs (↥L ⧸ Subgroup.center ↥L) CFSG.LocalAnalysis.GLTheoremA.S9.isU4two := by
  obtain ⟨Kb, hKbC, hsup, -, hsimp, hnc, -, hcat⟩ := m5_u4_layer
  have hLK : L ≤ Kb := by
    calc L = ⁅L, L⁆ := (commutator_self_eq_of_quasisimple_sub hL.2.2).symm
      _ ≤ ⁅Subgroup.centralizer ({yM5} : Set M5), Subgroup.centralizer ({yM5} : Set M5)⁆ :=
          Subgroup.commutator_mono hL.1 hL.1
      _ ≤ Kb := commutator_centralizer_le Kb hKbC hsup
  have hsub : CFSG.Open.IsSubnormal L Kb := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hL.2.1 hKbC
    rwa [inf_eq_left.mpr hLK] at h
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hsimp with h | h
  · exfalso
    haveI := hL.2.2.2
    have hnt : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    exact ((Subgroup.nontrivial_iff_ne_bot L).mp hnt) h
  · rw [h]
    haveI := hsimp
    have hZ := center_eq_bot_of_simple_not_comm Kb hnc
    let e : ↥Kb ⧸ Subgroup.center ↥Kb ≃* ↥Kb :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact catalogIs_of_mulEquiv e.symm hcat

theorem M5_nontrivial : Nontrivial M5 := by
  obtain ⟨Kb, -, -, -, hsimp, -, -, -⟩ := m5_u4_layer
  haveI := hsimp
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥Kb
  exact ⟨⟨(x : M5), (y : M5), fun h => hxy (Subtype.ext h)⟩⟩

theorem M5_comp {s : M5} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) {L : Subgroup M5}
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({s} : Set M5))) :
    catalogIs (↥L ⧸ Subgroup.center ↥L) CFSG.LocalAnalysis.GLTheoremA.S9.isU4two := by
  have hyside : ∀ (τ : M5 ≃* M5), τ s = yM5 ∨ τ s = yM5⁻¹ →
      catalogIs (↥L ⧸ Subgroup.center ↥L) CFSG.LocalAnalysis.GLTheoremA.S9.isU4two := by
    intro τ hτ
    have hLy : CFSG.Open.IsComponentOf (L.map (τ : M5 →* M5))
        (Subgroup.centralizer ({yM5} : Set M5)) := by
      have h := isComponentOf_map_mulEquiv hL τ
      rw [map_centralizer_singleton] at h
      rcases hτ with hτ | hτ
      · rw [hτ] at h
        exact h
      · rw [hτ, centralizer_inv_singleton] at h
        exact h
    let eL : ↥L ≃* ↥(L.map (τ : M5 →* M5)) :=
      Subgroup.equivMapOfInjective L (τ : M5 →* M5) τ.injective
    let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* (↥(L.map (τ : M5 →* M5)) ⧸
        Subgroup.center ↥(L.map (τ : M5 →* M5))) :=
      QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(L.map (τ : M5 →* M5))) eL
        (Subgroup.map_center_eq eL)
    exact catalogIs_of_mulEquiv eQ.symm (comp_yM5_catalog hLy)
  rcases normal_form s hs3 with h1 | ⟨τ, hτ⟩ | ⟨τ, d, hd, hcnt⟩
  · exact absurd h1 hs1
  · exact hyside τ hτ
  · exfalso
    have h := isComponentOf_map_mulEquiv hL τ
    rw [map_centralizer_singleton] at h
    exact not_isComponentOf_of_solvable (centralizer_diag_solvable (τ s) d hd hcnt) h

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
