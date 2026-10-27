module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofStatements
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup

theorem inSubgroup_layer_eq_self {G : Type*} [Group G] {H : Subgroup G}
    (hH : CFSG.IsQuasisimple H) : CFSG.inSubgroup CFSG.layer H = H := by
  have htop : CFSG.layer H = ⊤ :=
    eq_top_iff.mpr (le_sSup (⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hH,
      Subgroup.IsSubnormal.top⟩ : CFSG.IsComponent (⊤ : Subgroup H)))
  unfold CFSG.inSubgroup
  rw [htop]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem commutator_le_of_index_two_wilson {G : Type*} [Group G] {K : Subgroup G}
    (hK : K.index = 2) : _root_.commutator G ≤ K := by
  have : K.Normal := Subgroup.normal_of_index_eq_two hK
  have hc : Nat.card (G ⧸ K) = 2 := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (G ⧸ K) := isCyclic_of_prime_card hc
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).1 inferInstance

theorem inSubgroup_layer_eq_of_index_two {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hidx : (K.subgroupOf H).index = 2)
    (hK : CFSG.IsQuasisimple K) : CFSG.inSubgroup CFSG.layer H = K := by
  have hK'comp : CFSG.IsComponent (K.subgroupOf H) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hK,
      hKn.isSubnormal⟩
  have hcomm : _root_.commutator H ≤ K.subgroupOf H := commutator_le_of_index_two_wilson hidx
  have hlayer : CFSG.layer H = K.subgroupOf H := by
    refine le_antisymm (sSup_le fun L hL => ?_) (CFSG.LocalCores.component_le_layer hK'comp)
    have hLperf : L = ⁅L, L⁆ := (Subgroup.isPerfect_iff.1 hL.1.1).symm
    calc L = ⁅L, L⁆ := hLperf
      _ ≤ _root_.commutator H := Subgroup.commutator_mono le_top le_top
      _ ≤ K.subgroupOf H := hcomm
  unfold CFSG.inSubgroup
  rw [hlayer]
  exact Subgroup.map_subgroupOf_eq_of_le hKH

theorem layer_map_mulEquiv_wilson {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem centralizer_map_mulEquiv_wilson {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e g} : Set H) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy

theorem map_inSubgroup_layer_centralizer {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    (CFSG.inSubgroup CFSG.layer (Subgroup.centralizer ({x} : Set X))).map e.toMonoidHom =
      CFSG.inSubgroup CFSG.layer (Subgroup.centralizer ({e x} : Set Y)) := by
  let f : Subgroup.centralizer ({x} : Set X) ≃* Subgroup.centralizer ({e x} : Set Y) :=
    (e.subgroupMap (Subgroup.centralizer ({x} : Set X))).trans
      (MulEquiv.subgroupCongr (centralizer_map_mulEquiv_wilson e x))
  have hcomp : (Subgroup.centralizer ({e x} : Set Y)).subtype.comp f.toMonoidHom =
      e.toMonoidHom.comp (Subgroup.centralizer ({x} : Set X)).subtype :=
    MonoidHom.ext fun y => rfl
  unfold CFSG.inSubgroup
  rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, layer_map_mulEquiv_wilson f]

theorem isSylowOf_map_wilson {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ} [Fact p.Prime]
    (f : G →* H) {P S : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf p P S) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map f) (S.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective S), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem mem_center_map_subtype_iff_wilson {G : Type*} [Group G] (S : Subgroup G) (x : G) :
    x ∈ (Subgroup.center S).map S.subtype ↔ x ∈ S ∧ ∀ s ∈ S, x * s = s * x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun s hs => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨s, hs⟩)).symm
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g.1 g.2).symm, rfl⟩

theorem isCentral218_top_map_of_wilson {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) {x : X}
    (h : CFSG.RankThree.PartTwo.Sec21.IsCentral218 (⊤ : Subgroup X) x) :
    CFSG.RankThree.PartTwo.Sec21.IsCentral218 (⊤ : Subgroup Y) (e x) := by
  obtain ⟨S, hS, hx⟩ := h
  refine ⟨S.map e.toMonoidHom, ?_, ?_⟩
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have h1 := isSylowOf_map_wilson e.toMonoidHom hS
    rwa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
  · rw [mem_center_map_subtype_iff_wilson] at hx ⊢
    obtain ⟨hxS, hc⟩ := hx
    refine ⟨Subgroup.mem_map_of_mem e.toMonoidHom hxS, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    show e x * e s = e s * e x
    rw [← map_mul, ← map_mul, hc s hs]

theorem isCentral218_top_map_iff {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (x : X) :
    CFSG.RankThree.PartTwo.Sec21.IsCentral218 (⊤ : Subgroup X) x ↔
      CFSG.RankThree.PartTwo.Sec21.IsCentral218 (⊤ : Subgroup Y) (e x) := by
  refine ⟨isCentral218_top_map_of_wilson e, fun h => ?_⟩
  have :Finite Y := Finite.of_equiv X e.toEquiv
  have h' := isCentral218_top_map_of_wilson e.symm h
  rwa [MulEquiv.symm_apply_apply] at h'

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
