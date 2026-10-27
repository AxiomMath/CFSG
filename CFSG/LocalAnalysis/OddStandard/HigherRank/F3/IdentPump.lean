module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentNotChev2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Defs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalCentre
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.HarrisLit

section Setup

variable {G : Type} [Group G]

theorem mem_normalizer_subgroupOf {X K : Subgroup G} {v : G} (hv : v ∈ X)
    (hKv : K.map (MulAut.conj v).toMonoidHom = K) :
    (⟨v, hv⟩ : ↥X) ∈ normalizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
  have hconj : ∀ y : G, v * y * v⁻¹ ∈ K ↔ y ∈ K := by
    intro y
    have h1 : (MulAut.conj v) y ∈ K.map (MulAut.conj v).toMonoidHom ↔ y ∈ K :=
      Subgroup.mem_map_iff_mem (f := (MulAut.conj v).toMonoidHom) (MulAut.conj v).injective
    rw [hKv] at h1
    simpa [MulAut.conj_apply] using h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hcoe : ((⟨v, hv⟩ * x * ⟨v, hv⟩⁻¹ : ↥X) : G) = v * (x : G) * v⁻¹ := by
    simp
  rw [hcoe]
  exact (hconj (x : G)).symm

theorem centralizer_mk_eq {w v : G} (hv : v ∈ centralizer ({w} : Set G)) :
    centralizer ({(⟨v, hv⟩ : ↥(centralizer ({w} : Set G)))} :
        Set ↥(centralizer ({w} : Set G))) =
      (centralizer ({w} : Set G) ⊓ centralizer ({v} : Set G)).subgroupOf
        (centralizer ({w} : Set G)) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    simpa using (Subgroup.mem_centralizer_singleton_iff.mp h.2)

theorem mem_fusionZStar_map_subgroupOf {w : G} {K : Subgroup G} (hwK : w ∈ K)
    (hKX : K ≤ centralizer ({w} : Set G)) :
    (⟨w, hKX hwK⟩ : ↥(centralizer ({w} : Set G))) ∈
      (Open.fusionZStar ↥(K.subgroupOf (centralizer ({w} : Set G)))).map
        (K.subgroupOf (centralizer ({w} : Set G))).subtype := by
  let X := centralizer ({w} : Set G)
  let x : ↥(K.subgroupOf X) := ⟨⟨w, hKX hwK⟩, Subgroup.mem_subgroupOf.mpr hwK⟩
  have hx : x ∈ Open.fusionZStar ↥(K.subgroupOf X) := by
    apply GrSLit.center_le_fusionZStar
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change (y : G) * w = w * (y : G)
    have hy : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp y.2
    have hyc : (y : G) ∈ centralizer ({w} : Set G) := hKX hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    exact hyc
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem isSimpleChevalleyOver_of_subgroupOf [Finite G] {X K : Subgroup G} (hKX : K ≤ X) {p : ℕ}
    (h : IsSimpleChevalleyOver p (↥(K.subgroupOf X) ⧸ Open.fusionZStar ↥(K.subgroupOf X))) :
    IsSimpleChevalleyOver p (↥K ⧸ Open.fusionZStar ↥K) := by
  obtain ⟨τ, n, f, hm⟩ := h
  let e : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv e
  exact ⟨τ, n, f, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩

theorem classBShape_subgroupOf {X J : Subgroup G} (hJX : J ≤ X) (h : ClassBShape ↥J) :
    ClassBShape ↥(J.subgroupOf X) := by
  obtain ⟨τ, n, hm, hs⟩ := h
  let e : ↥J ≃* ↥(J.subgroupOf X) := (Subgroup.subgroupOfEquivOfLe hJX).symm
  obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv e
  exact ⟨τ, n, GSThmB.OddQuot.lieModel_of_equiv eZ hm, hs⟩

end Setup

theorem classBShape_cases {J : Type} [Group J] (h : ClassBShape J) :
    Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSp 2 3 1 ∨
      ∃ (τ : StatedLieTag) (n : ℕ), Blueprint.LieModel (J ⧸ Open.fusionZStar J) τ n 3 1 ∧
        ((τ = .PSL ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSU ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSp ∧ 3 ≤ n) ∨
          (τ = .POmegaPlus ∧ (n = 4 ∨ n = 6)) ∨ τ = .E7) := by
  obtain ⟨τ, n, hm, hs⟩ := h
  by_cases hsp : τ = .PSp ∧ n = 2
  · obtain ⟨rfl, rfl⟩ := hsp
    exact Or.inl hm
  · refine Or.inr ⟨τ, n, hm, ?_⟩
    rcases hs with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inl ⟨h.1, ?_⟩))
      have hn2 : n ≠ 2 := fun hn => hsp ⟨h.1, hn⟩
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem isSimpleChevalleyOver_bar_of_pumpup
    (hP2 : GS82PumpInputs.ChevOddCentralPumpInput)
    (hP8 : GS82PumpInputs.SpFourThreeCentralPumpInput)
    (hO : CatLeaf.LieOrderFormulasInput) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    {w v : G} (hw : orderOf w = 2) (hv2 : v * v = 1) (hvw : v ∉ zpowers w)
    (hvM : v ∈ centralizer {w}) {J K : Subgroup G}
    (hJ : IsTwoComponentIn J (centralizer {w} ⊓ centralizer {v})) (hs : ClassBShape ↥J)
    (hwJ : w ∈ J) (hJK : J ≤ K) (hKc : IsTwoComponentIn K (centralizer {w})) (hwK : w ∈ K)
    (hKv : K.map (MulAut.conj v).toMonoidHom = K) :
    IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKX : K ≤ centralizer ({w} : Set G) := hKc.1
  have hJY : J ≤ centralizer ({w} : Set G) ⊓ centralizer ({v} : Set G) := hJ.1
  have hJX : J ≤ centralizer ({w} : Set G) := hJY.trans inf_le_left
  have hwX : w ∈ centralizer ({w} : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  have hH : SectionRank.IsKGroupCat ↥(centralizer ({w} : Set G)) :=
    GSThmB.isKGroupCat_of_ne_top' hK (Helpers.centralizer_ne_top_of_involution G hnonab w hw)
  have hM : IsPComponent 2 (K.subgroupOf (centralizer ({w} : Set G))) :=
    (isTwoComponentIn_iff hKX).mp hKc
  have hxo : orderOf (⟨v, hvM⟩ : ↥(centralizer ({w} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]
    have hv1 : v ≠ 1 := fun h => hvw (h ▸ one_mem _)
    exact orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  have hxN := mem_normalizer_subgroupOf hvM hKv
  have hTM : J.subgroupOf (centralizer ({w} : Set G)) ≤ K.subgroupOf (centralizer ({w} : Set G)) :=
    fun x hx => mem_subgroupOf.mpr (hJK (mem_subgroupOf.mp hx))
  have hTx : J.subgroupOf (centralizer ({w} : Set G)) ≤
      centralizer ({(⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))} :
        Set ↥(centralizer ({w} : Set G))) := by
    rw [centralizer_mk_eq hvM]
    exact fun x hx => mem_subgroupOf.mpr (hJY (mem_subgroupOf.mp hx))
  have hTc : IsPComponent 2 ((J.subgroupOf (centralizer ({w} : Set G))).subgroupOf
      (centralizer ({(⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))} :
        Set ↥(centralizer ({w} : Set G))))) := by
    rw [centralizer_mk_eq hvM]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left : centralizer ({w} : Set G) ⊓ centralizer ({v} : Set G) ≤
        centralizer ({w} : Set G)) 2 Nat.prime_two).mpr ((isTwoComponentIn_iff hJY).mp hJ)
  have hw' : orderOf (⟨w, hwX⟩ : ↥(centralizer ({w} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hw
  have hwT : (⟨w, hwX⟩ : ↥(centralizer ({w} : Set G))) ∈
      J.subgroupOf (centralizer ({w} : Set G)) := mem_subgroupOf.mpr hwJ
  have hwZ := mem_fusionZStar_map_subgroupOf hwK hKX
  have hs' := classBShape_subgroupOf hJX hs
  refine isSimpleChevalleyOver_of_subgroupOf hKX ?_
  rcases classBShape_cases hs' with hm | ⟨τ, n, hm, hτ⟩
  · exact hP8 _ hH _ hM _ hxo hxN _ hTM hTx hTc hm _ hw' hwT hwZ
  · exact (hP2 _ hH _ hM _ hxo hxN _ hTM hTx hTc 3 Nat.prime_three (by norm_num) ⟨τ, n, 1, hm⟩
      (not_inChev2_of_classBShape hO hm hτ) _ hw' hwT hwZ).1

end CFSG.OddStandard.HigherRank.F3.Ident
