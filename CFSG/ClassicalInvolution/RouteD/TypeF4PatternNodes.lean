module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Nodes

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair longBlock
  shortBlock planeGroup stdPlane isHyperbolicPlane_stdPlane IsHyperbolicPlane)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_nodes_typeF4_img [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f 3 Ω z) :
    ∃ j : Fin 3 → Subgroup G, j 0 ∈ Ω ∧ j 0 ∈ centralizingMembers Ω {z} ∧ j 0 ≠ K ∧
      (∀ i, Commutes K (j i)) ∧ ⁅j 1, j 1⁆ = j 1 ∧ ⁅j 2, j 2⁆ = j 2 ∧ Commutes (j 0) (j 2) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 1) (j 2)) ∧
      (∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j 0) (j 1)) ∧
      (∀ i, j i ≤ locLayer Ω z) ∧
      locImg Ω z (j 0) = (planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))).map d.ψ ∧
      locImg Ω z (j 1) =
        (shortBlock (GaloisField p f) (by decide : (1 : Fin 3) ≠ 2)).range.map d.ψ ∧
      locImg Ω z (j 2) =
        (shortBlock (GaloisField p f) (by decide : (0 : Fin 3) ≠ 1)).range.map d.ψ := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
  have hex := exists_unit_ne_inv hq
  set F := GaloisField p f with hFdef
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have hperf : ∀ {i j : Fin 3} (hij : i ≠ j), (shortBlock F hij).range.map d.ψ ≤
      ⁅(shortBlock F hij).range.map d.ψ, (shortBlock F hij).range.map d.ψ⁆ := by
    intro i j hij
    have := range_perfect_of_sl2 h4 (d.ψ.comp (shortBlock F hij))
    rwa [MonoidHom.range_comp] at this
  obtain ⟨A₂, hA₂p, hA₂m⟩ := exists_perfect_lift hP1 (hperf h12)
  obtain ⟨A₃, hA₃p, hA₃m⟩ := exists_perfect_lift hP1 (hperf h01)
  obtain ⟨L, hLmem, hLK, hLimg⟩ := typeC_exists_member_of_plane (by norm_num : 2 ≤ 3) hq hΩ hK hz
    hP1 d (isHyperbolicPlane_stdPlane (Fin.last 2))
  set Yl : Subgroup G := locLayer Ω z with hYl
  let j₁ : Subgroup G := A₂.map Yl.subtype
  let j₂ : Subgroup G := A₃.map Yl.subtype
  have hj₁img : locImg Ω z j₁ = (shortBlock F h12).range.map d.ψ := by
    rw [locImg_map_subtype, hA₂m]
  have hj₂img : locImg Ω z j₂ = (shortBlock F h01).range.map d.ψ := by
    rw [locImg_map_subtype, hA₃m]
  have hj₁Y : j₁ ≤ Yl := Subgroup.map_subtype_le _
  have hj₂Y : j₂ ≤ Yl := Subgroup.map_subtype_le _
  have hj₁perf : j₁ ≤ ⁅j₁, j₁⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hA₂p
  have hj₂perf : j₂ ≤ ⁅j₂, j₂⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hA₃p
  have hLY : L ≤ Yl := le_centralizingLayer hLmem
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hKY : K ≤ Yl := le_centralizingLayer hKz
  have hKperf : K ≤ ⁅K, K⁆ := (commutator_eq_of_isClassicalMember hz).ge
  have hLperf : L ≤ ⁅L, L⁆ := by
    obtain ⟨zL, hzL⟩ := hΩ.classical L hLmem.1
    exact (commutator_eq_of_isClassicalMember hzL).ge
  have hKQ : locImg Ω z K ≤ d.Q₀ := typeC_locImg_self_le_Q₀ (by norm_num) hq hK hz d
  have hKc : ∀ M : Subgroup G, M ≤ Yl → locImg Ω z M ≤ d.ψ.range → Commutes K M := fun M hMY hMr =>
    commutes_of_commutes_locImg_perfect hP1 hKY hMY hKperf fun a ha b hb =>
      d.commutes a (hKQ ha) b (hMr hb)
  have hLrange : locImg Ω z L ≤ d.ψ.range := hLimg ▸ Subgroup.map_le_range _ _
  have hj₁range : locImg Ω z j₁ ≤ d.ψ.range := hj₁img ▸ Subgroup.map_le_range _ _
  have hj₂range : locImg Ω z j₂ ≤ d.ψ.range := hj₂img ▸ Subgroup.map_le_range _ _
  have hcommL₂ : Commutes L j₂ := by
    refine (commutes_of_commutes_locImg_perfect hP1 hj₂Y hLY hj₂perf ?_).symm
    rw [hj₂img, hLimg]
    refine commutes_map_hom d.ψ ?_
    rintro _ ⟨A, rfl⟩ y hy
    rw [Models.SymplecticPairs.planeGroup_stdPlane] at hy
    obtain ⟨B, rfl⟩ := hy
    exact (Models.SymplecticPairs.commute_shortBlock_longBlock h01 (k := Fin.last 2)
      (by decide) (by decide) A B).eq
  have hlin : ∃ W, LinearBlockStandardPair F W j₁ j₂ := by
    obtain ⟨W₁, hW₁⟩ := Models.SymplecticPairs.exists_linearBlockStandardPair_short_map (K := F)
      h01 h12 h02 hex d.ψ d.ker_le (Or.inl rfl) (Or.inl rfl)
    exact linearBlockStandardPair_of_locImg_perfect (p := p) (f := f) h4
      (CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3 (K := F) (p := p) (f := f)
        hcard hq) hP1 hj₁Y hj₂Y hj₁perf hj₂perf (W := W₁)
      (by rw [hj₁img, hj₂img]; exact hW₁.symm)
  have hsymp : ∃ W, SymplecticBlockStandardPair F W L j₁ := by
    have hinj : Function.Injective (d.ψ.comp (Models.SymplecticPairs.suppGroup
        (Models.SymplecticPairs.coords (1 : Fin 3) ∪ Models.SymplecticPairs.coords 2) :
        Subgroup (StatedSp 3 F)).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx1 : (x : StatedSp 3 F) ∈ d.ψ.ker := hx
      have hc := d.ker_le hx1
      have := Models.SymplecticPairs.eq_one_of_mem_center_of_mem_suppGroup hc x.2
        (t := Sum.inl (0 : Fin 3)) (by
          simp only [Models.SymplecticPairs.coords, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, not_or]
          decide)
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    obtain ⟨W₂, hW₂⟩ := Models.SymplecticPairs.exists_symplecticBlockStandardPair_short_comp
      (K := F) h12 _ hinj (Or.inl rfl)
    have e1 : ((longBlock F 3 (2 : Fin 3)).range.subgroupOf (Models.SymplecticPairs.suppGroup
        (Models.SymplecticPairs.coords (1 : Fin 3) ∪ Models.SymplecticPairs.coords 2))).map
          (d.ψ.comp (Models.SymplecticPairs.suppGroup (Models.SymplecticPairs.coords (1 : Fin 3) ∪
            Models.SymplecticPairs.coords 2) : Subgroup (StatedSp 3 F)).subtype) =
        (longBlock F 3 (2 : Fin 3)).range.map d.ψ := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (Models.SymplecticPairs.longBlock_range_le_suppGroup_right h12)]
    have e2 : ((shortBlock F h12).range.subgroupOf (Models.SymplecticPairs.suppGroup
        (Models.SymplecticPairs.coords (1 : Fin 3) ∪ Models.SymplecticPairs.coords 2))).map
          (d.ψ.comp (Models.SymplecticPairs.suppGroup (Models.SymplecticPairs.coords (1 : Fin 3) ∪
            Models.SymplecticPairs.coords 2) : Subgroup (StatedSp 3 F)).subtype) =
        (shortBlock F h12).range.map d.ψ := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (Models.SymplecticPairs.shortBlock_range_le_suppGroup h12)]
    rw [e1, e2] at hW₂
    exact symplecticBlockStandardPair_of_locImg_perfect hp2 hq hP1 hLY hj₁Y hLperf hj₁perf (W := W₂)
      (by
        rw [hj₁img, hLimg, Models.SymplecticPairs.planeGroup_stdPlane]
        exact hW₂)
  refine ⟨![L, j₁, j₂], hLmem.1, hLmem, hLK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hKc L hLY hLrange
    · exact hKc j₁ hj₁Y hj₁range
    · exact hKc j₂ hj₂Y hj₂range
  · exact le_antisymm (commutator_self_le _) hj₁perf
  · exact le_antisymm (commutator_self_le _) hj₂perf
  · exact hcommL₂
  · exact hlin
  · exact hsymp
  · intro i
    fin_cases i
    · exact hLY
    · exact hj₁Y
    · exact hj₂Y
  · exact hLimg
  · exact hj₁img
  · exact hj₂img

end CFSG.ClassicalInvolution.RouteD
