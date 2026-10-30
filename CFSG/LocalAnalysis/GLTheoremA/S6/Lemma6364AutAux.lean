module

import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Aut
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace L6364

variable {G : Type} [Group G] [Finite G] {p : ℕ}

private theorem centralizerQuot_eq_centModSubgroup (p : ℕ) (L : Subgroup G) :
    CFSG.HardMathSupport.Solomon.LocalBalance.centralizerQuot L (GLAPPrimeCoreOf p L) =
      centModSubgroup p L := by
  ext g
  constructor
  · rintro ⟨hgL, -, hg⟩
    exact ⟨hgL, fun l hl => by simpa [commutatorElement_def] using hg l hl⟩
  · rintro ⟨hgL, hg⟩
    exact ⟨hgL, normalizer_le_normalizer_glaPPrimeCoreOf p L hgL,
      fun l hl => by simpa [commutatorElement_def] using hg l hl⟩

theorem exists_elemAbelian_aut {L B : Subgroup G} (hB : IsElemAbelian p B)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) {k : ℕ}
    (hk : p ^ k * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B) :
    ∃ A : Subgroup (MulAut (PQuot p L)), IsElemAbelian p A ∧ p ^ k ≤ Nat.card A := by
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  let φ : ↥B' →* MulAut (PQuot p L) :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L).domRestrict B'
  have hker : ∀ b : ↥B', b ∈ φ.ker ↔ (((b : ↥N) : G) ∈ centModSubgroup p L) := by
    intro b
    rw [MonoidHom.mem_ker, ← centralizerQuot_eq_centModSubgroup,
      CFSG.HardMathSupport.Solomon.Coordinator.mem_centralizerQuot_iff_barAut_eq_one]
    rfl
  have hkercard : Nat.card φ.ker = Nat.card ↥(B ⊓ centModSubgroup p L) := by
    have hinj : Function.Injective (N.subtype.comp B'.subtype) :=
      N.subtype_injective.comp B'.subtype_injective
    rw [← Subgroup.card_map_of_injective hinj]
    congr 2
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨(Subgroup.mem_subgroupOf.1 b.2), (hker b).1 hb⟩
    · rintro ⟨hgB, hgc⟩
      have hgN : g ∈ N := hgc.1
      exact ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgB⟩, (hker _).2 hgc, rfl⟩
  have hB'card : Nat.card ↥B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥B' := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  refine ⟨φ.range, ?_, ?_⟩
  · rw [MonoidHom.domRestrict_range]
    exact CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hB N)
      (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L)
  · have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    rw [hkercard] at hpos h1
    rw [hB'card] at h1
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(B ⊓ centModSubgroup p L) * Nat.card φ.range <
        Nat.card ↥(B ⊓ centModSubgroup p L) * p ^ k := Nat.mul_lt_mul_of_pos_left hlt hpos
    nlinarith

end L6364

end CFSG.LocalAnalysis.GLTheoremA
