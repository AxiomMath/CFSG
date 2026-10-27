module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import CFSG.GF2Type.Aschbacher1976Common.DihedralEvenRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralTypeSub

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType

@[expose] def KDDihedralTypeSylow : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L S : Subgroup A),
    catalogIs ↥L (onLie IsDihedralTypeIndex) → CFSG.ABGLocalTools.IsSylowOf 2 S L →
      (∃ n : ℕ, 0 < n ∧ Nonempty (↥S ≃* DihedralGroup n)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.WreathedTwoGroup n))

theorem card_frattini_le_four_of_twoGen {A : Type} [Group A] [Finite A] {S R : Subgroup A}
    (hS : CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups ↥S) (hRS : R ≤ S)
    (hR2 : IsPGroup 2 ↥R) : Nat.card (↥R ⧸ frattini ↥R) ≤ 4 := by
  obtain ⟨s, hs, hcl⟩ := CFSG.GF2Type.Aschbacher1976Common.exists_two_gen_of_le S hS R hRS
  have hrank : Group.rank ↥R ≤ 2 := by
    rw [← hcl]
    exact (Subgroup.rank_closure_finset_le_card s).trans hs
  obtain ⟨d, hd, hcard, -, -⟩ :=
    CFSG.GF2Type.Aschbacher1976Common.frattini_quotient_elementary_of_rank_le_two hR2 hrank
  rw [hcard]
  calc 2 ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hd
    _ = 4 := by norm_num

theorem kFactDihedralTypeAut_of_sylow (h : KDDihedralTypeSylow) : KFactDihedralTypeAut := by
  intro A _ _ L R g r hL hRL hR2 _ hgN hr hr5 hord y hy
  have hR' : IsPGroup 2 ↥(R.subgroupOf L) :=
    hR2.of_injective (Subgroup.subgroupOfEquivOfLe hRL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRL).injective
  obtain ⟨Q, hQR⟩ := hR'.exists_le_sylow
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥L).map L.subtype) L := ⟨Q, rfl⟩
  have hS2 : IsPGroup 2 ↥((Q : Subgroup ↥L).map L.subtype) := Q.isPGroup'.map L.subtype
  have hRS : R ≤ (Q : Subgroup ↥L).map L.subtype := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hRL hx⟩, hQR (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  rcases h A L _ hL hSyl with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  ·
    haveI : NeZero n := ⟨by omega⟩
    have hTG := CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv e
      (CFSG.GF2Type.Aschbacher1976Common.twoGen_dihedral n)
    have h4 := card_frattini_le_four_of_twoGen hTG hRS hR2
    exact centralizes_of_frattini_bounds R hR2 hgN hr hr5 hord (le_trans h4 (by norm_num))
      (fun _ => h4) (by intro h8; exfalso; omega) y hy
  ·
    have hTG := CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv e
      (CFSG.GF2Type.Aschbacher1976Common.twoGen_semidihedral n hn)
    have h4 := card_frattini_le_four_of_twoGen hTG hRS hR2
    exact centralizes_of_frattini_bounds R hR2 hgN hr hr5 hord (le_trans h4 (by norm_num))
      (fun _ => h4) (by intro h8; exfalso; omega) y hy
  ·
    exact centralizes_of_wreath hS2 (by omega) e hRS hgN hr hr5 hord y hy

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
