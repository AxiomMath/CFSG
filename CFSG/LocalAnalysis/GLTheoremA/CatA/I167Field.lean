module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167FieldBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Step0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}

theorem fld_nontrivial_of_fieldOn {X : Subgroup Ω} {x : Ω} (hF : FieldOn p x X) :
    Nontrivial (PSimple p X) := by
  obtain ⟨-, lab, -, R, _, I, F, θ, -, ⟨a, b, hab⟩, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists hF.2
  by_contra hcon
  haveI : Subsingleton (PQuot p X ⧸ Subgroup.center (PQuot p X)) := not_nontrivial_iff_subsingleton.1 hcon
  exact hab (θ.symm.injective (Subsingleton.elim _ _))

section Case


theorem type167_of_fieldOn {B X D J : Subgroup Ω} (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B)
    (hX : CFSG.Open.IsQuasisimple ↥X) (hchev : IsChevSimple 2 (PSimple p X))
    (hBN : B ≤ Subgroup.normalizer (X : Set Ω))
    (hrank : GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B)
    (hSC : ∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B)
    (hcard : Nat.card ↥(B ⊓ cs X) = p) (hD : IsE2 p B D) (hJ : GLAPComponent p (X ⊓ cs D) J)
    (hDJ : D = B ⊓ cs J) (htype : Type167J p J)
    (hsplit : HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X)
    {x : Ω} (hxD : x ∈ D) (hfield : FieldOn p x X) : Type167 p X J := by
  have hxp : x ^ p = 1 := hD.2.1.2 x hxD
  have hSc : GLAPComponent p X X :=
    glaPComponent_self_of_nontrivial hX (fld_nontrivial_of_fieldOn hfield)
  have hxc : x ∉ cs X := notMem_cs_of_fieldOn hp hfield
  have hJx : GLAPComponent p (X ⊓ cx x) J :=
    glaPComponent_inf_cx_of_eq_sup
      (eq_sup_zpowers_of_notMem_cs hp hD hcard (inf_cs_le_of_glaPComponent hJ hDJ) hxD hxc) hJ
  rcases htype with ⟨rfl, n, hodd, hn5, hcat⟩ | ⟨rfl, n, heven, hn6, hcat⟩ |
    ⟨n, k, hodd, hn3, hnk, hk, hpk, hcat⟩
  ·
    refine Or.inl ⟨rfl, n, hodd, hcat, Or.inr ?_⟩
    have hr : FldRange .PSL n 1 := ⟨le_rfl, Or.inl ⟨rfl, Or.inl hn5⟩⟩
    have hm := fld_lieModel_of_fieldOn hp hp2 hchev hSc hxp hfield hJx hr
      (fld_lieModel_of_isLnA hn5 hcat)
    simpa using fld_catalogIs_isLnA_of_lieModel (fld_range_mul hp.two_le hr) hm
  ·
    refine Or.inr (Or.inl ⟨rfl, n, heven, hcat, Or.inr ?_⟩)
    have hr : FldRange .POmegaMinus n 1 := ⟨le_rfl, Or.inr ⟨Or.inr rfl, by omega⟩⟩
    have hm := fld_lieModel_of_fieldOn hp hp2 hchev hSc hxp hfield hJx hr
      (fld_lieModel_of_isOmMA (by omega) hcat)
    simpa using fld_catalogIs_isOmMA_of_lieModel (fld_range_mul hp.two_le hr) hm
  ·
    refine Or.inr (Or.inr ⟨n, k, hodd, hk, hpk, hcat, Or.inr (Or.inl ?_)⟩)
    rcases fld_lieModel_of_isOmPA hk hn3 hnk hcat with ⟨hn4, hm⟩ | ⟨rfl, hk2, hm⟩
    · have hr : FldRange .POmegaPlus n k := ⟨hk, Or.inr ⟨Or.inl rfl, hn4⟩⟩
      exact fld_catalogIs_isOmPA_of_lieModel (fld_range_mul hp.two_le hr)
        (fld_lieModel_of_fieldOn hp hp2 hchev hSc hxp hfield hJx hr hm)
    ·
      have hr : FldRange .PSL 4 k := ⟨hk, Or.inl ⟨rfl, Or.inr ⟨rfl, hk2⟩⟩⟩
      obtain ⟨i, hi, e⟩ := fld_catalogIs_isLnA_of_lieModel (fld_range_mul hp.two_le hr)
        (fld_lieModel_of_fieldOn hp hp2 hchev hSc hxp hfield hJx hr hm)
      exact ⟨i, Or.inr ⟨rfl, hi⟩, e⟩

theorem i167Field_holds : I167Field := by
  intro Ω _ _ p B X D J x hp hp2 hB hX hchev hBN hrank hSC hcard hD hJ hDJ htype hsplit hxD _ _ hfield
  exact type167_of_fieldOn hp hp2 hB hX hchev hBN hrank hSC hcard hD hJ hDJ htype hsplit hxD hfield

end Case

end CFSG.LocalAnalysis.GLTheoremA.I167

end

