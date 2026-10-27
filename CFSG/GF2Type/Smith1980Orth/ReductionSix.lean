module

public import CFSG.GF2Type.Smith1980Orth.PathGlue
public import CFSG.GF2Type.Entry
public import CFSG.GF2Type.Smith1980Orth.Four
public import CFSG.GF2Type.Smith1980Orth.Holt
public import CFSG.LargeExtraspecial.S14C12THyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.LargeExtraspecial.Bridge CFSG.Open
  CFSG.Blueprint CFSG.Timmesfeld.Connectivity CFSG.RankThree.PartTwo.Sec21

@[expose] def Smith1980OrthogonalSixStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      ∀ w : ℕ,
        Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
          2 ^ (1 + 2 * w) →
        6 ≤ w → Even w →
        ∀ (Mbar : Type) [Group Mbar],
          timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
          ∀ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q →
            (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
              Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) →
            (timmesfeldPlusType q → LieModel G .POmegaPlus ((w + 4) / 2) 2 1) ∧
            (¬ timmesfeldPlusType q → LieModel G .POmegaMinus ((w + 4) / 2) 2 1)

structure SixInputs : Prop where
  local_ : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → OLocal S
  path : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → OPath S
  index : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → S.M.index % 4 = 3

variable {G : Type} [Group G] [Finite G]

theorem conclusion_of_sixInputs [IsSimpleGroup G]
    (hAS : AschbacherSmithWideInput) (hDW : DW.DW37Statement)
    (hHolt : HoltUniqueFixedPointSimple) (hAlt : AltInput) (hId : IdentInput) (I : SixInputs)
    {S : Setting G} (O : OrthData S) (hw : 6 ≤ S.width) :
    (timmesfeldPlusType O.q → LieModel G .POmegaPlus ((S.width + 4) / 2) 2 1) ∧
      (¬ timmesfeldPlusType O.q → LieModel G .POmegaMinus ((S.width + 4) / 2) 2 1) := by
  obtain ⟨d, e, hd, he, hde⟩ := exists_isConj_orderOf_mul_eq_four hAS hDW O (by omega)
  have hloc := local_of_OLocal S (I.local_ G S O hw)
  have hD : ThreeFourPlusClass G {g | IsConj S.z g} := by
    refine threeFourPlusClass_of_products S fun a b ha hb => ?_
    have hra := reach_conjugatesOf hHolt hAlt O hd he hde ha
    have hrb := reach_conjugatesOf hHolt hAlt O hd he hde hb
    obtain ⟨v, hv, hav, hvb⟩ :=
      SmithGraph.exists_common_of_reach (I.path G S O hw) ha (reach_trans (reach_symm hra) hrb)
    exact SmithGraph.threeFour_of_common S hloc ha hb hv hav hvb
  exact hId G S O hw hD ⟨d, e, hd, he, hde⟩ (I.index G S O hw)

theorem smith1980OrthogonalSix_of_inputs
    (hAS : AschbacherSmithWideInput) (hDW : DW.DW37Statement)
    (hHolt : HoltUniqueFixedPointSimple) (hAlt : AltInput) (hId : IdentInput) (I : SixInputs) :
    Smith1980OrthogonalSixStatement := by
  intro G _ _ _ _ z hz hext w hcard h6 hev Mbar _ hMbar q hq hiso
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have hw : (Setting.ofFStar z hz hext').width = w := width_ofFStar hz hext' hcard'
  obtain ⟨e⟩ := nonempty_mulEquiv_Mbar_ofFStar hz hext' hMbar'
  subst hw
  exact conclusion_of_sixInputs hAS hDW hHolt hAlt hId I
    (S := Setting.ofFStar z hz hext')
    { q := q, nondeg := hq, four_le := by omega, even := hev,
      iso := hiso.imp (Nonempty.map e.trans) (Nonempty.map e.trans) } h6

end CFSG.GF2Type.Smith1980Orth
