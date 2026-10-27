module

public import CFSG.GF2Type.Smith1980Orth.ReductionSix
public import CFSG.GF2Type.Smith1980Orthogonal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.LargeExtraspecial.Bridge
  CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.Connectivity CFSG.RankThree.PartTwo.Sec21

@[expose] def Smith1980OrthogonalW4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) = 2 ^ 9 →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        ∀ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q →
          (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
            Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) →
          (timmesfeldPlusType q → LieModel G .POmegaPlus 4 2 1) ∧
          (¬ timmesfeldPlusType q → LieModel G .POmegaMinus 4 2 1)

theorem smith1980Orthogonal_of_six_of_four (h6 : Smith1980OrthogonalSixStatement)
    (h4 : Smith1980OrthogonalW4Statement) : Smith1980OrthogonalStatement := by
  intro G _ _ _ hna z hz hext w hcard hw4 hev Mbar _ hMbar q hq hiso
  by_cases hw : 6 ≤ w
  · exact h6 G hna z hz hext w hcard hw hev Mbar hMbar q hq hiso
  · have hw' : w = 4 := by
      obtain ⟨r, hr⟩ := hev
      omega
    subst hw'
    exact h4 G hna z hz hext hcard Mbar hMbar q hq hiso

structure W4Inputs : Prop where
  local_ : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    S.width = 4 → OLocal S
  path : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    S.width = 4 → OPath S
  index : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    S.width = 4 → S.M.index % 4 = 3

variable {G : Type} [Group G] [Finite G]

theorem conclusion_of_w4Inputs [IsSimpleGroup G]
    (hHolt : HoltUniqueFixedPointSimple) (hAlt : AltInput) (hIdW4 : IdentW4Input)
    (hW4 : FourW4Input) (I : W4Inputs) {S : Setting G} (O : OrthData S) (hw : S.width = 4) :
    (timmesfeldPlusType O.q → LieModel G .POmegaPlus ((S.width + 4) / 2) 2 1) ∧
      (¬ timmesfeldPlusType O.q → LieModel G .POmegaMinus ((S.width + 4) / 2) 2 1) := by
  obtain ⟨d, e, hd, he, hde⟩ := hW4 G S O hw
  have hloc := local_of_OLocal S (I.local_ G S O hw)
  have hD : ThreeFourPlusClass G {g | IsConj S.z g} := by
    refine threeFourPlusClass_of_products S fun a b ha hb => ?_
    have hra := reach_conjugatesOf hHolt hAlt O hd he hde ha
    have hrb := reach_conjugatesOf hHolt hAlt O hd he hde hb
    obtain ⟨v, hv, hav, hvb⟩ :=
      SmithGraph.exists_common_of_reach (I.path G S O hw) ha (reach_trans (reach_symm hra) hrb)
    exact SmithGraph.threeFour_of_common S hloc ha hb hv hav hvb
  rw [show (S.width + 4) / 2 = 4 by omega]
  exact hIdW4 G S O hw hD ⟨d, e, hd, he, hde⟩ (I.index G S O hw)

private theorem smith1980OrthogonalW4_aux
    (hHolt : HoltUniqueFixedPointSimple) (hAlt : AltInput) (hIdW4 : IdentW4Input)
    (hW4 : FourW4Input) (I : W4Inputs) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (z : G) (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ) (hcard : Nat.card (inSubgroup generalizedFitting
      (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w)) (h4 : w = 4)
    (Mbar : Type) [Group Mbar]
    (hMbar : timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar)
    (q : QuadraticForm (ZMod 2) (Fin w → ZMod 2)) (hq : timmesfeldNondegenerate q)
    (hiso : Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
      Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) :
    (timmesfeldPlusType q → LieModel G .POmegaPlus ((w + 4) / 2) 2 1) ∧
      (¬ timmesfeldPlusType q → LieModel G .POmegaMinus ((w + 4) / 2) 2 1) := by
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have hw : (Setting.ofFStar z hz hext').width = w := width_ofFStar hz hext' hcard'
  obtain ⟨e⟩ := nonempty_mulEquiv_Mbar_ofFStar hz hext' hMbar'
  subst hw
  exact conclusion_of_w4Inputs hHolt hAlt hIdW4 hW4 I
    (S := Setting.ofFStar z hz hext')
    { q := q, nondeg := hq, four_le := by omega, even := by rw [h4]; exact ⟨2, rfl⟩,
      iso := hiso.imp (Nonempty.map e.trans) (Nonempty.map e.trans) } h4

theorem smith1980OrthogonalW4_of_inputs
    (hHolt : HoltUniqueFixedPointSimple) (hAlt : AltInput) (hIdW4 : IdentW4Input)
    (hW4 : FourW4Input) (I : W4Inputs) : Smith1980OrthogonalW4Statement := by
  intro G _ _ _ _ z hz hext hcard Mbar _ hMbar q hq hiso
  exact smith1980OrthogonalW4_aux hHolt hAlt hIdW4 hW4 I G z hz hext 4 hcard rfl Mbar hMbar q hq
    hiso

end CFSG.GF2Type.Smith1980Orth
