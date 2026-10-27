module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open TwA5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot CFSG.SeitzReduction.LinearPilot
open CFSG.LocalAnalysis.GLTheoremA
open Matrix


variable {F : Type} [Field F]

private theorem exists_unit_orderOf_five [Finite F] (h : UnitaryFieldData 2 2 F) :
    ∃ ζ : Fˣ, orderOf ζ = 5 := by
  haveI := h.finite
  haveI : Fintype Fˣ := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine exists_prime_orderOf_dvd_card (G := Fˣ) 5 ?_
  have hfac : 5 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, h.card]
    norm_num
  simpa using hfac

private theorem commutator_mem_unitaryBlock_of_mem_centralizer [Finite F]
    (h : UnitaryFieldData 2 2 F)
    {x : unitarySU 2 2 F 6}
    (hxcent : Subgroup.centralizer ({x} : Set (unitarySU 2 2 F 6)) =
      unitaryBlockDiag h ((Finset.univ : Finset (Fin 6)).erase 5)) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set (unitarySU 2 2 F 6)),
      ∀ k ∈ Subgroup.centralizer ({x} : Set (unitarySU 2 2 F 6)),
      g * k * g⁻¹ * k⁻¹ ∈ unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
  intro g hg k hk
  rw [hxcent] at hg hk
  have hI : (({0, 1, 2, 3, 4} : Finset (Fin 6)))ᶜ = ({5} : Finset (Fin 6)) := by decide
  have := commutator_unitaryBlockDiag_le_unitaryBlock h (I := {0,1,2,3,4}) hI
    (Subgroup.commutator_mem_commutator hg hk)
  simpa [commutatorElement_def,
    show (Finset.univ : Finset (Fin 6)).erase 5 = ({0,1,2,3,4}:Finset (Fin 6)) by decide]
    using this

private theorem multiplier_unitarySU_six_four [Finite F] (h : UnitaryFieldData 2 2 F) :
    evenRank (unitarySU 2 2 F 6) + 2 ≤
      twoRank ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) ∧
      Odd (Nat.card (Subgroup.center ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))))) ∧
      3 * 5 ∣ Nat.card (↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) ⧸
        Subgroup.center ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)))) := by
  have hmult := unitaryFive_mult (J := ↥(unitaryBlock h {0,1,2,3,4})) (n := 2)
    (by norm_num) (hasLabel_unitaryBlock_four h)
    (CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
  obtain ⟨-, hodd, hm2five, hdvd5⟩ := hmult
  have he4 : evenRank (unitarySU 2 2 F 6) = 4 := evenRank_unitarySU_six_four h
  have hm2 : evenRank (unitarySU 2 2 F 6) + 2 ≤
      twoRank ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) := by
    rw [he4]
    change 6 ≤ twoRank ↥(unitaryBlock h {0,1,2,3,4})
    omega
  have hoddJ : Odd (Nat.card (Subgroup.center
      ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))))) := by
    change Odd (Nat.card (Subgroup.center ↥(unitaryBlock h {0,1,2,3,4})))
    exact hodd
  have hdvd : 3 * 5 ∣ Nat.card (↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) ⧸
      Subgroup.center ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)))) := by
    have h3 : 3 ∣ _ := hdvd5 3 Nat.prime_three (by norm_num) (by norm_num)
    have h5 : 5 ∣ _ := hdvd5 5 Nat.prime_five (by norm_num) (by norm_num)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
  exact ⟨hm2, hoddJ, hdvd⟩

private theorem six_unitarySU_six_four [Finite F] (h : UnitaryFieldData 2 2 F)
    (hJlab : HasLabel (unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)))
      (fun l : GLALabel => l = ⟨.twA, 4, 2⟩)) :
    (Subgroup.center ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) = ⊥ ∧
      TrivialMultiplierT ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)))) ∨
    (evenRank (unitarySU 2 2 F 6) = 4 ∧ ∃ labJ : GLALabel,
      HasLabel ↥(unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) (fun l : GLALabel => l = labJ) ∧
      labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
    (unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) = ⊤ ∧
      3 ∣ Nat.card (Subgroup.center (unitarySU 2 2 F 6)) ∧
      ∃ lab : GLALabel, HasLabel (unitarySU 2 2 F 6) (fun l : GLALabel => l = lab) ∧
        Odd lab.n ∧ ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) :=
  Or.inr (Or.inl ⟨evenRank_unitarySU_six_four h,
    ⟨⟨.twA, 4, 2⟩, hJlab, rfl, rfl, by norm_num⟩⟩)

private theorem shape_unitarySU_six_four [Finite F] (h : UnitaryFieldData 2 2 F) :
    ∀ lab : GLALabel, HasLabel (unitarySU 2 2 F 6) (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center (unitarySU 2 2 F 6))) ⟨.twA, 4, 2⟩ := by
  intro lab hlab
  have hKlab : HasLabel (unitarySU 2 2 F 6) (fun l : GLALabel => l = ⟨.twA, 5, 2⟩) :=
    hasLabel_unitarySU_six_four h
  have he : 4 ≤ evenRank (unitarySU 2 2 F 6) := by
    rw [evenRank_unitarySU_six_four h]
  have hcenterK : Subgroup.center (unitarySU 2 2 F 6) = ⊥ := by
    rw [center_unitarySU_eq_unitaryScalars h 6, unitaryScalars_six_four_eq_bot h]
  have hEq : lab = ⟨.twA, 5, 2⟩ := by
    rcases label_eq_or_BC (K := unitarySU 2 2 F 6) he hlab hKlab with h | ⟨-, h2, -⟩
    · exact h
    · exact absurd h2 (by simp)
  subst hEq
  refine ⟨rfl, ?_⟩
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center (unitarySU 2 2 F 6)) := by
    rw [hcenterK]; simp
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, hZ3, rfl, rfl⟩)))))

private theorem fiveLine_and_lineRadical_data [Finite F] (h : UnitaryFieldData 2 2 F) {ζu : Fˣ}
    (hζu : orderOf ζu = 5) :
    IsElemAbelian 5 (fiveLineSubgroup h) ∧ Nat.card (fiveLineSubgroup h) = 5 ^ 3 ∧
      fiveLineSubgroup h ≤ unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ∧
      diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) ∈ fiveLineSubgroup h ∧
      GLAPLayer 5 (unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) ⊓
        Subgroup.centralizer (fiveLineSubgroup h : Set (unitarySU 2 2 F 6))) ≠ ⊥ ∧
      InnerDiagMarking (unitaryTorusSU h ({0, 1} : Finset (Fin 6)))
        (unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) ∧
      unitaryLineRadical h ≤ unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) ∧
      IsPGroup 2 (unitaryLineRadical h) ∧
      unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ≤ Subgroup.normalizer
        (unitaryLineRadical h : Set (unitarySU 2 2 F 6)) ∧
      unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ⊓ Subgroup.centralizer
        (unitaryLineRadical h : Set (unitarySU 2 2 F 6)) =
        Subgroup.zpowers (diagFiveLast h (ζu : Fˣ) (norm_zeta hζu)) := by
  have hE : IsElemAbelian 5 (fiveLineSubgroup h) := isElemAbelian_fiveLineSubgroup h
  have hEcard : Nat.card (fiveLineSubgroup h) = 5 ^ 3 := card_fiveLineSubgroup h
  have hEB : fiveLineSubgroup h ≤ unitaryTorusSU h ({0, 1} : Finset (Fin 6)) :=
    fiveLineSubgroup_le_fiveTorus h
  have hxE : diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) ∈ fiveLineSubgroup h :=
    diagFiveLast_mem_fiveLineSubgroup hζu
  have he3 : GLAPLayer 5 (unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) ⊓
      Subgroup.centralizer (fiveLineSubgroup h : Set (unitarySU 2 2 F 6))) ≠ ⊥ :=
    glaPLayer_fiveLineSubgroup_ne_bot h hζu
  have hidiag : InnerDiagMarking (unitaryTorusSU h ({0, 1} : Finset (Fin 6)))
      (unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) := innerDiagMarking_fiveTorus h
  have hSJ : unitaryLineRadical h ≤ unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
    have := unitaryLineRadical_le_unitaryBlock (h := h)
    simpa [show (Finset.univ : Finset (Fin 6)).erase 5 =
      ({0,1,2,3,4} : Finset (Fin 6)) by decide] using this
  have hS2 : IsPGroup 2 (unitaryLineRadical h) := unitaryLineRadical_isPGroup h
  have hBS : unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ≤ Subgroup.normalizer
      (unitaryLineRadical h : Set (unitarySU 2 2 F 6)) :=
    unitaryTorusSU_le_normalizer_lineRadical hζu
  have h8 : unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ⊓ Subgroup.centralizer
      (unitaryLineRadical h : Set (unitarySU 2 2 F 6)) =
      Subgroup.zpowers (diagFiveLast h (ζu : Fˣ) (norm_zeta hζu)) :=
    inf_centralizer_lineRadical_eq_zpowers hζu
  exact ⟨hE, hEcard, hEB, hxE, he3, hidiag, hSJ, hS2, hBS, h8⟩

private theorem su_unitaryBlock [Finite F] (h : UnitaryFieldData 2 2 F) {x : unitarySU 2 2 F 6} :
    3 ∣ Nat.card (Subgroup.center (unitarySU 2 2 F 6)) →
      (∃ lab : GLALabel, HasLabel (unitarySU 2 2 F 6) (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) = ⊤ ∧ 5 = 3 ∧ ∀ k, k * x = x * k := by
  intro h3 _
  have hcenterK : Subgroup.center (unitarySU 2 2 F 6) = ⊥ := by
    rw [center_unitarySU_eq_unitaryScalars h 6, unitaryScalars_six_four_eq_bot h]
  rw [hcenterK] at h3
  norm_num at h3

private theorem evenRank_le_pRank_inf_unitaryBlock [Finite F] (h : UnitaryFieldData 2 2 F) :
    evenRank (unitarySU 2 2 F 6) ≤
      CFSG.Open.pRank 5 (unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ⊓
        unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) + 2 := by
  have he4 : evenRank (unitarySU 2 2 F 6) = 4 := evenRank_unitarySU_six_four h
  have hE : IsElemAbelian 5 (fiveLineSubgroup h) := isElemAbelian_fiveLineSubgroup h
  have hEcard : Nat.card (fiveLineSubgroup h) = 5 ^ 3 := card_fiveLineSubgroup h
  have hpE : CFSG.Open.pRank 5 (fiveLineSubgroup h) = 3 := by
    haveI : IsElementaryAbelian 5 ↥(fiveLineSubgroup h) := hE.isElementaryAbelian
    have h3 := CFSG.pRank_eq_of_card_eq_pow (A := ↥(fiveLineSubgroup h)) (p := 5) (k := 3)
      (by norm_num) hEcard
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact h3
  rw [he4]
  have hBJ : unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ⊓
      unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) = fiveLineSubgroup h :=
    (fiveLineSubgroup_eq_inf h).symm
  rw [hBJ, hpE]
  norm_num

theorem twA5FourModelAt_holds :
    ∀ (F : Type) [Field F] [Finite F] (hF : UnitaryFieldData 2 2 F),
      ∃ (q : ℕ) (B' : Subgroup (unitarySU 2 2 F 6)) (x' : unitarySU 2 2 F 6)
        (J : Subgroup (unitarySU 2 2 F 6)),
        Concl166S (unitarySU 2 2 F 6) 3 q B' x' J := by
  intro F _ _ h
  haveI := h.finite
  classical
  obtain ⟨ζu, hζu⟩ := exists_unit_orderOf_five (F := F) h
  let x : unitarySU 2 2 F 6 := diagFiveLast h (ζu : Fˣ) (norm_zeta hζu)
  let B : Subgroup (unitarySU 2 2 F 6) := unitaryTorusSU h ({0, 1} : Finset (Fin 6))
  let J : Subgroup (unitarySU 2 2 F 6) := unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))
  let E : Subgroup (unitarySU 2 2 F 6) := fiveLineSubgroup h
  let S : Subgroup (unitarySU 2 2 F 6) := unitaryLineRadical h
  have hζ6 : ((ζu : Fˣ) : F) ^ 6 ≠ 1 := by
    intro h6
    have h6' : ((ζu : Fˣ) : F) ^ 5 * ((ζu : Fˣ) : F) = 1 := by
      simpa [pow_succ] using h6
    rw [show (((ζu : Fˣ) : F) ^ 5) = 1 from by
      simpa [Units.val_pow_eq_pow_val] using
        congrArg (fun u : Fˣ => (u : F)) (zeta_pow_five hζu), one_mul] at h6'
    exact zeta_ne_one hζu (Units.ext h6')
  have hxcent : Subgroup.centralizer ({x} : Set (unitarySU 2 2 F 6)) =
      unitaryBlockDiag h ((Finset.univ : Finset (Fin 6)).erase 5) := by
    rw [show x = diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) from rfl]
    exact centralizer_diagFiveLast h (norm_zeta hζu) hζ6
  let labK : GLALabel := ⟨.twA, 5, 2⟩
  let labJ : GLALabel := ⟨.twA, 4, 2⟩
  have hKlab : HasLabel (unitarySU 2 2 F 6) (fun l : GLALabel => l = labK) :=
    hasLabel_unitarySU_six_four h
  have hJlab : HasLabel J (fun l : GLALabel => l = labJ) := by
    change HasLabel (unitaryBlock h {0, 1, 2, 3, 4})
      (fun l : GLALabel => l = ⟨.twA, 4, 2⟩)
    exact hasLabel_unitaryBlock_four h
  have hJq : CFSG.IsQuasisimple J := by
    change CFSG.IsQuasisimple ↥(unitaryBlock h {0, 1, 2, 3, 4})
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (unitaryBlockEquiv h _)
      (CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_unitarySU h (m := 5)
        (by norm_num) (by norm_num))
  have hJx : J ≤ Subgroup.centralizer ({x} : Set (unitarySU 2 2 F 6)) := by
    rw [hxcent]
    have hI : ({0, 1, 2, 3, 4} : Finset (Fin 6)) =
        (Finset.univ : Finset (Fin 6)).erase 5 := by decide
    rw [← hI]
    exact unitaryBlock_le_unitaryBlockDiag h _
  have hcomm := commutator_mem_unitaryBlock_of_mem_centralizer (F := F) h hxcent
  have he4 : evenRank (unitarySU 2 2 F 6) = 4 := evenRank_unitarySU_six_four h
  have he : 4 ≤ evenRank (unitarySU 2 2 F 6) := by rw [he4]
  have hBcard : Nat.card B = 5 ^ evenRank (unitarySU 2 2 F 6) := by
    rw [show B = unitaryTorusSU h {0,1} from rfl, card_unitaryTorusSU_two h, he4]
  have hB5 : IsElemAbelian 5 B := by
    change IsElemAbelian 5 (unitaryTorusSU h {0,1})
    exact isElemAbelian_unitaryTorusSU_two h
  have hx : x ∈ B := by
    change diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) ∈ unitaryTorusSU h {0,1}
    exact diagFiveLast_mem_unitaryTorusSU hζu
  have hx1 : x ≠ 1 := by
    change diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) ≠ 1
    exact diagFiveLast_ne_one hζu
  obtain ⟨hm2, hoddJ, hdvd⟩ := multiplier_unitarySU_six_four (F := F) h
  have hsix := six_unitarySU_six_four (F := F) h hJlab
  have hshape := shape_unitarySU_six_four (F := F) h
  obtain ⟨hE, hEcard, hEB, hxE, he3, hidiag, hSJ, hS2, hBS, h8⟩ :=
    fiveLine_and_lineRadical_data (F := F) h hζu
  have hseven : B ≤ J ⊔ Subgroup.zpowers x ∨
      HasLabel (unitarySU 2 2 F 6) (fun l : GLALabel => l = ⟨.twA, 5, 2⟩) :=
    Or.inr hKlab
  have hsu := su_unitaryBlock (F := F) h (x := x)
  have hrankinf := evenRank_le_pRank_inf_unitaryBlock (F := F) h
  exact ⟨5, B, x, J, concl166S_of_witness_idiag (K := unitarySU 2 2 F 6)
    (p := 3) (q := 5) (B := B) (x := x) (J := J) Nat.prime_five (by norm_num)
    hB5 hx hx1 hBcard he hJx hJq hcomm labJ hJlab hshape hm2 hoddJ hdvd hsix
    E hEB hE hEcard hxE he3 hidiag hseven hrankinf S hSJ hS2 hBS h8 hsu⟩


end CFSG.LocalAnalysis.GLTheoremA.Y10F
