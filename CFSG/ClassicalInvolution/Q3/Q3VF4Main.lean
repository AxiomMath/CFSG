module

public import CFSG.ClassicalInvolution.Q3.Q3VF4Frame
public import CFSG.ClassicalInvolution.Q3.Q3VCtMain
public import CFSG.ClassicalInvolution.Q3.Q3VCtMainSub
public import CFSG.ClassicalInvolution.WeakCT.DLDiagrams
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSp4Levi
public import CFSG.Timmesfeld.RankTwo.LeviData
public import CFSG.LieType.CurtisTits.Adjoint
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT
  (DoubleBondDiagram LinearBlockStandardPair blk spBlock)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.Q3.Q3Z CFSG.ClassicalInvolution.Q3.Q3TW
open scoped MatrixGroups

abbrev adjF4 (i j : Fin 4) : Prop :=
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2) ∨ (i.val = 3 ∧ j.val = 2)

theorem doubleBondDiagram_f4' :
    DoubleBondDiagram (Tag.cartan .F4) adjF4 ⟨1, by decide⟩ ⟨2, by decide⟩ where
  adj_ab := by decide
  cartan_ba := by decide
  cartan_ab := by decide
  cartan_adj := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  cartan_nadj := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  neighbour := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide

section Recognition


theorem weakCT3_f4_of_frame {X : Type} [Group X] (U : Fin 4 → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (fr : F4Frame3 U) :
    ∃ Ψ : (adjointGroup .F4 (GaloisField 3 1)) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (adjointGroup .F4 (GaloisField 3 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .F4 0 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : StatedLieAdmissible .F4 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hcard : Nat.card (GaloisField 3 1) = 3 := Q3Z.natCard_galoisField_three
  have h2 : (2 : GaloisField 3 1) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField 3 1) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField 3 1) 3] at h'
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1 h') (by norm_num)
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).isFiniteType
    (Dv := (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).divisible) rfl
  obtain ⟨C, -, hC⟩ := Steinberg.Adjoint.f4_commutatorFormula (GaloisField 3 1) O
  have hE := Steinberg.Adjoint.f4_chevalleyExtras (GaloisField 3 1) O C hC
  have hsq : ∀ k : Fin (Tag.rank .F4),
      Steinberg.weylElement (Steinberg.Adjoint.f4Par (GaloisField 3 1)) k 1 ^ 2 ∈
        Steinberg.Adjoint.torus (τ := .F4) (GaloisField 3 1) k := by
    intro k
    have h := (Steinberg.Adjoint.f4_isCTGroupDatum (GaloisField 3 1)).sq_mem k
    rw [Steinberg.Adjoint.weylElement_eq_xPar (Chevalley.rootOperatorFamily .F4) k] at h
    exact h
  have hdiag := doubleBondDiagram_f4'
  have hSp4 := CFSG.ComponentClassification.CatLeafProof.exists_sp4Levi_of_isQuasisimple
    (CFSG.ComponentClassification.CatLeafProof.isQuasisimple_statedSp_two (by rw [hcard]))
    h2 hE rfl hdiag.cartan_ba hdiag.cartan_ab
  have hcomm' : ∀ i j : Fin 4, i ≠ j → ¬ adjF4 i j → ¬ adjF4 j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hne h1 h2' u hu v hv
    simp only [adjF4] at h1 h2'
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm i j (by omega) u hu v hv
    · exact (hcomm j i (by omega) v hv u hu).symm
  have hψ : ∀ i j : Fin 4, adjF4 i j →
      ¬ (i = (⟨1, by decide⟩ : Fin 4) ∧ j = ⟨2, by decide⟩) →
      ∃ ψ : SL(3, GaloisField 3 1) →* X,
        ψ.comp (blk (GaloisField 3 1) 0) = fr.ρ i ∧ ψ.comp (blk (GaloisField 3 1) 1) = fr.ρ j := by
    intro i j hij hne
    rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 0 := Fin.ext hi
      have hj' : j = 1 := Fin.ext hj
      subst hi' hj'
      exact ⟨fr.ψL, fr.ψL_zero, fr.ψL_one⟩
    · exact absurd ⟨Fin.ext hi, Fin.ext hj⟩ hne
    · have hi' : i = 3 := Fin.ext hi
      have hj' : j = 2 := Fin.ext hj
      subst hi' hj'
      exact ⟨fr.ψR, fr.ψR_zero, fr.ψR_one⟩
  exact weakCT_of_frame_dl_of_sp4Levi (CurtisTits.curtisTitsConclusion_f4 3 1 hadm)
    (leviConePresented_f4 _) hE rfl hdiag hSp4
    (Steinberg.Adjoint.f4_steinbergExtras (GaloisField 3 1)).torus_iSupIndep hsq hgen hcomm'
    (fun k => ⟨fr.ρ_inj k, fr.ρ_range k⟩) hψ ⟨fr.ψ4, fr.ψ4_long, fr.ψ4_short⟩

end Recognition

end CFSG.ClassicalInvolution.Q3.Q3V
