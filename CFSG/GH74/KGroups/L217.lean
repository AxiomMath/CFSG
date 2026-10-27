module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSL2
public import CFSG.GH74.KGroups.PrimeField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.L217Inputs
public meta import CFSG.GH74.KGroups.L217Inputs
public import Certificates.Certificate5116
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GH74.KGroups.L217

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 2448 :=
  Certificates.certificate5116.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 4896 :=
  Certificates.certificate5116.2.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem orders_ok :
    orderIs pa 2 = true ∧ orderIs pb 3 = true ∧ pairInvB ws pa pb = true :=
  Certificates.certificate5116.2.2.1

theorem count_ok_check : pairCountB QP 2 3 ws = 4896 :=
  Certificates.certificate5116.2.2.2.2.2.2.2.2

theorem count_ok : pairCountB QP 2 3 ws = QA.orderCertificate := by
  rw [QA_valid.2]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList pa pb = true :=
  Certificates.certificate5116.2.2.2.1

theorem cent_ok :
    centTrivCheck (elemsT QA) pa pb = true :=
  Certificates.certificate5116.2.2.2.2.1

theorem e9all_ok : e9all (elemsT QA) = true :=
  Certificates.certificate5116.2.2.2.2.2.1

theorem inner3_ok :
    inner3check (elemsT QA) QP = true :=
  Certificates.certificate5116.2.2.2.2.2.2.1

theorem solv_ok :
    solvCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate5116.2.2.2.2.2.2.2.1

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl
  norm_num

instance factPrime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem card_F : Nat.card (PF 17) = 17 ^ 1 := by
  rw [PF.card, pow_one]

@[expose] def enum : Fin 17 → (PF 17) := fun k => PF.ofNat' k.val

theorem enum_bij : Function.Bijective enum := by decide

@[expose] def mA : Matrix.SpecialLinearGroup (Fin 2) (PF 17) :=
  ⟨!![(PF.ofNat' 0), (PF.ofNat' 1); (PF.ofNat' 16), (PF.ofNat' 0)], by
    rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def mB : Matrix.SpecialLinearGroup (Fin 2) (PF 17) :=
  ⟨!![(PF.ofNat' 0), (PF.ofNat' 1); (PF.ofNat' 16), (PF.ofNat' 1)], by
    rw [Matrix.det_fin_two_of]; decide⟩

theorem actA : ∀ i : Fin 18, ∃ c : (PF 17), c • ((mA : Matrix (Fin 2) (Fin 2) (PF 17)) *ᵥ PSL2.vecP enum i) =
    PSL2.vecP enum (pa i) := by
  decide +kernel

theorem actB : ∀ i : Fin 18, ∃ c : (PF 17), c • ((mB : Matrix (Fin 2) (Fin 2) (PF 17)) *ᵥ PSL2.vecP enum i) =
    PSL2.vecP enum (pb i) := by
  decide +kernel

theorem card_psl_F : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 17)) = 2448 := by
  have e := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField (PF 17) 17 1 (by norm_num) card_F) (Fin 2)
  rw [Nat.card_congr e.toEquiv]
  have hc : Nat.card (GaloisField 17 1) = 17 ^ 1 := GaloisField.card 17 1 (by norm_num)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 17 1)) :=
    ⟨17, 1, by norm_num, by decide, by norm_num, hc⟩
  have h := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 17 1) hodd
  rw [hc] at h
  norm_num at h
  exact h

theorem equiv_psl_P :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 17) ≃* QP.originalSubgroup) := by
  refine PSL2.psl2_equiv_closure (PSL2.ptEquiv enum enum_bij) mA mB pa pb
    (PSL2.pointwise_of_exists enum enum_bij mA pa actA)
    (PSL2.pointwise_of_exists enum enum_bij mB pb actB) QP.originalSubgroup QP_closure ?_
  rw [card_group QP QP_ok, QP_valid.2, card_psl_F]

theorem equiv_of_lieModel
    {K : Type} [Group K] (h : LieModel K .PSL 2 17 1) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨e1⟩ := PSL2.psl2_equiv_of_lieModel (F := (PF 17)) 17 1 (by norm_num) card_F h
  obtain ⟨e2⟩ := equiv_psl_P
  exact ⟨e1.trans e2⟩

theorem equiv_of_stated {K : Type} [Group K]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 2 17 1) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨e1⟩ := PSL2.psl2_equiv_of_stated (F := (PF 17)) 17 1 (by norm_num) card_F h
  obtain ⟨e2⟩ := equiv_psl_P
  exact ⟨e1.trans e2⟩

theorem autModel
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin 18)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  have ho := orders_ok
  exact autModel_exists QP QA QP_ok QA_ok pa pb QP_closure 2 3 (by norm_num) (by norm_num) ws
    ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1) ((orderIs_iff _ (by norm_num)).1 ho.2.1)
    ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok norm_ok cent_ok e

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem finite_K : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv

theorem finite_mulAut : Finite (MulAut K) := by
  obtain ⟨M, -, -⟩ := autModel e
  exact Finite.of_equiv M.A M.Φ.symm.toEquiv

theorem card_mulAut : Nat.card (MulAut K) = 4896 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  rw [M.card_mulAut, hA, card_group QA QA_ok, QA_valid.2]

theorem inner3
    (φ : MulAut K) (hφ : φ ^ 3 = 1) : ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have h := inner3check_sound QA QP QA_ok QP_ok inner3_ok
  exact M.inner3 (fun g hg h3 => by rw [hP]; rw [hA] at hg; exact h g hg h3) φ hφ

theorem autRank3_le_two
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 9 := by
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) 3 R hR 2 (by rw [card_mulAut e]; norm_num)
  simpa using this

theorem autRank3_le_one
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 3 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have he := e9all_sound QA QA_ok e9all_ok
  rw [← hA] at he
  exact M.autRank3_le_one he R hR

theorem autRank_ge5
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup (MulAut K))
    (hB : ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) p B hB 1 (by
    rw [card_mulAut e]
    intro hdvd
    have hle : p ^ 2 ≤ 4896 := Nat.le_of_dvd (by norm_num) hdvd
    have : p ≤ 69 := by nlinarith
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num))
  simpa using this

theorem fixed_solvable
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L : Subgroup K)
    (hL : ∀ x ∈ L, α x = x) : Group.IsSolvable L := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have hs := solvCheck_sound QA QP QA_ok QP_ok solv_ok
  refine M.fixed_solvable (fun τ hτ h2 h1 => ?_) α hα2 hα1 L hL
  have hτ' : τ ∈ QA.originalSubgroup := hA ▸ hτ
  have := hs τ hτ' h2 h1
  rwa [← hP] at this

end Consequences

end CFSG.GH74.KGroups.L217
