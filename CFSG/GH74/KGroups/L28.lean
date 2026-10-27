module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Quasithin.Recognition.CertF8
import CFSG.Walter.PSL2Facts.Even
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.L28Inputs
public meta import CFSG.GH74.KGroups.L28Inputs
public import Certificates.Certificate5118
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.GH74.KGroups.L28

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Quasithin CFSG.Blueprint Matrix

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 504 :=
  Certificates.certificate5118.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 1512 :=
  Certificates.certificate5118.2.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem orders_ok :
    orderIs pa 2 = true ∧ orderIs pb 3 = true ∧ pairInvB ws pa pb = true :=
  Certificates.certificate5118.2.2.1

theorem count_ok_check : pairCountB QP 2 3 ws = 1512 :=
  Certificates.certificate5118.2.2.2.2.2.2.2.2

theorem count_ok : pairCountB QP 2 3 ws = QA.orderCertificate := by
  rw [QA_valid.2]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList pa pb = true :=
  Certificates.certificate5118.2.2.2.1

theorem cent_ok :
    centTrivCheck (elemsT QA) pa pb = true :=
  Certificates.certificate5118.2.2.2.2.1

theorem e9_ok : e9free (elemsT QA) = true :=
  Certificates.certificate5118.2.2.2.2.2.1

theorem e27_ok : e27free (elemsT QA) = true :=
  Certificates.certificate5118.2.2.2.2.2.2.1

theorem solv_ok :
    solvCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate5118.2.2.2.2.2.2.2.1

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl
  norm_num

@[expose] def enum : Fin 8 → GF8 := fun k => GF8.ofNat' k.val

theorem enum_bij : Function.Bijective enum := by decide

@[expose] def mA : Matrix.SpecialLinearGroup (Fin 2) GF8 :=
  ⟨!![GF8.ofNat' 0, GF8.ofNat' 1; GF8.ofNat' 1, GF8.ofNat' 0], by
    rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def mB : Matrix.SpecialLinearGroup (Fin 2) GF8 :=
  ⟨!![GF8.ofNat' 0, GF8.ofNat' 2; GF8.ofNat' 5, GF8.ofNat' 1], by
    rw [Matrix.det_fin_two_of]; decide⟩

theorem actA : ∀ i : Fin 9, ∃ c : GF8, c • ((mA : Matrix (Fin 2) (Fin 2) GF8) *ᵥ PSL2.vecP enum i) =
    PSL2.vecP enum (pa i) := by
  decide +kernel

theorem actB : ∀ i : Fin 9, ∃ c : GF8, c • ((mB : Matrix (Fin 2) (Fin 2) GF8) *ᵥ PSL2.vecP enum i) =
    PSL2.vecP enum (pb i) := by
  decide +kernel

theorem card_GF8 : Nat.card GF8 = 2 ^ 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_psl_GF8 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF8) = 504 := by
  have e := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField GF8 2 3 (by norm_num) card_GF8) (Fin 2)
  rw [Nat.card_congr e.toEquiv]
  have h := CFSG.Walter.psl2_even_card (f := 3) (by norm_num)
  norm_num at h
  exact h

theorem equiv_psl_P :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF8 ≃* QP.originalSubgroup) := by
  refine PSL2.psl2_equiv_closure (PSL2.ptEquiv enum enum_bij) mA mB pa pb
    (PSL2.pointwise_of_exists enum enum_bij mA pa actA)
    (PSL2.pointwise_of_exists enum enum_bij mB pb actB) QP.originalSubgroup QP_closure ?_
  rw [card_group QP QP_ok, QP_valid.2, card_psl_GF8]

theorem equiv_of_lieModel
    {K : Type} [Group K] (h : LieModel K .PSL 2 2 3) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  obtain ⟨e1⟩ := PSL2.psl2_equiv_of_lieModel (F := GF8) 2 3 (by norm_num) card_GF8 h
  obtain ⟨e2⟩ := equiv_psl_P
  exact ⟨e1.trans e2⟩

theorem autModel {K : Type} [Group K] (h : LieModel K .PSL 2 2 3) :
    ∃ M : AutModel K (Equiv.Perm (Fin 9)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  obtain ⟨e⟩ := equiv_of_lieModel h
  have ho := orders_ok
  exact autModel_exists QP QA QP_ok QA_ok pa pb QP_closure 2 3 (by norm_num) (by norm_num) ws
    ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1) ((orderIs_iff _ (by norm_num)).1 ho.2.1)
    ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok norm_ok cent_ok e

section Consequences

variable {K : Type} [Group K] (h : LieModel K .PSL 2 2 3)

include h

theorem finite_K : Finite K := by
  obtain ⟨M, -, -⟩ := autModel h
  exact Finite.of_equiv M.P M.e.symm.toEquiv

theorem finite_mulAut : Finite (MulAut K) := by
  obtain ⟨M, -, -⟩ := autModel h
  exact Finite.of_equiv M.A M.Φ.symm.toEquiv

theorem card_mulAut : Nat.card (MulAut K) = 1512 := by
  obtain ⟨M, hP, hA⟩ := autModel h
  rw [M.card_mulAut, hA, card_group QA QA_ok, QA_valid.2]

theorem autCentralizer
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) (hcard : Nat.card R = 9)
    (ψ : MulAut K) (hψ : ψ ^ 2 = 1) (hc : ∀ r ∈ R, ψ * r = r * ψ) : ψ = 1 := by
  obtain ⟨M, hP, hA⟩ := autModel h
  have he := e9free_sound QA QA_ok e9_ok
  rw [← hA] at he
  exact M.autCentralizer he R hR hcard ψ hψ hc

theorem autRank3_le_two
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 9 := by
  obtain ⟨M, hP, hA⟩ := autModel h
  have he := e27free_sound QA QA_ok e27_ok
  rw [← hA] at he
  exact M.autRank3_le_two he R hR

theorem autRank_ge5
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup (MulAut K))
    (hB : ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_mulAut h
  have := elemAb_card_le (G := MulAut K) p B hB 1 (by
    rw [card_mulAut h]
    intro hdvd
    have hle : p ^ 2 ≤ 1512 := Nat.le_of_dvd (by norm_num) hdvd
    have : p ≤ 38 := by nlinarith
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num))
  simpa using this

theorem fixed_solvable
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L : Subgroup K)
    (hL : ∀ x ∈ L, α x = x) : Group.IsSolvable L := by
  obtain ⟨M, hP, hA⟩ := autModel h
  have hs := solvCheck_sound QA QP QA_ok QP_ok solv_ok
  refine M.fixed_solvable (fun τ hτ h2 h1 => ?_) α hα2 hα1 L hL
  have hτ' : τ ∈ QA.originalSubgroup := hA ▸ hτ
  have := hs τ hτ' h2 h1
  rwa [← hP] at this

end Consequences

end CFSG.GH74.KGroups.L28
