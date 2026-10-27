module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Quasithin.Recognition.CertF9
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.A6Inputs
public meta import CFSG.GH74.KGroups.A6Inputs
public import Certificates.Certificate5108
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.KGroups.A6

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix CFSG.Quasithin

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 360 :=
  Certificates.certificate5108.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 1440 :=
  Certificates.certificate5108.2.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem orders_ok :
    orderIs pa 2 = true ∧ orderIs pb 4 = true ∧ pairInvB ws pa pb = true :=
  Certificates.certificate5108.2.2.1

theorem count_ok_check : pairCountB QP 2 4 ws = 1440 :=
  Certificates.certificate5108.2.2.2.2.2.2.2.2.2

theorem count_ok : pairCountB QP 2 4 ws = QA.orderCertificate := by
  rw [QA_valid.2]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList pa pb = true :=
  Certificates.certificate5108.2.2.2.1

theorem cent_ok :
    centTrivCheck (elemsT QA) pa pb = true :=
  Certificates.certificate5108.2.2.2.2.1

theorem e9_ok : e9free (elemsT QA) = true :=
  Certificates.certificate5108.2.2.2.2.2.1

theorem inner3_ok :
    inner3check (elemsT QA) QP = true :=
  Certificates.certificate5108.2.2.2.2.2.2.1

theorem cent3_ok : cent3check (elemsT QP) = true :=
  Certificates.certificate5108.2.2.2.2.2.2.2.1

theorem solv_ok :
    solvCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate5108.2.2.2.2.2.2.2.2.1

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl
  norm_num

theorem card_F : Nat.card GF9 = 3 ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def enum : Fin 9 → GF9 := fun k => GF9.ofNat' k.val

theorem enum_bij : Function.Bijective enum := by decide

@[expose] def mA : Matrix.SpecialLinearGroup (Fin 2) GF9 :=
  ⟨!![(GF9.ofNat' 0), (GF9.ofNat' 1); (GF9.ofNat' 2), (GF9.ofNat' 0)], by
    rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def mB : Matrix.SpecialLinearGroup (Fin 2) GF9 :=
  ⟨!![(GF9.ofNat' 1), (GF9.ofNat' 3); (GF9.ofNat' 7), (GF9.ofNat' 5)], by
    rw [Matrix.det_fin_two_of]; decide⟩

theorem actA : ∀ i : Fin 10, ∃ c : GF9, c • ((mA : Matrix (Fin 2) (Fin 2) GF9) *ᵥ PSL2.vecP enum i) =
    PSL2.vecP enum (pa i) := by
  decide +kernel

theorem actB : ∀ i : Fin 10, ∃ c : GF9, c • ((mB : Matrix (Fin 2) (Fin 2) GF9) *ᵥ PSL2.vecP enum i) =
    PSL2.vecP enum (pb i) := by
  decide +kernel

theorem card_psl_F : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF9) = 360 := by
  have e := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField GF9 3 2 (by norm_num) card_F) (Fin 2)
  rw [Nat.card_congr e.toEquiv]
  have hc : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 2)) :=
    ⟨3, 2, by norm_num, by decide, by norm_num, hc⟩
  have h := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 3 2) hodd
  rw [hc] at h
  norm_num at h
  exact h

theorem equiv_psl_P :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF9 ≃* QP.originalSubgroup) := by
  refine PSL2.psl2_equiv_closure (PSL2.ptEquiv enum enum_bij) mA mB pa pb
    (PSL2.pointwise_of_exists enum enum_bij mA pa actA)
    (PSL2.pointwise_of_exists enum enum_bij mB pb actB) QP.originalSubgroup QP_closure ?_
  rw [card_group QP QP_ok, QP_valid.2, card_psl_F]

theorem equiv_of_lieModel
    {K : Type} [Group K] (h : LieModel K .PSL 2 3 2) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e1⟩ := PSL2.psl2_equiv_of_lieModel (F := GF9) 3 2 (by norm_num) card_F h
  obtain ⟨e2⟩ := equiv_psl_P
  exact ⟨e1.trans e2⟩

theorem equiv_of_stated {K : Type} [Group K]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 2 3 2) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e1⟩ := PSL2.psl2_equiv_of_stated (F := GF9) 3 2 (by norm_num) card_F h
  obtain ⟨e2⟩ := equiv_psl_P
  exact ⟨e1.trans e2⟩

theorem autModel
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin 10)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  have ho := orders_ok
  exact autModel_exists QP QA QP_ok QA_ok pa pb QP_closure 2 4 (by norm_num) (by norm_num) ws
    ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1) ((orderIs_iff _ (by norm_num)).1 ho.2.1)
    ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok norm_ok cent_ok e

theorem equiv_of_alt6
    {K : Type} [Group K] (h : Nonempty (K ≃* alternatingGroup (Fin 6))) :
    Nonempty (K ≃* QP.originalSubgroup) :=
  equiv_of_stated
    (CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six K h)

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem finite_K : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv

theorem finite_mulAut : Finite (MulAut K) := by
  obtain ⟨M, -, -⟩ := autModel e
  exact Finite.of_equiv M.A M.Φ.symm.toEquiv

theorem card_mulAut : Nat.card (MulAut K) = 1440 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  rw [M.card_mulAut, hA, card_group QA QA_ok, QA_valid.2]

theorem inner3
    (φ : MulAut K) (hφ : φ ^ 3 = 1) : ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have h := inner3check_sound QA QP QA_ok QP_ok inner3_ok
  exact M.inner3 (fun g hg h3 => by rw [hP]; rw [hA] at hg; exact h g hg h3) φ hφ

theorem autCentralizer
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) (hcard : Nat.card R = 9)
    (ψ : MulAut K) (hψ : ψ ^ 2 = 1) (hc : ∀ r ∈ R, ψ * r = r * ψ) : ψ = 1 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have he := e9free_sound QA QA_ok e9_ok
  rw [← hA] at he
  exact M.autCentralizer he R hR hcard ψ hψ hc

theorem autRank3_le_two
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 9 := by
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) 3 R hR 2 (by rw [card_mulAut e]; norm_num)
  simpa using this

theorem autRank_ge5
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup (MulAut K))
    (hB : ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) p B hB 1 (by
    rw [card_mulAut e]
    intro hdvd
    have hle : p ^ 2 ≤ 1440 := Nat.le_of_dvd (by norm_num) hdvd
    have : p ≤ 37 := by nlinarith
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num))
  simpa using this

theorem centralizer3
    (B : Subgroup K) (hB : ElemAb 3 B) (hcard : Nat.card B = 9) (k : K)
    (hk : ∀ b ∈ B, k * b = b * k) : k ∈ B :=
  centralizer3_of_model QP.originalSubgroup e (cent3check_sound QP QP_ok cent3_ok) B hB hcard k hk

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

end CFSG.GH74.KGroups.A6
