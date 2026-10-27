module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.A5Inputs
public meta import CFSG.GH74.KGroups.A5Inputs
public import Certificates.Certificate5107
public import Certificates.Certificate43
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.KGroups.A5

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 60 :=
  Certificates.certificate5107.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 120 :=
  Certificates.certificate5107.2.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem orders_ok :
    orderIs pa 2 = true ∧ orderIs pb 3 = true ∧ pairInvB ws pa pb = true :=
  Certificates.certificate5107.2.2.1

theorem count_ok_check : pairCountB QP 2 3 ws = 120 :=
  Certificates.certificate5107.2.2.2.2.2.2.2

theorem count_ok : pairCountB QP 2 3 ws = QA.orderCertificate := by
  rw [QA_valid.2]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList pa pb = true :=
  Certificates.certificate5107.2.2.2.1

theorem cent_ok :
    centTrivCheck (elemsT QA) pa pb = true :=
  Certificates.certificate5107.2.2.2.2.1

theorem inner3_ok :
    inner3check (elemsT QA) QP = true :=
  Certificates.certificate5107.2.2.2.2.2.1

theorem solv_ok :
    solvCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate5107.2.2.2.2.2.2.1

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl
  norm_num

theorem QP_eq_alt :
    QP.originalSubgroup = alternatingGroup (Fin 5) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [QP_closure, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]; decide
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]; decide
  · rw [card_group QP QP_ok, QP_valid.2, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]

theorem equiv_of_alt
    {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 5)) :
    Nonempty (K ≃* QP.originalSubgroup) :=
  ⟨e.trans (MulEquiv.subgroupCongr QP_eq_alt.symm)⟩

theorem autModel
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin 5)), M.P = QP.originalSubgroup ∧
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

theorem card_mulAut : Nat.card (MulAut K) = 120 := by
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
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) 3 R hR 1 (by rw [card_mulAut e]; norm_num)
  simpa using this

theorem autRank_ge5
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup (MulAut K))
    (hB : ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) p B hB 1 (by
    rw [card_mulAut e]
    intro hdvd
    have hle : p ^ 2 ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
    have : p ≤ 10 := by nlinarith
    interval_cases p <;> omega)
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
theorem equiv_of_lieModel22
    {K : Type} [Group K] (h : LieModel K .PSL 2 2 2) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model K h
  exact equiv_of_alt e

theorem equiv_of_lieModel25
    {K : Type} [Group K] (h : LieModel K .PSL 2 5 1) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (ZMod 5) = 5 ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨e1⟩ := PSLN.psl_equiv_of_lieModel (F := ZMod 5) 2 5 1 (by norm_num) hc h
  obtain ⟨e2⟩ := PSLN.psl_equiv_of_stated (F := ZMod 5) (K := alternatingGroup (Fin 5)) 2 5 1
    (by norm_num) hc
    (CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five _
      ⟨MulEquiv.refl _⟩)
  exact ⟨(e1.trans e2.symm).trans (MulEquiv.subgroupCongr QP_eq_alt.symm)⟩


end CFSG.GH74.KGroups.A5
