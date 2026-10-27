module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.L33Inputs
public meta import CFSG.GH74.KGroups.L33Inputs
public import Certificates.Certificate5120

public section

namespace CFSG.GH74.KGroups.L33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix

theorem QP13_valid :
    QP13.check = true ∧ QP13.orderCertificate = 5616 :=
  Certificates.certificate5120.1

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 5616 :=
  Certificates.certificate5120.2.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 11232 :=
  Certificates.certificate5120.2.2.1

theorem QP13_ok : ValidSchreier QP13 := QP13_valid.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP13_closure : QP13.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP13, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {PA, PB} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem orders_ok :
    orderIs PA 2 = true ∧ orderIs PB 3 = true ∧ pairInvB ws PA PB = true :=
  Certificates.certificate5120.2.2.2.1

theorem count_ok_check : pairCountB QP 2 3 ws = 11232 :=
  Certificates.certificate5120.2.2.2.2.2.2.2.2.2.2.2.2

theorem count_ok : pairCountB QP 2 3 ws = QA.orderCertificate := by
  rw [QA_valid.2]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList PA PB = true :=
  Certificates.certificate5120.2.2.2.2.1

theorem cent_ok :
    centTrivCheck (elemsT QA) PA PB = true :=
  Certificates.certificate5120.2.2.2.2.2.1

theorem e9_ok : e9free (elemsT QA) = true :=
  Certificates.certificate5120.2.2.2.2.2.2.1

theorem e27_ok : e27free (elemsT QA) = true :=
  Certificates.certificate5120.2.2.2.2.2.2.2.1

theorem inner3_ok :
    inner3check (elemsT QA) QP = true :=
  Certificates.certificate5120.2.2.2.2.2.2.2.2.1

theorem cent3_ok : cent3check (elemsT QP) = true :=
  Certificates.certificate5120.2.2.2.2.2.2.2.2.2.1

theorem solv_ok :
    solvCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate5120.2.2.2.2.2.2.2.2.2.2.1

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl | rfl <;> norm_num

@[expose] def vec : Fin 13 → (Fin 3 → ZMod 3) := fun i =>
  if i.val < 9 then ![1, ((i.val / 3 : ℕ) : ZMod 3), ((i.val % 3 : ℕ) : ZMod 3)]
  else if i.val < 12 then ![0, 1, ((i.val - 9 : ℕ) : ZMod 3)] else ![0, 0, 1]

theorem vec_ne : ∀ i, vec i ≠ 0 := by decide +kernel

theorem vec_inj : ∀ i j (c : ZMod 3), c • vec j = vec i → i = j := by decide +kernel

theorem vec_surj : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ i, ∃ c : ZMod 3, c • v = vec i := by
  decide +kernel

@[expose] def mA : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
  ⟨!![(0 : ZMod 3), (0 : ZMod 3), (1 : ZMod 3); (0 : ZMod 3), (2 : ZMod 3), (0 : ZMod 3); (1 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)], by
    rw [Matrix.det_fin_three]; decide⟩

@[expose] def mB : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
  ⟨!![(0 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3); (1 : ZMod 3), (0 : ZMod 3), (2 : ZMod 3); (2 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3)], by
    rw [Matrix.det_fin_three]; decide⟩

theorem actA : ∀ i : Fin 13, ∃ c : ZMod 3, c • ((mA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ vec i) =
    vec (pa i) := by
  decide +kernel

theorem actB : ∀ i : Fin 13, ∃ c : ZMod 3, c • ((mB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ vec i) =
    vec (pb i) := by
  decide +kernel

theorem card_F : Nat.card (ZMod 3) = 3 ^ 1 := by
  rw [Nat.card_zmod, pow_one]

theorem cube_one : ∀ r : ZMod 3, r ^ 3 = 1 → r = 1 := by decide

theorem center_bot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have h1 : r = 1 := cube_one r (by simpa using hr)
    subst h1
    apply Subtype.ext
    rw [← hA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

theorem card_psl : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
  rw [PSLN.card_psl_of_center_bot center_bot, Matrix.card_SL_field 3]
  norm_num [ZMod.card, Fin.prod_univ_three]

theorem equiv_psl_P13 :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) ≃* QP13.originalSubgroup) := by
  refine PSLN.psl_equiv_closure (PSLN.ptEquivOf vec vec_ne vec_inj vec_surj) mA mB pa pb
    (PSLN.pointwise_of_exists vec vec_ne vec_inj vec_surj mA pa actA)
    (PSLN.pointwise_of_exists vec vec_ne vec_inj vec_surj mB pb actB) QP13.originalSubgroup
    QP13_closure ?_
  rw [card_group QP13 QP13_ok, QP13_valid.2, card_psl]

theorem blk :
    blockHom 13 13 (pa, pa') = PA ∧ blockHom 13 13 (pb, pb') = PB :=
  Certificates.certificate5120.2.2.2.2.2.2.2.2.2.2.2.1

theorem equiv_P13_P :
    Nonempty (QP13.originalSubgroup ≃* QP.originalSubgroup) := by
  have hpa : pa ∈ QP13.originalSubgroup := by
    rw [QP13_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hpb : pb ∈ QP13.originalSubgroup := by
    rw [QP13_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨φ, -⟩ := blockIso pa pb pa' pb' PA PB blk.1 blk.2 QP13.originalSubgroup QP.originalSubgroup
    QP13_closure QP_closure hpa hpb (by rw [card_group QP QP_ok, card_group QP13 QP13_ok,
      QP_valid.2, QP13_valid.2])
  exact ⟨φ⟩

theorem equiv_of_lieModel
    {K : Type} [Group K] (h : LieModel K .PSL 3 3 1) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e1⟩ := PSLN.psl_equiv_of_lieModel (F := ZMod 3) 3 3 1 (by norm_num) card_F h
  obtain ⟨e2⟩ := equiv_psl_P13
  obtain ⟨e3⟩ := equiv_P13_P
  exact ⟨e1.trans (e2.trans e3)⟩

theorem autModel
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin 26)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  have ho := orders_ok
  exact autModel_exists QP QA QP_ok QA_ok PA PB QP_closure 2 3 (by norm_num) (by norm_num) ws
    ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1) ((orderIs_iff _ (by norm_num)).1 ho.2.1)
    ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok norm_ok cent_ok e

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem finite_K : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv

theorem finite_mulAut : Finite (MulAut K) := by
  obtain ⟨M, -, -⟩ := autModel e
  exact Finite.of_equiv M.A M.Φ.symm.toEquiv

theorem card_mulAut : Nat.card (MulAut K) = 11232 := by
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
  obtain ⟨M, hP, hA⟩ := autModel e
  have he := e27free_sound QA QA_ok e27_ok
  rw [← hA] at he
  exact M.autRank3_le_two he R hR

theorem autRank_ge5
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup (MulAut K))
    (hB : ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) p B hB 1 (by
    rw [card_mulAut e]
    intro hdvd
    have hle : p ^ 2 ≤ 11232 := Nat.le_of_dvd (by norm_num) hdvd
    have : p ≤ 105 := by nlinarith
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

end CFSG.GH74.KGroups.L33
