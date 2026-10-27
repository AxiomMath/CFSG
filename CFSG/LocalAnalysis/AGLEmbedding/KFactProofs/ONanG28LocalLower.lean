module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalQ

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.PreuniquenessRankFour.Helpers

section Lower

attribute [local irreducible] txL tU tZ tO tzc gW


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem cert_q1 : qOK txL tzc tB1 tY1 = true :=
  Certificates.certificate9557.2.2.2.2.2.2.2.1

theorem cert_q2 : qOK txL tzc tB2 tY2 = true :=
  Certificates.certificate9557.2.2.2.2.2.2.2.2.1

theorem cert_g : gOK tzc txL[tB1]! txL[tB2]! gW = true :=
  Certificates.certificate9557.2.2.2.2.2.2.2.2.2

@[expose] noncomputable def gElt (j : ℕ) : adjointGroup .G2 K := M.wordElt gW[j]!

@[expose] noncomputable def gInv (j : ℕ) : adjointGroup .G2 K := M.wordElt (gW[j]!).reverse

@[expose] def bIdx (j : ℕ) : ℕ := if j < 2 then tB1 else tB2

theorem rho_gElt (j : ℕ) : M.rho (gElt M j) = decode (wordCode gW[j]!) := M.rho_wordElt _

theorem rho_gInv (j : ℕ) : M.rho (gInv M j) = decode (wordCode (gW[j]!).reverse) :=
  M.rho_wordElt _

theorem gElt_mul_gInv {j : ℕ} (hj : j < 4) : gElt M j * gInv M j = 1 := by
  obtain ⟨-, hg⟩ := gOK_spec cert_g
  obtain ⟨h1, -⟩ := hg j hj
  exact (M.eq_one_iff_code (valid_mulCode (valid_wordCode _) (valid_wordCode _))
    (M.rho_mul_code (valid_wordCode _) (valid_wordCode _) (rho_gElt M j) (rho_gInv M j))).2 h1

theorem gInv_eq {j : ℕ} (hj : j < 4) : gInv M j = (gElt M j)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (gElt_mul_gInv M hj)).symm

theorem txL_bIdx (j : ℕ) : txL[bIdx j]! = if j < 2 then txL[tB1]! else txL[tB2]! := by
  unfold bIdx
  split_ifs <;> rfl

theorem bIdx_lt (j : ℕ) : bIdx j < 243 := by
  unfold bIdx
  split_ifs <;> decide

theorem gElt_conj_z {j : ℕ} (hj : j < 4) :
    gElt M j * zE M * (gElt M j)⁻¹ = zE M ∨ gElt M j * zE M * (gElt M j)⁻¹ = zE M * zE M := by
  obtain ⟨-, hg⟩ := gOK_spec cert_g
  obtain ⟨-, -, h3, -⟩ := hg j hj
  rw [← gInv_eq M hj]
  have hv : Valid (mulCode (mulCode (wordCode gW[j]!) tzc) (wordCode (gW[j]!).reverse)) :=
    valid_mulCode (valid_mulCode (valid_wordCode _) valid_tzc) (valid_wordCode _)
  have hrho : M.rho (gElt M j * zE M * gInv M j) =
      decode (mulCode (mulCode (wordCode gW[j]!) tzc) (wordCode (gW[j]!).reverse)) :=
    M.rho_mul_code (valid_mulCode (valid_wordCode _) valid_tzc) (valid_wordCode _)
      (M.rho_mul_code (valid_wordCode _) valid_tzc (rho_gElt M j) (rho_zE M)) (rho_gInv M j)
  rcases h3 with h | h
  · exact Or.inl ((M.eq_iff_codes hv valid_tzc hrho (rho_zE M)).2 h)
  · exact Or.inr ((M.eq_iff_codes hv (valid_mulCode valid_tzc valid_tzc) hrho
      (M.rho_mul_code valid_tzc valid_tzc (rho_zE M) (rho_zE M))).2 h)

theorem gElt_conj_b {j : ℕ} (hj : j < 4) : ∃ t < 9,
    gElt M j * bE M (bIdx j) * (gElt M j)⁻¹ = zE M ^ (t / 3) * bE M (bIdx j) ^ (t % 3) := by
  obtain ⟨-, hg⟩ := gOK_spec cert_g
  obtain ⟨-, -, -, t, ht, h4⟩ := hg j hj
  refine ⟨t, ht, ?_⟩
  rw [← gInv_eq M hj]
  have hb : Valid txL[bIdx j]! := valid_txL (bIdx_lt j)
  have hbj : (if j < 2 then txL[tB1]! else txL[tB2]!) = txL[bIdx j]! := (txL_bIdx j).symm
  rw [hbj] at h4
  obtain ⟨hp1, hp1'⟩ := M.rho_pow (zE M) valid_tzc (rho_zE M) (t / 3)
  obtain ⟨hp2, hp2'⟩ := M.rho_pow (bE M (bIdx j)) hb (rho_bE M (bIdx_lt j)) (t % 3)
  have hrho : M.rho (gElt M j * bE M (bIdx j) * gInv M j) =
      decode (mulCode (mulCode (wordCode gW[j]!) txL[bIdx j]!) (wordCode (gW[j]!).reverse)) :=
    M.rho_mul_code (valid_mulCode (valid_wordCode _) hb) (valid_wordCode _)
      (M.rho_mul_code (valid_wordCode _) hb (rho_gElt M j) (rho_bE M (bIdx_lt j))) (rho_gInv M j)
  exact (M.eq_iff_codes (valid_mulCode (valid_mulCode (valid_wordCode _) hb) (valid_wordCode _))
    (valid_mulCode hp1 hp2) hrho (M.rho_mul_code hp1 hp2 hp1' hp2')).2 h4

theorem gElt_normalizes_QX {j : ℕ} (hj : j < 4) :
    ∀ q ∈ QX M (bIdx j), gElt M j * q * (gElt M j)⁻¹ ∈ QX M (bIdx j) := by
  set f : adjointGroup .G2 K →* adjointGroup .G2 K :=
    (MulAut.conj (gElt M j)).toMonoidHom with hf
  have hfapply : ∀ x, f x = gElt M j * x * (gElt M j)⁻¹ := fun x => by
    simp [hf, MulAut.conj_apply]
  have hz : f (zE M) ∈ QX M (bIdx j) := by
    rw [hfapply]
    have hzQ : zE M ∈ QX M (bIdx j) := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    rcases gElt_conj_z M hj with h | h
    · rw [h]; exact hzQ
    · rw [h]; exact Subgroup.mul_mem _ hzQ hzQ
  have hb : f (bE M (bIdx j)) ∈ QX M (bIdx j) := by
    rw [hfapply]
    obtain ⟨t, -, ht⟩ := gElt_conj_b M hj
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)
  have hle : (QX M (bIdx j)).map f ≤ QX M (bIdx j) := by
    rw [QX, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, sup_le_iff,
      Subgroup.zpowers_le, Subgroup.zpowers_le]
    exact ⟨hz, hb⟩
  intro q hq
  rw [← hfapply]
  exact hle ⟨q, hq, rfl⟩

theorem conj_gElt_mem_normalizer {j : ℕ} (hj : j < 4) :
    (MulAut.conj (gElt M j) : MulAut (adjointGroup .G2 K)) ∈
      Subgroup.normalizer (QA M (bIdx j) : Set (MulAut (adjointGroup .G2 K))) :=
  mem_normalizer_of_conj_le fun x hx => by
    obtain ⟨q, hq, rfl⟩ := hx
    refine ⟨gElt M j * q * (gElt M j)⁻¹, gElt_normalizes_QX M hj q hq, ?_⟩
    simp [map_mul, map_inv]

theorem conj_gElt_mem_weakCore (hK : Nat.card K = 8) {j : ℕ} (hj : j < 4) :
    (MulAut.conj (gElt M j) : MulAut (adjointGroup .G2 K)) ∈
      GLBWeakCore 3 (T0 M hK : Subgroup (MulAut (adjointGroup .G2 K))) := by
  have hn := conj_gElt_mem_normalizer M hj
  unfold bIdx at hn
  split_ifs at hn with h
  · exact normalizer_QA_le_weakCore M cert_q1 hK (by decide) (by decide) hn
  · exact normalizer_QA_le_weakCore M cert_q2 hK (by decide) (by decide) hn

theorem phi_mem_weakCore (hK : Nat.card K = 8) :
    (phi : MulAut (adjointGroup .G2 K)) ∈
      GLBWeakCore 3 (T0 M hK : Subgroup (MulAut (adjointGroup .G2 K))) := by
  have h := yA_mem_normalizer_QA M cert_q2 hK
  have h0 : yA M tY2 = (phi : MulAut (adjointGroup .G2 K)) := by simp [yA, txElt, tY2, mk]
  rw [h0] at h
  exact normalizer_QA_le_weakCore M cert_q2 hK (by decide) (by decide) h

end Lower

end CFSG.AGLEmbedding.KFactProofs.G28
