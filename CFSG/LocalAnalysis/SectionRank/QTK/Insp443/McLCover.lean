module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CoverThree
public import CFSG.RankThree.PartTwo.KFacts.K426McL
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenArr
public import Certificates.Certificate589302

public section

namespace CFSG.SectionRank.QTK.Insp443

namespace McLCover

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open CFSG.Sporadic.Schreier (mclP)


theorem rep_of_covSift {x : Array ℕ} (hx : mclCovSift x = true) :
    Rep 275 x (permOfArr 275 x) ∧ Rep 275 (invCand 275 x) (permOfArr 275 x)⁻¹ := by
  simp only [mclCovSift, Bool.and_eq_true] at hx
  exact rep_permOfArr hx.1


theorem mem_mclP_of_covSift {x : Array ℕ} (hx : mclCovSift x = true) :
    permOfArr 275 x ∈ mclP := by
  simp only [mclCovSift, Bool.and_eq_true] at hx
  exact CFSG.RankThree.PartTwo.KFacts.K426.mem_mclP_of_sift (rep_permOfArr hx.1).1 hx.2

@[expose] noncomputable def covM {x : Array ℕ} (hx : mclCovSift x = true) : mclP :=
  ⟨permOfArr 275 x, mem_mclP_of_covSift hx⟩

theorem rep_covM {x : Array ℕ} (hx : mclCovSift x = true) :
    Rep 275 x (covM hx : Equiv.Perm (Fin 275)) :=
  (rep_of_covSift hx).1

theorem rep_covM_inv {x : Array ℕ} (hx : mclCovSift x = true) :
    Rep 275 (invCand 275 x) ((covM hx : Equiv.Perm (Fin 275)))⁻¹ :=
  (rep_of_covSift hx).2

theorem covM_comm {x y : Array ℕ} (hx : mclCovSift x = true) (hy : mclCovSift y = true)
    (h : commN 275 x y = true) : covM hx * covM hy = covM hy * covM hx :=
  Subtype.ext (mul_comm_of_commN (rep_covM hx) (rep_covM hy) h)

theorem covM_dist (ha : mclCovSift (mclCovArr 1) = true) (hb : mclCovSift (mclCovArr 2) = true)
    (i j k l : Fin 3)
    (h : covM ha ^ (i : ℕ) * covM hb ^ (j : ℕ) = covM ha ^ (k : ℕ) * covM hb ^ (l : ℕ)) :
    i = k ∧ j = l := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := Certificates.certificate589302
  have hrep : ∀ u : ℕ, Rep 275 (mclCovProd u)
      ((covM ha : Equiv.Perm (Fin 275)) ^ (u % 3) * (covM hb : Equiv.Perm (Fin 275)) ^ (u / 3)) :=
    fun u => rep_pN (rep_covM ha) (rep_covM hb) (u % 3, u / 3)
  have hu := List.all_eq_true.mp hd (i + 3 * j) (List.mem_range.mpr (by omega))
  have hv := List.all_eq_true.mp hu (k + 3 * l) (List.mem_range.mpr (by omega))
  have hi : ((i : ℕ) + 3 * j) % 3 = i := by omega
  have hj : ((i : ℕ) + 3 * j) / 3 = j := by omega
  have hk : ((k : ℕ) + 3 * l) % 3 = k := by omega
  have hl : ((k : ℕ) + 3 * l) / 3 = l := by omega
  have hP : (covM ha : Equiv.Perm (Fin 275)) ^ (((i : ℕ) + 3 * j) % 3) *
      (covM hb : Equiv.Perm (Fin 275)) ^ (((i : ℕ) + 3 * j) / 3) =
      (covM ha : Equiv.Perm (Fin 275)) ^ (((k : ℕ) + 3 * l) % 3) *
      (covM hb : Equiv.Perm (Fin 275)) ^ (((k : ℕ) + 3 * l) / 3) := by
    rw [hi, hj, hk, hl]
    exact congrArg Subtype.val h
  have he := (eqA_iff (hrep _) (hrep _)).2 hP
  simp only [he, Bool.not_true, Bool.or_false, beq_iff_eq] at hv
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

end McLCover

open McLCover CFSG.Monster.B.Co2 CFSG.RankThree.PartTwo.Sec4.Item434SporGen in
theorem KConf.false_of_threeMcL
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K} (hK : KConf K L V MK)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.Carrier .McL)
    (hZ : Nat.card (Subgroup.center K) = 3) : False := by
  obtain ⟨s0, s1, s2, s3, s4, hz2, hz1, ha3, hb3, hab, haz, hbz, -, hg1, hg2a, hg2b⟩ :=
    Certificates.certificate589302
  set z := covM s0
  set a := covM s1
  set b := covM s2
  set g₁ := covM s3
  set g₂ := covM s4
  have hza : a * z * a⁻¹ = z := by
    rw [covM_comm s1 s0 haz, mul_inv_cancel_right]
  have hzb : b * z * b⁻¹ = z := by
    rw [covM_comm s2 s0 hbz, mul_inv_cancel_right]
  have hzsq : z ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, sq, Subgroup.coe_one]
    exact eq_of_eqA (rep_compA (rep_covM s0) (rep_covM s0)) rep_idA hz2
  refine KConf.false_of_threeCover hK (e.trans CFSG.Sporadic.Schreier.mclPermEquiv) hZ
    (q₁ := z) (q₂ := z) (a := a) (b := b) (g₁ := g₁) (g₂ := g₂) hzsq hzsq rfl ?_ ?_ ?_
    (covM_comm s1 s2 hab) (covM_dist s1 s2) ?_ ?_ ?_ ?_ ?_
  · intro h
    have h1 : (z : Equiv.Perm (Fin 275)) = 1 := by rw [h]; rfl
    rw [(eqA_iff (rep_covM s0) rep_idA).2 h1] at hz1
    exact Bool.noConfusion hz1
  · refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (rep_powN (rep_covM s1) 3) rep_idA ha3
  · refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (rep_powN (rep_covM s2) 3) rep_idA hb3
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at hq
    subst hq
    rw [hza]
    exact Set.mem_insert _ _
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at hq
    subst hq
    rw [hzb]
    exact Set.mem_insert _ _
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    exact eq_of_eqA (rep_compA (rep_compA (rep_covM s3) (rep_covM s1)) (rep_covM_inv s3))
      (rep_covM_inv s1) hg1
  · rw [covM_comm s4 s1 hg2a, mul_inv_cancel_right]
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    exact eq_of_eqA (rep_compA (rep_compA (rep_covM s4) (rep_covM s2)) (rep_covM_inv s4))
      (rep_covM_inv s2) hg2b

end CFSG.SectionRank.QTK.Insp443

end
