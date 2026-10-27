module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CoverThree
public import CFSG.RankThree.PartTwo.KFacts.K426J3
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenArr
public import Certificates.Certificate589303

public section

namespace CFSG.SectionRank.QTK.Insp443

namespace J3Cover

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open CFSG.Sporadic.Schreier (j3P)


theorem rep_of_covSift {x : Array ℕ} (hx : j3CovSift x = true) :
    Rep 6156 x (permOfArr 6156 x) ∧ Rep 6156 (invCand 6156 x) (permOfArr 6156 x)⁻¹ := by
  simp only [j3CovSift, Bool.and_eq_true] at hx
  exact rep_permOfArr hx.1


theorem mem_j3P_of_covSift {x : Array ℕ} (hx : j3CovSift x = true) :
    permOfArr 6156 x ∈ j3P := by
  simp only [j3CovSift, Bool.and_eq_true] at hx
  exact CFSG.RankThree.PartTwo.KFacts.K426.mem_j3P_of_sift (rep_permOfArr hx.1).1 hx.2

@[expose] noncomputable def covJ {x : Array ℕ} (hx : j3CovSift x = true) : j3P :=
  ⟨permOfArr 6156 x, mem_j3P_of_covSift hx⟩

theorem rep_covJ {x : Array ℕ} (hx : j3CovSift x = true) :
    Rep 6156 x (covJ hx : Equiv.Perm (Fin 6156)) :=
  (rep_of_covSift hx).1

theorem rep_covJ_inv {x : Array ℕ} (hx : j3CovSift x = true) :
    Rep 6156 (invCand 6156 x) ((covJ hx : Equiv.Perm (Fin 6156)))⁻¹ :=
  (rep_of_covSift hx).2

theorem covJ_comm {x y : Array ℕ} (hx : j3CovSift x = true) (hy : j3CovSift y = true)
    (h : commN 6156 x y = true) : covJ hx * covJ hy = covJ hy * covJ hx :=
  Subtype.ext (mul_comm_of_commN (rep_covJ hx) (rep_covJ hy) h)

theorem rep_covJ_conj {t q : Array ℕ} (ht : j3CovSift t = true) (hq : j3CovSift q = true) :
    Rep 6156 (j3CovConj t q) ((covJ ht * covJ hq * (covJ ht)⁻¹ : j3P) : Equiv.Perm (Fin 6156)) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact rep_compA (rep_compA (rep_covJ ht) (rep_covJ hq)) (rep_covJ_inv ht)

theorem covJ_conj_mem {t q : Array ℕ} (ht : j3CovSift t = true) (hq : j3CovSift q = true)
    (h0 : j3CovSift (j3CovArr 0) = true) (h1 : j3CovSift (j3CovArr 1) = true)
    (h : j3CovInQ t q = true) :
    covJ ht * covJ hq * (covJ ht)⁻¹ ∈
      ({covJ h0, covJ h1, covJ h0 * covJ h1} : Set j3P) := by
  simp only [j3CovInQ, Bool.or_eq_true] at h
  have hc := rep_covJ_conj ht hq
  rcases h with (h | h) | h
  · exact Or.inl (Subtype.ext (eq_of_eqA hc (rep_covJ h0) h))
  · exact Or.inr (Or.inl (Subtype.ext (eq_of_eqA hc (rep_covJ h1) h)))
  · refine Or.inr (Or.inr (Subtype.ext ?_))
    rw [Subgroup.coe_mul]
    exact eq_of_eqA hc (rep_compA (rep_covJ h0) (rep_covJ h1)) h

theorem covJ_dist (ha : j3CovSift (j3CovArr 2) = true) (hb : j3CovSift (j3CovArr 3) = true)
    (i j k l : Fin 3)
    (h : covJ ha ^ (i : ℕ) * covJ hb ^ (j : ℕ) = covJ ha ^ (k : ℕ) * covJ hb ^ (l : ℕ)) :
    i = k ∧ j = l := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := Certificates.certificate589303
  have hrep : ∀ u : ℕ, Rep 6156 (j3CovProd u)
      ((covJ ha : Equiv.Perm (Fin 6156)) ^ (u % 3) *
        (covJ hb : Equiv.Perm (Fin 6156)) ^ (u / 3)) :=
    fun u => rep_pN (rep_covJ ha) (rep_covJ hb) (u % 3, u / 3)
  have hu := List.all_eq_true.mp hd (i + 3 * j) (List.mem_range.mpr (by omega))
  have hv := List.all_eq_true.mp hu (k + 3 * l) (List.mem_range.mpr (by omega))
  have hi : ((i : ℕ) + 3 * j) % 3 = i := by omega
  have hj : ((i : ℕ) + 3 * j) / 3 = j := by omega
  have hk : ((k : ℕ) + 3 * l) % 3 = k := by omega
  have hl : ((k : ℕ) + 3 * l) / 3 = l := by omega
  have hP : (covJ ha : Equiv.Perm (Fin 6156)) ^ (((i : ℕ) + 3 * j) % 3) *
      (covJ hb : Equiv.Perm (Fin 6156)) ^ (((i : ℕ) + 3 * j) / 3) =
      (covJ ha : Equiv.Perm (Fin 6156)) ^ (((k : ℕ) + 3 * l) % 3) *
      (covJ hb : Equiv.Perm (Fin 6156)) ^ (((k : ℕ) + 3 * l) / 3) := by
    rw [hi, hj, hk, hl]
    exact congrArg Subtype.val h
  have he := (eqA_iff (hrep _) (hrep _)).2 hP
  simp only [he, Bool.not_true, Bool.or_false, beq_iff_eq] at hv
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

end J3Cover

open J3Cover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.PartTwo.Sec4.Item434SporGen in
theorem KConf.false_of_threeJ3
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K} (hK : KConf K L V MK)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.Carrier .J3)
    (hZ : Nat.card (Subgroup.center K) = 3) : False := by
  obtain ⟨s0, s1, s2, s3, s4, s5, hq1, hq2, hq12, hq1ne, ha3, hb3, hab, -, haq1, haq2, hbq1,
    hbq2, hg1, hg2a, hg2b⟩ := Certificates.certificate589303
  set q₁ := covJ s0
  set q₂ := covJ s1
  set a := covJ s2
  set b := covJ s3
  set g₁ := covJ s4
  set g₂ := covJ s5
  have hsq : ∀ {x : Array ℕ} (hx : j3CovSift x = true),
      eqA 6156 (compA 6156 x x) (idA 6156) = true → covJ hx ^ 2 = 1 := by
    intro x hx h
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, sq, Subgroup.coe_one]
    exact eq_of_eqA (rep_compA (rep_covJ hx) (rep_covJ hx)) rep_idA h
  have hcube : ∀ {x : Array ℕ} (hx : j3CovSift x = true),
      eqA 6156 (powN 6156 x 3) (idA 6156) = true → covJ hx ^ 3 = 1 := by
    intro x hx h
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (rep_powN (rep_covJ hx) 3) rep_idA h
  have hinv : ∀ {x y : Array ℕ} (hx : j3CovSift x = true) (hy : j3CovSift y = true),
      eqA 6156 (j3CovConj x y) (invCand 6156 y) = true →
        covJ hx * covJ hy * (covJ hx)⁻¹ = (covJ hy)⁻¹ := by
    intro x y hx hy h
    refine Subtype.ext ?_
    rw [Subgroup.coe_inv]
    exact eq_of_eqA (rep_covJ_conj hx hy) (rep_covJ_inv hy) h
  refine KConf.false_of_threeCover hK (e.trans CFSG.Sporadic.Schreier.j3PermEquiv) hZ
    (q₁ := q₁) (q₂ := q₂) (a := a) (b := b) (g₁ := g₁) (g₂ := g₂) (hsq s0 hq1) (hsq s1 hq2)
    (covJ_comm s0 s1 hq12) ?_ (hcube s2 ha3) (hcube s3 hb3) (covJ_comm s2 s3 hab)
    (covJ_dist s2 s3) ?_ ?_ (hinv s4 s2 hg1) ?_ (hinv s5 s3 hg2b)
  · intro h
    have h1 : (q₁ : Equiv.Perm (Fin 6156)) = 1 := by rw [h]; rfl
    rw [(eqA_iff (rep_covJ s0) rep_idA).2 h1] at hq1ne
    exact Bool.noConfusion hq1ne
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact covJ_conj_mem s2 s0 s0 s1 haq1
    · exact covJ_conj_mem s2 s1 s0 s1 haq2
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact covJ_conj_mem s3 s0 s0 s1 hbq1
    · exact covJ_conj_mem s3 s1 s0 s1 hbq2
  · rw [covJ_comm s5 s2 hg2a, mul_inv_cancel_right]

end CFSG.SectionRank.QTK.Insp443

end
