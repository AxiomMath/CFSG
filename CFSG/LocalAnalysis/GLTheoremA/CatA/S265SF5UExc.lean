module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UKill
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5URoot
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UTorus
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.Blueprint.Chevalley

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

private theorem rk2Ord_five_cases (n : ℕ) :
    rk2Ord 5 n = 1 ∨ rk2Ord 5 n = 2 ∨ rk2Ord 5 n = 4 := by
  have h4 : rk2Ord 5 n ∣ 4 := by
    unfold rk2Ord
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← pow_mul, mul_comm, pow_mul, show (2 : ZMod 5) ^ 4 = 1 from by decide, one_pow]
  have hpos := rk2Ord_pos Nat.prime_five (by norm_num) n
  have hle := Nat.le_of_dvd (by norm_num) h4
  obtain ⟨e, he⟩ : ∃ e, rk2Ord 5 n = e := ⟨_, rfl⟩
  rw [he] at h4 hpos hle ⊢
  interval_cases e <;> omega


theorem false_of_exc_five (h : QSNL 5 S B T x D K) (hF : catalogIs (PSimple 5 K) (tyFUni 5))
    (hZ : Subgroup.center ↥K = ⊥) {lab : GLALabel} (hlab : LabelOf S lab)
    (hlab2 : GLAInLambda2 lab) (h3 : 3 ≤ rk2Mult lab (rk2Ord 5 lab.n))
    (ht : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hE8 : lab.tag = .E8 → rk2Ord 5 lab.n ≠ 4) : False := by
  have hH := exists_nonabelian_exponent_five_le h hF
  rcases rk2Ord_five_cases lab.n with he | he | he
  · have h5 : 5 ∣ 2 ^ lab.n - 1 := rk2Ord_eq_one_iff.1 he
    rcases ht with ht | ht | ht | ht | ht
    · obtain ⟨F, _, _, _, hFc, ⟨θ⟩⟩ := exists_adjoint_of_labelOf hlab (Or.inl ⟨ht, rfl⟩)
      exact false_of_sylowTorus h hZ hH θ
        (sylowTorus_F4_five_of_dvd_sub_one F (by rw [hFc]; exact h5))
    · obtain ⟨F, _, _, _, hFc, ⟨θ⟩⟩ :=
        exists_adjoint_of_labelOf hlab (Or.inr (Or.inl ⟨ht, rfl⟩))
      exact false_of_E6_dvd_sub_one h hF (by rw [hFc]; exact h5) θ
    · exact false_of_labelAll_torusLift_five h hF hlab le_rfl
        (CFSG.StandardType.largeEvenLabelAll_torusLift_twE6Dvd Nat.prime_five (by norm_num)
          hlab2 ⟨ht, h5⟩)
    · obtain ⟨F, _, _, _, hFc, ⟨θ⟩⟩ :=
        exists_adjoint_of_labelOf hlab (Or.inr (Or.inr (Or.inl ⟨ht, rfl⟩)))
      exact false_of_E7_dvd_sub_one h hF (by rw [hFc]; exact h5) θ
    · obtain ⟨F, _, _, _, hFc, ⟨θ⟩⟩ :=
        exists_adjoint_of_labelOf hlab (Or.inr (Or.inr (Or.inr ⟨ht, rfl⟩)))
      exact false_of_E8_dvd_sub_one h hF (by rw [hFc]; exact h5) θ
  · have h5 : 5 ∣ 2 ^ lab.n + 1 := (rk2Ord_eq_two_iff Nat.prime_five (by norm_num)).1 he
    rcases ht with ht | ht | ht | ht | ht
    · obtain ⟨F, _, _, _, hFc, ⟨θ⟩⟩ := exists_adjoint_of_labelOf hlab (Or.inl ⟨ht, rfl⟩)
      exact false_of_sylowTorus h hZ hH θ
        (sylowTorus_F4_five_of_dvd_add_one F (by rw [hFc]; exact h5))
    · obtain ⟨F, _, _, _, hFc, ⟨θ⟩⟩ :=
        exists_adjoint_of_labelOf hlab (Or.inr (Or.inl ⟨ht, rfl⟩))
      exact false_of_sylowTorus h hZ hH θ
        (sylowTorus_E6_five_of_dvd_add_one F (by rw [hFc]; exact h5))
    · exact false_of_labelAll_torusLift_five h hF hlab
        (by rw [CFSG.StandardType.TwE6Delta.liftRank_of_ne (by norm_num)]; norm_num)
        (CFSG.StandardType.largeEvenLabelAll_torusLift_twE6Add_holds Nat.prime_five hlab2
          ⟨ht, h5⟩)
    · obtain ⟨F, _, _, _, hFc, ⟨θ⟩⟩ :=
        exists_adjoint_of_labelOf hlab (Or.inr (Or.inr (Or.inl ⟨ht, rfl⟩)))
      exact false_of_E7_dvd_add_one h hF (by rw [hFc]; exact h5) θ
    · obtain ⟨F, _, _, _, hFc, ⟨θ⟩⟩ :=
        exists_adjoint_of_labelOf hlab (Or.inr (Or.inr (Or.inr ⟨ht, rfl⟩)))
      exact false_of_E8_dvd_add_one h hF (by rw [hFc]; exact h5) θ
  · rw [he] at h3
    rcases ht with ht | ht | ht | ht | ht
    · simp only [rk2Mult, ht] at h3
      exact absurd h3 (by decide)
    · simp only [rk2Mult, ht] at h3
      exact absurd h3 (by decide)
    · simp only [rk2Mult, ht] at h3
      exact absurd h3 (by decide)
    · simp only [rk2Mult, ht] at h3
      exact absurd h3 (by decide)
    · exact hE8 ht he

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
