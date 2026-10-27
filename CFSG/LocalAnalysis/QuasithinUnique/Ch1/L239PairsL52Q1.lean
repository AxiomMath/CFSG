module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Frame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSL

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L52

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] [Finite K]

section Q1

variable (K)

omit [Finite K] in
theorem blockLeft_q1 : BlockLeft (flagStabilizer 5 K {1, 4}) 1 3 :=
  blockLeft_of_cut 3 (Or.inr (by simp))

omit [Finite K] in
theorem blockRight_q1 : BlockRight (flagStabilizer 5 K {1, 4}) 1 3 :=
  blockRight_of_cut (Or.inr (by simp))

@[expose] noncomputable def q1 (hK : Nat.card K = 2) :
    ↥(flagStabilizer 5 K {1, 4}) →* SpecialLinearGroup (Fin 3) K :=
  blkSLTwo hK _ 1 3 (by norm_num) (blockLeft_q1 K) (blockRight_q1 K)

variable {K}

theorem q1_coe (hK : Nat.card K = 2) (x : ↥(flagStabilizer 5 K {1, 4})) :
    ((q1 K hK x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blkAt 1 3 (by norm_num) ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := rfl

theorem q1_surjective (hK : Nat.card K = 2) : Function.Surjective (q1 K hK) := by
  intro A
  obtain ⟨x, hx⟩ := bigBlockHom_surjective (K := K) (n := 5) hK (I := {1, 4}) (a := 1) (m := 3)
    (by norm_num) le_rfl (Or.inr (by simp)) (Or.inr (by simp))
    (by
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      omega) A
  refine ⟨⟨x.1, CFSG.Quasithin.perfectCore_le _ x.2⟩, Subtype.ext ?_⟩
  have h := congrArg (fun B : SpecialLinearGroup (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K)) hx
  rw [bigBlockHom_coe] at h
  exact h

theorem q1_unitriangular (hK : Nat.card K = 2) (x : ↥(flagStabilizer 5 K {1, 4}))
    (hx : q1 K hK x = 1) : (x : SpecialLinearGroup (Fin 5) K) ∈ unitriangular 5 K := by
  refine mem_unitriangular_of_blocks x.2 ?_
  intro a m h ha hb hno
  have h1 := hno 1 (by simp)
  have h4 := hno 4 (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  have hcases : m = 0 ∨ (a = 0 ∧ m = 1) ∨ (a = 1 ∧ m = 3) ∨ (a = 4 ∧ m = 1) := by omega
  rcases hcases with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkAt_zero a h _
  · exact blkAt_one_eq_one hK _ 0 h (blockLeft_zero _ 1) (blockRight_of_cut (Or.inr (by simp))) x
  · have h2 := congrArg (fun B : SpecialLinearGroup (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K)) hx
    exact h2
  · exact blkAt_one_eq_one hK _ 4 h (blockLeft_of_cut 1 (Or.inr (by simp)))
      (blockRight_top _ (by norm_num)) x

theorem q1_ker_isPGroup [CharP K 2] (hK : Nat.card K = 2) : IsPGroup 2 (q1 K hK).ker :=
  isPGroup_ker_of_unitriangular (by norm_num) (q1 K hK) (q1_unitriangular hK)

omit [Finite K] in
theorem tv0_mem_q1 {k : Fin 5} (hk : (0 : Fin 5) < k) :
    SpecialLinearGroup.transvection hk.ne (1 : K) ∈ flagStabilizer 5 K {1, 4} :=
  transvection_mem_flagStabilizer hk 1 _

theorem tv0_mem_ker_q1 (hK : Nat.card K = 2) {k : Fin 5} (hk : (0 : Fin 5) < k) :
    (⟨SpecialLinearGroup.transvection hk.ne (1 : K), tv0_mem_q1 hk⟩ :
      ↥(flagStabilizer 5 K {1, 4})) ∈ (q1 K hK).ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  rw [q1_coe]
  exact blkAt_transvection hk.ne 1 1 3 (by norm_num) (by simp)

theorem q1_centralizer (hK : Nat.card K = 2) (x : ↥(flagStabilizer 5 K {1, 4}))
    (hx : ∀ n : ↥(flagStabilizer 5 K {1, 4}), n ∈ (q1 K hK).ker → x * n = n * x) :
    x ∈ (q1 K hK).ker := by
  have hx00 : ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 0 = 1 := by
    have h := congrFun (congrFun (blkAt_one_eq_one hK _ 0 (by norm_num) (blockLeft_zero _ 1)
      (blockRight_of_cut (Or.inr (by simp))) x) 0) 0
    exact h
  have hrow : ∀ k : Fin 5, (0 : Fin 5) < k → ∀ b : Fin 5,
      ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) k b = if k = b then 1 else 0 := by
    intro k hk b
    have h := congrArg (fun y : ↥(flagStabilizer 5 K {1, 4}) =>
      (y : SpecialLinearGroup (Fin 5) K)) (hx _ (tv0_mem_ker_q1 hK hk))
    have h' := transvection_commute_entry hk.ne (1 : K) h 0 b
    simp only [hx00, ite_true, one_mul, mul_ite, mul_one, mul_zero] at h'
    exact h'.symm
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  ext p q
  rw [q1_coe, blkAt_apply]
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  have hp : (0 : Fin 5) < ⟨1 + (p : ℕ), by have := p.isLt; omega⟩ := by
    show 0 < 1 + (p : ℕ)
    omega
  rw [hrow _ hp]
  simp [Fin.ext_iff]

end Q1

section Good

open scoped Classical

theorem goodSub_q1 [CharP K 2] (hK : Nat.card K = 2) : GoodSub (flagStabilizer 5 K {1, 4}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple := sl_isSimple_of_card_two hK (m := 3) le_rfl
  have hT2 : ¬ IsPGroup 2 (SpecialLinearGroup (Fin 3) K) := fun hp => by
    have : Group.IsNilpotent (SpecialLinearGroup (Fin 3) K) := hp.isNilpotent
    obtain ⟨a, b, hab⟩ := sl_nonabelian_of_card_two hK (m := 3) le_rfl
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)
  exact GoodSub.of_quotient (q1 K hK) (q1_surjective hK) hsimple hT2 (q1_ker_isPGroup hK)
    (q1_centralizer hK) (by rw [card_sl_three hK]; exact not_chi0Order_168)

end Good

end CFSG.QuasithinUnique.Vol2Native.L239.L52
