module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3
public import Certificates.Certificate1322007

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis

open CFSG.Open

section Concrete

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.RankThree.Asc83Table CFSG.Blueprint CFSG.SectionRank.LocalWitness
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive (seedCertCheck mem_normalizer_of_conj_mem
  conj_eq_of_mul_eq)

theorem centGen_eq_top_of_j4Facts {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : ¬ 3 ^ 4 ∣ Nat.card G)
    {x y z g11 g12 g13 g14 g15 g16 g17 g18 g19 g110 g111 g112 g113 g114 g115 g116 w2 w3 w4 : G}
    (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1)
    (hz : z ^ 3 = 1)
    (hz1 : z ≠ 1)
    (hxy : x * y = y * z * x)
    (hzx : z * x = x * z)
    (hzy : z * y = y * z)
    (e11z : g11 * z = z ^ 1 * x ^ 1 * g11)
    (e11t : g11 * x = z ^ 1 * x ^ 0 * g11)
    (e12z : g12 * z = z ^ 2 * x ^ 1 * g12)
    (e12t : g12 * x = z ^ 2 * x ^ 0 * g12)
    (e13z : g13 * z = z ^ 1 * x ^ 0 * g13)
    (e13t : g13 * x = z ^ 0 * x ^ 1 * g13)
    (e14z : g14 * z = z ^ 1 * x ^ 0 * g14)
    (e14t : g14 * x = z ^ 0 * x ^ 1 * g14)
    (e15z : g15 * z = z ^ 1 * x ^ 0 * g15)
    (e15t : g15 * x = z ^ 0 * x ^ 1 * g15)
    (e16z : g16 * z = z ^ 1 * x ^ 0 * g16)
    (e16t : g16 * x = z ^ 0 * x ^ 1 * g16)
    (e17z : g17 * z = z ^ 1 * x ^ 0 * g17)
    (e17t : g17 * x = z ^ 0 * x ^ 1 * g17)
    (e18z : g18 * z = z ^ 1 * x ^ 0 * g18)
    (e18t : g18 * x = z ^ 2 * x ^ 1 * g18)
    (e19z : g19 * z = z ^ 1 * x ^ 1 * g19)
    (e19t : g19 * x = z ^ 1 * x ^ 0 * g19)
    (e110z : g110 * z = z ^ 2 * x ^ 1 * g110)
    (e110t : g110 * x = z ^ 2 * x ^ 0 * g110)
    (e111z : g111 * z = z ^ 1 * x ^ 0 * g111)
    (e111t : g111 * x = z ^ 0 * x ^ 1 * g111)
    (e112z : g112 * z = z ^ 1 * x ^ 0 * g112)
    (e112t : g112 * x = z ^ 0 * x ^ 1 * g112)
    (e113z : g113 * z = z ^ 1 * x ^ 0 * g113)
    (e113t : g113 * x = z ^ 0 * x ^ 1 * g113)
    (e114z : g114 * z = z ^ 1 * x ^ 0 * g114)
    (e114t : g114 * x = z ^ 2 * x ^ 1 * g114)
    (e115z : g115 * z = z ^ 2 * x ^ 0 * g115)
    (e115t : g115 * x = z ^ 0 * x ^ 2 * g115)
    (c1 : g116 * z = z * g116)
    (hgen1 : Subgroup.closure ({g11, g12, g13, g14, g15, g16, g17, g18, g19, g110, g111, g112,
      g113, g114, g115, g116} : Set G) = ⊤)
    (l2 : w2 * x = x ^ 0 * y ^ 1 * z ^ 2 * w2)
    (l2z : w2 * z = z ^ 2 * w2)
    (l3 : w3 * x = x ^ 1 * y ^ 1 * z ^ 0 * w3)
    (l3z : w3 * z = z ^ 2 * w3)
    (l4 : w4 * x = x ^ 2 * y ^ 1 * z ^ 0 * w4)
    (l4z : w4 * z = z ^ 1 * w4)
    (A : Subgroup G) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9) : centGen A = ⊤ := by
  have hnf1 : nf x y z ⟨1, 0, 0⟩ = x := by
    show x ^ 1 * y ^ 0 * z ^ 0 = _
    simp
  have hbase1 : centGen (Subgroup.closure ({z, nf x y z ⟨1, 0, 0⟩} : Set G)) = ⊤ := by
    rw [hnf1]
    have hzS : z ∈ Subgroup.closure ({z, x} : Set G) := Subgroup.subset_closure (by simp)
    have htS : x ∈ Subgroup.closure ({z, x} : Set G) :=
      Subgroup.subset_closure (by simp)
    have ht1 : x ≠ 1 := fun h => Heis.ne_one_of_ne_zero _ (by decide)
      (nfHom_injective hx hy hz hzx hzy hxy hz1
        (((nfHom_apply hx hy hz hzx hzy hxy _).trans hnf1).trans
          (h.trans (map_one _).symm)))
    refine centGen_eq_top_of_forall_mem hzS hz1 ?_ hgen1
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e11z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e11t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e12z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e12t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e13z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e13t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e14z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e14t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e15z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e15t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e16z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e16t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e17z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e17t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e18z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e18t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e19z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e19t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e110z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e110t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e111z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e111t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e112z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e112t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e113z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e113t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e114z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e114t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e115z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e115t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · exact Or.inr ⟨z, hzS, hz1, c1⟩
  refine centGen_eq_top_of_heis hx hy hz hzx hzy hxy hz1 hcard ?_ A hA hAc
  intro u hu
  have key : ∀ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) →
      (1 * b = a * 0 ∨ 0 * b = a * 1 ∨ 1 * b = a * 1 ∨ 2 * b = a * 1) := by
    decide
  rcases key u.a u.b hu with h | h | h | h
  · exact ⟨⟨1, 0, 0⟩, 1, ⟨1, 0, 0⟩, by decide, hbase1, by simp, by decide, h,
      by simp⟩
  · refine ⟨⟨1, 0, 0⟩, w2, ⟨0, 1, 2⟩, by decide, hbase1, ?_, by decide, h, ?_⟩
    · rw [hnf1, conj_eq_of_mul_eq l2]
      rfl
    · rw [conj_eq_of_mul_eq l2z]
      exact pow_mem (Subgroup.mem_zpowers z) _
  · refine ⟨⟨1, 0, 0⟩, w3, ⟨1, 1, 0⟩, by decide, hbase1, ?_, by decide, h, ?_⟩
    · rw [hnf1, conj_eq_of_mul_eq l3]
      rfl
    · rw [conj_eq_of_mul_eq l3z]
      exact pow_mem (Subgroup.mem_zpowers z) _
  · refine ⟨⟨1, 0, 0⟩, w4, ⟨2, 1, 0⟩, by decide, hbase1, ?_, by decide, h, ?_⟩
    · rw [hnf1, conj_eq_of_mul_eq l4]
      rfl
    · rw [conj_eq_of_mul_eq l4z]
      exact pow_mem (Subgroup.mem_zpowers z) _

theorem centGen_J4_three_of_check
    (hC : seedCertCheck (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4Cert = true)
    [Finite (NativeSporadic.Carrier .J4)] [IsSimpleGroup (NativeSporadic.Carrier .J4)]
    (hcard : ¬ 3 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .J4))
    (A : Subgroup (NativeSporadic.Carrier .J4))
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9) : centGen A = ⊤ := by
  have : Finite NativeSporadic.J4 := ‹Finite (NativeSporadic.Carrier .J4)›
  have : IsSimpleGroup NativeSporadic.J4 := ‹IsSimpleGroup (NativeSporadic.Carrier .J4)›
  unfold seedCertCheck at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hM, hAeq⟩, hBeq⟩ := hC
  let Sp := spec2 112
  set x := regUnit Sp hM 146
  set y := regUnit Sp hM 285
  set z := regUnit Sp hM 290
  set g11 := regUnit Sp hM 438
  set g12 := regUnit Sp hM 643
  set g13 := regUnit Sp hM 648
  set g14 := regUnit Sp hM 651
  set g15 := regUnit Sp hM 652
  set g16 := regUnit Sp hM 787
  set g17 := regUnit Sp hM 798
  set g18 := regUnit Sp hM 800
  set g19 := regUnit Sp hM 802
  set g110 := regUnit Sp hM 804
  set g111 := regUnit Sp hM 806
  set g112 := regUnit Sp hM 808
  set g113 := regUnit Sp hM 810
  set g114 := regUnit Sp hM 812
  set g115 := regUnit Sp hM 814
  set g116 := regUnit Sp hM 767
  set w2 := regUnit Sp hM 793
  set w3 := regUnit Sp hM 815
  set w4 := regUnit Sp hM 767
  have hx : x ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 2 rfl)
  have hy : y ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 3 rfl)
  have hz : z ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 4 rfl)
  have hz1 : z ≠ 1 := by
    have := regUnit_ne Sp hM (mem_facts 23 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
    simpa [wordUnit_cons, wordUnit_nil] using this
  have hxy : x * y = y * z * x := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 24 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hzx : z * x = x * z := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 25 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hzy : z * y = y * z := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 26 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e11z : g11 * z = z ^ 1 * x ^ 1 * g11 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 27 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e11t : g11 * x = z ^ 1 * x ^ 0 * g11 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 28 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e12z : g12 * z = z ^ 2 * x ^ 1 * g12 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 29 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e12t : g12 * x = z ^ 2 * x ^ 0 * g12 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 30 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e13z : g13 * z = z ^ 1 * x ^ 0 * g13 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 31 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e13t : g13 * x = z ^ 0 * x ^ 1 * g13 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 32 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e14z : g14 * z = z ^ 1 * x ^ 0 * g14 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 33 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e14t : g14 * x = z ^ 0 * x ^ 1 * g14 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 34 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e15z : g15 * z = z ^ 1 * x ^ 0 * g15 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 35 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e15t : g15 * x = z ^ 0 * x ^ 1 * g15 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 36 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e16z : g16 * z = z ^ 1 * x ^ 0 * g16 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 37 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e16t : g16 * x = z ^ 0 * x ^ 1 * g16 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 38 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e17z : g17 * z = z ^ 1 * x ^ 0 * g17 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 39 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e17t : g17 * x = z ^ 0 * x ^ 1 * g17 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 40 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e18z : g18 * z = z ^ 1 * x ^ 0 * g18 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 41 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e18t : g18 * x = z ^ 2 * x ^ 1 * g18 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 42 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e19z : g19 * z = z ^ 1 * x ^ 1 * g19 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 43 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e19t : g19 * x = z ^ 1 * x ^ 0 * g19 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 44 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e110z : g110 * z = z ^ 2 * x ^ 1 * g110 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 45 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e110t : g110 * x = z ^ 2 * x ^ 0 * g110 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 46 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e111z : g111 * z = z ^ 1 * x ^ 0 * g111 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 47 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e111t : g111 * x = z ^ 0 * x ^ 1 * g111 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 48 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e112z : g112 * z = z ^ 1 * x ^ 0 * g112 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 49 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e112t : g112 * x = z ^ 0 * x ^ 1 * g112 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 50 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e113z : g113 * z = z ^ 1 * x ^ 0 * g113 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 51 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e113t : g113 * x = z ^ 0 * x ^ 1 * g113 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 52 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e114z : g114 * z = z ^ 1 * x ^ 0 * g114 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 53 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e114t : g114 * x = z ^ 2 * x ^ 1 * g114 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 54 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e115z : g115 * z = z ^ 2 * x ^ 0 * g115 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 55 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e115t : g115 * x = z ^ 0 * x ^ 2 * g115 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 56 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have c1 : g116 * z = z * g116 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 57 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hgen1 : Subgroup.closure ({g11, g12, g13, g14, g15, g16, g17, g18, g19, g110, g111, g112,
      g113, g114, g115, g116} : Set _) = ⊤ := by
    have hrA : 0 < j4Cert.nregs := by decide
    have hrB : 1 < j4Cert.nregs := by decide
    have hvalA : valHom (certMonoid 2 112 NativeSporadic.J4Seed1 NativeSporadic.J4Seed2)
        (regUnit Sp hM 0) = NativeSporadic.decode 2 112 1 NativeSporadic.J4Seed1 := by
      rw [val_regUnit Sp hM (mem_facts 0 rfl),
        Sp.toMat_eq (reg_ok Sp hM hrA).1 (Sp.decode_wf _) hAeq, Sp.toMat_decode]
    have hvalB : valHom (certMonoid 2 112 NativeSporadic.J4Seed1 NativeSporadic.J4Seed2)
        (regUnit Sp hM 1) = NativeSporadic.decode 2 112 1 NativeSporadic.J4Seed2 := by
      rw [val_regUnit Sp hM (mem_facts 1 rfl),
        Sp.toMat_eq (reg_ok Sp hM hrB).1 (Sp.decode_wf _) hBeq, Sp.toMat_decode]
    have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top
      (certMonoid 2 112 NativeSporadic.J4Seed1 NativeSporadic.J4Seed2) rfl
      (regUnit Sp hM 0) (regUnit Sp hM 1) hvalA hvalB
    set T := Subgroup.closure ({g11, g12, g13, g14, g15, g16, g17, g18, g19, g110, g111, g112,
      g113, g114, g115, g116} :
      Set (certMonoid 2 112 NativeSporadic.J4Seed1 NativeSporadic.J4Seed2)ˣ)
    have hreg : ∀ q : ℕ × ℕ, (q.1 = 438 ∨ q.1 = 643 ∨ q.1 = 648 ∨ q.1 = 651 ∨ q.1 = 652 ∨
        q.1 = 767 ∨ q.1 = 787 ∨ q.1 = 798 ∨ q.1 = 800 ∨ q.1 = 802 ∨ q.1 = 804 ∨ q.1 = 806 ∨
        q.1 = 808 ∨ q.1 = 810 ∨ q.1 = 812 ∨ q.1 = 814) →
        regUnit Sp hM q.1 ∈ T := by
      rintro q (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> rw [h] <;>
        exact Subgroup.subset_closure (by simp [g11, g12, g13, g14, g15, g16, g17, g18, g19, g110,
          g111, g112, g113, g114, g115, g116])
    have hA0 := regUnit_eq Sp hM (mem_facts 58 rfl) (hasOrd_of_bool rfl)
      (hasOrd_of_bool rfl)
    have hB0 := regUnit_eq Sp hM (mem_facts 59 rfl) (hasOrd_of_bool rfl)
      (hasOrd_of_bool rfl)
    rw [wordUnit_cons, wordUnit_nil, pow_one, mul_one] at hA0 hB0
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [hA0]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hM T _
        fun q hq => hreg q (by revert q hq; decide)
    · rw [hB0]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hM T _
        fun q hq => hreg q (by revert q hq; decide)
  have l2 : w2 * x = x ^ 0 * y ^ 1 * z ^ 2 * w2 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 60 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l2z : w2 * z = z ^ 2 * w2 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 61 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l3 : w3 * x = x ^ 1 * y ^ 1 * z ^ 0 * w3 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 62 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l3z : w3 * z = z ^ 2 * w3 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 63 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l4 : w4 * x = x ^ 2 * y ^ 1 * z ^ 0 * w4 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 64 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l4z : w4 * z = z ^ 1 * w4 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 65 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  exact centGen_eq_top_of_j4Facts hcard hx hy hz hz1 hxy hzx hzy e11z e11t e12z e12t e13z e13t
    e14z e14t e15z e15t e16z e16t e17z e17t e18z e18t e19z e19t e110z e110t e111z e111t e112z
    e112t e113z e113t e114z e114t e115z e115t c1 hgen1 l2 l2z l3 l3z l4 l4z A hA hAc

end Concrete

section Wrapper

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.RankThree.Asc83Table CFSG.Blueprint TauCeti
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive (seedCertCheck centGen_eq_top_of_equiv
  isElemAbelian_map card_map)

set_option linter.unusedSectionVars false

theorem sporadicCentGen_J4_three_of_check
    (hC : seedCertCheck (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4Cert =
      true) :
    SporadicCentGen 3 .J4 := by
  intro L _ _ ⟨e⟩ A hA hAc
  have hf := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M .J4
    (by decide)
  have : Finite (NativeSporadic.Carrier .J4) := hf.1
  have : IsSimpleGroup (NativeSporadic.Carrier .J4) := hf.2.1
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .J4
  let ψ : L ≃* NativeSporadic.Carrier .J4 := e.trans f.symm
  have hcard : ¬ 3 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .J4) := by
    rw [CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder .J4 (by decide)]
    norm_num [CFSG.AGLEmbeddingD2.d2SporadicOrder]
  refine centGen_eq_top_of_equiv ψ ?_
  exact centGen_J4_three_of_check hC hcard _ (isElemAbelian_map hA ψ)
    (by rw [card_map, hAc]; norm_num)

theorem sporadicCentGen_J4_three : SporadicCentGen 3 .J4 :=
  sporadicCentGen_J4_three_of_check Certificates.certificate1322007

end Wrapper

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis
