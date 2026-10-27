module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3
public import Certificates.Certificate1322005

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis

open CFSG.Open

section Concrete

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.RankThree.Asc83Table CFSG.Blueprint CFSG.SectionRank.LocalWitness
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive (seedCertCheck mem_normalizer_of_conj_mem
  conj_eq_of_mul_eq)

theorem centGen_eq_top_of_heFacts {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : ¬ 3 ^ 4 ∣ Nat.card G)
    {x y z g11 g12 g13 t2 g21 g22 g23 g24 g25 w2 w4 : G}
    (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1)
    (hz : z ^ 3 = 1)
    (hz1 : z ≠ 1)
    (hxy : x * y = y * z * x)
    (hzx : z * x = x * z)
    (hzy : z * y = y * z)
    (e11z : g11 * z = z ^ 1 * x ^ 1 * g11)
    (e11t : g11 * x = z ^ 2 * x ^ 1 * g11)
    (e12z : g12 * z = z ^ 1 * x ^ 2 * g12)
    (e12t : g12 * x = z ^ 0 * x ^ 1 * g12)
    (c1 : g13 * x = x * g13)
    (hgen1 : Subgroup.closure ({g11, g12, g13} : Set G) = ⊤)
    (ht2 : t2 = x * y ^ 1)
    (e21z : g21 * z = z ^ 1 * t2 ^ 0 * g21)
    (e21t : g21 * t2 = z ^ 2 * t2 ^ 2 * g21)
    (e22z : g22 * z = z ^ 1 * t2 ^ 0 * g22)
    (e22t : g22 * t2 = z ^ 0 * t2 ^ 1 * g22)
    (e23z : g23 * z = z ^ 2 * t2 ^ 0 * g23)
    (e23t : g23 * t2 = z ^ 2 * t2 ^ 1 * g23)
    (e24z : g24 * z = z ^ 1 * t2 ^ 0 * g24)
    (e24t : g24 * t2 = z ^ 1 * t2 ^ 2 * g24)
    (c2 : g25 * t2 = t2 * g25)
    (hgen2 : Subgroup.closure ({g21, g22, g23, g24, g25} : Set G) = ⊤)
    (l2 : w2 * x = x ^ 0 * y ^ 1 * z ^ 0 * w2)
    (l2z : w2 * z = z ^ 2 * w2)
    (l4 : w4 * t2 = x ^ 1 * y ^ 2 * z ^ 0 * w4)
    (l4z : w4 * z = z ^ 2 * w4)
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
    rintro g (rfl | rfl | rfl)
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
    · exact Or.inr ⟨x, htS, ht1, c1⟩
  have hnf2 : nf x y z ⟨1, 1, 0⟩ = t2 := by
    rw [ht2]
    show x ^ 1 * y ^ 1 * z ^ 0 = _
    simp
  have hbase2 : centGen (Subgroup.closure ({z, nf x y z ⟨1, 1, 0⟩} : Set G)) = ⊤ := by
    rw [hnf2]
    have hzS : z ∈ Subgroup.closure ({z, t2} : Set G) := Subgroup.subset_closure (by simp)
    have htS : t2 ∈ Subgroup.closure ({z, t2} : Set G) :=
      Subgroup.subset_closure (by simp)
    have ht1 : t2 ≠ 1 := fun h => Heis.ne_one_of_ne_zero _ (by decide)
      (nfHom_injective hx hy hz hzx hzy hxy hz1
        (((nfHom_apply hx hy hz hzx hzy hxy _).trans hnf2).trans
          (h.trans (map_one _).symm)))
    refine centGen_eq_top_of_forall_mem hzS hz1 ?_ hgen2
    rintro g (rfl | rfl | rfl | rfl | rfl)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e21z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e21t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e22z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e22t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e23z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e23t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · left
      refine mem_normalizer_of_conj_mem ?_
      rintro s (hs | hs) <;> rw [show s = _ from hs]
      · rw [conj_eq_of_mul_eq e24z]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
      · rw [conj_eq_of_mul_eq e24t]
        exact mul_mem (pow_mem hzS _) (pow_mem htS _)
    · exact Or.inr ⟨t2, htS, ht1, c2⟩
  refine centGen_eq_top_of_heis hx hy hz hzx hzy hxy hz1 hcard ?_ A hA hAc
  intro u hu
  have key : ∀ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) →
      (1 * b = a * 0 ∨ 0 * b = a * 1 ∨ 1 * b = a * 1 ∨ 1 * b = a * 2) := by
    decide
  rcases key u.a u.b hu with h | h | h | h
  · exact ⟨⟨1, 0, 0⟩, 1, ⟨1, 0, 0⟩, by decide, hbase1, by simp, by decide, h,
      by simp⟩
  · refine ⟨⟨1, 0, 0⟩, w2, ⟨0, 1, 0⟩, by decide, hbase1, ?_, by decide, h, ?_⟩
    · rw [hnf1, conj_eq_of_mul_eq l2]
      rfl
    · rw [conj_eq_of_mul_eq l2z]
      exact pow_mem (Subgroup.mem_zpowers z) _
  · exact ⟨⟨1, 1, 0⟩, 1, ⟨1, 1, 0⟩, by decide, hbase2, by simp, by decide, h,
      by simp⟩
  · refine ⟨⟨1, 1, 0⟩, w4, ⟨1, 2, 0⟩, by decide, hbase2, ?_, by decide, h, ?_⟩
    · rw [hnf2, conj_eq_of_mul_eq l4]
      rfl
    · rw [conj_eq_of_mul_eq l4z]
      exact pow_mem (Subgroup.mem_zpowers z) _

theorem centGen_He_three_of_check
    (hC : seedCertCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2 heCert = true)
    [Finite (NativeSporadic.Carrier .He)] [IsSimpleGroup (NativeSporadic.Carrier .He)]
    (hcard : ¬ 3 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .He))
    (A : Subgroup (NativeSporadic.Carrier .He))
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9) : centGen A = ⊤ := by
  have : Finite NativeSporadic.He := ‹Finite (NativeSporadic.Carrier .He)›
  have : IsSimpleGroup NativeSporadic.He := ‹IsSimpleGroup (NativeSporadic.Carrier .He)›
  unfold seedCertCheck at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hM, hAeq⟩, hBeq⟩ := hC
  let Sp := specP 7 50
  set x := regUnit Sp hM 79
  set y := regUnit Sp hM 170
  set z := regUnit Sp hM 175
  set g11 := regUnit Sp hM 233
  set g12 := regUnit Sp hM 282
  set g13 := regUnit Sp hM 333
  set t2 := regUnit Sp hM 334
  set g21 := regUnit Sp hM 399
  set g22 := regUnit Sp hM 445
  set g23 := regUnit Sp hM 524
  set g24 := regUnit Sp hM 598
  set g25 := regUnit Sp hM 665
  set w2 := regUnit Sp hM 744
  set w4 := regUnit Sp hM 837
  have hx : x ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 2 rfl)
  have hy : y ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 3 rfl)
  have hz : z ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 4 rfl)
  have hz1 : z ≠ 1 := by
    have := regUnit_ne Sp hM (mem_facts 16 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
    simpa [wordUnit_cons, wordUnit_nil] using this
  have hxy : x * y = y * z * x := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 17 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hzx : z * x = x * z := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 18 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hzy : z * y = y * z := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 19 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e11z : g11 * z = z ^ 1 * x ^ 1 * g11 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 20 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e11t : g11 * x = z ^ 2 * x ^ 1 * g11 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 21 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e12z : g12 * z = z ^ 1 * x ^ 2 * g12 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 22 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e12t : g12 * x = z ^ 0 * x ^ 1 * g12 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 23 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have c1 : g13 * x = x * g13 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 24 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hgen1 : Subgroup.closure ({g11, g12, g13} : Set _) = ⊤ := by
    have hrA : 0 < heCert.nregs := by decide
    have hrB : 1 < heCert.nregs := by decide
    have hvalA : valHom (certMonoid 7 50 NativeSporadic.HeSeed1 NativeSporadic.HeSeed2)
        (regUnit Sp hM 0) = NativeSporadic.decode 7 50 1 NativeSporadic.HeSeed1 := by
      rw [val_regUnit Sp hM (mem_facts 0 rfl),
        Sp.toMat_eq (reg_ok Sp hM hrA).1 (Sp.decode_wf _) hAeq, Sp.toMat_decode]
    have hvalB : valHom (certMonoid 7 50 NativeSporadic.HeSeed1 NativeSporadic.HeSeed2)
        (regUnit Sp hM 1) = NativeSporadic.decode 7 50 1 NativeSporadic.HeSeed2 := by
      rw [val_regUnit Sp hM (mem_facts 1 rfl),
        Sp.toMat_eq (reg_ok Sp hM hrB).1 (Sp.decode_wf _) hBeq, Sp.toMat_decode]
    have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top
      (certMonoid 7 50 NativeSporadic.HeSeed1 NativeSporadic.HeSeed2) rfl
      (regUnit Sp hM 0) (regUnit Sp hM 1) hvalA hvalB
    set T := Subgroup.closure ({g11, g12, g13} :
      Set (certMonoid 7 50 NativeSporadic.HeSeed1 NativeSporadic.HeSeed2)ˣ)
    have hreg : ∀ q : ℕ × ℕ, (q.1 = 233 ∨ q.1 = 282 ∨ q.1 = 333) →
        regUnit Sp hM q.1 ∈ T := by
      rintro q (h | h | h) <;> rw [h] <;>
        exact Subgroup.subset_closure (by simp [g11, g12, g13])
    have hA0 := regUnit_eq Sp hM (mem_facts 25 rfl) (hasOrd_of_bool rfl)
      (hasOrd_of_bool rfl)
    have hB0 := regUnit_eq Sp hM (mem_facts 26 rfl) (hasOrd_of_bool rfl)
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
  have ht2 : t2 = x * y ^ 1 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 27 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e21z : g21 * z = z ^ 1 * t2 ^ 0 * g21 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 28 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e21t : g21 * t2 = z ^ 2 * t2 ^ 2 * g21 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 29 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e22z : g22 * z = z ^ 1 * t2 ^ 0 * g22 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 30 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e22t : g22 * t2 = z ^ 0 * t2 ^ 1 * g22 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 31 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e23z : g23 * z = z ^ 2 * t2 ^ 0 * g23 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 32 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e23t : g23 * t2 = z ^ 2 * t2 ^ 1 * g23 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 33 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e24z : g24 * z = z ^ 1 * t2 ^ 0 * g24 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 34 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e24t : g24 * t2 = z ^ 1 * t2 ^ 2 * g24 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 35 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have c2 : g25 * t2 = t2 * g25 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 36 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hgen2 : Subgroup.closure ({g21, g22, g23, g24, g25} : Set _) = ⊤ := by
    have hrA : 0 < heCert.nregs := by decide
    have hrB : 1 < heCert.nregs := by decide
    have hvalA : valHom (certMonoid 7 50 NativeSporadic.HeSeed1 NativeSporadic.HeSeed2)
        (regUnit Sp hM 0) = NativeSporadic.decode 7 50 1 NativeSporadic.HeSeed1 := by
      rw [val_regUnit Sp hM (mem_facts 0 rfl),
        Sp.toMat_eq (reg_ok Sp hM hrA).1 (Sp.decode_wf _) hAeq, Sp.toMat_decode]
    have hvalB : valHom (certMonoid 7 50 NativeSporadic.HeSeed1 NativeSporadic.HeSeed2)
        (regUnit Sp hM 1) = NativeSporadic.decode 7 50 1 NativeSporadic.HeSeed2 := by
      rw [val_regUnit Sp hM (mem_facts 1 rfl),
        Sp.toMat_eq (reg_ok Sp hM hrB).1 (Sp.decode_wf _) hBeq, Sp.toMat_decode]
    have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top
      (certMonoid 7 50 NativeSporadic.HeSeed1 NativeSporadic.HeSeed2) rfl
      (regUnit Sp hM 0) (regUnit Sp hM 1) hvalA hvalB
    set T := Subgroup.closure ({g21, g22, g23, g24, g25} :
      Set (certMonoid 7 50 NativeSporadic.HeSeed1 NativeSporadic.HeSeed2)ˣ)
    have hreg : ∀ q : ℕ × ℕ, (q.1 = 399 ∨ q.1 = 445 ∨ q.1 = 524 ∨ q.1 = 598 ∨ q.1 = 665) →
        regUnit Sp hM q.1 ∈ T := by
      rintro q (h | h | h | h | h) <;> rw [h] <;>
        exact Subgroup.subset_closure (by simp [g21, g22, g23, g24, g25])
    have hA0 := regUnit_eq Sp hM (mem_facts 37 rfl) (hasOrd_of_bool rfl)
      (hasOrd_of_bool rfl)
    have hB0 := regUnit_eq Sp hM (mem_facts 38 rfl) (hasOrd_of_bool rfl)
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
  have l2 : w2 * x = x ^ 0 * y ^ 1 * z ^ 0 * w2 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 39 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l2z : w2 * z = z ^ 2 * w2 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 40 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l4 : w4 * t2 = x ^ 1 * y ^ 2 * z ^ 0 * w4 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 41 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l4z : w4 * z = z ^ 2 * w4 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 42 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  exact centGen_eq_top_of_heFacts hcard hx hy hz hz1 hxy hzx hzy e11z e11t e12z e12t c1 hgen1 ht2
    e21z e21t e22z e22t e23z e23t e24z e24t c2 hgen2 l2 l2z l4 l4z A hA hAc

end Concrete

section Wrapper

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.RankThree.Asc83Table CFSG.Blueprint TauCeti
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive (seedCertCheck centGen_eq_top_of_equiv
  isElemAbelian_map card_map)

set_option linter.unusedSectionVars false

theorem sporadicCentGen_He_three_of_check
    (hC : seedCertCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2 heCert =
      true) :
    SporadicCentGen 3 .He := by
  intro L _ _ ⟨e⟩ A hA hAc
  have hf := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M .He
    (by decide)
  have : Finite (NativeSporadic.Carrier .He) := hf.1
  have : IsSimpleGroup (NativeSporadic.Carrier .He) := hf.2.1
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .He
  let ψ : L ≃* NativeSporadic.Carrier .He := e.trans f.symm
  have hcard : ¬ 3 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .He) := by
    rw [CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder .He (by decide)]
    norm_num [CFSG.AGLEmbeddingD2.d2SporadicOrder]
  refine centGen_eq_top_of_equiv ψ ?_
  exact centGen_He_three_of_check hC hcard _ (isElemAbelian_map hA ψ)
    (by rw [card_map, hAc]; norm_num)

theorem sporadicCentGen_He_three : SporadicCentGen 3 .He :=
  sporadicCentGen_He_three_of_check Certificates.certificate1322005

end Wrapper

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis
