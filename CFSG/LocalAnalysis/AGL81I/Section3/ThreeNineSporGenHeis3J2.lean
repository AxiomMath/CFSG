module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3
public import Certificates.Certificate1322004

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis

open CFSG.Open

section Concrete

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.RankThree.Asc83Table CFSG.Blueprint CFSG.SectionRank.LocalWitness
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive (seedCertCheck mem_normalizer_of_conj_mem
  conj_eq_of_mul_eq)

theorem centGen_eq_top_of_j2Facts {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : ¬ 3 ^ 4 ∣ Nat.card G)
    {x y z g11 g12 g13 g14 w2 w3 w4 : G}
    (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1)
    (hz : z ^ 3 = 1)
    (hz1 : z ≠ 1)
    (hxy : x * y = y * z * x)
    (hzx : z * x = x * z)
    (hzy : z * y = y * z)
    (e11z : g11 * z = z ^ 1 * x ^ 0 * g11)
    (e11t : g11 * x = z ^ 2 * x ^ 2 * g11)
    (e12z : g12 * z = z ^ 1 * x ^ 0 * g12)
    (e12t : g12 * x = z ^ 1 * x ^ 1 * g12)
    (e13z : g13 * z = z ^ 1 * x ^ 0 * g13)
    (e13t : g13 * x = z ^ 1 * x ^ 1 * g13)
    (c1 : g14 * x = x * g14)
    (hgen1 : Subgroup.closure ({g11, g12, g13, g14} : Set G) = ⊤)
    (l2 : w2 * x = x ^ 0 * y ^ 2 * z ^ 2 * w2)
    (l2z : w2 * z = z ^ 2 * w2)
    (l3 : w3 * x = x ^ 2 * y ^ 2 * z ^ 2 * w3)
    (l3z : w3 * z = z ^ 1 * w3)
    (l4 : w4 * x = x ^ 2 * y ^ 1 * z ^ 0 * w4)
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
    rintro g (rfl | rfl | rfl | rfl)
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
    · exact Or.inr ⟨x, htS, ht1, c1⟩
  refine centGen_eq_top_of_heis hx hy hz hzx hzy hxy hz1 hcard ?_ A hA hAc
  intro u hu
  have key : ∀ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) →
      (1 * b = a * 0 ∨ 0 * b = a * 2 ∨ 2 * b = a * 2 ∨ 2 * b = a * 1) := by
    decide
  rcases key u.a u.b hu with h | h | h | h
  · exact ⟨⟨1, 0, 0⟩, 1, ⟨1, 0, 0⟩, by decide, hbase1, by simp, by decide, h,
      by simp⟩
  · refine ⟨⟨1, 0, 0⟩, w2, ⟨0, 2, 2⟩, by decide, hbase1, ?_, by decide, h, ?_⟩
    · rw [hnf1, conj_eq_of_mul_eq l2]
      rfl
    · rw [conj_eq_of_mul_eq l2z]
      exact pow_mem (Subgroup.mem_zpowers z) _
  · refine ⟨⟨1, 0, 0⟩, w3, ⟨2, 2, 2⟩, by decide, hbase1, ?_, by decide, h, ?_⟩
    · rw [hnf1, conj_eq_of_mul_eq l3]
      rfl
    · rw [conj_eq_of_mul_eq l3z]
      exact pow_mem (Subgroup.mem_zpowers z) _
  · refine ⟨⟨1, 0, 0⟩, w4, ⟨2, 1, 0⟩, by decide, hbase1, ?_, by decide, h, ?_⟩
    · rw [hnf1, conj_eq_of_mul_eq l4]
      rfl
    · rw [conj_eq_of_mul_eq l4z]
      exact pow_mem (Subgroup.mem_zpowers z) _

theorem centGen_J2_three_of_check
    (hC : seedCertCheck (opsP 5 14) NativeSporadic.J2Seed1 NativeSporadic.J2Seed2 j2Cert = true)
    [Finite (NativeSporadic.Carrier .J2)] [IsSimpleGroup (NativeSporadic.Carrier .J2)]
    (hcard : ¬ 3 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .J2))
    (A : Subgroup (NativeSporadic.Carrier .J2))
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9) : centGen A = ⊤ := by
  have : Finite NativeSporadic.J2 := ‹Finite (NativeSporadic.Carrier .J2)›
  have : IsSimpleGroup NativeSporadic.J2 := ‹IsSimpleGroup (NativeSporadic.Carrier .J2)›
  unfold seedCertCheck at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hM, hAeq⟩, hBeq⟩ := hC
  let Sp := specP 5 14
  set x := regUnit Sp hM 61
  set y := regUnit Sp hM 136
  set z := regUnit Sp hM 141
  set g11 := regUnit Sp hM 202
  set g12 := regUnit Sp hM 269
  set g13 := regUnit Sp hM 345
  set g14 := regUnit Sp hM 406
  set w2 := regUnit Sp hM 485
  set w3 := regUnit Sp hM 529
  set w4 := regUnit Sp hM 600
  have hx : x ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 2 rfl)
  have hy : y ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 3 rfl)
  have hz : z ^ 3 = 1 := regUnit_pow Sp hM (mem_facts 4 rfl)
  have hz1 : z ≠ 1 := by
    have := regUnit_ne Sp hM (mem_facts 12 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
    simpa [wordUnit_cons, wordUnit_nil] using this
  have hxy : x * y = y * z * x := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 13 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hzx : z * x = x * z := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 14 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hzy : z * y = y * z := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 15 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e11z : g11 * z = z ^ 1 * x ^ 0 * g11 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 16 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e11t : g11 * x = z ^ 2 * x ^ 2 * g11 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 17 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e12z : g12 * z = z ^ 1 * x ^ 0 * g12 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 18 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e12t : g12 * x = z ^ 1 * x ^ 1 * g12 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 19 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e13z : g13 * z = z ^ 1 * x ^ 0 * g13 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 20 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e13t : g13 * x = z ^ 1 * x ^ 1 * g13 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 21 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have c1 : g14 * x = x * g14 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 22 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hgen1 : Subgroup.closure ({g11, g12, g13, g14} : Set _) = ⊤ := by
    have hrA : 0 < j2Cert.nregs := by decide
    have hrB : 1 < j2Cert.nregs := by decide
    have hvalA : valHom (certMonoid 5 14 NativeSporadic.J2Seed1 NativeSporadic.J2Seed2)
        (regUnit Sp hM 0) = NativeSporadic.decode 5 14 1 NativeSporadic.J2Seed1 := by
      rw [val_regUnit Sp hM (mem_facts 0 rfl),
        Sp.toMat_eq (reg_ok Sp hM hrA).1 (Sp.decode_wf _) hAeq, Sp.toMat_decode]
    have hvalB : valHom (certMonoid 5 14 NativeSporadic.J2Seed1 NativeSporadic.J2Seed2)
        (regUnit Sp hM 1) = NativeSporadic.decode 5 14 1 NativeSporadic.J2Seed2 := by
      rw [val_regUnit Sp hM (mem_facts 1 rfl),
        Sp.toMat_eq (reg_ok Sp hM hrB).1 (Sp.decode_wf _) hBeq, Sp.toMat_decode]
    have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top
      (certMonoid 5 14 NativeSporadic.J2Seed1 NativeSporadic.J2Seed2) rfl
      (regUnit Sp hM 0) (regUnit Sp hM 1) hvalA hvalB
    set T := Subgroup.closure ({g11, g12, g13, g14} :
      Set (certMonoid 5 14 NativeSporadic.J2Seed1 NativeSporadic.J2Seed2)ˣ)
    have hreg : ∀ q : ℕ × ℕ, (q.1 = 202 ∨ q.1 = 269 ∨ q.1 = 345 ∨ q.1 = 406) →
        regUnit Sp hM q.1 ∈ T := by
      rintro q (h | h | h | h) <;> rw [h] <;>
        exact Subgroup.subset_closure (by simp [g11, g12, g13, g14])
    have hA0 := regUnit_eq Sp hM (mem_facts 23 rfl) (hasOrd_of_bool rfl)
      (hasOrd_of_bool rfl)
    have hB0 := regUnit_eq Sp hM (mem_facts 24 rfl) (hasOrd_of_bool rfl)
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
  have l2 : w2 * x = x ^ 0 * y ^ 2 * z ^ 2 * w2 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 25 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l2z : w2 * z = z ^ 2 * w2 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 26 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l3 : w3 * x = x ^ 2 * y ^ 2 * z ^ 2 * w3 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 27 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l3z : w3 * z = z ^ 1 * w3 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 28 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l4 : w4 * x = x ^ 2 * y ^ 1 * z ^ 0 * w4 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 29 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have l4z : w4 * z = z ^ 2 * w4 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, pow_zero, mul_one, one_mul, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 30 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  exact centGen_eq_top_of_j2Facts hcard hx hy hz hz1 hxy hzx hzy e11z e11t e12z e12t e13z e13t c1
    hgen1 l2 l2z l3 l3z l4 l4z A hA hAc

end Concrete

section Wrapper

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.RankThree.Asc83Table CFSG.Blueprint TauCeti
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive (seedCertCheck centGen_eq_top_of_equiv
  isElemAbelian_map card_map)

set_option linter.unusedSectionVars false

theorem sporadicCentGen_J2_three_of_check
    (hC : seedCertCheck (opsP 5 14) NativeSporadic.J2Seed1 NativeSporadic.J2Seed2 j2Cert =
      true) :
    SporadicCentGen 3 .J2 := by
  intro L _ _ ⟨e⟩ A hA hAc
  have hf := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M .J2
    (by decide)
  have : Finite (NativeSporadic.Carrier .J2) := hf.1
  have : IsSimpleGroup (NativeSporadic.Carrier .J2) := hf.2.1
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .J2
  let ψ : L ≃* NativeSporadic.Carrier .J2 := e.trans f.symm
  have hcard : ¬ 3 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .J2) := by
    rw [CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder .J2 (by decide)]
    norm_num [CFSG.AGLEmbeddingD2.d2SporadicOrder]
  refine centGen_eq_top_of_equiv ψ ?_
  exact centGen_J2_three_of_check hC hcard _ (isElemAbelian_map hA ψ)
    (by rw [card_map, hAc]; norm_num)

theorem sporadicCentGen_J2_three : SporadicCentGen 3 .J2 :=
  sporadicCentGen_J2_three_of_check Certificates.certificate1322004

end Wrapper

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis
