module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddBasic
public import CFSG.Blueprint.NativeSporadic
import CFSG.RankThree.PartTwo.Census.Sporadic.J3
import CFSG.RankThree.PartOne.CTP.SporadicOrders
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census
  CFSG.Blueprint
open scoped commutatorElement

theorem localRank_le_two_of_cubic {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h4 : ¬ p ^ 4 ∣ Nat.card T) {x y : T} (hxy : ⁅x, y⁆ ≠ 1)
    (hc : Nat.card (Subgroup.closure ({x, y} : Set T)) = p ^ 3) : localRank p T ≤ 2 := by
  refine localRank_le_of_pRank_le hp (pRank_le_two_of_nonabelian hp h4 hc
    ⟨x, Subgroup.subset_closure (Set.mem_insert _ _), y,
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), fun hc => hxy ?_⟩)
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact hc

variable {G H : Type} [Group G] [Finite G] [Group H]

theorem Standing.false_of_card_cubic (hS : Standing G) (e : G ≃* H) {N : ℕ} (E : Finset ℕ)
    (hN : Nat.card H = N)
    (hE : ∀ r ∈ E, r.Prime → r ≠ 2 → ∃ x y : H, ⁅x, y⁆ ≠ 1 ∧
      Nat.card (Subgroup.closure ({x, y} : Set H)) = r ^ 3 ∧ ¬ r ^ 4 ∣ N)
    (hcube : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ E → ¬ r ^ 3 ∣ N) : False :=
  hS.false_of_card e E hN (fun r hr hrp hr2 => by
    obtain ⟨x, y, hxy, hc, h4⟩ := hE r hr hrp hr2
    exact localRank_le_two_of_cubic hrp (hN ▸ h4) hxy hc) hcube

theorem cube_free_7920 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ (∅ : Finset ℕ) → ¬ p ^ 3 ∣ 7920 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 11} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_95040 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 95040 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 11} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_443520 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ (∅ : Finset ℕ) → ¬ p ^ 3 ∣ 443520 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7, 11} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_10200960 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ (∅ : Finset ℕ) → ¬ p ^ 3 ∣ 10200960 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7, 11, 23} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_244823040 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 244823040 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7, 11, 23} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_175560 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ (∅ : Finset ℕ) → ¬ p ^ 3 ∣ 175560 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7, 11, 19} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_604800 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 604800 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_86775571046077562880 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3, 11} : Finset ℕ) → ¬ p ^ 3 ∣ 86775571046077562880 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_44352000 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({5} : Finset ℕ) → ¬ p ^ 3 ∣ 44352000 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7, 11} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_4030387200 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3, 7} : Finset ℕ) → ¬ p ^ 3 ∣ 4030387200 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7, 17} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_145926144000 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3, 5} : Finset ℕ) → ¬ p ^ 3 ∣ 145926144000 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7, 13, 29} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_50232960 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 50232960 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 17, 19} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem Standing.false_of_M11
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .M11) : False :=
  hS.false_of_card_cubic e ∅ CFSG.Sporadic.Mathieu.card_M11
    (fun _ h => by simp at h) cube_free_7920

theorem Standing.false_of_M12
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .M12) : False := by
  refine hS.false_of_card_cubic e {3} CFSG.Sporadic.Mathieu.card_M12 ?_ cube_free_95040
  intro r hr hrp hr2
  obtain rfl : r = 3 := by simpa using hr
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
  exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing.false_of_M22
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .M22) : False :=
  hS.false_of_card_cubic e ∅ CFSG.Sporadic.Mathieu.card_M22
    (fun _ h => by simp at h) cube_free_443520

theorem Standing.false_of_M23
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .M23) : False :=
  hS.false_of_card_cubic e ∅ CFSG.RankThree.PartOne.CTP.card_M23
    (fun _ h => by simp at h) cube_free_10200960

theorem Standing.false_of_M24
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .M24) : False := by
  refine hS.false_of_card_cubic e {3} CFSG.Sporadic.Mathieu.card_M24 ?_ cube_free_244823040
  intro r hr hrp hr2
  obtain rfl : r = 3 := by simpa using hr
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing.false_of_J1
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .J1) : False :=
  hS.false_of_card_cubic e ∅ CFSG.Sporadic.J1.card_J1
    (fun _ h => by simp at h) cube_free_175560

theorem Standing.false_of_J2
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .J2) : False := by
  refine hS.false_of_card_cubic e {3} CFSG.Sporadic.J2.card_J2 ?_ cube_free_604800
  intro r hr hrp hr2
  obtain rfl : r = 3 := by simpa using hr
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
  exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing.false_of_J4
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .J4) : False := by
  refine hS.false_of_card_cubic e {3, 11} CFSG.Sporadic.J4.card_J4 ?_ cube_free_86775571046077562880
  intro r hr hrp hr2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow11_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing.false_of_HS
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .HS) : False := by
  refine hS.false_of_card_cubic e {5} CFSG.Sporadic.HS.card_HS ?_ cube_free_44352000
  intro r hr hrp hr2
  obtain rfl : r = 5 := by simpa using hr
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
  exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing.false_of_He
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .He) : False := by
  refine hS.false_of_card_cubic e {3, 7} CFSG.Sporadic.He.card_He ?_ cube_free_4030387200
  intro r hr hrp hr2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow7_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing.false_of_Ru
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .Ru) : False := by
  refine hS.false_of_card_cubic e {3, 5} CFSG.Sporadic.Ru.card_Ru ?_ cube_free_145926144000
  intro r hr hrp hr2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩
  · obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
    exact ⟨x, y, hxy, hc, by norm_num⟩

theorem Standing.false_of_J3
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .J3) : False := by
  refine hS.false_of_card (e.trans CFSG.Sporadic.Schreier.j3PermEquiv) {3}
    ((Nat.card_congr CFSG.Sporadic.Schreier.j3PermEquiv.toEquiv).symm.trans
      CFSG.Sporadic.J3.card_J3) ?_ cube_free_50232960
  intro _ r hr _ _
  obtain rfl : r = 3 := by simpa using hr
  exact localRank_three_le_two_of_centralizer fun t ht h9 => by
    rw [card_centralizer_j3P ht] at h9
    exact absurd h9 (by norm_num)

end CFSG.LocalAnalysis.RankThreeUC
