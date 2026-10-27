module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3F2Gen
public import CFSG.GH74.KGroups.Checks3
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
public import Certificates.Certificate2012
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45Inputs
public import Certificates.Certificate2015

public section

namespace CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native
  CFSG.GH74.KGroups.NativeChecks

local notation "P45" => Equiv.Perm (Fin 45)

theorem x45_mem : x45 ∈ QP45.originalSubgroup := by
  rw [QP45_closure]
  exact subset_closure (by simp)

theorem y45_mem : y45 ∈ QP45.originalSubgroup := by
  rw [QP45_closure]
  exact subset_closure (by simp)

theorem P_le_A : QP45.originalSubgroup ≤ QA45.originalSubgroup := by
  rw [QP45_closure, QA45_closure]
  exact closure_mono (by intro g hg; rcases hg with rfl | rfl <;> simp)

theorem cent_triv : ∀ g ∈ QA45.originalSubgroup,
    (∀ x ∈ QP45.originalSubgroup, g * x = x * g) → g = 1 := by
  intro g hg hc
  by_contra hne
  have h1 := List.all_eq_true.1 cent_ok g ((mem_elemsT QA45 QA45_ok g).2 hg)
  simp [hc x45 x45_mem, hc y45 y45_mem, hne] at h1

theorem card_P : Nat.card QP45.originalSubgroup = 25920 := by
  rw [card_group QP45 QP45_ok, QP45_valid.2]

theorem card_A_eq : Nat.card QA45.originalSubgroup = 2 * Nat.card QP45.originalSubgroup := by
  rw [card_group QA45 QA45_ok, QA45_valid.2, card_P]

@[expose] def oddTest (x : P45) : Bool := decide (x ^ 9 = 1) || decide (x ^ 5 = 1)

theorem oddTestA_toA (x : P45) : oddTestA (toA x) = oddTest x := by
  rw [oddTestA, oddTest, eqA_eq_decide (rep_powA (rep_toA x) 9) (rep_idA (n := 45)),
    eqA_eq_decide (rep_powA (rep_toA x) 5) (rep_idA (n := 45))]

theorem noNilpA_ok : noNilpA 45 (enumA QA45) ((enumA QP45).filter oddTestA) 405 = true :=
  Certificates.certificate2015.1

theorem noNilp_ok :
    noNilpA 45 ((elemsT QA45).map toA) (((elemsT QP45).filter oddTest).map toA) 405 = true := by
  have h : ((elemsT QP45).filter oddTest).map toA = (enumA QP45).filter oddTestA := by
    rw [enumA_eq, List.filter_map]
    exact congrArg (List.map toA) (List.filter_congr fun x _ => (oddTestA_toA x).symm)
  rw [h, ← enumA_eq]
  exact noNilpA_ok

theorem pow_of_oddTest {x : P45} (h : oddTest x = true) : x ^ 405 = 1 := by
  simp only [oddTest, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [show 405 = 9 * 45 by norm_num, pow_mul, h, one_pow]
  · rw [show 405 = 5 * 81 by norm_num, pow_mul, h, one_pow]

theorem noNilp_fact {s : P45} (hs : s ∈ QA45.originalSubgroup) (hs2 : s * s = 1) :
    ∃ x₁ ∈ QP45.originalSubgroup, ∃ x₂ ∈ QP45.originalSubgroup, x₁ * s = s * x₁ ∧
      x₂ * s = s * x₂ ∧ x₁ ^ 405 = 1 ∧ x₂ ^ 405 = 1 ∧ (x₁ * x₂) ^ 405 ≠ 1 := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hc₁, hc₂, h12⟩ :=
    noNilpA_sound noNilp_ok ((mem_elemsT QA45 QA45_ok s).2 hs) hs2
  rw [List.mem_filter] at hx₁ hx₂
  exact ⟨x₁, (mem_elemsT QP45 QP45_ok x₁).1 hx₁.1, x₂, (mem_elemsT QP45 QP45_ok x₂).1 hx₂.1,
    hc₁, hc₂, pow_of_oddTest hx₁.2, pow_of_oddTest hx₂.2, h12⟩

@[expose] def five45 : List P45 :=
  (elemsT QP45).filter fun x => decide (x ^ 5 = 1) && !decide (x = 1)

theorem five45A_eq : five45A = five45.map toA := by
  rw [five45A, five45, enumA_eq, List.filter_map]
  refine congrArg (List.map toA) (List.filter_congr fun x _ => ?_)
  simp only [Function.comp, eqA_eq_decide (rep_powA (rep_toA x) 5) (rep_idA (n := 45)),
    eqA_eq_decide (rep_toA x) (rep_idA (n := 45))]

theorem admA_ok : admCheckA (elemsTab QA45) QP45 five45A s045 admConj = true :=
  Certificates.certificate2015.2.1

theorem adm_ok : admCheckA (elemsT QA45) QP45 (five45.map toA) s045 admConj = true := by
  rw [← elemsTab_eq, ← five45A_eq]
  exact admA_ok

theorem admConj_mem : ∀ k ∈ admConj, k ∈ QA45.originalSubgroup := by
  intro k hk
  simp only [admConj, List.mem_map] at hk
  obtain ⟨w, -, rfl⟩ := hk
  rw [tab_eq]
  refine evalCodes_mem_of_gens _ QA45.originalSubgroup (fun g hg => ?_) w
  rw [QA45_closure]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> rw [tab_eq] <;> exact subset_closure (by simp)

theorem s045_mem : s045 ∈ QA45.originalSubgroup := by
  rw [mem_iff_sift QA45 QA45_ok]
  exact Certificates.certificate2015.2.2.1

theorem QL45_valid : QL45.check = true ∧ QL45.orderCertificate = 360 :=
  Certificates.certificate2015.2.2.2.1

theorem QL45_ok : ValidSchreier QL45 := QL45_valid.1

theorem card_QL45 : Nat.card QL45.originalSubgroup = 360 := by
  rw [card_group QL45 QL45_ok, QL45_valid.2]

theorem oddNormal_ok : oddNormalCheck (elemsT QL45) 45 = true :=
  Certificates.certificate2015.2.2.2.2.1

theorem card_C0 :
    Nat.card ↥(QP45.originalSubgroup ⊓ centralizer ({s045} : Set P45)) = 720 := by
  rw [card_inf_centralizer QP45 QP45_ok]
  exact Certificates.certificate2015.2.2.2.2.2.1

theorem la_facts : QP45.sift la1 0 = true ∧ QP45.sift lb1 0 = true ∧ QP45.sift lb2 0 = true ∧
    la1 * s045 = s045 * la1 ∧ lb1 * s045 = s045 * lb1 ∧ lb2 * s045 = s045 * lb2 :=
  Certificates.certificate2015.2.2.2.2.2.2.1

theorem la1_mem : la1 ∈ QP45.originalSubgroup ⊓ centralizer ({s045} : Set P45) :=
  ⟨(mem_iff_sift QP45 QP45_ok _).2 la_facts.1, mem_centralizer_singleton_iff.2 la_facts.2.2.2.1⟩

theorem lb1_mem : lb1 ∈ QP45.originalSubgroup ⊓ centralizer ({s045} : Set P45) :=
  ⟨(mem_iff_sift QP45 QP45_ok _).2 la_facts.2.1,
    mem_centralizer_singleton_iff.2 la_facts.2.2.2.2.1⟩

theorem lb2_mem : lb2 ∈ QP45.originalSubgroup ⊓ centralizer ({s045} : Set P45) :=
  ⟨(mem_iff_sift QP45 QP45_ok _).2 la_facts.2.2.1,
    mem_centralizer_singleton_iff.2 la_facts.2.2.2.2.2⟩

theorem QL45_eq : QL45.originalSubgroup = closure {l1, l2} := by
  rw [QL45, certificate_originalSubgroup]
  congr 1
  ext g
  simp [tab_eq]

theorem commutator_C0 :
    ⁅QP45.originalSubgroup ⊓ centralizer ({s045} : Set P45),
      QP45.originalSubgroup ⊓ centralizer ({s045} : Set P45)⁆ = QL45.originalSubgroup := by
  set C := QP45.originalSubgroup ⊓ centralizer ({s045} : Set P45)
  have h1 : l1 ∈ ⁅C, C⁆ := commutator_mem_commutator la1_mem lb1_mem
  have h2 : l2 ∈ ⁅C, C⁆ := commutator_mem_commutator la1_mem lb2_mem
  have hle : QL45.originalSubgroup ≤ ⁅C, C⁆ := by
    rw [QL45_eq, closure_le]
    rintro g (rfl | rfl)
    · exact h1
    · exact h2
  have hLC : QL45.originalSubgroup ≤ C := hle.trans (commutator_le_self C)
  have : Finite C := inferInstance
  exact commutator_eq_of_index_two hLC (by rw [card_C0, card_QL45]) hle

theorem L_oddNormal (N : Subgroup P45) (hN : N ≤ QL45.originalSubgroup)
    (hnorm : ∀ x ∈ QL45.originalSubgroup, ∀ y ∈ N, x * y * x⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  refine oddNormal_of_check QL45 QL45_ok (fun d hd hdo => ?_) oddNormal_ok N hN hnorm hodd
  rw [card_QL45] at hd
  have hc : Nat.Coprime d 8 := Nat.Coprime.pow_right 3 (Odd.coprime_two_right hdo)
  exact hc.dvd_of_dvd_mul_left (by simpa [mul_comm] using hd)

theorem QQ45_valid : QQ45.check = true ∧ QQ45.orderCertificate = 32 :=
  Certificates.certificate2015.2.2.2.2.2.2.2.1

theorem QQ45_ok : ValidSchreier QQ45 := QQ45_valid.1

theorem g045_facts : (elemsT QQ45).all (fun q => QQ45.sift (g045 * q * g045⁻¹) 0) = true ∧
    QQ45.sift g045 0 = false ∧ QQ45.sift (g045 * g045) 0 = true ∧ QP45.sift g045 0 = true ∧
    QP45.sift (s045 * (g045⁻¹ * s045 * g045)) 0 = true ∧
    (q0gens.all fun q => QA45.sift q 0 && decide (q * s045 = s045 * q)) = true :=
  Certificates.certificate2015.2.2.2.2.2.2.2.2.1

theorem card_CA0 :
    Nat.card ↥(QA45.originalSubgroup ⊓ centralizer ({s045} : Set P45)) = 2 ^ 5 * 45 := by
  rw [card_inf_centralizer QA45 QA45_ok]
  exact Certificates.certificate2015.2.2.2.2.2.2.2.2.2

theorem QQ45_le :
    QQ45.originalSubgroup ≤ QA45.originalSubgroup ⊓ centralizer ({s045} : Set P45) := by
  rw [QQ45, certificate_originalSubgroup, closure_le]
  intro g hg
  simp only [List.mem_map, Set.mem_ofPred_eq] at hg
  obtain ⟨q, hq, rfl⟩ := hg
  have h := List.all_eq_true.1 g045_facts.2.2.2.2.2 q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [tab_eq]
  exact ⟨(mem_iff_sift QA45 QA45_ok q).2 h.1, mem_centralizer_singleton_iff.2 h.2⟩

theorem g045_mem : g045 ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok _).2 g045_facts.2.2.2.1

theorem g045_sigma : s045 * (g045⁻¹ * s045 * g045) ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok _).2 g045_facts.2.2.2.2.1

theorem g045_norm : ∀ q ∈ QQ45.originalSubgroup, g045 * q * g045⁻¹ ∈ QQ45.originalSubgroup := by
  intro q hq
  rw [mem_iff_sift QQ45 QQ45_ok]
  exact List.all_eq_true.1 g045_facts.1 q ((mem_elemsT QQ45 QQ45_ok q).2 hq)

theorem g045_not_mem : g045 ∉ QQ45.originalSubgroup := by
  rw [mem_iff_sift QQ45 QQ45_ok, g045_facts.2.1]
  simp

theorem g045_sq : g045 * g045 ∈ QQ45.originalSubgroup := by
  rw [mem_iff_sift QQ45 QQ45_ok]
  exact g045_facts.2.2.1

theorem card_QQ45 : Nat.card QQ45.originalSubgroup = 2 ^ 5 := by
  rw [card_group QQ45 QQ45_ok, QQ45_valid.2]
  norm_num

end CFSG.ComponentClassification.CatFactsSmall.PSp43
