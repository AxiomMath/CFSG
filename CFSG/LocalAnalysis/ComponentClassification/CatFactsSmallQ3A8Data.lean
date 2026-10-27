module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3F2Gen
public import CFSG.GH74.KGroups.Checks3
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
public import Certificates.Certificate2007
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8DataInputs
public import Certificates.Certificate2014

public section

namespace CFSG.ComponentClassification.CatFactsSmall.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

local notation "P8" => Equiv.Perm (Fin 8)

theorem adm_ok : admCheck (elemsT QS8) QA8 five8 s8 admConj = true :=
  Certificates.certificate2014.1

theorem admConj_mem : ∀ k ∈ admConj, k ∈ QS8.originalSubgroup := by
  intro k _
  rw [QS8_eq]
  exact mem_top k

theorem QL8_valid : QL8.check = true ∧ QL8.orderCertificate = 360 :=
  Certificates.certificate2014.2.1

theorem QL8_ok : ValidSchreier QL8 := QL8_valid.1

theorem card_QL8 : Nat.card QL8.originalSubgroup = 360 := by
  rw [card_group QL8 QL8_ok, QL8_valid.2]

theorem oddNormal_ok : oddNormalCheck (elemsT QL8) 45 = true :=
  Certificates.certificate2014.2.2.1

theorem card_C0 : Nat.card ↥(QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8)) = 720 := by
  rw [card_inf_centralizer QA8 QA8_ok]
  exact Certificates.certificate2014.2.2.2.1

theorem mem_C0 {x : P8} (hx : Equiv.Perm.sign x = 1) (hc : x * s8 = s8 * x) :
    x ∈ QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8) :=
  ⟨QA8_eq ▸ Equiv.Perm.mem_alternatingGroup.2 hx, mem_centralizer_singleton_iff.2 hc⟩

theorem la1_mem : la1 ∈ QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8) :=
  mem_C0 (by decide) (by decide)

theorem lb1_mem : lb1 ∈ QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8) :=
  mem_C0 (by decide) (by decide)

theorem lb2_mem : lb2 ∈ QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8) :=
  mem_C0 (by decide) (by decide)

theorem QL8_eq : QL8.originalSubgroup = closure {l1, l2} := by
  rw [QL8, certificate_originalSubgroup]
  congr 1
  ext g
  simp [tab_eq]

theorem commutator_C0 :
    ⁅QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8),
      QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8)⁆ = QL8.originalSubgroup := by
  set C := QA8.originalSubgroup ⊓ centralizer ({s8} : Set P8)
  have h1 : l1 ∈ ⁅C, C⁆ := commutator_mem_commutator la1_mem lb1_mem
  have h2 : l2 ∈ ⁅C, C⁆ := commutator_mem_commutator la1_mem lb2_mem
  have hle : QL8.originalSubgroup ≤ ⁅C, C⁆ := by
    rw [QL8_eq, closure_le]
    rintro g (rfl | rfl)
    · exact h1
    · exact h2
  have hLC : QL8.originalSubgroup ≤ C := hle.trans (commutator_le_self C)
  have : Finite C := inferInstance
  exact commutator_eq_of_index_two hLC (by rw [card_C0, card_QL8]) hle

theorem L_oddNormal (N : Subgroup P8) (hN : N ≤ QL8.originalSubgroup)
    (hnorm : ∀ x ∈ QL8.originalSubgroup, ∀ y ∈ N, x * y * x⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  refine oddNormal_of_check QL8 QL8_ok (fun d hd hdo => ?_) oddNormal_ok N hN hnorm hodd
  rw [card_QL8] at hd
  have hc : Nat.Coprime d 8 := Nat.Coprime.pow_right 3 (Odd.coprime_two_right hdo)
  exact hc.dvd_of_dvd_mul_left (by simpa [mul_comm] using hd)

theorem QQ8_valid : QQ8.check = true ∧ QQ8.orderCertificate = 32 :=
  Certificates.certificate2014.2.2.2.2.1

theorem QQ8_ok : ValidSchreier QQ8 := QQ8_valid.1

theorem g08_facts : (elemsT QQ8).all (fun q => QQ8.sift (g08 * q * g08⁻¹) 0) = true ∧
    QQ8.sift g08 0 = false ∧ QQ8.sift (g08 * g08) 0 = true :=
  Certificates.certificate2014.2.2.2.2.2.1

theorem card_CA0 : Nat.card ↥(QS8.originalSubgroup ⊓ centralizer ({s8} : Set P8)) =
    2 ^ 5 * 45 := by
  rw [card_inf_centralizer QS8 QS8_ok]
  exact Certificates.certificate2014.2.2.2.2.2.2

theorem QQ8_le : QQ8.originalSubgroup ≤ QS8.originalSubgroup ⊓ centralizer ({s8} : Set P8) := by
  rw [QQ8, certificate_originalSubgroup, closure_le]
  intro g hg
  simp only [q0gens, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, Set.mem_ofPred_eq] at hg
  refine ⟨by rw [QS8_eq]; exact mem_top g, mem_centralizer_singleton_iff.2 ?_⟩
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> rw [tab_eq] <;> decide

theorem g08_mem : g08 ∈ QA8.originalSubgroup :=
  QA8_eq ▸ Equiv.Perm.mem_alternatingGroup.2 (by decide)

theorem g08_sigma : s8 * (g08⁻¹ * s8 * g08) ∈ QA8.originalSubgroup :=
  QA8_eq ▸ Equiv.Perm.mem_alternatingGroup.2 (by decide)

theorem g08_norm : ∀ q ∈ QQ8.originalSubgroup, g08 * q * g08⁻¹ ∈ QQ8.originalSubgroup := by
  intro q hq
  rw [mem_iff_sift QQ8 QQ8_ok]
  exact List.all_eq_true.1 g08_facts.1 q ((mem_elemsT QQ8 QQ8_ok q).2 hq)

theorem g08_not_mem : g08 ∉ QQ8.originalSubgroup := by
  rw [mem_iff_sift QQ8 QQ8_ok, g08_facts.2.1]
  simp

theorem g08_sq : g08 * g08 ∈ QQ8.originalSubgroup := by
  rw [mem_iff_sift QQ8 QQ8_ok]
  exact g08_facts.2.2

theorem card_QQ8 : Nat.card QQ8.originalSubgroup = 2 ^ 5 := by
  rw [card_group QQ8 QQ8_ok, QQ8_valid.2]
  norm_num

end CFSG.ComponentClassification.CatFactsSmall.A8
