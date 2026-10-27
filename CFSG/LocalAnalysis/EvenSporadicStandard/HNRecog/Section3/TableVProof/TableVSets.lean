module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpRows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private lemma tab5_mul_conj {a k : G} (hk : k ∈ Gx a) : k * a * k⁻¹ = a := by
  have h : k * a = a * k := (mem_Gx.mp hk).symm
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private lemma tab5_isConj_conj {p q k : G} (h : IsConj p q) : IsConj p (k * q * k⁻¹) :=
  h.trans (isConj_iff.2 ⟨k, rfl⟩)

private lemma tab5_conj_mem_orb2B {a z k c : G} (hk : k ∈ Gx a) (hc : c ∈ orb2B a z a) :
    k * c * k⁻¹ ∈ orb2B a z a := by
  refine ⟨tab5_isConj_conj hc.1, ?_⟩
  rw [mul_conj_of_fix (tab5_mul_conj hk)]
  exact tab5_isConj_conj hc.2

private lemma tab5_conj_mem_orb4A {a z k c : G} (hk : k ∈ Gx a) (hc : c ∈ orb4A a z a) :
    k * c * k⁻¹ ∈ orb4A a z a := by
  refine ⟨tab5_isConj_conj hc.1, ?_⟩
  rw [mul_conj_of_fix (tab5_mul_conj hk), conj_pow]
  exact tab5_isConj_conj hc.2

private lemma tab5_conj_mem_orb4B {a k c : G} (hk : k ∈ Gx a) (hc : c ∈ orb4B a a) :
    k * c * k⁻¹ ∈ orb4B a a := by
  refine ⟨tab5_isConj_conj hc.1, ?_⟩
  rw [mul_conj_of_fix (tab5_mul_conj hk), conj_pow]
  exact tab5_isConj_conj hc.2

private lemma tab5_conj_mem_orb6A {a k c : G} (hk : k ∈ Gx a) (hc : c ∈ orb6A a a) :
    k * c * k⁻¹ ∈ orb6A a a := by
  have hmc := tab5_mul_conj hk
  refine ⟨tab5_isConj_conj hc.1, ?_, ?_⟩
  · rw [mul_conj_of_fix hmc, ← MulAut.conj_apply k (a * c)]
    exact (MulEquiv.orderOf_eq (MulAut.conj k) (a * c)).trans hc.2.1
  · rw [mul_conj_of_fix hmc, conj_pow]
    exact tab5_isConj_conj hc.2.2

theorem tableV_conj_mem {a z k c : G} (hk : k ∈ Gx a) (i : Fin 5) (hc : c ∈ tab5Set a z i) :
    k * c * k⁻¹ ∈ tab5Set a z i := by
  fin_cases i
  · exact perp_conj_mem_orb2A hk hc
  · exact tab5_conj_mem_orb2B hk hc
  · exact tab5_conj_mem_orb4A hk hc
  · exact tab5_conj_mem_orb4B hk hc
  · exact tab5_conj_mem_orb6A hk hc

theorem tableV_subset {a z : G} (h : IsF5Type a z) (i : Fin 5) : tab5Set a z i ⊆ tab5Base a := by
  intro c hc
  fin_cases i
  · exact ⟨hc.1, by rw [perp_orderOf_of_isConj_a h hc.2]; exact ⟨1, rfl⟩⟩
  · exact ⟨hc.1, by rw [perp_orderOf_of_isConj_z h hc.2]; exact ⟨1, rfl⟩⟩
  · exact ⟨hc.1, by rw [tableV_orderOf_orb4A h hc]; exact ⟨2, rfl⟩⟩
  · exact ⟨hc.1, by rw [tableV_orderOf_orb4B h hc]; exact ⟨2, rfl⟩⟩
  · exact ⟨hc.1, by rw [hc.2.1]; exact ⟨3, rfl⟩⟩

theorem tableV_disjoint (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z) (i j : Fin 5)
    (hij : i ≠ j) : Disjoint (tab5Set a z i) (tab5Set a z j) := by
  rw [Set.disjoint_left]
  intro c hci hcj
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact (not_isConj_of_isF5Type hI h) (hci.2.trans hcj.2.symm)
  · have h2 := perp_orderOf_of_isConj_a h hci.2
    have h4 := tableV_orderOf_orb4A h hcj
    omega
  · have h2 := perp_orderOf_of_isConj_a h hci.2
    have h4 := tableV_orderOf_orb4B h hcj
    omega
  · have h2 := perp_orderOf_of_isConj_a h hci.2
    have h6 := hcj.2.1
    omega
  · exact (not_isConj_of_isF5Type hI h) (hcj.2.trans hci.2.symm)
  · exact absurd rfl hij
  · have h2 := perp_orderOf_of_isConj_z h hci.2
    have h4 := tableV_orderOf_orb4A h hcj
    omega
  · have h2 := perp_orderOf_of_isConj_z h hci.2
    have h4 := tableV_orderOf_orb4B h hcj
    omega
  · have h2 := perp_orderOf_of_isConj_z h hci.2
    have h6 := hcj.2.1
    omega
  · have h4 := tableV_orderOf_orb4A h hci
    have h2 := perp_orderOf_of_isConj_a h hcj.2
    omega
  · have h4 := tableV_orderOf_orb4A h hci
    have h2 := perp_orderOf_of_isConj_z h hcj.2
    omega
  · exact absurd rfl hij
  · exact (not_isConj_of_isF5Type hI h) (hci.2.trans hcj.2.symm).symm
  · have h4 := tableV_orderOf_orb4A h hci
    have h6 := hcj.2.1
    omega
  · have h4 := tableV_orderOf_orb4B h hci
    have h2 := perp_orderOf_of_isConj_a h hcj.2
    omega
  · have h4 := tableV_orderOf_orb4B h hci
    have h2 := perp_orderOf_of_isConj_z h hcj.2
    omega
  · exact (not_isConj_of_isF5Type hI h) (hci.2.trans hcj.2.symm)
  · exact absurd rfl hij
  · have h4 := tableV_orderOf_orb4B h hci
    have h6 := hcj.2.1
    omega
  · have h6 := hci.2.1
    have h2 := perp_orderOf_of_isConj_a h hcj.2
    omega
  · have h6 := hci.2.1
    have h2 := perp_orderOf_of_isConj_z h hcj.2
    omega
  · have h6 := hci.2.1
    have h4 := tableV_orderOf_orb4A h hcj
    omega
  · have h6 := hci.2.1
    have h4 := tableV_orderOf_orb4B h hcj
    omega
  · exact absurd rfl hij

end CFSG.EvenSporadicStandard.HNRecog.Section3
