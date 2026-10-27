module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45
public import Certificates.Certificate2007
public import Certificates.Certificate2012
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2015

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.GSThmB

namespace PSp43

noncomputable def q3Data {K₀ : Type} [Group K₀] (e : K₀ ≃* QP45.originalSubgroup) :
    Q3ModelData K₀ (Equiv.Perm (Fin 45)) := by
  classical
  let M := (exists_model e).choose
  have hP : M.P = QP45.originalSubgroup := (exists_model e).choose_spec.1
  have hA : M.A = QA45.originalSubgroup := (exists_model e).choose_spec.2
  have hK : Nat.card K₀ = 2 ^ 6 * 405 := by
    rw [Nat.card_congr e.toEquiv, card_P]
    norm_num
  exact
    { M := M
      PA := by rw [hP, hA]; exact P_le_A
      cent := by rw [hP, hA]; exact cent_triv
      card := by rw [hP, hA]; exact card_A_eq
      m := 405
      hm := by decide
      hK := fun d hd hdo => odd_dvd_of_dvd_mul (hK ▸ hd) hdo
      noNilp := by rw [hP, hA]; exact fun s hs hs2 => noNilp_fact hs hs2
      s₀ := s045
      adm := by
        rw [hP, hA]
        intro s hs hs2 hsP h5
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' 5 h5
        rw [Subgroup.orderOf_mk] at hxo
        have hx5 : x ∈ five45 := by
          rw [five45, List.mem_filter, mem_elemsT QP45 QP45_ok]
          refine ⟨hx.1, ?_⟩
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
            decide_eq_false_iff_not]
          exact ⟨hxo ▸ pow_orderOf_eq_one x, fun h1 => by rw [h1, orderOf_one] at hxo; omega⟩
        obtain ⟨k, hk, hks⟩ := exists_conj_of_admCheckA QP45_ok adm_ok
          ((mem_elemsT QA45 QA45_ok s).2 hs) hs2 hsP hx5 (mem_centralizer_singleton_iff.1 hx.2)
        exact ⟨k, admConj_mem k hk, hks⟩
      L := QL45.originalSubgroup
      commL := by rw [hP]; exact commutator_C0
      cardL := card_QL45
      oddL := L_oddNormal
      Q₀ := QQ45.originalSubgroup
      Q₀le := by rw [hA]; exact QQ45_le
      cardCA := by rw [hA]; exact card_CA0
      cardQ₀ := card_QQ45
      g₀ := g045
      g₀P := by rw [hP]; exact g045_mem
      g₀N := g045_norm
      g₀Q := g045_not_mem
      g₀2 := g045_sq
      g₀σ := by rw [hP]; exact g045_sigma }

end PSp43

theorem exists_q3ModelData {K₀ : Type} [Group K₀] (h : IsSec8Socle K₀ 3 1) :
    Nonempty (Q3ModelData K₀ (Equiv.Perm (Fin 8))) ∨
      Nonempty (Q3ModelData K₀ (Equiv.Perm (Fin 45))) := by
  rcases h with hL | ⟨-, -, ⟨e⟩⟩
  · obtain ⟨e⟩ := PSp43.equiv_of_lieModel hL
    exact .inr ⟨PSp43.q3Data e⟩
  · exact .inl ⟨A8.q3Data e⟩

theorem cfQ3Out : CFQ3Out := by
  intro K₀ _ _ hK α hα
  rcases exists_q3ModelData hK with h | h
  · obtain ⟨D⟩ := h; exact q3Out_of_data D α hα
  · obtain ⟨D⟩ := h; exact q3Out_of_data D α hα

theorem cfQ3NoNilp : CFQ3NoNilp := by
  intro K₀ _ _ hK α hα
  rcases exists_q3ModelData hK with h | h
  · obtain ⟨D⟩ := h; exact q3NoNilp_of_data D α hα
  · obtain ⟨D⟩ := h; exact q3NoNilp_of_data D α hα

theorem cfQ3L0 : CFQ3L0 := by
  intro K₀ _ _ hK α hα
  rcases exists_q3ModelData hK with h | h
  · obtain ⟨D⟩ := h; exact q3L0_of_data D α hα
  · obtain ⟨D⟩ := h; exact q3L0_of_data D α hα

theorem cfQ3F2 : CFQ3F2 := by
  intro K₀ _ _ hK α hα Q hQC hQS
  rcases exists_q3ModelData hK with h | h
  · obtain ⟨D⟩ := h; exact q3F2_of_data D α hα Q hQC hQS
  · obtain ⟨D⟩ := h; exact q3F2_of_data D α hα Q hQC hQS

end CFSG.ComponentClassification.CatFactsSmall
