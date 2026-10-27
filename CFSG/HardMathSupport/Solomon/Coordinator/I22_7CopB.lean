module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

theorem i227cop_isElemAbelian_of_le {K : Type*} [Group K] {p : ℕ} {E Q : Subgroup K}
    (hE : CFSG.Open.IsElemAbelian p E) (hQE : Q ≤ E) : CFSG.Open.IsElemAbelian p Q :=
  CFSG.Open.IsElemAbelian.mono hE hQE

theorem i227cop_normal_le_weakCore {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) (P : Subgroup K) (hrk : 3 ≤ CFSG.Open.pRank 3 P) :
    N ≤ weakCoreIn 3 P ⊤ := by
  classical
  have h3 : 1 < 3 := by norm_num
  obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_pRank h3 P
  set r := CFSG.Open.pRank 3 P with hr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEA : CFSG.IsElementaryAbelian 3 E :=
    { hE.1 with
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hE.2 (a : K) a.2) }
  have hnt : Nontrivial E := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hcard]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hN3 : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hN
  let : MulDistribMulAction E N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp E.subtype)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 3) (A := E) (H := N) hN3
  have hle : ∀ B : Subgroup E, B.index = 3 →
      (CFSG.fixedPointSubgroup B N).map N.subtype ≤ weakCoreIn 3 P ⊤ := by
    intro B hB
    set Q : Subgroup K := B.map E.subtype with hQ
    have hQE : Q ≤ E := Subgroup.map_subtype_le B
    have hQP : Q ≤ P := hQE.trans hEP
    have hcardQ : Nat.card Q = 3 ^ (r - 1) := by
      have h1 : Nat.card B * 3 = 3 ^ r := by
        rw [← hcard, ← hB]; exact Subgroup.card_mul_index B
      have h2 : 3 ^ r = 3 ^ (r - 1) * 3 := by
        rw [← pow_succ]; congr 1; omega
      have h3' : Nat.card B = 3 ^ (r - 1) := by
        rw [h2] at h1; exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
      rw [hQ, Subgroup.card_map_of_injective E.subtype_injective]
      exact h3'
    have hQab : CFSG.Open.IsElemAbelian 3 Q := i227cop_isElemAbelian_of_le hE hQE
    have hrQ : 2 ≤ CFSG.Open.pRank 3 Q := by
      have := CFSG.SectionRank.le_pRank h3 le_rfl hQab hcardQ
      omega
    have hET : E ≤ Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set K)) := by
      refine le_sup_of_le_right (le_inf hEP ?_)
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have := mul_comm' (⟨q, hQE hq⟩ : E) ⟨e, he⟩
      exact congrArg Subtype.val this
    have hrT : 3 ≤ CFSG.Open.pRank 3 (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set K))) :=
      hrk.trans (CFSG.SectionRank.le_pRank h3 hET hE hcard)
    rintro _ ⟨n, hn, rfl⟩
    unfold weakCoreIn
    refine Subgroup.mem_iSup_of_mem Q (Subgroup.mem_iSup_of_mem ⟨hQP, hrQ, hrT⟩ ?_)
    have hc : N.subtype n ∈ Subgroup.centralizer (Q : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have h : (b : K) * n * (b : K)⁻¹ = n := congrArg Subtype.val (hn ⟨b, hb⟩)
      change (b : K) * n = n * (b : K)
      calc (b : K) * n = (b : K) * n * (b : K)⁻¹ * b := by group
        _ = n * b := by rw [h]
    exact ⟨Subgroup.mem_top _, Subgroup.centralizer_le_normalizer (Q : Set K) hc⟩
  have hmap : (⊤ : Subgroup N).map N.subtype ≤ weakCoreIn 3 P ⊤ := by
    have h : (⨆ (B : Subgroup E) (_ : B.index = 3), CFSG.fixedPointSubgroup B N).map N.subtype
        ≤ weakCoreIn 3 P ⊤ := by
      simp only [Subgroup.map_iSup]
      exact iSup₂_le fun B hB => hle B hB
    rwa [hgen] at h
  intro x hx
  exact hmap ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

end CFSG.HardMathSupport.Solomon.Coordinator
