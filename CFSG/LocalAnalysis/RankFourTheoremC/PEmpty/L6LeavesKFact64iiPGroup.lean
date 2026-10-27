module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmRank1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64ii

open CFSG.Open CFSG.GH74.Uniqueness.SU Subgroup

theorem isMetacyclic_of_omega_not_mem_frattini {A : Type} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Q B : Subgroup A} (hQ : IsPGroup p Q) (hBQ : B ≤ Q)
    (hBc : Nat.card B = p ^ 2) (hΩ : ∀ q ∈ Q, q ^ p = 1 → q ∈ B) {x : A} (hxB : x ∈ B)
    (hfr : x ∉ (frattini ↥Q).map Q.subtype) : CFSG.IsMetacyclic ↥Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p ↥Q) := ⟨hQ⟩
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  set x' : ↥Q := ⟨x, hBQ hxB⟩ with hx'
  have hx'fr : x' ∉ frattini ↥Q := fun h => hfr ⟨x', h, rfl⟩
  obtain ⟨Q₁, hQ₁, hxQ₁⟩ : ∃ Q₁ : Subgroup ↥Q, IsCoatom Q₁ ∧ x' ∉ Q₁ := by
    by_contra hcon
    push Not at hcon
    apply hx'fr
    show x' ∈ Order.radical (Subgroup ↥Q)
    unfold Order.radical
    simp only [Subgroup.mem_iInf]
    exact fun m hm => hcon m hm
  have hidx : Q₁.index = p := (IsPGroup.isCoatom_iff_index_eq_prime hQ).mp hQ₁
  haveI hQ₁n : Q₁.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom Q₁ Group.normalizerCondition_of_isNilpotent hQ₁
  have hQ₁p : IsPGroup p Q₁ := hQ.to_subgroup Q₁
  have hrk : Open.pRank p Q₁ ≤ 1 := by
    refine SU1.pRank_le_of fun E hEQ₁ hE k hk => ?_
    set E' : Subgroup A := E.map Q.subtype with hE'
    set C : Subgroup A := B ⊓ Q₁.map Q.subtype with hC
    have hE'C : E' ≤ C := by
      rintro _ ⟨e, he, rfl⟩
      refine ⟨hΩ _ e.2 ?_, ⟨e, hEQ₁ he, rfl⟩⟩
      have := (SU1.isElemAbelian_iff.mp hE).2 e he
      have h2 := congrArg Subtype.val this
      simpa using h2
    have hE'card : Nat.card E' = p ^ k := by
      rw [hE', Subgroup.card_map_of_injective Q.subtype_injective, hk]
    have hxC : x ∉ Q₁.map Q.subtype := by
      rintro ⟨q, hq, hqx⟩
      apply hxQ₁
      have : q = x' := Subtype.ext hqx
      rw [← this]
      exact hq
    have hCle : Nat.card C ≤ p := by
      have hdvd : Nat.card C ∣ p ^ 2 := by
        rw [← hBc]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      have hi2 : i ≠ 2 := by
        rintro rfl
        have hCB : C = B := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hCi, hBc])
        apply hxC
        have : x ∈ C := hCB ▸ hxB
        exact this.2
      have hi1 : i ≤ 1 := by omega
      rw [hCi]
      calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hi1
        _ = p := pow_one p
    have h1 := Subgroup.card_le_of_le hE'C
    rw [hE'card] at h1
    have h2 : p ^ k ≤ p := h1.trans hCle
    by_contra hk1
    push Not at hk1
    have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk1
    have h3 : p < p ^ 2 := by
      have := hp.one_lt
      nlinarith
    omega
  haveI : IsCyclic Q₁ := P64Asm.isCyclic_of_pRank_le_one hp hp2 hQ₁p hrk
  refine ⟨Q₁, hQ₁n, inferInstance, ?_⟩
  exact isCyclic_of_prime_card (p := p) (by rw [← Subgroup.index_eq_card, hidx])

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64ii
