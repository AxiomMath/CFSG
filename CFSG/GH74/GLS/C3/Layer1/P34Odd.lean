module

public import CFSG.GH74.GLS.C3.Layer1.P34Cfg
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.RankTwoShapes

theorem oddMove : OddMove := by
  intro M _ _ H hodd hne
  by_contra hcon
  push Not at hcon
  have hcon' : ∀ m : M, Odd (orderOf m) → m ∈ H := hcon
  set S : Set M := {m | Odd (orderOf m)} with hS
  let M₀ : Subgroup M := Subgroup.normalClosure S
  have hM₀H : M₀ ≤ H := by
    refine (Subgroup.closure_le H).2 ?_
    intro y hy
    obtain ⟨m, hm, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    refine hcon' _ ?_
    obtain ⟨c, hc⟩ := hconj
    rw [← SemiconjBy.orderOf_eq (c : M) hc]
    exact hm
  have hp : IsPGroup 2 (M ⧸ M₀) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, k, hk, hak⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf m) (orderOf_pos m).ne'
    refine ⟨a, ?_⟩
    have hmem : m ^ 2 ^ a ∈ M₀ := by
      refine Subgroup.subset_normalClosure ?_
      show Odd (orderOf (m ^ 2 ^ a))
      have h1 : orderOf (m ^ 2 ^ a) = k := by
        rw [orderOf_pow_of_dvd (by positivity) ⟨k, hak⟩, hak]
        simp
      rw [h1]; exact hk
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hmem
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hp)
  have hidx : M₀.index = 2 ^ n := by rw [Subgroup.index_eq_card, hn]
  have hdvd : H.index ∣ 2 ^ n := hidx ▸ Subgroup.index_dvd_of_le hM₀H
  have hcop : Nat.Coprime H.index (2 ^ n) :=
    Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  have h1 : H.index = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  exact hne (Subgroup.index_eq_one.1 h1)

section Alperin

variable {X : Type} [Group X]

private theorem mem_map_conj_inv_iff' {H : Subgroup X} {g y : X} :
    y ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

theorem exists_moving_step_subgroup [Finite X] {p : ℕ} {S P : Subgroup X} {c : X}
    (h : AlperinDecomposition p S P c) (hc : ∃ a ∈ P, c⁻¹ * a * c ∉ P) :
    ∃ Q : Subgroup X, IsAlperinSubgroup p S Q ∧ P ≤ Q ∧
      ∃ n ∈ Subgroup.normalizer (Q : Set X), ∃ a ∈ P, n⁻¹ * a * n ∉ P := by
  induction h with
  | one =>
    obtain ⟨a, ha, hna⟩ := hc
    exact absurd (by simpa using ha) hna
  | @step c n Q hdec hQ hPQ hn ih =>
    by_cases hmove : ∃ a ∈ P, c⁻¹ * a * c ∉ P
    · exact ih hmove
    · push Not at hmove
      have hmapP : P.map (MulAut.conj c⁻¹).toMonoidHom = P := by
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · rintro y ⟨a, ha, rfl⟩
          simpa using hmove a ha
        · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
      have hPQ' : P ≤ Q := hmapP ▸ hPQ
      obtain ⟨a, ha, hna⟩ := hc
      refine ⟨Q, hQ, hPQ', n, hn, ?_⟩
      refine ⟨c⁻¹ * a * c, hmove a ha, ?_⟩
      intro hcon
      apply hna
      have e : (c * n)⁻¹ * a * (c * n) = n⁻¹ * (c⁻¹ * a * c) * n := by group
      rwa [e]

theorem alperinStep : AlperinStep := by
  intro X _ _ T P hT hTi hPT ⟨g, hgT, a₀, ha₀, ha₀g⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 X := hT.toSylow hTi
  have hPS : P ≤ (S : Subgroup X) := hPT
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup X) := by
    rintro y ⟨a, ha, rfl⟩
    have h := hgT a ha
    exact (show (MulAut.conj g⁻¹).toMonoidHom a ∈ T by simpa using h)
  obtain ⟨c, hdec, hcg⟩ := alperin_centric_radical_fusion S hPS hPg
  obtain ⟨Q, hQ, hPQ, n, hn, hmove⟩ := exists_moving_step_subgroup hdec
    ⟨a₀, ha₀, by rw [hcg a₀ ha₀]; exact ha₀g⟩
  exact ⟨Q, hPQ, hQ.1, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hQ.2.1, n, hn, hmove⟩

end Alperin

end CFSG.GH74.GLS.C3.Layer1.P34
