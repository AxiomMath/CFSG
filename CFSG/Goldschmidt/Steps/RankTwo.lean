module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Milestones.LR_rank_two_isomorphism_types
public import CFSG.Goldschmidt.Statements

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace RankTwo

theorem omega1_le_of_isConj {G : Type} [Group G] [Finite G] (S : Sylow 2 G) {A : Subgroup G}
    (hAS : A ≤ S) (hA1 : A ≠ ⊥) (hcl : fusionStronglyClosed (A : Set G) (S : Subgroup G))
    (hconj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    Omega1 (S : Subgroup G) ≤ A := by
  have hAp : IsPGroup 2 A := (S.isPGroup').to_le hAS
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.card_eq_one.1 (by simpa using hn))
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hao : orderOf (a : G) = 2 := by rw [Subgroup.orderOf_coe, ha]
  rw [Omega1, Subgroup.closure_le]
  rintro t ⟨htS, ht2⟩
  by_cases ht1 : t = 1
  · rw [ht1]
    exact A.one_mem
  · obtain ⟨c, hc⟩ := isConj_iff.1 (hconj _ _ hao (orderOf_eq_prime ht2 ht1))
    have ht : (c⁻¹)⁻¹ * (a : G) * c⁻¹ = t := by rw [inv_inv]; exact hc
    have := hcl a a.2 c⁻¹ (by rw [ht]; exact htS)
    rwa [ht] at this

theorem isMulCommutative_sylow_of_psl2 {G : Type} [Group G] [Finite G] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f) (S : Sylow 2 G) :
    IsMulCommutative (S : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField G 2 p f hM
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) :=
    Finite.of_equiv G e.toEquiv
  obtain ⟨P⟩ :=
    (inferInstance : Nonempty (Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField p f))))
  have hP :=
    CFSG.Walter.psl2_sylow_two_card_eq_four (GaloisField p f) (GaloisField.card p f (by omega))
      (hp.odd_of_ne_two hp2) (by omega) h8 P
  have hcard : Nat.card (S : Subgroup G) = 2 ^ 2 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv, ← Sylow.card_eq_multiplicity P, hP]
    norm_num
  exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard

end RankTwo

open RankTwo in
theorem N40_of
    (h15 : S_N15) : S_N40 := by
  intro G _ _ _ hnab hrank S A hAS hA1 hAab hcl
  have hexcl : ((∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
      ∀ S : Sylow 2 G, ¬ IsMulCommutative (Omega1 (S : Subgroup G))) → False := by
    rintro ⟨hconj, hnc⟩
    apply hnc S
    have hle := omega1_le_of_isConj S hAS hA1 hcl hconj
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have h : (x : G) * y = y * x :=
      congrArg Subtype.val (hAab.is_comm.comm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩)
    exact h
  rcases CFSG.Milestones.lr_rank_two_isomorphism_types G hnab hrank with
    ⟨p, f, hp, hp2, hf, hM⟩ | hM | hM | hM | hM | hM
  ·
    have hodd : p ^ f % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
    have hq : (p ^ f % 8 = 1 ∨ p ^ f % 8 = 7) ∨ (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) := by omega
    rcases hq with h | h
    · exact (hexcl (h15 G (Or.inl ⟨p, f, hp, hp2, hf, h, hM⟩))).elim
    · exact Or.inl (isMulCommutative_sylow_of_psl2 hp hp2 hf h hM S)
  · exact (hexcl (h15 G (Or.inr (Or.inl hM)))).elim
  · exact (hexcl (h15 G (Or.inr (Or.inr (Or.inl hM))))).elim
  ·
    obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff G 2 le_rfl).1 hM
    have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = PSU3 2 2 := by
      simp only [CFSG.Theory.Comparator.PSU3Model, PSU3]
    exact Or.inr ⟨e.trans (MulEquiv.subgroupCongr hmodel)⟩
  · exact (hexcl (h15 G (Or.inr (Or.inr (Or.inr (Or.inl hM)))))).elim
  · exact (hexcl (h15 G (Or.inr (Or.inr (Or.inr (Or.inr hM)))))).elim

end CFSG.Goldschmidt
