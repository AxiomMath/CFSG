module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGrp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bTrans

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpRkProof

theorem two_le_pRank_of_prod_aux1 {A B : Type} [Group A] [Group B] {p : ℕ} {a : A} {b : B}
    (ha : orderOf a = p) (hb : orderOf b = p) :
    CFSG.Open.IsElemAbelian p ((Subgroup.zpowers a).prod (Subgroup.zpowers b)) ∧
      Nat.card ((Subgroup.zpowers a).prod (Subgroup.zpowers b)) = p ^ 2 := by
  have hpa : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hpb : b ^ p = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hexpA : ∀ x ∈ Subgroup.zpowers a, x ^ p = 1 :=
    (K421GrpProof.isElemAbelian_zpowers hpa).2
  have hexpB : ∀ y ∈ Subgroup.zpowers b, y ^ p = 1 :=
    (K421GrpProof.isElemAbelian_zpowers hpb).2
  have hcomm : IsMulCommutative (↥((Subgroup.zpowers a).prod (Subgroup.zpowers b))) := by
    refine ⟨⟨fun x y => Subtype.ext (Prod.ext ?_ ?_)⟩⟩
    · exact congrArg Subtype.val
        ((inferInstance : IsMulCommutative (Subgroup.zpowers a)).is_comm.comm
          ⟨_, (Subgroup.mem_prod.1 x.2).1⟩ ⟨_, (Subgroup.mem_prod.1 y.2).1⟩)
    · exact congrArg Subtype.val
        ((inferInstance : IsMulCommutative (Subgroup.zpowers b)).is_comm.comm
          ⟨_, (Subgroup.mem_prod.1 x.2).2⟩ ⟨_, (Subgroup.mem_prod.1 y.2).2⟩)
  have hexp : ∀ x ∈ (Subgroup.zpowers a).prod (Subgroup.zpowers b), x ^ p = 1 := by
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hx
    exact Prod.ext (hexpA _ h1) (hexpB _ h2)
  have hcard : Nat.card ((Subgroup.zpowers a).prod (Subgroup.zpowers b)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers a) (Subgroup.zpowers b)).toEquiv,
      Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ha, hb, sq]
  exact ⟨⟨hcomm, hexp⟩, hcard⟩

theorem two_le_pRank_of_prod {A B X : Type} [Group A] [Group B] [Group X] [Finite A] [Finite B]
    [Finite X] {p : ℕ} [hp : Fact p.Prime] (hA : p ∣ Nat.card A) (hB : p ∣ Nat.card B)
    (φ : A × B →* X) (hφ : Function.Injective φ) {C : Subgroup X} (hC : φ.range ≤ C) :
    2 ≤ CFSG.Open.pRank p C := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hA
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p hB
  obtain ⟨hE, hcard⟩ := two_le_pRank_of_prod_aux1 ha hb
  have hmapE := K21bTransProof.isElemAbelian_map_inj hφ hE
  have hcardmap : Nat.card (((Subgroup.zpowers a).prod (Subgroup.zpowers b)).map φ) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hφ]
    exact hcard
  have hle : ((Subgroup.zpowers a).prod (Subgroup.zpowers b)).map φ ≤ C := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact hC ⟨x, rfl⟩
  have hmem : (2 : ℕ) ∈ {k | ∃ E : Subgroup X, E ≤ C ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k} :=
    ⟨_, hle, hmapE, hcardmap⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup X, E ≤ C ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨E, -, -, hk⟩
    have h1 : p ^ k ≤ Nat.card X := hk ▸ Subgroup.card_le_card_group E
    exact (Nat.lt_pow_self hp.out.one_lt).le.trans h1
  exact le_csSup hbdd hmem

end K421SpRkProof

end CFSG.LocalAnalysis.RankThreeUC.S15
