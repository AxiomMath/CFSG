module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.E9Transitive.Proj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndexResidue
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.E9Transitive

open CFSG.Open CFSG.AGLEmbedding

section Generic

variable {Q : Type*} [Group Q]

theorem card_map_subgroupOf_dvd {Lb P : Subgroup Q} (hPL : P ≤ Lb) :
    Nat.card ((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))) ∣
      Nat.card P := by
  have h := Subgroup.card_map_dvd (H := P.subgroupOf Lb)
    (QuotientGroup.mk' (Subgroup.center ↥Lb))
  rwa [show Nat.card (P.subgroupOf Lb) = Nat.card P from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv] at h

theorem mem_normalizer_inf {A B : Subgroup Q} {x : Q}
    (hA : x ∈ Subgroup.normalizer (A : Set Q)) (hB : x ∈ Subgroup.normalizer (B : Set Q)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  exact ⟨fun hy => ⟨(hA y).mp hy.1, (hB y).mp hy.2⟩,
    fun hy => ⟨(hA y).mpr hy.1, (hB y).mpr hy.2⟩⟩

theorem not_three_dvd_index_of_card {A J : Subgroup Q} (hAJ : A ≤ J) (hA : Nat.card A = 9)
    (hJ : ¬ 27 ∣ Nat.card J) : ¬ 3 ∣ (A.subgroupOf J).index := by
  intro h3
  apply hJ
  have h := Subgroup.card_mul_index (A.subgroupOf J)
  rw [show Nat.card (A.subgroupOf J) = Nat.card A from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv, hA] at h
  rw [← h]
  exact Nat.mul_dvd_mul_left 9 h3

variable [Finite Q]

theorem not_twentySeven_dvd_card {P K : Subgroup Q} (hPK : P ≤ K)
    (hel : ∀ T : Subgroup Q, T ≤ P → IsPGroup 3 T → Open.IsElemAbelian 3 T)
    (hrk : Open.pRank 3 K ≤ 2) : ¬ 27 ∣ Nat.card P := by
  intro h27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T₀, hT₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) 3 (n := 3)
    (by norm_num; exact h27)
  have hTc : Nat.card (T₀.map P.subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hT₀]
  have hTP : T₀.map P.subtype ≤ P := Subgroup.map_subtype_le T₀
  have hT3 : IsPGroup 3 (T₀.map P.subtype) := IsPGroup.of_card hTc
  have h3 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (hTP.trans hPK) (hel _ hTP hT3) hTc
  omega

end Generic

theorem not_nine_dvd_of_perm {P : Type*} [Group P] [Finite P] {n : ℕ} (hn : n ≤ 4)
    (e : P ⧸ CFSG.pCore 2 P ≃* Equiv.Perm (Fin n)) : ¬ 9 ∣ Nat.card P := by
  intro h9
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := P))
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 P)
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin, hk] at hcard
  rw [hcard] at h9
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have h9' := hcop.dvd_of_dvd_mul_right h9
  interval_cases n <;> simp [Nat.factorial] at h9' <;> omega

section Block

variable {G : Type} [Group G] {M S L : Subgroup G}

theorem range_le_block {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hQS : pCoreOf 2 M ≤ S)
    (hEL : E ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hEK : E ≤ barM M (Subgroup.normalizer (S : Set G)))
    (hCK : Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G))) :
    (projHom hEL).range ≤ ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
      (barM M L)).map (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) :=
  range_projHom_le hEL hEK hCK (CFSG.AGLEmbeddingD2.McLaughlin.barM_normalizer_inf_eq hQS).ge

end Block

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.E9Transitive
