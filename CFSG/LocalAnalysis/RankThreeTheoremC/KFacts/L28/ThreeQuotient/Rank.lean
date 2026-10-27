module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Shape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient

open CFSG.Open Subgroup

theorem exists_conj_le {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (S : Sylow p X) {F : Subgroup X} (hF : IsPGroup p F) :
    ∃ g : X, ∀ f ∈ F, g * f * g⁻¹ ∈ (S : Subgroup X) := by
  obtain ⟨S', hFS'⟩ := hF.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' S
  refine ⟨g, fun f hf => ?_⟩
  have hgS : ((g • S' : Sylow p X) : Subgroup X) =
      (S' : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [← hg, hgS]
  exact ⟨f, hFS' hf, rfl⟩

theorem exists_sylow_eq_of_isSylowOf_top {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {Q : Subgroup X} (hQ : CFSG.ABGLocalTools.IsSylowOf p Q ⊤) :
    ∃ S : Sylow p X, (S : Subgroup X) = Q := by
  have hcard : Nat.card Q = p ^ (Nat.card X).factorization p := by
    rw [hQ.card_eq, Subgroup.card_top]
  exact ⟨Sylow.ofCard Q hcard, Sylow.coe_ofCard _ _⟩

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_of_isElemAbelian {F : Subgroup X} (hF : IsElemAbelian 3 F) : IsPGroup 3 F :=
  fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩

namespace ShapeData

variable {Q₀ : Subgroup X}

theorem card_le_of_isElemAbelian_of_sylow (S : Sylow 3 X) (hD : ShapeData (S : Subgroup X) Q₀)
    {F : Subgroup X} (hF : IsElemAbelian 3 F) : Nat.card F ≤ 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_le S (isPGroup_of_isElemAbelian hF)
  have hle : F.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup X) := by
    rintro _ ⟨f, hf, rfl⟩
    simpa [MulAut.conj_apply] using hg f hf
  have h := hD.card_le_of_isElemAbelian hle (CFSG.SectionRank.isElemAbelian_map hF _)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h

theorem pRank_le_three (S : Sylow 3 X) (hD : ShapeData (S : Subgroup X) Q₀) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 :=
  CFSG.SectionRank.pRank_le (by norm_num) fun _ _ hF =>
    (hD.card_le_of_isElemAbelian_of_sylow S hF).trans (by norm_num)

end ShapeData

theorem not_le_commutator_of_normal_index {p : ℕ} [Fact p.Prime] (S : Sylow p X)
    (N : Subgroup X) [N.Normal] (hidx : ∃ k : ℕ, N.index = p ^ k) (hN : N ≠ ⊤) :
    ¬ (S : Subgroup X) ≤ ⁅(⊤ : Subgroup X), ⊤⁆ := by
  intro hS
  obtain ⟨k, hk⟩ := hidx
  have hp : p.Prime := Fact.out
  have hSN : (S : Subgroup X) ⊔ N = ⊤ := by
    have h1 : ((S : Subgroup X) ⊔ N).index ∣ (S : Subgroup X).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h2 : ((S : Subgroup X) ⊔ N).index ∣ p ^ k := hk ▸ Subgroup.index_dvd_of_le le_sup_right
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h2
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact Subgroup.index_eq_one.1 hj
    · exfalso
      apply S.not_dvd_index
      rw [hj] at h1
      exact (dvd_pow_self p (Nat.succ_ne_zero j)).trans h1
  have hcard : Nat.card (X ⧸ N) = p ^ k := by rw [← Subgroup.index_eq_card, hk]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hN (Subgroup.index_eq_one.1 hk)
  haveI : Nontrivial (X ⧸ N) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow hk0 hp.one_lt
  haveI : Group.IsNilpotent (X ⧸ N) := (IsPGroup.of_card hcard).isNilpotent
  have hsurj := QuotientGroup.mk'_surjective N
  have htop : (S : Subgroup X).map (QuotientGroup.mk' N) = ⊤ := by
    have h1 : ((S : Subgroup X) ⊔ N).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hSN]
      exact Subgroup.map_top_of_surjective _ hsurj
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
  have hcomm : commutator (X ⧸ N) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← htop, commutator_def]
    calc (S : Subgroup X).map (QuotientGroup.mk' N) ≤
          Subgroup.map (QuotientGroup.mk' N) ⁅(⊤ : Subgroup X), ⊤⁆ := Subgroup.map_mono hS
      _ = ⁅(⊤ : Subgroup X).map (QuotientGroup.mk' N), (⊤ : Subgroup X).map
          (QuotientGroup.mk' N)⁆ := Subgroup.map_commutator _ _ _
      _ = ⁅(⊤ : Subgroup (X ⧸ N)), ⊤⁆ := by rw [Subgroup.map_top_of_surjective _ hsurj]
  exact (IsSolvable.commutator_lt_top_of_nontrivial (X ⧸ N)).ne hcomm

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient
