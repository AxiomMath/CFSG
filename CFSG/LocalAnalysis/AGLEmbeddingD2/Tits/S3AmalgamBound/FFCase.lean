module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFTrivial
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.CyclicSylowNormal

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_of_sylow_eq_bot {X : Type*} [Group X] [Finite X] (S : Sylow 3 X)
    (hS : (S : Subgroup X) = ⊥) : ¬ 3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Sylow.card_eq_multiplicity S
  rw [hS, Subgroup.card_bot] at h
  intro hd
  have h3 : (Nat.card X).factorization 3 ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hd).ne'
  have := Nat.pow_eq_one.1 h.symm
  omega

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.exists_normal_order_three_of_ff_case3
    {M T : Subgroup G} (hK : CFSG.Open.IsKGroup ↥M)
    (hF : CharTwo M) (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) (hI59 : AGL81I59)
    (hT : IsSylowTwoOf T M)
    (hTh : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G) → ¬ 3 ∣ Nat.card ↥(ffC M T) → False)
    (hr2 : FFRankTwoCase M T)
    (hSolv : ∀ S : Sylow 3 ↥(ffC M T),
      IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) →
        CFSG.HallHigman.IsPSolvable 3 ↥(ffC M T))
    (hnc : ∀ S : Sylow 3 ↥(ffC M T),
      ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) →
      ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
        ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal) :
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := conjClosure (quasithinOmegaOneCenter T) M with hV
  obtain ⟨hU, -⟩ := B2_15 hF hT
  have hMN : M ≤ Subgroup.normalizer (V : Set G) :=
    (conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)).2.2.2.1
  have hCM : ffC M T ≤ M := inf_le_right
  have hCn : ((ffC M T).subgroupOf M).Normal := centralizer_inf_subgroupOf_normal hU hMN
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥(ffC M T)))
  set D : Subgroup G := (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype with hD
  by_cases hD0 : D = ⊥
  · have hS0 : (S : Subgroup ↥(ffC M T)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (x : G) ∈ D := ⟨x, hx, rfl⟩
      rw [hD0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T) := not_dvd_card_of_sylow_eq_bot S hS0
    by_cases hJ : thompsonJ T ≤ Subgroup.centralizer
        (conjClosure (quasithinOmegaOneCenter T) M : Set G)
    · exact (hTh hJ hC3).elim
    · exact exists_normal_order_three_of_coprime_centralizer hK hF hcon hI59 hT hJ hC3 hr2
  · by_cases hDc : IsCyclic ↥D
    · obtain ⟨P₀, hP₀D, hP₀, hnorm⟩ :=
        CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_normal_order_three_of_cyclic_sylow
          (M := M) (C := ffC M T) (D := D) hCM hCn (hSolv S hDc) ⟨S, rfl⟩ hDc hD0
      exact ⟨P₀, hP₀D.trans ((Subgroup.map_subtype_le _).trans hCM), hP₀, hnorm⟩
    · exact hnc S hDc

theorem exists_normal_order_three_of_ff_case {M T : Subgroup G} (hK : IsKGroup ↥M)
    (hF : CharTwo M) (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) (hI59 : AGL81I59)
    (hT : IsSylowTwoOf T M)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G))
    (hr2 : FFRankTwoCase M T)
    (hSolv : ∀ S : Sylow 3 ↥(ffC M T),
      IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) →
        CFSG.HallHigman.IsPSolvable 3 ↥(ffC M T))
    (hnc : ∀ S : Sylow 3 ↥(ffC M T),
      ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) → False) :
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal :=
  CFSG.LocalAnalysis.RankThreeTheoremC.exists_normal_order_three_of_ff_case3 hK hF hcon hI59 hT
    (fun h _ => hJ h) hr2 hSolv fun S hS => (hnc S hS).elim

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
