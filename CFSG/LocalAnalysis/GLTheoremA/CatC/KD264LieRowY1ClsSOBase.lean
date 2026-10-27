module

public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourLin
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourOrth
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1Pieces

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Open.StatedAPI CFSG.Models CFSG.Yardstones.Md0ec50421ce4

theorem statedClassical_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (hn : n ≠ 0) : StatedClassicalModel G t n p f :=
  h.2.resolve_right fun h0 => hn h0.1

theorem characteristic_ne_three_of_not_chev (d : TauCeti.ValidLieTypeIndex)
    (h : ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group) : d.1.characteristic ≠ 3 := by
  intro hc
  apply h
  unfold IsChevSimple catalogIs
  exact Or.inl ⟨TauCeti.CFSGIndex.lie d, hc, ⟨MulEquiv.refl _⟩⟩

theorem pRank_le_two_of_psp_two {G : Type} [Group G] [Finite G] {p f : ℕ}
    (hC : StatedClassicalModel G .PSp 2 p f) (h3 : p ≠ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2 := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have h3K : (3 : K) ≠ 0 := by
    intro h
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h)
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd)
  have hN : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) :=
    not_dvd_card_statedScalars_subgroupOf (StatedSp 2 K) (p := 3) (d := 2) Nat.prime_three
      (by norm_num) fun c hc => (scalar_mem_statedSp_iff (by norm_num) c).1 hc
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e,
    CFSG.SectionRank.pRank_quotient_eq _ hN]
  apply CFSG.SectionRank.pRank_le (p := 3) (by norm_num)
  intro E _ hE
  have := CFSG.StandardType.SpJoin.card_le_pow_of_isElemAbelian (F := K) Nat.prime_three
    (by norm_num) (by simpa using h3K) E hE
  simpa using this

theorem four_le_pRank_of_psp {G : Type} [Group G] [Finite G] {n p f : ℕ} (hn : 4 ≤ n)
    (hC : StatedClassicalModel G .PSp n p f) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hC
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.four_le_pRank_projSp_of_four_le
    hn

theorem pRank_le_two_of_B2 {G : Type} [Group G] [Finite G] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) (hq : q.p ≠ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2 := by
  rcases lieModel_B 2 q hv e with h | h
  · exact pRank_le_two_of_psp_two (statedClassical_of_lieModel h (by norm_num)) hq
  · exfalso
    have hadm := h.1
    have h32 : 3 ≤ 2 := hadm.2.2.1
    omega

theorem four_le_pRank_of_B {G : Type} [Group G] [Finite G] (n : ℕ) (q : TauCeti.PrimePower)
    (hn : 4 ≤ n) (hv : (TauCeti.LieTypeIndex.B n q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B n q, hv⟩) (hq : q.p ≠ 3) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  rcases lieModel_B n q hv e with h | h
  · exact four_le_pRank_of_psp hn (statedClassical_of_lieModel h (by omega))
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.four_le_pRank_three_orth
      (statedClassical_of_lieModel h (by omega)) (Or.inl ⟨rfl, hn⟩) hq

theorem four_le_pRank_of_C {G : Type} [Group G] [Finite G] (n : ℕ) (q : TauCeti.PrimePower)
    (hn : 4 ≤ n) (hv : (TauCeti.LieTypeIndex.C n q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.C n q, hv⟩) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
  four_le_pRank_of_psp hn (statedClassical_of_lieModel (lieModel_C n q hv e) (by omega))

theorem four_le_pRank_of_D {G : Type} [Group G] [Finite G] (n : ℕ) (q : TauCeti.PrimePower)
    (hn : 4 ≤ n) (hv : (TauCeti.LieTypeIndex.D n q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D n q, hv⟩) (hq : q.p ≠ 3) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.four_le_pRank_three_orth
    (statedClassical_of_lieModel (lieModel_D n q hv e) (by omega))
    (Or.inr (Or.inl ⟨rfl, hn⟩)) hq

theorem four_le_pRank_of_twistedD {G : Type} [Group G] [Finite G] (n : ℕ) (q : TauCeti.PrimePower)
    (hn : 5 ≤ n) (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedD n q, hv⟩) (hq : q.p ≠ 3) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.four_le_pRank_three_orth
    (statedClassical_of_lieModel (lieModel_twistedD n q hv e) (by omega))
    (Or.inr (Or.inr ⟨rfl, hn⟩)) hq

theorem fam_of_B3 {e : TauCeti.LieTypeIndex} (h : KD264Y1FamB3 e) : KD264Y1Fam e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem fam_of_C3 {e : TauCeti.LieTypeIndex} (h : KD264Y1FamC3 e) : KD264Y1Fam e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem fam_of_D4 {e : TauCeti.LieTypeIndex} (h : KD264Y1FamD4 e) : KD264Y1Fam e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
