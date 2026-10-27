module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34TwoCoreBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GoldschmidtPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Only

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def IsS3Parabolic (T I : Subgroup G) : Prop :=
  IsSylowTwoOf T I ∧ Nonempty (↥I ⧸ Open.pCore 2 ↥I ≃* Equiv.Perm (Fin 3))

@[expose] def IsBetaBase (H M U : Subgroup G) : Prop :=
  IsPGroup 2 U ∧ pCoreOf 2 H ≤ U ∧
    U ≤ (primeComplementCore (G := H) 3).map H.subtype ⊔ pCoreOf 2 (H ⊓ M) ∧
    ¬ U ≤ (primeComplementCore (G := H) 3).map H.subtype

@[expose] def D2L34BetaHPara : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    ∀ U : Subgroup G, IsBetaBase H M U →
      ∃ Y : Subgroup G, Y ≤ H ∧ ¬ Y ≤ M ∧ Nat.card Y = 3 ∧ IsS3Parabolic U (U ⊔ Y)

@[expose] def D2L34BetaMSide : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    D2L34AllResidue P M →
    GLBStronglyEmbedded 3 M ∧ ∃ U Q : Subgroup G, IsBetaBase H M U ∧ Q ≤ M ∧ Nat.card Q = 3 ∧
      IsS3Parabolic U (U ⊔ Q) ∧ ∀ g : G, ¬ Q.map (MulAut.conj g).toMonoidHom ≤ H

@[expose] def D2L34BetaCoreFree : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2OnlyL34At P M →
    ∀ U Y Q : Subgroup G, IsBetaBase H M U → Y ≤ H → ¬ Y ≤ M → Nat.card Y = 3 →
      IsS3Parabolic U (U ⊔ Y) → Q ≤ M → Nat.card Q = 3 → IsS3Parabolic U (U ⊔ Q) →
      (∀ g : G, ¬ Q.map (MulAut.conj g).toMonoidHom ≤ H) →
      pCoreOf 2 ((U ⊔ Y) ⊔ (U ⊔ Q)) = ⊥

theorem D2Escape.primeComplementCore_le_inf {P : Sylow 3 G} {M A H R : Subgroup G}
    (h : D2Escape 3 P M A H R) : primeComplementCore (G := H) 3 ≤ (H ⊓ M).subgroupOf H := by
  rw [← glbPrimeCore_subgroupOf]
  exact glbPrimeCore_subgroupOf_le_inf h.primeCore_le

theorem IsS3Parabolic.eq_or_eq {T I J : Subgroup G} (h : IsS3Parabolic T I) (hTJ : T ≤ J)
    (hJI : J ≤ I) : J = T ∨ J = I := by
  have h3 : T.relIndex I = 3 := F6.GoldPair.relIndex_eq_three h.2 h.1
  have hmul := Subgroup.relIndex_mul_relIndex T J I hTJ hJI
  rw [h3] at hmul
  rcases (Nat.prime_mul_iff.mp (hmul ▸ Nat.prime_three)) with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact Or.inr (le_antisymm hJI (Subgroup.relIndex_eq_one.mp h1))
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hTJ)

theorem d2L34BetaResidueU_of_amalgam
    (hHP : D2L34BetaHPara) (hMS : D2L34BetaMSide) (hCF : D2L34BetaCoreFree) :
    D2L34BetaResidueU := by
  intro d G _ _ P M A H R Rbar K hc hAll
  obtain ⟨hstr, U, Q, hU, hQM, hQ3, hQpar, hQconj⟩ := hMS d G P M A H R Rbar K hc hAll
  obtain ⟨Y, hYH, hYM, hY3, hYpar⟩ := hHP d G P M A H R Rbar K hc U hU
  have hcore := hCF d G P M A H R Rbar K hc hstr hAll.onlyL34At U Y Q hU hYH hYM hY3 hYpar hQM
    hQ3 hQpar hQconj
  have hWM : (primeComplementCore (G := H) 3).map H.subtype ≤ M := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp (hc.esc.primeComplementCore_le_inf hw)).2
  have hT₀M : pCoreOf 2 (H ⊓ M) ≤ M :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_right
  have hUM : U ≤ M := hU.2.2.1.trans (sup_le hWM hT₀M)
  have hmeet : (U ⊔ Y) ⊓ (U ⊔ Q) = U := by
    rcases hYpar.eq_or_eq (le_inf le_sup_left le_sup_left) inf_le_left with h | h
    · exact h
    · exfalso
      apply hYM
      have hle : U ⊔ Y ≤ U ⊔ Q := h ▸ inf_le_right
      exact le_sup_right.trans (hle.trans (sup_le hUM hQM))
  have hpair : F6.IsGoldschmidtVPair (U ⊔ Y) (U ⊔ Q) :=
    ⟨hYpar.2, hQpar.2, by rw [hmeet]; exact hYpar.1, by rw [hmeet]; exact hQpar.1, hcore⟩
  have hgold := card_inf_le_two_pow_seven_of_vPair hpair
  rw [hmeet] at hgold
  have hS := hc.esc.two_pow_eight_le_card_twoCore_of_l34 hc.glob.toAGLGlobal hc.l34 hc.iso hc.le_K
  have hSU : Nat.card (pCoreOf 2 H) ≤ Nat.card U := Subgroup.card_le_of_le hU.2.1
  omega


end CFSG.AGLEmbeddingD2
