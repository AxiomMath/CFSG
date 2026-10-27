module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs
public import CFSG.LocalAnalysis.AGLEmbedding.G28InSituAux
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Orbit
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOneAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Pkg

variable {G : Type} [Group G] [Finite G]

structure D1Sp48Data₂ (P : Sylow 3 G) (M H R X U A : Subgroup G) : Prop
    extends D1Sp48Data P M H R X U A where
  center_le : centerOf R ≤ X

@[expose] def StmtSp48MSide₂ : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A : Subgroup G},
    D1Sp48Data₂ P M H R X U A → CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

variable {P : Sylow 3 G} {M H R X U A : Subgroup G}

theorem D1Sp48Data₂.coprime_of_perfect (h : D1Sp48Data₂ P M H R X U A)
    {W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hW : W ≤ barM M (H ⊓ M)) (hWW : ⁅W, W⁆ = W) :
    Nat.Coprime 3 (Nat.card W) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Q₀ := (H ⊓ M).subgroupOf M ⊓ W.comap mk with hQ₀
  have hQmap : Q₀.map mk = W := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · intro w hw
      obtain ⟨k, hk, rfl⟩ := hW hw
      exact ⟨k, ⟨hk, hw⟩, rfl⟩
  obtain ⟨P', hP'Q, hP'P, hP'map⟩ := exists_perfect_le_map_eq' mk hQmap hWW
  have hP'K : P'.map M.subtype ≤ H ⊓ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hP'Q hx).1
  have hP'N := h.perfect_le _ hP'K (by rw [← Subgroup.map_commutator, hP'P])
  have hWN : W ≤ barM M (GLBPrimeCore 3 H) := by
    rw [← hP'map]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hP'N ⟨x, hx, rfl⟩))
  exact Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le hWN).trans
    (card_barM_dvd h.surv.ph3.primeCore_le)) (glbPrimeCore_coprime 3 H)

theorem D1Sp48Data₂.isSylowOf_Pi (h : D1Sp48Data₂ P M H R X U A) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IsSylowOf 3 (R ⊓ ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L))
      ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) := by
  have h3 := h.surv.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRH : IsSylowOf 3 R H := h3.isSylow
  exact (hRH.of_le h3.le_inf inf_le_left).inf_of_le_normalizer inf_le_left
    (h3.mem_Pi' hB3 hL).1

theorem pow_dvd_card_of_isSylowOf {Pi Q : Subgroup G} (hS : IsSylowOf 3 Q Pi) {b : ℕ}
    (hb : 3 ^ b ∣ Nat.card Pi) : 3 ^ b ∣ Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [isSylowOf_iff] at hS
  obtain ⟨hle, -, hidx⟩ := hS
  have hmul := Subgroup.relIndex_mul_relIndex ⊥ Q Pi bot_le hle
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at hmul
  rw [← hmul] at hb
  exact (Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    hidx)).dvd_of_dvd_mul_right hb

theorem D1Sp48Data₂.card_dvd_of_le_barPi (h : D1Sp48Data₂ P M H R X U A) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hB : B ≤ barM M ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L)) (hB3' : IsPGroup 3 B) :
    Nat.card B ∣ Nat.card (R ⊓ ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) : Subgroup G) := by
  obtain ⟨b, hb⟩ := hB3'.exists_card_eq
  rw [hb]
  refine pow_dvd_card_of_isSylowOf (h.isSylowOf_Pi hB3 hL) ?_
  rw [← hb]
  exact (Subgroup.card_dvd_of_le hB).trans (card_barM_dvd (inf_le_left.trans inf_le_right))

theorem D1Sp48Data₂.Pi_cases (h : D1Sp48Data₂ P M H R X U A) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    X ≤ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ∧
    (R ⊓ ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) = X ∨
      R ⊓ ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) = A ∨
      R ⊓ ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) = U ∨
      R ⊓ ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) = R) := by
  have h3 := h.surv.ph3
  have hXPi : X ≤ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L :=
    le_inf (h.surv.le_R.trans h3.le_inf) (h.surv.le_blockClosure rfl hL (hB3 h3 hL))
  exact ⟨hXPi, h.sylow_normal _ inf_le_left (h3.mem_Pi' hB3 hL).1 hXPi⟩

end Pkg

end CFSG.AGLEmbedding
