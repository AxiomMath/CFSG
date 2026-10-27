module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.L54
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Borel
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CentC

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_two_group_le_centralizer_layer [Fact p.Prime] (hG : FrobGlobal G)
    (hl : FrobLocal p P M x) {W : Subgroup G} (hW2 : IsPGroup 2 W)
    (hWZ : W ≤ centralizer ((layerOf x : Subgroup G) : Set G)) : W = ⊥ := by
  have hodd := fr_centralizer_layer_odd hG hl
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW2
  have hdvd : Nat.card W ∣ Nat.card (centralizer ((layerOf x : Subgroup G) : Set G)) :=
    Subgroup.card_dvd_of_le hWZ
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ Nat.card (centralizer ((layerOf x : Subgroup G) : Set G)) :=
      (hk ▸ dvd_pow_self 2 hne).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.mp hk

theorem fr_cT_eq_bot [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {w : G} (hw1 : w ≠ 1) (hwZ : w ∈ centralizer ((layerOf x : Subgroup G) : Set G))
    (hcase : IsSylowOf p (frU P x) (centralizer ({w} : Set G)) ∨ x ∈ centralizer ({w} : Set G)) :
    CFSG.Open.pCoreOf 2 M ⊓ centralizer ({w} : Set G) = ⊥ := by
  have hp2 : p ≠ 2 := by have := hl.p5; omega
  set W : Subgroup G := CFSG.Open.pCoreOf 2 M ⊓ centralizer ({w} : Set G) with hW
  have hT2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMT : M ≤ normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hW2 : IsPGroup 2 W := hT2.to_le inf_le_left
  have hWp : Nat.Coprime p (Nat.card W) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW2
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2)
  have hUW : frU P x ≤ normalizer (W : Set G) := fun u hu =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hMT (frU_le_M hl hu),
      le_normalizer (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hwZ u hu.2))⟩
  have hLN : layerOf x ≤ centralizer ({w} : Set G) := fun l hl' =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hwZ l hl')
  have hzp : zpowers w ≠ ⊥ := fun h => hw1 (Subgroup.zpowers_eq_bot.mp h)
  have hNtop : centralizer ({w} : Set G) ≠ ⊤ := by
    obtain ⟨hn, -⟩ := fr_normalizer_ne_top hG hl hzp (zpowers_le.mpr hwZ)
    intro htop
    refine hn (top_le_iff.mp ?_)
    rw [← htop, ← centralizer_zpowers_eq]
    exact centralizer_le_normalizer _
  have hW1 := fr_L54_N hK hG hl hNtop hLN hcase hWp inf_le_right hUW
  exact fr_two_group_le_centralizer_layer hG hl hW2 hW1

theorem fr_fpf [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    ∀ f ∈ CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G)), f ≠ 1 →
      ∀ t ∈ CFSG.Open.pCoreOf 2 M, t * f = f * t → t = 1 := by
  intro f hf hf1 t ht htf
  have hfZ : f ∈ centralizer ((layerOf x : Subgroup G) : Set G) :=
    fr_primeCore_le_centralizer_layer hG hl hf
  have hfx : x ∈ centralizer ({f} : Set G) := by
    have h := mem_centralizer_singleton_iff.mp
      (CFSG.AGLEmbedding.glbPrimeCore_le p (centralizer ({x} : Set G)) hf)
    exact mem_centralizer_singleton_iff.mpr h.symm
  have hbot := fr_cT_eq_bot hK hG hl hf1 hfZ (Or.inr hfx)
  have htW : t ∈ CFSG.Open.pCoreOf 2 M ⊓ centralizer ({f} : Set G) :=
    ⟨ht, mem_centralizer_singleton_iff.mpr htf⟩
  rw [hbot, mem_bot] at htW
  exact htW

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
