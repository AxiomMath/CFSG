module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section MSide

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem coprime_card_preimage_pCore {s : ℕ} (hs : s.Prime) (hp : p.Prime) (hsp : s ≠ p)
    (hp2 : p ≠ 2) : p.Coprime (Nat.card (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)) := by
  have := Fact.mk hs
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set W := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)
  rw [Subgroup.card_map_of_injective M.subtype_injective]
  have h1 := Subgroup.relIndex_mul_relIndex ⊥ π.ker (W.comap π) bot_le (π.ker_le_comap W)
  have h2 : π.ker.relIndex (W.comap π) = Nat.card W := by
    rw [← MonoidHom.comap_bot, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.relIndex_bot_left]
  rw [h2, Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, QuotientGroup.ker_mk'] at h1
  rw [← h1]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := s) (G := ↥M ⧸ CFSG.pCore 2 ↥M))
  rw [ha, hb]
  exact Nat.Coprime.mul_right
    (Nat.Coprime.pow_right a ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
    (Nat.Coprime.pow_right b ((Nat.coprime_primes hp hs).mpr (Ne.symm hsp)))

theorem D1PhaseThree.false_of_four_le_pRank_of_primeCore (h3 : D1PhaseThree p P M H R)
    (hpc : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p)
    (h4 : 4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)) : False := by
  have hp : p.Prime := h3.prime
  have := Fact.mk hs
  set Sh : Subgroup G := ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype with hSh
  have hShK : Sh ≤ H ⊓ M := h3.preimage_le_inf (h3.le_barM_inf_of_le_centralizer
    ((pCore_le_pPrimeCore_two hs hs2).trans (h3.oddCore_le_centralizer h84 hD2)))
  have hShn : H ⊓ M ≤ Subgroup.normalizer (Sh : Set G) :=
    inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le _)).mp (normal_preimage_subgroupOf _))
  have hShN : Sh ≤ GLBPrimeCore p H := by
    rw [← hpc]
    exact le_glbPrimeCore hShK hShn (coprime_card_preimage_pCore hs hp hsp h3.ne_two)
  exact h3.false_of_preimage_le hs hs2
    (mem_glbBetaFour_of_le_pRank hs hs2 h3.maxTwoLocal_M.1 (Subgroup.map_subtype_le _) h4)
    CFSG.pCore_isPGroup ((by norm_num : 3 ≤ 4).trans h4) (glbPrimeCore_le p H)
    (le_normalizer_glbPrimeCore p H) h3.primeCore_le hShN

theorem D1OneLieData.false_of_four_le_pRank (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsp : s ≠ p)
    (h4 : 4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)) : False :=
  (hd.toPhaseThree hK).false_of_four_le_pRank_of_primeCore (hd.primeCore_inf_eq hK) h84 hD2 hs
    hs2 hsp h4

theorem D1CompCore.le_centralizer_pCore (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hd : D1CompCore p P M H R Rbar K)
    (hYX : pCorePreimage p M ⊓ d1LiftX p H R K = ⊥) :
    barM M (d1LiftX p H R K) ≤ Subgroup.centralizer
      ((CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hYH : pCorePreimage p M ≤ H := (h3.pCorePreimage_le_inf h84 hD2).trans inf_le_left
  obtain ⟨-, hWR, hWn, -, hWiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  have hKn : K.Normal := hd.red.normal_of_rankOne hd.comp hd.noncyclic
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set W := d1MapPCore p M H with hW
  set T : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K with hT
  have hWT : W ⊓ T = ⊥ := by
    by_contra hne
    exact hWiff.mpr hne hYX
  have hcomm : ∀ w ∈ W, ∀ t ∈ T, w * t * w⁻¹ * t⁻¹ = 1 := by
    intro w hw t ht
    have hwT : w ∈ Subgroup.normalizer (T : Set (H ⧸ primeComplementCore (G := H) p)) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hWR hw),
        (Subgroup.normalizer_eq_top (H := K)).ge (Subgroup.mem_top w)⟩
    have htW : t ∈ Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) :=
      hWn ⟨ht.2, Subgroup.le_normalizer ht⟩
    have h1 : w * t * w⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.mp hwT t).mp ht) (T.inv_mem ht)
    have h2 : w * t * w⁻¹ * t⁻¹ ∈ W := by
      have h := (Subgroup.mem_normalizer_iff.mp htW w⁻¹).mp (W.inv_mem hw)
      rw [show w * t * w⁻¹ * t⁻¹ = w * (t * w⁻¹ * t⁻¹) by group]
      exact W.mul_mem hw h
    have h12 : w * t * w⁻¹ * t⁻¹ ∈ W ⊓ T := ⟨h2, h1⟩
    rw [hWT] at h12
    exact Subgroup.mem_bot.mp h12
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro ybar hybar
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) ybar
  have hyY : (y : G) ∈ pCorePreimage p M := ⟨y, hybar, rfl⟩
  have hyH : (y : G) ∈ H := hYH hyY
  have hxX : (x : G) ∈ d1LiftX p H R K := hx
  have hxH : (x : G) ∈ H := d1LiftX_le_H p H R K hxX
  have hc1 : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ pCorePreimage p M := by
    have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCorePreimage p M x.2) _).mp
      ((pCorePreimage p M).inv_mem hyY)
    rw [show (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ = y * (x * (y : G)⁻¹ * (x : G)⁻¹) by group]
    exact (pCorePreimage p M).mul_mem hyY h
  have hc2 : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ GLBPrimeCore p H := by
    have hπy : π ⟨y, hyH⟩ ∈ W := ⟨⟨y, hyH⟩, hyY, rfl⟩
    have hπx : π ⟨x, hxH⟩ ∈ T := by
      rw [hT, ← hd.map_d1LiftX_eq_inf]
      exact ⟨⟨x, hxH⟩, hxX, rfl⟩
    have h := hcomm _ hπy _ hπx
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h
    exact (mk'_primeComplementCore_eq_one_iff p _).mp h
  have hc : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 M :=
    h3.pCorePreimage_inf_le ⟨hc1, hc2⟩
  have h1 := (mk_eq_one_iff_coe_mem_pCoreOf (y * x * y⁻¹ * x⁻¹)).mpr (by simpa using hc)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem D1OneLieData.le_centralizer_pCore (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hYX : pCorePreimage p M ⊓ d1LiftX p H R K = ⊥) :
    barM M (d1LiftX p H R K) ≤ Subgroup.centralizer
      ((CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  hd.toCore.le_centralizer_pCore (hd.toPhaseThree hK) h84 hD2 hYX

theorem d1OneLieMSide_of_core (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hcore : D1OneLieMSideCore) : D1OneLieMSide := by
  intro G _ _ p P M H R Rbar K hd huniq hYX
  obtain ⟨X₁, hX₁X, hX₁, hcomp, hodd⟩ := hcore G p P M H R Rbar K hd huniq
  have hX₁p : IsPGroup p (barM M X₁) :=
    ((hd.cfg.ext.isPGroup.to_le (hX₁X.trans (d1LiftX_le p H R K))).comap_subtype).map _
  have hcen : barM M X₁ ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
    refine le_pCore_of_le_centralizer_components hX₁p hcomp fun l hl => ?_
    by_cases hl2 : l = 2
    · rw [hl2, pCore_quotient_pCore_eq_bot']
      exact Subgroup.le_centralizer_iff.mp bot_le
    by_cases hlp : l = p
    · rw [hlp]
      exact (Subgroup.map_mono (Subgroup.comap_mono hX₁X)).trans
        (hd.le_centralizer_pCore hK h84 hD2 (eq_bot_iff.mpr (le_of_eq hYX)))
    rcases hodd l hl hl2 hlp with h | h
    · exact h
    · exact (hd.false_of_four_le_pRank hK h84 hD2 hl hl2 hlp h).elim
  apply hX₁
  rw [eq_bot_iff, ← hYX]
  refine le_inf (fun x hx => ?_) hX₁X
  have hxM : x ∈ M := (d1LiftX_le p H R K).trans hd.cfg.ext.le_M (hX₁X hx)
  exact ⟨⟨x, hxM⟩, hcen ⟨⟨x, hxM⟩, hx, rfl⟩, rfl⟩

end MSide

end CFSG.AGLEmbedding
