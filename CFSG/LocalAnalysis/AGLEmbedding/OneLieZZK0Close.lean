module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Plus
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieKMax

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieKZeroData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem false_of_kZeroMax (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S) (hK : KFactOneLie)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    (hcon : ¬ HasPrimeConstraint (G := H₁) p)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hL : IsComponentOf L ⊤)
    (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L)
    (hZ : Subgroup.center L = ⊥) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩)
    (hmax : ∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → nclIn H (d1LiftX p H R K) ≤ H₂ →
      pCoreOf 2 M ≤ H₂ →
      Nat.card (nclIn H₂ (d1LiftX p H R K)) ≤ Nat.card (nclIn H₁ (d1LiftX p H R K))) :
    False := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set X := d1LiftX p H R K with hXdef
  set N := d1PlusCore p H₁ L with hNdef
  have h3₁ := hc.toPhaseThree hK hcon hL hLn hJL hZ ψ hψ
  have hXH₁ : X ≤ H₁ := hc.liftX_le_H₁
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  obtain ⟨hNHM, hH₁N, hON⟩ := hc.plusCore_facts hLn hJL hZ
  have hNH₁ : N ≤ H₁ := hNHM.trans inf_le_left
  obtain ⟨hND, hNJ⟩ := hc.plusCore_le_and_commutator hK h84 hD2 hY hWK h3₁ hL hLn hJL hZ
  obtain ⟨hJJ₁, hJ₁eq⟩ := hc.nclIn_le_and_nclIn_eq hL hLn hJL hZ
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
  set T : Subgroup G := (T₀ : Subgroup ↥N).map N.subtype with hTdef
  have hTN : T ≤ N := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := T₀.isPGroup'.map _
  have hTidx : ¬ 2 ∣ (T.subgroupOf N).index := by
    rw [hTdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    exact T₀.not_dvd_index
  have hp2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hc.escape.ne_two
  obtain ⟨hST, hT1⟩ := twoCore_le_of_sylowTwo hc.escape.maxTwoLocal_H.1 hNH₁
    ((pCoreOf_le_glbPrimeCore Nat.prime_two hp2 H₁).trans hON) hTN hT2 hTidx
  have hJT : nclIn H₁ X ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_sylowTwo_of_commutator_le hTN (hNJ.trans hST)
  have hQT : pCoreOf 2 M ≤ Subgroup.normalizer (T : Set G) :=
    ((h3₁.twoCore_M_le h3₁.twoCore_inf).trans hST).trans Subgroup.le_normalizer
  have hloc : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H₁ := fun C hCT hC hchar =>
    normalizer_le_of_forall_maxTwoLocal_eq hT2 hJT (sup_le (bot_le : (⊥ : Subgroup G) ≤ _) hQT)
      (fun H₂ hH₂ hJH₂ hRQ => eq_of_maxTwoLocal_of_kMax h3₁ hc.liftX_le hd.d1LiftX_ne_bot hXH₁
        hJJ₁ hJ₁eq (fun H₃ h1 h2 h3 _ => hmax H₃ h1 h2 h3) H₂ hH₂ hJH₂ hRQ) hCT hC hchar
  obtain ⟨hDM, hMD, hQD, -⟩ := pCoreCentralizerPreimage_facts p M
  exact h3₁.false_of_normal_inf_le_sup_of hXp hXH₁ hNH₁ (hXH₁.trans hH₁N) hTN hT2 hTidx hT1 hloc
    hDM hMD hQD hND (hc.pCoreCentralizer_inf_le hK h84 hD2 hY hWK hU3 h3₁ hLn hJL ψ hψ) hCGT hD2

end D1OneLieKZeroData

end CFSG.AGLEmbedding
