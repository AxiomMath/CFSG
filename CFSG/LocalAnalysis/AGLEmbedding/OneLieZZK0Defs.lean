module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieKMax
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZCompCloseDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1OneLieZZK0Small : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ → d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    Nat.card R ≤ Nat.card (d1LiftX p H R K) ^ 2 →
    ∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → nclIn H (d1LiftX p H R K) ≤ H₁ →
      pCoreOf 2 M ≤ H₁ →
      Nat.card (nclIn H (d1LiftX p H R K)) < Nat.card (nclIn H₁ (d1LiftX p H R K)) →
      (∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → nclIn H (d1LiftX p H R K) ≤ H₂ →
        pCoreOf 2 M ≤ H₂ →
        Nat.card (nclIn H₂ (d1LiftX p H R K)) ≤ Nat.card (nclIn H₁ (d1LiftX p H R K))) →
      False

@[expose] def D1OneLieZZK0Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ → d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧ L ≠ K) →
    p ^ 2 ∣ Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) →
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ →
    ∀ L : Subgroup G, IsTwoPrimeComponent M L → z ∈ L →
      H ⊓ M ≤ Subgroup.normalizer (L : Set G) →
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ d1PlusCore p H K →
      (∃ m ∈ M, IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj m).toMonoidHom)) →
    Nat.card (d1LiftX p H R K) ^ 2 < Nat.card R →
    ∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → nclIn H (d1LiftX p H R K) ≤ H₁ →
      pCoreOf 2 M ≤ H₁ →
      Nat.card (nclIn H (d1LiftX p H R K)) < Nat.card (nclIn H₁ (d1LiftX p H R K)) →
      (∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → nclIn H (d1LiftX p H R K) ≤ H₂ →
        pCoreOf 2 M ≤ H₂ →
        Nat.card (nclIn H₂ (d1LiftX p H R K)) ≤ Nat.card (nclIn H₁ (d1LiftX p H R K))) →
      False

@[expose] def D1OneLieZZbSlice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ → d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧ L ≠ K) →
    p ^ 2 ∣ Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) →
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ →
    ∀ L : Subgroup G, IsTwoPrimeComponent M L → z ∈ L →
      H ⊓ M ≤ Subgroup.normalizer (L : Set G) →
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ d1PlusCore p H K →
      (∃ m ∈ M, IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj m).toMonoidHom)) → False

theorem d1OneLieZZbSlice_of (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock) (hSmall : D1OneLieZZK0Small)
    (hBig : D1OneLieZZK0Big) : D1OneLieZZbSlice := by
  intro G _ _ p P M H R Rbar K hd hJ hY hWK hU3 hno hI hsq z hzR hzN hzp hzJ L hL hzL hLK hLN
    hLm
  have h3 := hd.toPhaseThree hK
  obtain ⟨H₁, ⟨hH₁, hJH₁, hQH₁⟩, hmax⟩ := Set.exists_max_image
    {H₂ : Subgroup G | GLBIsMaxTwoLocal H₂ ∧ nclIn H (d1LiftX p H R K) ≤ H₂ ∧
      pCoreOf 2 M ≤ H₂}
    (fun H₂ => Nat.card (nclIn H₂ (d1LiftX p H R K))) (Set.toFinite _)
    ⟨H, hd.cfg.ext.maxTwoLocal_H, nclIn_le_self H _,
      h3.twoCore_M_le_glbPrimeCore.trans (glbPrimeCore_le p H)⟩
  by_cases hlt : Nat.card (nclIn H (d1LiftX p H R K)) < Nat.card (nclIn H₁ (d1LiftX p H R K))
  · by_cases hc : Nat.card R ≤ Nat.card (d1LiftX p H R K) ^ 2
    · exact hSmall G p P M H R Rbar K hd hJ hY hWK hU3 hc H₁ hH₁ hJH₁ hQH₁ hlt
        fun H₂ h1 h2 h3 => hmax H₂ ⟨h1, h2, h3⟩
    · exact hBig G p P M H R Rbar K hd hJ hY hWK hU3 hno hI hsq z hzR hzN hzp hzJ L hL hzL hLK
        hLN hLm (by omega) H₁ hH₁ hJH₁ hQH₁ hlt fun H₂ h1 h2 h3 => hmax H₂ ⟨h1, h2, h3⟩
  · have hle := not_lt.mp hlt
    obtain ⟨T₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥(d1PlusCore p H K)))
    have hTidx : ¬ 2 ∣ (((T₀ : Subgroup ↥(d1PlusCore p H K)).map
        (d1PlusCore p H K).subtype).subgroupOf (d1PlusCore p H K)).index := by
      rw [Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (d1PlusCore p H K).subtype_injective]
      exact T₀.not_dvd_index
    exact hd.false_of_kMax_self hK h84 hD2 hCGT hY hWK hU3 (R₁ := ⊥)
      (Subgroup.map_subtype_le _) (T₀.isPGroup'.map _) hTidx bot_le
      fun H₂ h1 h2 h3 _ => (hmax H₂ ⟨h1, h2, h3⟩).trans hle

theorem d1OneLieZZbBig_of_slice (h : D1OneLieZZbSlice) : D1OneLieZZbBig := by
  intro G _ _ p P M H R Rbar K hd hJ hY hWK hU3 hno hI hsq z hzR hzN hzp hzJ L hL hzL hLK hLN hLm
    _ _ _ _ _ _ _ _ _ _ _
  exact h G p P M H R Rbar K hd hJ hY hWK hU3 hno hI hsq z hzR hzN hzp hzJ L hL hzL hLK hLN hLm

end CFSG.AGLEmbedding
