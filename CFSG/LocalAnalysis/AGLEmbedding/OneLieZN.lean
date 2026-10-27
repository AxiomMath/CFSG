module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZNAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1OneLieZZaCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
    d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) →
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ → False

@[expose] def D1OneLieZZbCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧ L ≠ K) →
    d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) →
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ → False

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.exists_mem_d1PlusCore (hd : D1OneLieData p P M H R Rbar K) :
    ∃ z : G, z ∈ R ∧ z ∈ d1PlusCore p H K ∧ orderOf z = p := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨zb, hzbR, -, hzbp, hzbc⟩ := hd.z
  rw [hd.cfg.rbar] at hzbR
  obtain ⟨r, hr, rfl⟩ := hzbR
  refine ⟨r, hr, ⟨r, hzbc, rfl⟩, orderOf_eq_prime ?_ ?_⟩
  · have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) (r ^ p) = 1 := by
      have h0 := pow_orderOf_eq_one (QuotientGroup.mk' (primeComplementCore (G := H) p) r)
      rw [hzbp] at h0
      rw [map_pow]
      exact h0
    have hN : ((r ^ p : H) : G) ∈ GLBPrimeCore p H :=
      (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have hR : ((r ^ p : H) : G) ∈ R := by
      rw [Subgroup.coe_pow]
      exact R.pow_mem hr p
    have hcop : (orderOf ((r ^ p : H) : G)).Coprime p :=
      Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard _ hN)
        (glbPrimeCore_coprime p H).symm
    have h2 := eq_one_of_mem_of_coprime hd.cfg.ext.isPGroup hR hcop
    rwa [Subgroup.coe_pow] at h2
  · intro h1
    have hr1 : r = 1 := Subtype.ext h1
    rw [hr1, map_one, orderOf_one] at hzbp
    exact hp.one_lt.ne hzbp

theorem D1OneLieData.false_of_not_mem_normal (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    {C' : Subgroup G} (hMC' : M ≤ Subgroup.normalizer (C' : Set G))
    (hNJC' : ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ ≤ C')
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) (hzC' : z ∉ C') :
    False :=
  hd.toCore.false_of_not_mem_normal (hd.toPhaseThree hK) h84 hCGT hD2 huniq hY
    (hd.centralizer_d1MapPCore_le hK h84 hD2 hY hU3) hMC' hNJC' hzR hzN hzp hzC'

theorem D1OneLieData.mem_nclIn_commutator (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) :
    z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ := by
  by_contra hz
  exact hd.false_of_not_mem_normal hK h84 hCGT hD2 huniq hY hU3 (le_normalizer_nclIn M _)
    (le_nclIn ((hd.commutator_nclIn_le hK h84 hD2 hY).trans (hd.toPhaseThree hK).twoCore_le))
    hzR hzN hzp hz

end Config

theorem d1OneLieZZa_of_core (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hc : D1OneLieZZaCore) :
    D1OneLieZZa := by
  intro G _ _ p P M H R Rbar K hd huniq hY hI hWK hU hno
  obtain ⟨z, hzR, hzN, hzp⟩ := hd.exists_mem_d1PlusCore
  exact hc G p P M H R Rbar K hd huniq hY hI hWK hU hno z hzR hzN hzp
    (hd.mem_nclIn_commutator hK h84 hCGT hD2 (huniq.toUniqueOver hd.cfg.ext.isPGroup) hY hU
      hzR hzN hzp)

theorem d1OneLieZZb_of_core (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hc : D1OneLieZZbCore) :
    D1OneLieZZb := by
  intro G _ _ p P M H R Rbar K hd huniq hY hI hWK hU hno
  obtain ⟨z, hzR, hzN, hzp⟩ := hd.exists_mem_d1PlusCore
  exact hc G p P M H R Rbar K hd huniq hY hI hWK hU hno z hzR hzN hzp
    (hd.mem_nclIn_commutator hK h84 hCGT hD2 (huniq.toUniqueOver hd.cfg.ext.isPGroup) hY hU
      hzR hzN hzp)

theorem d1OneLieResidue_of_core (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hc : D1OneLieZZaCore ∧ D1OneLieZZbCore ∧
        D1OneLieU3Z) :
    D1OneLieResidue :=
  ⟨d1OneLieZZa_of_core hK h84 hCGT hD2 hc.1, d1OneLieZZb_of_core hK h84 hCGT hD2 hc.2.1, hc.2.2⟩

end CFSG.AGLEmbedding
