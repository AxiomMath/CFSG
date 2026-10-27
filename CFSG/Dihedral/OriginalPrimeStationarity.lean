module

public import CFSG.Dihedral.OriginalASevenOddCore
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.Dihedral.StationarySylowCore
public import CFSG.Dihedral.GorensteinWalter.PSL2OddCentralizerNormalizer
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.Dihedral.PrimeClassPartition

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem prime_sylow_stationary_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G))) := by
  have hR : d.R ≠ ⊥ := by
    intro h
    have hd := hp.2
    rw [h, Subgroup.card_bot] at hd
    exact hp.1.not_dvd_one hd
  have hRcard := d.R_card_of_aSeven_model hR e
  have hp3 : p = 3 := by
    have hd := hp.2
    rw [hRcard] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hp1 | hp3
    · exact (hp.1.ne_one hp1).elim
    · exact hp3
  have hPeq : P = d.R :=
    isSylowIn_eq_of_card_prime p hp.1 P d.R hP (hRcard.trans hp3.symm)
  obtain ⟨f, ht⟩ := d.aSeven_equiv_aligned e
  have hcore := d.N_oddCore_of_aligned_aSeven_model hR f ht
  rw [hPeq]
  change IsSylowIn p d.R (oddCoreOf d.N)
  rw [hcore]
  exact hPeq ▸ hP

theorem prime_sylow_stationary_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G))) := by
  have hPne := isSylowIn_ne_bot p hp.1 P d.R hP hp.2
  have hmapne : P.map e.toMonoidHom ≠ ⊥ := by
    intro h
    exact hPne ((Subgroup.map_eq_bot_iff_of_injective P e.injective).mp h)
  have hPodd : Odd (Nat.card P) :=
    d.R_odd.of_dvd_nat (Subgroup.card_dvd_of_le hP.1)
  have hmapodd : ∀ x : PSL2 K, x ∈ P.map e.toMonoidHom → Odd (orderOf x) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change Odd (orderOf (e y))
    rw [e.orderOf_eq]
    exact hPodd.of_dvd_nat (P.orderOf_dvd_natCard hy)
  have hmapC : P.map e.toMonoidHom ≤ Subgroup.centralizer ({e d.t} : Set (PSL2 K)) := by
    rw [← centralizer_singleton_map]
    apply Subgroup.map_mono
    simpa only [d.centralizer, t] using hP.1.trans d.R_le
  have ht : BenderSuzuki.PFAppendixIII.IsInvolution (e d.t) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact d.t_isInvolution_general.1 (e.injective (by simpa using h))
    · simpa only [map_pow, map_one] using congrArg e d.t_isInvolution_general.2
  have hnormalizer := psl2_odd_centralizer_normalizer hK ht (P.map e.toMonoidHom)
    hmapne hmapodd hmapC
  have hNmap : (Subgroup.normalizer (P : Set G)).map e.toMonoidHom =
      d.C.map e.toMonoidHom := by
    rw [Subgroup.map_normalizer_eq_of_bijective P e.bijective, hnormalizer]
    rw [show d.C = Subgroup.centralizer ({d.t} : Set G) by
      simpa only [t] using d.centralizer, centralizer_singleton_map]
  have hN : Subgroup.normalizer (P : Set G) = d.C :=
    Subgroup.map_injective e.injective hNmap
  rw [hN, d.centralizer_oddCore_eq_R]
  exact hP

theorem prime_sylow_stationary [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G))) := by
  rcases gorenstein_walter G hnonab d.S
      ⟨2 ^ (d.n - 1), d.sylow_mulEquiv_dihedral⟩ with hA | hL
  · exact d.prime_sylow_stationary_of_aSeven_model hA.some p hp P hP
  · obtain ⟨r, k, hr, hrodd, hsize, ⟨e⟩⟩ := hL
    let _ : Fact r.Prime := hr
    have hk : k ≠ 0 := by
      intro h
      simp [h] at hsize
    have hK : IsOddPrimePower (Nat.card (GaloisField r k)) :=
      ⟨r, k, hr.out, hrodd, by omega, GaloisField.card r k hk⟩
    exact d.prime_sylow_stationary_of_psl2_model (GaloisField r k) hK e p hp P hP

theorem sigma_two_eq_empty [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : sigma 2 d.R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hprime, P, hP, hpred⟩ := (mem_sigma_iff 2 p d.R).mp hp
  exact hpred.2 (d.prime_sylow_stationary hnonab p hprime P hP)

theorem sigma_three_eq_empty [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : sigma 3 d.R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hprime, P, hP, hpred⟩ := (mem_sigma_iff 3 p d.R).mp hp
  exact hpred.2 (d.prime_sylow_stationary hnonab p hprime P hP)

theorem stationary_prime_classes_partition [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    primeSupport d.R = sigma 0 d.R ∪ sigma 1 d.R ∧ Disjoint (sigma 0 d.R) (sigma 1 d.R) := by
  refine ⟨?_, sigma_pairwise_disjoint d.R (by decide : (0 : Fin 4) ≠ 1)⟩
  ext p
  constructor
  · intro hp
    obtain ⟨P, hP⟩ := exists_isSylowIn p d.R
    have hstationary := d.prime_sylow_stationary hnonab p hp P hP
    by_cases hcomp : HasNormalTwoComplement (Subgroup.normalizer (P : Set G))
    · exact Or.inl ((mem_sigma_iff_of_isSylowIn 0 p P d.R hP).mpr
        ⟨hp, hstationary, hcomp⟩)
    · exact Or.inr ((mem_sigma_iff_of_isSylowIn 1 p P d.R hP).mpr
        ⟨hp, hstationary, hcomp⟩)
  · intro hp
    rcases hp with hp | hp
    · exact ((mem_sigma_iff 0 p d.R).mp hp).1
    · exact ((mem_sigma_iff 1 p d.R).mp hp).1

theorem prime_sylow_core_and_no_growth [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G))) ∧
    P = (Assembly.pCore p (oddCoreOf (Subgroup.normalizer (P : Set G)))).map
      (oddCoreOf (Subgroup.normalizer (P : Set G))).subtype ∧
    ∀ Q : Subgroup G, IsSylowIn p Q (oddCoreOf (Subgroup.normalizer (P : Set G))) → Q = P := by
  have hstationary := d.prime_sylow_stationary hnonab p hp P hP
  obtain ⟨hcore, hall⟩ := stationary_sylow_core_and_unique p hp.1 P hstationary
  refine ⟨hstationary, hcore, ?_⟩
  intro Q hQ
  have hQP := hall Q hQ.2.1 hQ.1
  exact le_antisymm hQP (by
    have heq := hQ.2.2 P hstationary.1 hstationary.2.1 hQP
    exact heq ▸ le_rfl)

theorem prime_stationarity_and_no_growth [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    sigma 2 d.R = ∅ ∧ sigma 3 d.R = ∅ ∧
    primeSupport d.R = sigma 0 d.R ∪ sigma 1 d.R ∧ Disjoint (sigma 0 d.R) (sigma 1 d.R) ∧
    (∀ p ∈ primeSupport d.R, ∀ P : Subgroup G, IsSylowIn p P d.R →
      ∀ T : Subgroup G, IsSylowIn 2 T (d.C ⊓ Subgroup.normalizer (P : Set G)) →
      ∀ Q : Subgroup G, IsSylowIn p Q (oddCoreOf (Subgroup.normalizer (P : Set G))) →
        P ≤ Q → NormalizedBy Q T →
        IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G))) ∧
        P = (Assembly.pCore p (oddCoreOf (Subgroup.normalizer (P : Set G)))).map
          (oddCoreOf (Subgroup.normalizer (P : Set G))).subtype ∧ Q = P) := by
  have hpart := d.stationary_prime_classes_partition hnonab
  refine ⟨d.sigma_two_eq_empty hnonab, d.sigma_three_eq_empty hnonab, hpart.1, hpart.2, ?_⟩
  intro p hp P hP T _hT Q hQ _hPQ _hQT
  have h := d.prime_sylow_core_and_no_growth hnonab p hp P hP
  exact ⟨h.1, h.2.1, h.2.2 Q hQ⟩

end CFSG.DihedralBlueprint.OriginalData
