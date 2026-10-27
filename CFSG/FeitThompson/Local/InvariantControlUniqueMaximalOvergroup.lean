module

public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.SharedFittingRankBound
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.PrimeFixedKernelsEqualFitting
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientSylowNormalizer
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] [Finite G] {p d : ℕ} {M B : Subgroup G}

theorem fittingRaw_le_sup_pComplCore {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    {S : Subgroup X} (hS : Nat.card ↥S = p ^ (Nat.card X).factorization p) :
    fittingRaw X ≤ S ⊔ pComplCore p X := by
  have := Fact.mk hp
  rw [fittingRaw_eq_iSup_pCore]
  refine iSup₂_le fun q hq => ?_
  have hq' : q.Prime := hq
  have := Fact.mk hq'
  rcases eq_or_ne q p with rfl | hqp
  · exact le_sup_of_le_left
      (IsPGroup.le_sylow_of_normal (isPGroup_pCore hq' X) (Sylow.ofCard S hS))
  · refine le_sup_of_le_right (le_pComplCore (pCore_normal q X) ?_)
    intro hmem
    obtain ⟨n, hn⟩ := (isPGroup_pCore hq' X).exists_card_eq
    have hdvd : p ∣ q ^ n := hn ▸ Nat.dvd_of_mem_primeFactors hmem
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq').1 (hp.dvd_of_dvd_pow hdvd)).symm

theorem mixedFitting_le_sup_pComplCoreIn (hp : p.Prime) {H R : Subgroup G} (hRH : R ≤ H)
    (hRcard : Nat.card ↥R = p ^ (Nat.card ↥H).factorization p) :
    mixedFitting H ≤ R ⊔ pComplCoreIn p H := by
  have hR' : Nat.card ↥(R.subgroupOf H) = p ^ (Nat.card ↥H).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv, hRcard]
  have h := Subgroup.map_mono (f := H.subtype) (fittingRaw_le_sup_pComplCore hp hR')
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRH] at h
  rwa [mixedFitting_eq, pComplCoreIn_eq]

theorem elementaryAbelianPRank_fittingRaw_eq (hp : p.Prime) (H : Subgroup G) :
    elementaryAbelianPRank p ↥(fittingRaw ↥H) = elementaryAbelianPRank p ↥(mixedFitting H) :=
  elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
    ((Subgroup.equivMapOfInjective (fittingRaw ↥H) H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (mixedFitting_eq H).symm))

theorem commutator_le_mixedFitting {H : Subgroup G} (hsolv : Group.IsSolvable ↥H)
    (hodd : Odd (Nat.card ↥H))
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(mixedFitting H) ≤ 2) :
    ⁅H, H⁆ ≤ mixedFitting H := by
  have := hsolv
  have h := commutator_le_fittingRaw (G := ↥H) hodd
    (fun q hq => (elementaryAbelianPRank_fittingRaw_eq hq H).le.trans (hrank q hq))
  rw [← Subgroup.map_subtype_commutator, mixedFitting_eq]
  exact Subgroup.map_mono h

theorem le_sup_normalizer_of_le_normalizer (hp : p.Prime) {H T R : Subgroup G} (hTH : T ≤ H)
    (hHT : H ≤ normalizer (T : Set G)) (hRT : R ≤ T)
    (hRcard : Nat.card ↥R = p ^ (Nat.card ↥H).factorization p) :
    H ≤ T ⊔ normalizer (R : Set G) := by
  have := Fact.mk hp
  have hRH : R ≤ H := hRT.trans hTH
  have hTn : (T.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hTH]
    intro h k hh hk
    exact Subgroup.le_normalizer_iff.1 hHT k hk h hh
  have hcard : Nat.card ↥(R.subgroupOf H)
      = p ^ (Nat.card ↥(T.subgroupOf H)).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv]
    exact natCard_eq_pow_factorization_of_le_of_le hp hRT hTH hRcard
  have hfr := normalizer_sup_eq_top_of_normal (X := ↥H) (p := p)
    (R := T.subgroupOf H) (P := R.subgroupOf H) (Subgroup.subgroupOf_mono H hRT) hcard
  have key := congrArg (fun K : Subgroup ↥H => K.map H.subtype) hfr
  simp only [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hTH,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at key
  rw [← key, ← Subgroup.subgroupOf_normalizer_eq hRH, Subgroup.subgroupOf_map_subtype]
  exact sup_le (le_sup_of_le_right inf_le_left) le_sup_left

theorem isUniqueMaximalOvergroup_of_control_le [IsSimpleGroup G] (hp : p.Prime)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hB : ⊥ < B) (hBp : IsPGroup p ↥B) (hBM : B ≤ M)
    (hcontrol : ∀ K : Subgroup G, p.Coprime (Nat.card ↥K) →
      B ≤ normalizer (K : Set G) → K ≤ M) :
    IsUniqueMaximalOvergroup B M := by
  refine ⟨hM, hBM, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨N₀, hN₀, hBN₀, hN₀M⟩ := hcon
  have : Nonempty {H : Subgroup G // IsCoatom H ∧ B ≤ H ∧ H ≠ M} := ⟨⟨N₀, hN₀, hBN₀, hN₀M⟩⟩
  obtain ⟨⟨H, hH, hBH, hHM⟩, hmaxc⟩ := Finite.exists_max
    (fun x : {H : Subgroup G // IsCoatom H ∧ B ≤ H ∧ H ≠ M} =>
      (Nat.card ((x : Subgroup G) ⊓ M : Subgroup G)).factorization p)
  obtain ⟨R, hBR, hRHM, hRcard⟩ :=
    exists_le_natCard_eq_pow_factorization hp (le_inf hBH hBM) hBp
  obtain ⟨P, hRP, hPM, hPcard⟩ := exists_le_natCard_eq_pow_factorization hp
    (hRHM.trans inf_le_right) (IsPGroup.of_card hRcard)
  have hNP : normalizer (P : Set G) ≤ M :=
    normalizer_le_of_control_of_coprime hna hodd hsolv hM hp hPM hPcard hB (hBR.trans hRP) hcontrol
  have hmax' : ∀ D : Subgroup G, IsCoatom D → D ≠ M → B ≤ D →
      p ^ (Nat.card (D ⊓ M : Subgroup G)).factorization p ≤
        p ^ (Nat.card (H ⊓ M : Subgroup G)).factorization p :=
    fun D hD hDM hBD => Nat.pow_le_pow_right hp.one_lt.le (hmaxc ⟨D, hD, hBD, hDM⟩)
  have hNR : normalizer (R : Set G) ≤ M :=
    normalizer_le_of_maximal_inf hp hM hB hmax' hBR hRcard hRP hPM hPcard hNP
  have hRH : R ≤ H := hRHM.trans inf_le_left
  have hRM : R ≤ M := hRHM.trans inf_le_right
  have hRHcard : Nat.card ↥R = p ^ (Nat.card ↥H).factorization p :=
    natCard_eq_pow_factorization_of_inf_of_normalizer_le (M := M) hp hRH hRcard hNR
  set D : Subgroup G := pComplCoreIn p H
  have hDM : D ≤ M :=
    hcontrol D (hp.coprime_iff_not_dvd.2 (not_dvd_natCard_pComplCoreIn hp H))
      (hBH.trans (le_normalizer_pComplCoreIn p H))
  have hDH : D ≤ H := pComplCoreIn_le p H
  have hFRD : mixedFitting H ≤ R ⊔ D := mixedFitting_le_sup_pComplCoreIn hp hRH hRHcard
  have hFM : mixedFitting H ≤ M := hFRD.trans (sup_le hRM hDM)
  have hHodd : Odd (Nat.card ↥H) := hodd.of_dvd_nat H.card_subgroup_dvd_card
  have hcomm : ⁅H, H⁆ ≤ R ⊔ D :=
    (commutator_le_mixedFitting (hsolv H hH.1) hHodd
      (forall_prime_elementaryAbelianPRank_mixedFitting_le_two hna hodd hsolv hH hM hHM
        hFM)).trans hFRD
  have hHnorm : H ≤ normalizer ((R ⊔ D : Subgroup G) : Set G) :=
    le_normalizer_of_commutator_le (sup_le hRH hDH) hcomm
  have hle : H ≤ M :=
    (le_sup_normalizer_of_le_normalizer hp (sup_le hRH hDH) hHnorm le_sup_left hRHcard).trans
      (sup_le (sup_le hRM hDM) hNR)
  rcases eq_or_lt_of_le hle with h | h
  · exact hHM h
  · exact hM.1 (hH.2 M h)

theorem isUniqueMaximalOvergroup_of_control_le_elementaryAbelian [IsSimpleGroup G] (hp : p.Prime)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hBe : IsElementaryAbelian p B) (hBcard : Nat.card ↥B = p ^ d) (hd : 2 ≤ d)
    (hBM : B ≤ M)
    (hcontrol : ∀ K : Subgroup G, p.Coprime (Nat.card ↥K) →
      B ≤ normalizer (K : Set G) → K ≤ M) :
    IsUniqueMaximalOvergroup B M := by
  refine isUniqueMaximalOvergroup_of_control_le hp hna hodd hsolv hM ?_ hBe.isPGroup hBM hcontrol
  rw [bot_lt_iff_ne_bot, Ne, ← Subgroup.card_eq_one, hBcard]
  have : 1 < p ^ d := Nat.one_lt_pow (by omega) hp.one_lt
  omega

theorem isUniqueMaximalOvergroup_of_control_le_pi [IsSimpleGroup G] (hp : p.Prime)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hBiso : Nonempty (↥B ≃* (Fin d → Multiplicative (ZMod p)))) (hd : 2 ≤ d)
    (hBM : B ≤ M)
    (hcontrol : ∀ K : Subgroup G, p.Coprime (Nat.card ↥K) →
      B ≤ normalizer (K : Set G) → K ≤ M) :
    IsUniqueMaximalOvergroup B M := by
  have := Fact.mk hp
  obtain ⟨e⟩ := hBiso
  have hBcard : Nat.card ↥B = p ^ d := by rw [Nat.card_congr e.toEquiv]; simp
  exact isUniqueMaximalOvergroup_of_control_le_elementaryAbelian hp hna hodd hsolv hM
    (isElementaryAbelian_of_nonempty_mulEquiv_pi ⟨e⟩) hBcard hd hBM hcontrol

end

end CFSG.FeitThompson
