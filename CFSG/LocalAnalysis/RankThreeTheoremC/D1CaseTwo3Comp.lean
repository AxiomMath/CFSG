module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ReducedA
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Families
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3DataU
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem D1CaseTwoData3.of_central (hcen : D1CaseTwoCentral3 G) {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig3 p P M H R Rbar)
    (hcyc : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    D1CaseTwoData3 p P M H R Rbar :=
  ⟨hcfg, hcyc, fun z hz hm => hcen p P M H R Rbar hcfg hcyc z hz hm⟩

@[expose] def D1HasNormalCyclic (p : ℕ) (R : Subgroup G) : Prop :=
  ∃ S : Subgroup G, S ≤ R ∧ (∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S) ∧ IsCyclic S ∧ p < Nat.card S

@[expose] def CaseTwoGroupFacts : Prop :=
  ∀ (p : ℕ) (L : Type) [Group L] [Finite L], IsCaseTwoGroup p L →
    p ^ 2 ∣ Nat.card L ∧ (p = 3 → 7 ∣ Nat.card L) ∧ (p = 5 → 41 ∣ Nat.card L)

@[expose] def KFactKlingenSylowNormalCyclic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (d : TauCeti.ValidLieTypeIndex), IsKlingenIndex p d →
    ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* CatGroup d) → ∀ (T : Sylow p K)
      (N : Subgroup K), N ≤ (T : Subgroup K) → (T : Subgroup K) ≤ Subgroup.normalizer (N : Set K) →
      IsCyclic N → Nat.card N ≤ p

structure D1CaseTwoComp3 (G : Type) [Group G] [Finite G] : Prop where
  central : D1CaseTwoCentral3 G
  notKlingen : D1CaseThreeNotKlingen3 G
  other : D1CaseThreeKlingenOther3 G
  klingenLocal : KFactKlingenLocal
  model : StmtKlingenModel
  klingenSylow : KFactKlingenSylowNormalCyclic
  grp : CaseTwoGroupFacts

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataU.exists_normalCyclic_of_comp (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hGrp : CaseTwoGroupFacts) (hd : D1CaseTwoDataU p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) :
    ∃ S : Subgroup G, S ≤ R ∧ (∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S) ∧ IsCyclic S ∧ p < Nat.card S ∧
      (S.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hiso : IsCaseTwoGroup p L :=
    hd.cfg.red.isCaseTwoGroup_of_not_le3 hd.cfg.catalog hOut hS hd.cyclic hd.rank hL hLX
  obtain ⟨TL, hTL⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  set D : Subgroup (H ⧸ primeComplementCore (G := H) p) := (Rbar : Subgroup _) ⊓ L with hD
  have hDcard : p ^ 2 ≤ Nat.card D := by
    have h1 : Nat.card D = Nat.card (TL : Subgroup L) := by
      rw [← hTL, Subgroup.card_map_of_injective L.subtype_injective]
    have h2 : 2 ≤ (Nat.card L).factorization p :=
      (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (hGrp p L hiso).1
    rw [h1, TL.card_eq_multiplicity]
    exact Nat.pow_le_pow_right hp.pos h2
  have hDnorm : ∀ r ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), ∀ x ∈ D,
      r * x * r⁻¹ ∈ D := by
    rintro r hr x ⟨hxR, hxL⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hxR) (Subgroup.inv_mem _ hr), ?_⟩
    have hrN : r ∈ Subgroup.normalizer (L : Set _) := by
      simpa using hd.cfg.red.conj_mem_normalizer_component hL hr 1
    exact (Subgroup.mem_normalizer_iff.mp hrN x).mp hxL
  have hRH : R ≤ H := hd.cfg.ext.le_H
  obtain ⟨S, hSH, hSR, hSmap, hSall, ψ, -⟩ := exists_lift_of_le_map hp hRH hd.cfg.ext.isPGroup
    (primeComplementCore (G := H) p) (primeComplementCore_coprime p) (Sbar := D)
    (inf_le_left.trans hd.cfg.rbar.le)
  refine ⟨S, hSR, ?_, ?_, ?_, hSmap⟩
  · intro r hr s hs
    have hrH : r ∈ H := hRH hr
    have hsH : s ∈ H := hSH hs
    have hmem : QuotientGroup.mk' (primeComplementCore (G := H) p)
        (⟨r, hrH⟩ * ⟨s, hsH⟩ * ⟨r, hrH⟩⁻¹) ∈ D := by
      rw [map_mul, map_mul, map_inv]
      refine hDnorm _ ?_ _ ?_
      · rw [hd.cfg.rbar]
        exact Subgroup.mem_map_of_mem _ (show (⟨r, hrH⟩ : H) ∈ R.subgroupOf H from hr)
      · rw [← hSmap]
        exact Subgroup.mem_map_of_mem _ (show (⟨s, hsH⟩ : H) ∈ S.subgroupOf H from hs)
    exact hSall (⟨r, hrH⟩ * ⟨s, hsH⟩ * ⟨r, hrH⟩⁻¹)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr (hSR hs)) (Subgroup.inv_mem _ hr)) hmem
  · exact (ψ.isCyclic).mpr (hd.cyclic L hL)
  · rw [Nat.card_congr ψ.toEquiv]
    exact lt_of_lt_of_le (by nlinarith [hp.two_le]) hDcard

theorem D1CaseTwoData3.exists_normalCyclic (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hGrp : CaseTwoGroupFacts) (hd : D1CaseTwoData3 p P M H R Rbar) : D1HasNormalCyclic p R := by
  obtain ⟨L, hL, hLX⟩ := hd.exists_not_le hOut
  obtain ⟨S, hSR, hSn, hSc, hSp, -⟩ := hd.toU.exists_normalCyclic_of_comp hOut hS hGrp hL hLX
  exact ⟨S, hSR, hSn, hSc, hSp⟩

theorem D1CaseTwoComp3.false_of_caseThree (hC : D1CaseTwoComp3 G) {p : ℕ} {P : Sylow p G}
    {M H' R : Subgroup G} {Rbar' : Sylow p (H' ⧸ primeComplementCore (G := H') p)}
    (hcfg' : D1ComponentConfig3 p P M H' R Rbar') (hNC : D1HasNormalCyclic p R)
    {K' : Subgroup (H' ⧸ primeComplementCore (G := H') p)} (hK' : IsComponentOf K' ⊤)
    (huniq' : ∀ L : Subgroup (H' ⧸ primeComplementCore (G := H') p), IsComponentOf L ⊤ → L = K')
    (hnc' : ¬ IsCyclic ((Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ⊓ K' :
      Subgroup (H' ⧸ primeComplementCore (G := H') p)))
    (hcent' : ∀ c ∈ (Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ⊓
        Subgroup.centralizer (K' : Set (H' ⧸ primeComplementCore (G := H') p)),
      orderOf c = p → c ∈ (Subgroup.center K').map K'.subtype) : False := by
  have hp : p.Prime := hcfg'.red.prime
  have : Fact p.Prime := ⟨hp⟩
  by_cases hKD' : HasKlingenData p Rbar'
      (((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p)))
  swap
  · exact hC.notKlingen p P M H' R Rbar' hcfg' K' hK' huniq' hnc' hcent' hKD'
  by_cases hsp' : IsKlingenComponent p K'
  swap
  · exact hC.other p P M H' R Rbar' hcfg' K' hK' huniq' hnc' hcent' hKD' hsp'
  obtain ⟨d', hd', ⟨e'⟩⟩ := hsp'
  have hZ' : Subgroup.center K' = ⊥ :=
    hC.model.center K' p d' hcfg'.loc.ne_two hd' hK'.2.2 (hcfg'.isPGroup_center hK') ⟨e'⟩
  have eK' : K' ≃* CatGroup d' :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ'.symm)).trans e'
  have hC' := hcfg'.centralizer_eq_bot hK' huniq' hcent' hZ'
  have hKn' : K'.Normal := normal_of_forall_isComponentOf_eq hK' huniq'
  have hOut' := hC.klingenLocal.outer p hcfg'.loc.ne_two d' hd' K' ⟨eK'⟩
  set π' := QuotientGroup.mk' (primeComplementCore (G := H') p) with hπ'
  have hRK : (R.subgroupOf H').map π' ≤ K' := by
    have : Finite (MulAut K') := MulEquiv.finite_left
    intro x hx
    rw [← hcfg'.rbar] at hx
    obtain ⟨n, hn⟩ := Rbar'.isPGroup' ⟨x, hx⟩
    have hxn : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hmem := mem_sup_centralizer_of_pow hp hOut' hxn
    rwa [hC', sup_bot_eq] at hmem
  obtain ⟨S, hSR, hSnorm, hScyc, hSp⟩ := hNC
  have hRH' : R ≤ H' := hcfg'.ext.le_H
  have hSH' : S ≤ H' := hSR.trans hRH'
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar' hKn'.isSubnormal
  have hTR : ∀ t : K', t ∈ (T : Subgroup K') ↔ (t : H' ⧸ primeComplementCore (G := H') p) ∈
      (Rbar' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) := by
    intro t
    constructor
    · intro ht
      have : (t : H' ⧸ primeComplementCore (G := H') p) ∈ (T : Subgroup K').map K'.subtype :=
        ⟨t, ht, rfl⟩
      rw [hT] at this
      exact this.1
    · intro ht
      have : (t : H' ⧸ primeComplementCore (G := H') p) ∈ (Rbar' : Subgroup _) ⊓ K' :=
        ⟨ht, t.2⟩
      rw [← hT] at this
      obtain ⟨t', ht', hteq⟩ := this
      rwa [← Subtype.ext hteq]
  set A : Subgroup (H' ⧸ primeComplementCore (G := H') p) := (S.subgroupOf H').map π' with hA
  have hAR : A ≤ (Rbar' : Subgroup _) := by
    rw [hcfg'.rbar]
    exact Subgroup.map_mono fun x hx => hSR hx
  have hAK : A ≤ K' := hAR.trans (by rw [hcfg'.rbar]; exact hRK)
  have hSp' : IsPGroup p (S.subgroupOf H') := (hcfg'.ext.isPGroup.to_le hSR).comap_subtype
  have hAcard : Nat.card A = Nat.card S := by
    rw [hA, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hSp']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH').toEquiv
  have hAcyc : IsCyclic A := by
    have : IsCyclic (S.subgroupOf H') :=
      (Subgroup.subgroupOfEquivOfLe hSH').isCyclic.mpr hScyc
    exact isCyclic_of_surjective (π'.subgroupMap (S.subgroupOf H'))
      (π'.subgroupMap_surjective _)
  set N : Subgroup K' := A.subgroupOf K' with hN
  have hNcyc : IsCyclic N := (Subgroup.subgroupOfEquivOfLe hAK).isCyclic.mpr hAcyc
  have hNcard : Nat.card N = Nat.card S := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hAcard]
  have hNT : N ≤ (T : Subgroup K') := fun x hx => (hTR x).mpr (hAR hx)
  have hconj : ∀ t ∈ (T : Subgroup K'), ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    intro t ht n hn
    have hnA : (n : H' ⧸ primeComplementCore (G := H') p) ∈ A := hn
    obtain ⟨s, hs, hsn⟩ := hnA
    have htR := (hTR t).mp ht
    rw [hcfg'.rbar] at htR
    obtain ⟨r, hr, hrt⟩ := htR
    have hrsr : r * s * r⁻¹ ∈ S.subgroupOf H' := by
      show ((r * s * r⁻¹ : H') : G) ∈ S
      exact hSnorm (r : G) hr (s : G) hs
    show ((t * n * t⁻¹ : K') : H' ⧸ primeComplementCore (G := H') p) ∈ A
    refine ⟨r * s * r⁻¹, hrsr, ?_⟩
    rw [map_mul, map_mul, map_inv]
    change π' r * π' s * (π' r)⁻¹ = (t : _) * (n : _) * (t : _)⁻¹
    rw [hrt, hsn]
    rfl
  have hTN : (T : Subgroup K') ≤ Subgroup.normalizer (N : Set K') := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact fun hn => hconj t ht n hn
    · intro hn
      have h1 := hconj t⁻¹ ((T : Subgroup K').inv_mem ht) _ hn
      have e : t⁻¹ * (t * n * t⁻¹) * t⁻¹⁻¹ = n := by group
      rwa [e] at h1
  have hle := hC.klingenSylow p hcfg'.loc.ne_two d' hd' K' ⟨eK'⟩ T N hNT hTN hNcyc
  rw [hNcard] at hle
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
